#!/usr/bin/env python3
"""Collapse a Lean build log into a deduplicated diagnostic inventory.

A `lake build` log for this project is several thousand lines.  Almost all of
it is a handful of distinct diagnostics repeated once per module rebuild, which
makes the tail of a CI log useless for answering the only question that matters
after a red run: *which source positions are still noisy?*

This script groups every `warning:`/`error:`/`info:` diagnostic by the source
file it points at, deduplicates identical `file:line:col` positions, and prints
one sorted line per position.  With `--gate PREFIX` it exits non-zero when any
diagnostic points into a source tree whose path starts with `PREFIX`, which is
how the workflow keeps the repository-owned StrongPNT 4.24 port silent.

Lean and Lake have emitted diagnostics in more than one shape over the years:

    warning: Foo/Bar.lean:12:4: This simp argument is unused:
    Foo/Bar.lean:12:4: warning: This simp argument is unused:
    error: Foo/Bar.lean:12:4: Type mismatch

so the position is matched wherever it sits on the line rather than assuming a
single formatter.  Lines with no `file:line:col` at all (`error: build failed`,
`Some required targets logged failures:`) carry no position to fix and are
skipped.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

# `path:line:col` where path ends in `.lean`.  Paths may be absolute (the
# `trace:` lines echo full runner paths) or repository relative.
POSITION = re.compile(r"(?P<path>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+)")
SEVERITY = re.compile(r"\b(?P<severity>warning|error|info):")

# Diagnostics whose text continues on following lines; only the first line
# carries the position, which is all the inventory reports.
SEVERITY_ORDER = {"error": 0, "warning": 1, "info": 2}


def normalize(path: str) -> str:
    """Strip runner-specific prefixes so keys are stable across machines."""
    cleaned = path.lstrip("./")
    for marker in (".lake/packages/",):
        index = cleaned.find(marker)
        if index != -1:
            cleaned = cleaned[index + len(marker) :]
            # `.lake/packages/StrongPNT/StrongPNT/PNT5_Strong.lean` names the
            # package once as a directory and once as the module root.  Drop
            # the outer package directory so the key reads as the module path.
            head, _, tail = cleaned.partition("/")
            if tail.startswith(head + "/"):
                cleaned = tail
            else:
                cleaned = tail or cleaned
            break
    else:
        # Absolute checkout paths, e.g. /home/runner/work/<repo>/<repo>/Foo.lean.
        # The checkout directory name is not fixed, so anchor on the package
        # root that every owned source sits under instead.
        marker = "/RHLean"
        index = cleaned.rfind(marker)
        if index != -1:
            cleaned = cleaned[index + 1 :]
    return cleaned


def collect(log: str) -> dict[str, set[tuple[int, int, str, str]]]:
    """Map source file -> {(line, col, severity, first line of message)}."""
    found: dict[str, set[tuple[int, int, str, str]]] = defaultdict(set)
    lines = log.splitlines()
    for index, raw in enumerate(lines):
        # `trace:` lines echo the whole `lean` command line, including the
        # source path; they are provenance, not diagnostics.
        if raw.lstrip().startswith("trace:"):
            continue
        severity_match = SEVERITY.search(raw)
        if severity_match is None:
            continue
        severity = severity_match.group("severity")
        position = POSITION.search(raw)
        if position is None:
            continue
        message = raw[position.end() :].lstrip(": ").strip()
        # When the formatter puts the severity after the position, the message
        # still begins with `warning:`; drop it so identical diagnostics under
        # the two formatters collapse to one entry.
        message = SEVERITY.sub("", message, count=1).strip()
        # `This simp argument is unused:` names the argument on the following
        # line, and that name is the whole content of the diagnostic.  Pull the
        # first indented continuation line up so the inventory says what to fix
        # rather than only that something needs fixing.
        if message.endswith(":"):
            message = f"{message} {continuation(lines, index)}".strip()
        found[normalize(position.group("path"))].add(
            (int(position.group("line")), int(position.group("col")), severity, message)
        )
    return found


def continuation(lines: list[str], index: int) -> str:
    """First indented, non-blank line after `index`, or the empty string."""
    for raw in lines[index + 1 : index + 4]:
        if not raw.strip():
            continue
        if raw[:1].isspace():
            return " ".join(raw.split())
        return ""
    return ""


def is_noise(entry: tuple[int, int, str, str]) -> bool:
    """Does this diagnostic represent linter churn a patch should remove?

    Warnings and errors always do.  `info` covers two very different things:
    Lean's suggestion mechanism (`Try this: ring_nf`), which is a failed tactic
    reported politely and is exactly the noise being removed, and deliberate
    reports such as the `#print axioms Strong_PNT` audit that upstream keeps at
    the end of the file.  Only the former is gated.
    """
    _line, _col, severity, message = entry
    if severity in ("warning", "error"):
        return True
    return message.startswith("Try this:")


def report(found: dict[str, set[tuple[int, int, str, str]]]) -> None:
    if not found:
        print("No Lean diagnostics with source positions in this build log.")
        return
    for path in sorted(found):
        entries = sorted(
            found[path], key=lambda e: (e[0], e[1], SEVERITY_ORDER.get(e[2], 9))
        )
        print(f"\n{path}  ({len(entries)} distinct)")
        for line, col, severity, message in entries:
            print(f"  {line}:{col}  {severity}: {message}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="path to the captured lake build log")
    parser.add_argument(
        "--gate",
        action="append",
        default=[],
        metavar="PREFIX",
        help="fail when a diagnostic points at a source path starting with PREFIX",
    )
    args = parser.parse_args()

    found = collect(args.log.read_text(errors="replace"))

    if not args.gate:
        print("Deduplicated Lean diagnostic inventory")
        print("=====================================")
        report(found)
        return 0

    offending = {}
    for path, entries in found.items():
        if not any(path.startswith(prefix) for prefix in args.gate):
            continue
        gated = {entry for entry in entries if is_noise(entry)}
        if gated:
            offending[path] = gated
    if offending:
        joined = ", ".join(args.gate)
        print(f"Diagnostics remain in gated sources ({joined}):")
        report(offending)
        print(
            "\nThese sources are rewritten by scripts/strongpnt_424/, so each "
            "position above is fixed by extending those patches."
        )
        return 1
    print(f"No diagnostics in gated sources ({', '.join(args.gate)}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
