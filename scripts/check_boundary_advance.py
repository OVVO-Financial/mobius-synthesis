#!/usr/bin/env python3
"""Fail-closed scope gate for Möbius synthesis research PRs.

A Lean-source PR may pass in either of two ways:

1. quantitatively strengthen the certified bound on the canonical nonzero
   response H_{k,n}; or
2. add a new synthesis theorem whose printed Lean declaration directly invokes
   pre-existing square-block and prime-wheel anchors.

The second lane deliberately allows exact structural progress.  The checker is
not a novelty oracle: it enforces that structural work is genuinely cross-track
and synthesis-facing rather than an isolated reformulation of one initiative.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

FRONTIER_PATH = "boundary/frontier.json"
SYNTHESIS_PATH = "boundary/synthesis.json"
CONTRACT_PATH = "RHLean/Analysis/MobiusSynthesisBoundary.lean"
LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
ALLOWED_KINDS = {"exact_reduction", "power_bound", "rh_scale"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Structural synthesis witnesses must invoke established declarations from both
# initiatives.  These families intentionally describe the two source tracks, not
# the already-joined SquareWheel names, so a witness must expose both sides.
SQUARE_ANCHOR_FAMILIES = (
    "squareprefix",
    "squareblock",
    "survivor",
    "lifetime",
    "deathshell",
    "ancestry",
)
PRIME_WHEEL_ANCHOR_FAMILIES = (
    "primorial",
    "primewheel",
    "ramanujan",
    "conductor",
    "coconductor",
)

SYNTHESIS_BEGIN = "MOBIUS_SYNTHESIS_WITNESS_BEGIN"
SYNTHESIS_END = "MOBIUS_SYNTHESIS_WITNESS_END"


class GateError(RuntimeError):
    pass


def run_git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise GateError(
            f"git {' '.join(args)} failed with exit code {proc.returncode}:\n{proc.stderr.strip()}"
        )
    return proc.stdout


def try_git(repo: Path, *args: str) -> str | None:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode == 0:
        return proc.stdout
    return None


def load_json_text(text: str, source: str) -> dict[str, Any]:
    try:
        value = json.loads(text)
    except json.JSONDecodeError as exc:
        raise GateError(f"invalid JSON in {source}: {exc}") from exc
    if not isinstance(value, dict):
        raise GateError(f"{source} must contain a JSON object")
    return value


def load_base_json(repo: Path, base_sha: str, path: str) -> dict[str, Any] | None:
    text = try_git(repo, "show", f"{base_sha}:{path}")
    if text is None:
        return None
    return load_json_text(text, f"{base_sha}:{path}")


def load_head_json(repo: Path, path: str) -> dict[str, Any]:
    file_path = repo / path
    if not file_path.is_file():
        raise GateError(f"candidate is missing required {path}")
    return load_json_text(file_path.read_text(encoding="utf-8"), path)


def changed_files(repo: Path, base_sha: str, head_sha: str) -> set[str]:
    text = run_git(repo, "diff", "--name-only", f"{base_sha}...{head_sha}")
    return {line.strip() for line in text.splitlines() if line.strip()}


def manifest_kind(manifest: dict[str, Any], which: str) -> str:
    certified = manifest.get("certified")
    if not isinstance(certified, dict):
        raise GateError(f"{which} manifest is missing object field 'certified'")
    kind = certified.get("kind")
    if kind not in ALLOWED_KINDS:
        raise GateError(
            f"{which} certified.kind must be one of {sorted(ALLOWED_KINDS)}, got {kind!r}"
        )
    return kind


def exponent_fraction(manifest: dict[str, Any], which: str) -> Fraction:
    certified = manifest["certified"]
    exponent = certified.get("exponent")
    if not isinstance(exponent, dict):
        raise GateError(f"{which} power_bound requires certified.exponent")
    numerator = exponent.get("numerator")
    denominator = exponent.get("denominator")
    if not isinstance(numerator, int) or isinstance(numerator, bool):
        raise GateError(f"{which} exponent numerator must be an integer")
    if not isinstance(denominator, int) or isinstance(denominator, bool) or denominator <= 0:
        raise GateError(f"{which} exponent denominator must be a positive integer")
    return Fraction(numerator, denominator)


def parse_witness(witness_obj: Any, which: str) -> tuple[str, str]:
    if not isinstance(witness_obj, dict):
        raise GateError(f"{which} requires a witness object")
    module = witness_obj.get("module")
    theorem = witness_obj.get("theorem")
    if not isinstance(module, str) or not LEAN_IDENT_RE.fullmatch(module):
        raise GateError(f"{which} witness.module is not a valid Lean module name: {module!r}")
    if not isinstance(theorem, str) or not LEAN_IDENT_RE.fullmatch(theorem):
        raise GateError(f"{which} witness.theorem is not a valid Lean declaration name: {theorem!r}")
    return module, theorem


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def validate_frontier_common(base: dict[str, Any], head: dict[str, Any]) -> None:
    if base.get("schema_version") != 1 or head.get("schema_version") != 1:
        raise GateError("boundary frontier schema_version must remain 1")
    if base.get("frontier_id") != head.get("frontier_id"):
        raise GateError("frontier_id is immutable")
    if base.get("target") != head.get("target"):
        raise GateError(
            "the canonical quantitative target is immutable in a boundary-advance PR; "
            "do not redefine the problem to make the gate pass"
        )


def validate_quantitative_transition(
    base: dict[str, Any], head: dict[str, Any], changed: set[str]
) -> dict[str, Any]:
    validate_frontier_common(base, head)
    base_kind = manifest_kind(base, "base")
    head_kind = manifest_kind(head, "candidate")

    if base.get("certified") == head.get("certified"):
        raise GateError(
            f"{FRONTIER_PATH} changed without strengthening the certified quantitative frontier"
        )
    if base_kind == "rh_scale":
        raise GateError("the RH-scale quantitative frontier is already certified")

    certified = head["certified"]
    module, theorem = parse_witness(certified.get("witness"), "candidate quantitative frontier")
    witness_path = module_path(module)
    if witness_path not in changed:
        raise GateError(
            f"the quantitative witness module {witness_path} must be changed in the same PR"
        )

    if head_kind == "rh_scale":
        return {"module": module, "theorem": theorem, "exponent": None}

    if head_kind != "power_bound":
        raise GateError(
            "a quantitative frontier edit must move to power_bound or rh_scale; "
            "exact_reduction is not a quantitative advance"
        )

    candidate_exp = exponent_fraction(head, "candidate")
    if base_kind == "exact_reduction":
        if not candidate_exp < 1:
            raise GateError(
                "the first quantitative frontier must certify a genuine power saving: exponent < 1"
            )
    elif base_kind == "power_bound":
        base_exp = exponent_fraction(base, "base")
        if not candidate_exp < base_exp:
            raise GateError(
                f"candidate exponent {candidate_exp} is not strictly smaller than certified exponent {base_exp}"
            )
    else:
        raise GateError(f"unsupported base frontier kind {base_kind!r}")

    return {"module": module, "theorem": theorem, "exponent": candidate_exp}


def synthesis_revision(manifest: dict[str, Any], which: str) -> int:
    if manifest.get("schema_version") != 1:
        raise GateError(f"{which} synthesis schema_version must be 1")
    revision = manifest.get("revision")
    if not isinstance(revision, int) or isinstance(revision, bool) or revision < 0:
        raise GateError(f"{which} synthesis revision must be a nonnegative integer")
    return revision


def parse_anchor_list(value: Any, which: str, families: tuple[str, ...]) -> list[str]:
    if not isinstance(value, list) or not value:
        raise GateError(f"{which} must be a nonempty list of Lean declaration names")
    anchors: list[str] = []
    for item in value:
        if not isinstance(item, str) or not LEAN_IDENT_RE.fullmatch(item):
            raise GateError(f"{which} contains an invalid Lean declaration name: {item!r}")
        if not item.startswith("RHLean."):
            raise GateError(f"{which} anchor must be an RHLean declaration: {item}")
        lowered = item.lower()
        if not any(family in lowered for family in families):
            raise GateError(
                f"{which} anchor {item} is not recognizable as a source track declaration"
            )
        anchors.append(item)
    if len(set(anchors)) != len(anchors):
        raise GateError(f"{which} contains duplicate anchors")
    return anchors


def base_contains_anchor(repo: Path, base_sha: str, anchor: str) -> bool:
    leaf = anchor.rsplit(".", 1)[-1]
    proc = subprocess.run(
        ["git", "-C", str(repo), "grep", "-F", "-n", leaf, base_sha, "--", "RHLean"],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return proc.returncode == 0 and bool(proc.stdout.strip())


def validate_synthesis_transition(
    repo: Path,
    base_sha: str,
    base: dict[str, Any],
    head: dict[str, Any],
    changed: set[str],
) -> dict[str, Any]:
    base_revision = synthesis_revision(base, "base")
    head_revision = synthesis_revision(head, "candidate")
    if head_revision != base_revision + 1:
        raise GateError(
            f"synthesis revision must advance exactly once: expected {base_revision + 1}, got {head_revision}"
        )

    witness_obj = head.get("last_witness")
    module, theorem = parse_witness(witness_obj, "candidate synthesis revision")
    witness_path = module_path(module)
    if witness_path not in changed:
        raise GateError(
            f"the synthesis witness module {witness_path} must be changed in the same PR"
        )

    summary = witness_obj.get("summary") if isinstance(witness_obj, dict) else None
    if not isinstance(summary, str) or not summary.strip():
        raise GateError("candidate synthesis witness requires a nonempty summary")

    square_anchors = parse_anchor_list(
        witness_obj.get("square_anchors"),
        "square_anchors",
        SQUARE_ANCHOR_FAMILIES,
    )
    wheel_anchors = parse_anchor_list(
        witness_obj.get("prime_wheel_anchors"),
        "prime_wheel_anchors",
        PRIME_WHEEL_ANCHOR_FAMILIES,
    )
    overlap = set(square_anchors) & set(wheel_anchors)
    if overlap:
        raise GateError(
            "square and prime-wheel anchors must be distinct declarations: "
            + ", ".join(sorted(overlap))
        )

    for anchor in square_anchors + wheel_anchors:
        if not base_contains_anchor(repo, base_sha, anchor):
            raise GateError(
                f"synthesis anchor {anchor} was not found in the base RHLean source; "
                "anchors must pre-exist the PR"
            )

    return {
        "module": module,
        "theorem": theorem,
        "summary": summary.strip(),
        "square_anchors": square_anchors,
        "prime_wheel_anchors": wheel_anchors,
        "revision": head_revision,
    }


def validate_synthesis_bootstrap(head: dict[str, Any]) -> None:
    revision = synthesis_revision(head, "candidate")
    if revision != 0 or head.get("last_witness") is not None:
        raise GateError(
            "a synthesis ledger added without Lean-source changes may only initialize revision 0 with null last_witness"
        )


def quantitative_check_lines(plan: dict[str, Any]) -> list[str]:
    theorem = plan["theorem"]
    exponent = plan["exponent"]
    lines = [
        "open RHLean.Analysis.MobiusSynthesisBoundary",
        "",
    ]
    if exponent is None:
        lines.append(f"example : NonzeroResponseRHScale := {theorem}")
    else:
        lines.append(
            "example : NonzeroResponsePowerBound "
            f"(({exponent.numerator} : ℝ) / {exponent.denominator}) := {theorem}"
        )
    lines.extend([f"#print axioms {theorem}", ""])
    return lines


def synthesis_check_lines(plan: dict[str, Any]) -> list[str]:
    theorem = plan["theorem"]
    anchors = plan["square_anchors"] + plan["prime_wheel_anchors"]
    lines: list[str] = []
    for anchor in anchors:
        lines.append(f"#check {anchor}")
    lines.extend(
        [
            f'#eval IO.println "{SYNTHESIS_BEGIN}"',
            "set_option pp.fullNames true in",
            f"#print {theorem}",
            f'#eval IO.println "{SYNTHESIS_END}"',
            f"#print axioms {theorem}",
            "",
        ]
    )
    return lines


def lean_check_source(
    quantitative: dict[str, Any] | None,
    synthesis: dict[str, Any] | None,
) -> str:
    imports: list[str] = []
    if quantitative is not None:
        imports.extend(
            [
                "RHLean.Analysis.MobiusSynthesisBoundary",
                quantitative["module"],
            ]
        )
    if synthesis is not None:
        imports.append(synthesis["module"])

    lines = [f"import {module}" for module in dict.fromkeys(imports)]
    lines.append("")
    if quantitative is not None:
        lines.extend(quantitative_check_lines(quantitative))
    if synthesis is not None:
        lines.extend(synthesis_check_lines(synthesis))
    return "\n".join(lines)


def audit_axioms(text: str) -> None:
    no_axiom_messages = text.count("does not depend on any axioms")
    matches = re.findall(r"depends on axioms:\s*\[([^]]*)\]", text, flags=re.DOTALL)
    if not matches and no_axiom_messages == 0:
        raise GateError("could not locate Lean #print axioms output for the research witness")

    names: set[str] = set()
    for payload in matches:
        for item in payload.split(","):
            name = item.strip()
            if name:
                names.add(name)
    unexpected = names - ALLOWED_AXIOMS
    if unexpected:
        raise GateError(
            "research witness depends on nonstandard axioms: "
            + ", ".join(sorted(unexpected))
        )
    print(
        "BOUNDARY AXIOM AUDIT: PASS (only standard logical axioms: "
        + (", ".join(sorted(names)) if names else "none")
        + ")"
    )


def audit_synthesis_block(text: str, plan: dict[str, Any]) -> None:
    start = text.find(SYNTHESIS_BEGIN)
    end = text.find(SYNTHESIS_END, start + len(SYNTHESIS_BEGIN)) if start >= 0 else -1
    if start < 0 or end < 0 or end <= start:
        raise GateError("could not isolate the printed synthesis witness declaration")
    block = text[start + len(SYNTHESIS_BEGIN) : end]

    missing: list[str] = []
    for anchor in plan["square_anchors"] + plan["prime_wheel_anchors"]:
        leaf = anchor.rsplit(".", 1)[-1]
        if anchor not in block and leaf not in block:
            missing.append(anchor)
    if missing:
        raise GateError(
            "synthesis witness does not directly invoke declared track anchors: "
            + ", ".join(missing)
        )

    print(
        "SYNTHESIS COUPLING AUDIT: PASS (witness directly invokes square-block and prime-wheel anchors)"
    )


def audit_witness_log(log_path: Path, spec_path: Path) -> None:
    if not log_path.is_file():
        raise GateError(f"witness audit log does not exist: {log_path}")
    if not spec_path.is_file():
        raise GateError(f"witness audit spec does not exist: {spec_path}")
    text = log_path.read_text(encoding="utf-8", errors="replace")
    spec = load_json_text(spec_path.read_text(encoding="utf-8"), str(spec_path))
    audit_axioms(text)
    synthesis = spec.get("synthesis")
    if synthesis is not None:
        if not isinstance(synthesis, dict):
            raise GateError("invalid synthesis audit specification")
        audit_synthesis_block(text, synthesis)


def write_output(path: str | None, key: str, value: str) -> None:
    if not path:
        return
    with open(path, "a", encoding="utf-8") as handle:
        handle.write(f"{key}={value}\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default=".")
    parser.add_argument("--base-sha")
    parser.add_argument("--head-sha")
    parser.add_argument("--audit-witness-log")
    parser.add_argument("--audit-spec-file", default="/tmp/mobius_boundary_audit.json")
    parser.add_argument("--github-output")
    parser.add_argument("--lean-check-file", default="/tmp/mobius_boundary_witness.lean")
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    try:
        if args.audit_witness_log:
            audit_witness_log(Path(args.audit_witness_log), Path(args.audit_spec_file))
            return 0
        if not args.base_sha or not args.head_sha:
            raise GateError("--base-sha and --head-sha are required for research evaluation")

        changed = changed_files(repo, args.base_sha, args.head_sha)
        source_changed = {
            path
            for path in changed
            if path == "RHLean.lean" or (path.startswith("RHLean/") and path.endswith(".lean"))
        }
        frontier_changed = FRONTIER_PATH in changed
        synthesis_changed = SYNTHESIS_PATH in changed
        contract_changed = CONTRACT_PATH in changed

        if not source_changed:
            if frontier_changed:
                raise GateError(
                    f"{FRONTIER_PATH} changed without a Lean-source witness"
                )
            if synthesis_changed:
                base_synthesis = load_base_json(repo, args.base_sha, SYNTHESIS_PATH)
                head_synthesis = load_head_json(repo, SYNTHESIS_PATH)
                if base_synthesis is None:
                    validate_synthesis_bootstrap(head_synthesis)
                    write_output(args.github_output, "needs_lean", "false")
                    print("BOUNDARY GATE: PASS (initialized synthesis ledger at revision 0)")
                    return 0
                raise GateError(
                    f"{SYNTHESIS_PATH} changed without a Lean-source synthesis witness"
                )
            write_output(args.github_output, "needs_lean", "false")
            print("BOUNDARY GATE: PASS (maintenance or documentation only)")
            return 0

        if contract_changed:
            raise GateError(
                f"{CONTRACT_PATH} is the quantitative contract and cannot be rewritten in the same research PR"
            )

        if not frontier_changed and not synthesis_changed:
            raise GateError(
                "Lean mathematical source changed without a research certificate. "
                f"Either strictly advance {FRONTIER_PATH}, or increment {SYNTHESIS_PATH} with a new theorem "
                "that directly couples square-block and prime-wheel anchors."
            )

        quantitative_plan: dict[str, Any] | None = None
        synthesis_plan: dict[str, Any] | None = None

        if frontier_changed:
            base_frontier = load_base_json(repo, args.base_sha, FRONTIER_PATH)
            if base_frontier is None:
                raise GateError(f"base branch is missing required {FRONTIER_PATH}")
            head_frontier = load_head_json(repo, FRONTIER_PATH)
            quantitative_plan = validate_quantitative_transition(
                base_frontier, head_frontier, changed
            )

        if synthesis_changed:
            base_synthesis = load_base_json(repo, args.base_sha, SYNTHESIS_PATH)
            if base_synthesis is None:
                raise GateError(
                    f"base branch is missing {SYNTHESIS_PATH}; initialize revision 0 before using the synthesis lane"
                )
            head_synthesis = load_head_json(repo, SYNTHESIS_PATH)
            synthesis_plan = validate_synthesis_transition(
                repo,
                args.base_sha,
                base_synthesis,
                head_synthesis,
                changed,
            )

        check_path = Path(args.lean_check_file)
        check_path.write_text(
            lean_check_source(quantitative_plan, synthesis_plan),
            encoding="utf-8",
        )
        spec_path = Path(args.audit_spec_file)
        spec_path.write_text(
            json.dumps({"synthesis": synthesis_plan}, indent=2, default=str) + "\n",
            encoding="utf-8",
        )
        write_output(args.github_output, "needs_lean", "true")
        write_output(args.github_output, "witness_check", str(check_path))
        write_output(args.github_output, "audit_spec", str(spec_path))

        if quantitative_plan is not None:
            exponent = quantitative_plan["exponent"]
            theorem = quantitative_plan["theorem"]
            if exponent is None:
                print(f"BOUNDARY GATE: quantitative lane certifies RH scale via {theorem}")
            else:
                print(
                    "BOUNDARY GATE: quantitative lane strictly advances to "
                    f"power exponent {exponent} via {theorem}"
                )
        if synthesis_plan is not None:
            print(
                "BOUNDARY GATE: synthesis lane advances to revision "
                f"{synthesis_plan['revision']} via {synthesis_plan['theorem']}"
            )
        print(f"Lean witness check written to {check_path}")
        return 0
    except GateError as exc:
        print("BOUNDARY GATE: FAIL", file=sys.stderr)
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
