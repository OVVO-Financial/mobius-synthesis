#!/usr/bin/env python3
"""Reject Markdown math delimiters that do not render reliably on GitHub."""
from pathlib import Path
import sys

BAD = (r'\[', r'\]', r'\(', r'\)')
failures = []

def plain_segments(line: str):
    i = 0
    start = 0
    while i < len(line):
        if line[i] != '`':
            i += 1
            continue
        j = i
        while j < len(line) and line[j] == '`':
            j += 1
        ticks = line[i:j]
        close = line.find(ticks, j)
        if close == -1:
            i = j
            continue
        yield line[start:i]
        i = close + len(ticks)
        start = i
    yield line[start:]

scanned = 0
for path in sorted(Path('.').rglob('*.md')):
    if '.git' in path.parts:
        continue
    scanned += 1
    fence = None
    for lineno, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
        stripped = line.lstrip()
        if fence is None and (stripped.startswith('```') or stripped.startswith('~~~')):
            fence = stripped[:3]
            continue
        if fence is not None:
            if stripped.startswith(fence):
                fence = None
            continue
        for segment in plain_segments(line):
            for token in BAD:
                if token in segment:
                    failures.append(f'{path}:{lineno}: unsupported delimiter {token}')

if failures:
    print('Unsupported GitHub Markdown math delimiters found:', file=sys.stderr)
    print('\n'.join(failures), file=sys.stderr)
    raise SystemExit(1)
print(f'Markdown math delimiter audit passed for {scanned} file(s).')
