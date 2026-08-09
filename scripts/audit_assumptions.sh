#!/usr/bin/env bash
set -euo pipefail

# Strip Lean line comments and nested block comments before looking for proof
# escapes or opaque declarations.  Grepping raw source produces false positives
# on ordinary prose such as "constant coefficient" inside doc comments.
strip_lean_comments() {
  awk '
    BEGIN { depth = 0 }
    {
      line = $0
      out = ""
      i = 1
      while (i <= length(line)) {
        two = substr(line, i, 2)
        if (depth > 0) {
          if (two == "/-") {
            depth++
            i += 2
          } else if (two == "-/") {
            depth--
            i += 2
          } else {
            i++
          }
        } else {
          if (two == "/-") {
            depth++
            i += 2
          } else if (two == "--") {
            break
          } else {
            out = out substr(line, i, 1)
            i++
          }
        }
      }
      print out
    }
  '
}

scan_pattern() {
  local pattern="$1"
  local found=0
  local file
  local matches

  while IFS= read -r -d '' file; do
    if matches=$(strip_lean_comments < "$file" | grep -nE "$pattern"); then
      while IFS= read -r match; do
        printf '%s:%s\n' "$file" "$match"
      done <<< "$matches"
      found=1
    fi
  done < <(find RHLean RHLean.lean -type f -name '*.lean' -print0)

  return "$found"
}

if ! scan_pattern '\b(sorry|admit)\b'; then
  echo 'Unfinished Lean proof found.' >&2
  exit 1
fi

if ! scan_pattern '^[[:space:]]*(axiom|constant)[[:space:]]'; then
  echo 'New Lean axiom or opaque constant found.' >&2
  exit 1
fi

echo 'Lean source audit passed.'
