#!/usr/bin/env bash
set -euo pipefail

# Strip Lean line comments and nested block comments before looking for proof
# escapes or opaque declarations. Grepping raw source produces false positives
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

# Standalone-publication invariant. The repository may describe its own source,
# theorem history, and CI, but must not carry provenance or navigation back to
# another project repository. This also checks Lean doc comments: inherited
# change numbers and source-repository prose are documentation once this tree
# stands on its own.
standalone_patterns=(
  'RH_Lean'
  'square-block-mobius'
  'prime-wheel-mobius'
  'github\.com/OVVO-Financial/'
  'raw\.githubusercontent\.com/OVVO-Financial/'
  'api\.github\.com/repos/OVVO-Financial/'
  'parent_source_commit'
  'parent_lean_anchor'
  'development[ -]tree'
  'development repository'
  'parent repository'
  'source repository'
  '#[0-9]+'
)

standalone_failed=0
for pattern in "${standalone_patterns[@]}"; do
  while IFS= read -r -d '' file; do
    if grep -nE "$pattern" "$file"; then
      printf 'Forbidden cross-repository reference in %s (pattern: %s)\n' "$file" "$pattern" >&2
      standalone_failed=1
    fi
  done < <(
    find . -type f \
      ! -path './.git/*' \
      ! -path './.lake/*' \
      ! -path './scripts/audit_assumptions.sh' \
      \( -name '*.md' -o -name '*.json' -o -name '*.yml' -o -name '*.yaml' \
         -o -name '*.lean' -o -name '*.sh' -o -name '*.py' -o -name 'CODEOWNERS' \) \
      -print0
  )
done

if [[ "$standalone_failed" -ne 0 ]]; then
  echo 'Standalone repository reference audit failed.' >&2
  exit 1
fi

echo 'Lean source audit passed.'
echo 'Standalone repository reference audit passed.'
