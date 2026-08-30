#!/usr/bin/env bash
set -euo pipefail

# Strip Lean line comments and nested block comments before looking for proof
# escapes or opaque declarations.  Grepping raw source creates false positives
# in ordinary documentation comments.
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

# Standalone-publication invariant.  Public research text must not contain
# provenance, navigation, or lineage pointers to a separate development
# workspace.  The two named companion projects are the only project-level
# cross-references permitted.
lineage_patterns=(
  'parent_source_commit'
  'parent_lean_anchor'
  'development[ -]tree'
  'development repository'
  'parent repository'
  'source repository'
  'sibling repository'
  'private repository'
  'private workspace'
  'internal repository'
  'internal workspace'
  'monorepo'
  '/home/oai/'
)

standalone_failed=0
for pattern in "${lineage_patterns[@]}"; do
  while IFS= read -r -d '' file; do
    if grep -nEi "$pattern" "$file"; then
      printf 'Forbidden standalone-provenance text in %s (pattern: %s)\n' "$file" "$pattern" >&2
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

# Restrict project-level references within the OVVO-Financial organization to
# the two public companion projects.  Workflow action dependencies from other
# organizations are infrastructure dependencies and are outside this research-
# provenance check.
allowed_projects='^(prime-wheel-mobius|square-block-mobius)$'
while IFS= read -r -d '' file; do
  while IFS=: read -r line ref; do
    [[ -z "${ref:-}" ]] && continue
    project="${ref#OVVO-Financial/}"
    if [[ ! "$project" =~ $allowed_projects ]]; then
      printf '%s:%s: forbidden project reference OVVO-Financial/%s\n' \
        "$file" "$line" "$project" >&2
      standalone_failed=1
    fi
  done < <(grep -nEo 'OVVO-Financial/[A-Za-z0-9._-]+' "$file" || true)
done < <(
  find . -type f \
    ! -path './.git/*' \
    ! -path './.lake/*' \
    ! -path './scripts/audit_assumptions.sh' \
    \( -name '*.md' -o -name '*.json' -o -name '*.yml' -o -name '*.yaml' \
       -o -name '*.lean' -o -name '*.sh' -o -name '*.py' -o -name 'CODEOWNERS' \) \
    -print0
)

# Tracker references belong to a development workflow, not to a published
# research package.  Issue and pull-request numbers are rewritten to name the
# layer they actually refer to before a module is published here, and the
# originating workspace is never named.  This check keeps that from regressing:
# a '#' followed by digits is the tracker-reference form, and the workspace name
# is matched in both spellings.
while IFS= read -r -d '' file; do
  if grep -nEi '(^|[^A-Za-z0-9_])#[0-9]{1,5}([^0-9]|$)|RH[_-]Lean' "$file"; then
    printf 'Forbidden tracker or workspace reference in %s\n' "$file" >&2
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

if [[ "$standalone_failed" -ne 0 ]]; then
  echo 'Standalone repository reference audit failed.' >&2
  exit 1
fi

echo 'Lean source audit passed.'
echo 'Standalone repository reference audit passed.'
