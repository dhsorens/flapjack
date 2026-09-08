#!/usr/bin/env bash
# Fail if `native_decide` is used beyond the documented allowlist.
#
# A ratchet, not a ban: counts may fall freely, but any increase -- or any use
# in a file that is not listed -- fails. See scripts/native-decide-allowlist.txt
# for why each permitted use exists.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1
ALLOWLIST=scripts/native-decide-allowlist.txt

if [ ! -f "$ALLOWLIST" ]; then
  echo "error: $ALLOWLIST is missing" >&2
  exit 1
fi

# allowed[path] = permitted count
declare -A allowed=()
while read -r count path; do
  [ -z "${count:-}" ] && continue
  case "$count" in \#*) continue ;; esac
  if ! [[ "$count" =~ ^[0-9]+$ ]]; then
    echo "error: malformed allowlist line: $count $path" >&2
    exit 1
  fi
  allowed["$path"]=$count
done < <(sed 's/#.*//' "$ALLOWLIST")

# actual[path] = occurrences in tracked .lean sources
declare -A actual=()
while IFS=: read -r path count; do
  [ -n "${path:-}" ] && actual["$path"]=$count
done < <(git grep -o '\bnative_decide\b' -- '*.lean' \
           | cut -d: -f1 | sort | uniq -c \
           | awk '{print $2":"$1}')

status=0
total=0
for path in "${!actual[@]}"; do
  n=${actual[$path]}
  total=$((total + n))
  limit=${allowed[$path]:-0}
  if [ "$n" -gt "$limit" ]; then
    if [ "$limit" -eq 0 ]; then
      echo "FAIL $path: $n use(s) of native_decide; this file is not in the allowlist"
    else
      echo "FAIL $path: $n use(s) of native_decide, allowlist permits $limit"
    fi
    status=1
  elif [ "$n" -lt "$limit" ]; then
    echo "note $path: $n use(s), allowlist permits $limit -- please lower the allowlist"
  fi
done

# a listed file that no longer exists, or has none left, is worth flagging too
for path in "${!allowed[@]}"; do
  if [ -z "${actual[$path]:-}" ] && [ "${allowed[$path]}" -gt 0 ]; then
    echo "note $path: no uses left, please remove it from the allowlist"
  fi
done

if [ "$status" -ne 0 ]; then
  cat >&2 <<'MSG'

`native_decide` compiles the goal and trusts the result, attaching a
per-theorem axiom. Try in order:

  decide            -- when the elaborator can reduce the Decidable instance
  decide +kernel    -- when it cannot, because reduction stalls on a
                       `termination_by` definition; the kernel unfolds these
  #guard <prop>     -- for an `example` or an uncited regression check: keeps
                       the check, produces no proof term, needs no axiom

If none apply and the use is genuinely necessary, add it to
scripts/native-decide-allowlist.txt with a note saying why.
MSG
  exit 1
fi

echo "native_decide: $total use(s), all within the allowlist"
