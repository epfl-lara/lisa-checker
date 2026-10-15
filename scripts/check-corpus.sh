#!/usr/bin/env bash
# Check each serialized bundle in a separate process with a time limit.
set -euo pipefail

if (( $# < 2 || $# > 3 )); then
  echo "Usage: $0 CORPUS_DIRECTORY NEW_RESULTS_DIRECTORY [TIMEOUT_SECONDS]" >&2
  exit 2
fi

corpus=$1
results=$2
seconds=${3:-30}
checker=${LISA_CHECKER:-.lake/build/bin/lisa-checker}

[[ -d $corpus ]] || { echo "Missing corpus directory: $corpus" >&2; exit 2; }
[[ ! -e $results ]] || { echo "Results path already exists: $results" >&2; exit 2; }
[[ $seconds =~ ^[1-9][0-9]*$ ]] || { echo "Timeout must be positive" >&2; exit 2; }
[[ -x $checker ]] || { echo "Build lisa-checker first: $checker" >&2; exit 2; }
for command in rg sort timeout; do
  command -v "$command" >/dev/null || { echo "Missing command: $command" >&2; exit 2; }
done
[[ -x /usr/bin/time ]] || { echo "GNU time is required" >&2; exit 2; }

mkdir -p "$results"
cp "$checker" "$results/checker"
checker="$results/checker"
sha256sum "$checker" > "$results/checker.sha256"
printf 'bundle\tstatus\texit_code\telapsed_s\tpeak_rss_kib\n' > "$results/summary.tsv"
index=0
failed=0
while IFS= read -r -d '' prefix; do
  index=$((index + 1))
  printf -v stem '%05d' "$index"
  status=0
  /usr/bin/time -f '%e\t%M' -o "$results/$stem.time" \
    timeout --kill-after=5 "$seconds" "$checker" "$prefix" \
    > "$results/$stem.tsv" 2> "$results/$stem.log" || status=$?
  case $status in
    0) label=PASS ;;
    124) label=TIMEOUT ;;
    137) label=KILLED ;;
    1) label=FAIL ;;
    *) label=ERROR ;;
  esac
  if (( status != 0 )); then failed=$((failed + 1)); fi
  timing=$(tail -n 1 "$results/$stem.time")
  printf '%s\t%s\t%s\t%s\n' "$prefix" "$label" "$status" "$timing" \
    >> "$results/summary.tsv"
  printf '%s: %s\n' "$prefix" "$label" >&2
done < <(
  while IFS= read -r -d '' file; do
    printf '%s\0' "${file%.*}"
  done < <(rg --files -0 -g '*.proof' -g '*.trees' "$corpus") | sort -zu
)
echo "$index bundles; $failed failures/timeouts. Results: $results" >&2
(( index > 0 && failed == 0 ))
