#!/bin/bash
# Run corpus roundtrip tests across top-level script folders
# Outputs a formatted table with pass rates per folder
set -euo pipefail

SCRIPTS_DIR="${1:-/Users/kim/dev/fs25/dataS/scripts}"
TMPDIR_RESULTS=$(mktemp -d)
MAX_JOBS="${MAX_JOBS:-8}"

# Build first so parallel jobs don't race
cargo build -p lantern-verify 2>&1 | tail -1

# Collect all jobs: root l64 files + subdirectories
jobs=()
if ls "$SCRIPTS_DIR"/*.l64 &>/dev/null; then
    jobs+=("(root)|$SCRIPTS_DIR/*.l64")
fi
for dir in "$SCRIPTS_DIR"/*/; do
    name=$(basename "$dir")
    jobs+=("$name|$dir")
done

# Sum up "N checked, N passed, N mismatches" lines into "C P M"
sum_results() {
    awk '
    /checked/ { for(i=1;i<=NF;i++) if($(i+1)~/^checked/) c+=$i }
    /passed/  { for(i=1;i<=NF;i++) if($(i+1)~/^passed/)  p+=$i }
    /mismatches/ { for(i=1;i<=NF;i++) if($(i+1)~/^mismatch/) m+=$i }
    END { print c+0, p+0, m+0 }
    '
}

# Run jobs with limited concurrency
running=0
for job in "${jobs[@]}"; do
    name="${job%%|*}"
    target="${job#*|}"
    (
        # shellcheck disable=SC2086
        output=$(cargo run -p lantern-verify -- roundtrip $target 2>/dev/null | grep "compile roundtrip:" || true)
        if [ -z "$output" ]; then
            echo "0 0 0" > "$TMPDIR_RESULTS/$name"
        else
            echo "$output" | sum_results > "$TMPDIR_RESULTS/$name"
        fi
    ) &
    running=$((running + 1))
    if [ "$running" -ge "$MAX_JOBS" ]; then
        wait -n 2>/dev/null || true
        running=$((running - 1))
    fi
done
wait

# Print table header
fmt="%-40s %8s %8s %8s %7s\n"
printf "\n$fmt" "Folder" "Check" "Pass" "Fail" "Rate"
printf "$fmt" "---" "---" "---" "---" "---"

# Collect and display sorted results as a table
total_checked=0
total_passed=0
total_mismatch=0

for f in $(ls "$TMPDIR_RESULTS"/ | sort); do
    name="$f"
    read -r checked passed mismatch < "$TMPDIR_RESULTS/$f"

    if [ "$checked" -gt 0 ]; then
        pct=$(echo "scale=1; $passed * 100 / $checked" | bc)
    else
        pct="0.0"
    fi

    printf "%-40s %8d %8d %8d %6s%%\n" "$name" "$checked" "$passed" "$mismatch" "$pct"

    total_checked=$((total_checked + checked))
    total_passed=$((total_passed + passed))
    total_mismatch=$((total_mismatch + mismatch))
done

# Summary
printf "$fmt" "---" "---" "---" "---" "---"
if [ "$total_checked" -gt 0 ]; then
    total_pct=$(echo "scale=1; $total_passed * 100 / $total_checked" | bc)
else
    total_pct="0.0"
fi
printf "%-40s %8d %8d %8d %6s%%\n" "TOTAL" "$total_checked" "$total_passed" "$total_mismatch" "$total_pct"

rm -rf "$TMPDIR_RESULTS"
