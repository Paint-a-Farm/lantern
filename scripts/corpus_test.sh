#!/bin/bash
# Run corpus roundtrip tests across top-level script folders.
# Produces:
#   1. A formatted table with per-folder pass rates (to stdout)
#   2. An LCOV tracefile (to --lcov <path> or corpus_roundtrip.lcov)
#
# Usage:
#   scripts/corpus_test.sh [SCRIPTS_DIR] [--lcov PATH]
set -euo pipefail

# Parse arguments
SCRIPTS_DIR="/Users/kim/dev/fs25/dataS/scripts"
LCOV_PATH="corpus_roundtrip.lcov"
while [[ $# -gt 0 ]]; do
    case "$1" in
        --lcov) LCOV_PATH="$2"; shift 2 ;;
        *)      SCRIPTS_DIR="$1"; shift ;;
    esac
done

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

# Run jobs with limited concurrency — each emits LCOV to a temp file
running=0
for job in "${jobs[@]}"; do
    name="${job%%|*}"
    target="${job#*|}"
    (
        # shellcheck disable=SC2086
        cargo run -p lantern-verify -- roundtrip --format lcov $target 2>/dev/null \
            > "$TMPDIR_RESULTS/${name}.lcov" || true
    ) &
    running=$((running + 1))
    if [ "$running" -ge "$MAX_JOBS" ]; then
        wait -n 2>/dev/null || true
        running=$((running - 1))
    fi
done
wait

# Merge all LCOV files into one
> "$LCOV_PATH"
for f in "$TMPDIR_RESULTS"/*.lcov; do
    cat "$f" >> "$LCOV_PATH"
done

# Parse LCOV to build the table: per-folder FNF/FNH sums
# Each SF: line gives us the source path; we extract the folder from it.
fmt="%-40s %8s %8s %8s %7s\n"
printf "\n$fmt" "Folder" "Check" "Pass" "Fail" "Rate"
printf "$fmt" "---" "---" "---" "---" "---"

awk -v scripts_dir="$SCRIPTS_DIR" '
BEGIN {
    total_fnf = 0; total_fnh = 0;
}
/^SF:/ {
    path = substr($0, 4)
    sub("^" scripts_dir "/?", "", path)
    idx = index(path, "/")
    if (idx > 0) {
        folder = substr(path, 1, idx - 1)
    } else {
        folder = "(root)"
    }
}
/^FNF:/ { fnf = substr($0, 5) + 0; folders_fnf[folder] += fnf; total_fnf += fnf }
/^FNH:/ { fnh = substr($0, 5) + 0; folders_fnh[folder] += fnh; total_fnh += fnh }
END {
    # Collect and sort folder names (portable: no asorti)
    n = 0
    for (f in folders_fnf) { names[n++] = f }
    for (i = 0; i < n; i++) {
        for (j = i + 1; j < n; j++) {
            if (names[i] > names[j]) {
                t = names[i]; names[i] = names[j]; names[j] = t
            }
        }
    }
    for (i = 0; i < n; i++) {
        f = names[i]
        checked = folders_fnf[f]
        passed = folders_fnh[f] + 0
        fail = checked - passed
        if (checked > 0) {
            pct = sprintf("%.1f", passed * 100.0 / checked)
        } else {
            pct = "0.0"
        }
        printf "%-40s %8d %8d %8d %6s%%\n", f, checked, passed, fail, pct
    }
    printf "%-40s %8s %8s %8s %7s\n", "---", "---", "---", "---", "---"
    if (total_fnf > 0) {
        total_pct = sprintf("%.1f", total_fnh * 100.0 / total_fnf)
    } else {
        total_pct = "0.0"
    }
    printf "%-40s %8d %8d %8d %6s%%\n", "TOTAL", total_fnf, total_fnh, total_fnf - total_fnh, total_pct
}
' "$LCOV_PATH"

echo ""
echo "LCOV tracefile written to: $LCOV_PATH"

rm -rf "$TMPDIR_RESULTS"
