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
COMPARE_MODE="loose"
while [[ $# -gt 0 ]]; do
    case "$1" in
        --lcov) LCOV_PATH="$2"; shift 2 ;;
        --compare-mode) COMPARE_MODE="$2"; shift 2 ;;
        *)      SCRIPTS_DIR="$1"; shift ;;
    esac
done

TMPDIR_RESULTS=$(mktemp -d)
MAX_JOBS="${MAX_JOBS:-8}"

# Build first so parallel jobs use the binary directly (no cargo lock contention)
cargo build -p lantern-verify 2>&1 | tail -1
TARGET_DIR="$(cargo metadata --format-version=1 --no-deps 2>/dev/null \
    | jq -r '.target_directory')"
VERIFY_BIN="$TARGET_DIR/debug/lantern-verify"
if [ ! -x "$VERIFY_BIN" ]; then
    echo "ERROR: binary not found at $VERIFY_BIN" >&2
    exit 1
fi

# Collect all jobs: root l64 files + subdirectories
jobs=()
if ls "$SCRIPTS_DIR"/*.l64 &>/dev/null; then
    jobs+=("(root)|$SCRIPTS_DIR/*.l64")
fi
for dir in "$SCRIPTS_DIR"/*/; do
    name=$(basename "$dir")
    jobs+=("$name|$dir")
done

run_job() {
    local name="$1"
    local target="$2"
    # shellcheck disable=SC2086
    "$VERIFY_BIN" roundtrip --compare-mode "$COMPARE_MODE" --format lcov $target \
        > "$TMPDIR_RESULTS/${name}.lcov" \
        2> "$TMPDIR_RESULTS/${name}.err" || true
}

# Run jobs with limited concurrency — each emits LCOV to a temp file
running=0
for job in "${jobs[@]}"; do
    name="${job%%|*}"
    target="${job#*|}"
    run_job "$name" "$target" &
    running=$((running + 1))
    if [ "$running" -ge "$MAX_JOBS" ]; then
        wait -n 2>/dev/null || true
        running=$((running - 1))
    fi
done
wait

# Retry any jobs that produced empty LCOV (panics, stack overflows)
retried=0
for job in "${jobs[@]}"; do
    name="${job%%|*}"
    target="${job#*|}"
    lcov_file="$TMPDIR_RESULTS/${name}.lcov"
    if [ ! -s "$lcov_file" ]; then
        retried=$((retried + 1))
        run_job "$name" "$target" &
        running=$((running + 1))
        if [ "$running" -ge "$MAX_JOBS" ]; then
            wait -n 2>/dev/null || true
            running=$((running - 1))
        fi
    fi
done
if [ "$retried" -gt 0 ]; then
    wait
    echo "(retried $retried failed jobs)" >&2
fi

# Report any jobs that still failed after retry
failed_jobs=()
for job in "${jobs[@]}"; do
    name="${job%%|*}"
    lcov_file="$TMPDIR_RESULTS/${name}.lcov"
    err_file="$TMPDIR_RESULTS/${name}.err"
    if [ ! -s "$lcov_file" ]; then
        failed_jobs+=("$name")
        if [ -s "$err_file" ]; then
            echo "WARNING: $name failed: $(tail -1 "$err_file")" >&2
        else
            echo "WARNING: $name produced no output" >&2
        fi
    fi
done

# Merge all LCOV files into one, stripping SCRIPTS_DIR prefix from SF: lines
> "$LCOV_PATH"
for f in "$TMPDIR_RESULTS"/*.lcov; do
    [ -s "$f" ] && sed "s|^SF:${SCRIPTS_DIR}|SF:|" "$f" >> "$LCOV_PATH"
done

# Parse LCOV to build the table: per-folder FNF/FNH sums
# Each SF: line gives us the source path; we extract the folder from it.
fmt="%-40s %8s %8s %8s %7s\n"
printf "\n$fmt" "Folder" "Check" "Pass" "Fail" "Rate"
printf "$fmt" "---" "---" "---" "---" "---"

awk '
BEGIN {
    total_fnf = 0; total_fnh = 0;
}
/^SF:/ {
    path = substr($0, 4)
    sub("^/", "", path)
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
if [ ${#failed_jobs[@]} -gt 0 ]; then
    echo "WARNING: ${#failed_jobs[@]} job(s) failed: ${failed_jobs[*]}"
fi
echo "LCOV tracefile written to: $LCOV_PATH"

rm -rf "$TMPDIR_RESULTS"
