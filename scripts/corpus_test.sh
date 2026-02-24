#!/bin/bash
# Run corpus roundtrip tests in parallel across top-level script folders
set -euo pipefail

SCRIPTS_DIR="${1:-/Users/kim/dev/fs25/dataS/scripts}"
TMPDIR_RESULTS=$(mktemp -d)

# Build first so parallel jobs don't race
cargo build -p lantern-verify 2>&1 | tail -1

# Run each top-level folder in parallel, write results to temp files
pids=()
for dir in "$SCRIPTS_DIR"/*/; do
    name=$(basename "$dir")
    (
        result=$(cargo run -p lantern-verify -- roundtrip "$dir" 2>/dev/null | grep "compile roundtrip:" || echo "compile roundtrip: ERROR")
        echo "$name: $result" > "$TMPDIR_RESULTS/$name"
    ) &
    pids+=($!)
done

# Wait for all
for pid in "${pids[@]}"; do
    wait "$pid" 2>/dev/null || true
done

# Collect and display sorted results
cat "$TMPDIR_RESULTS"/* | sort

# Summary
echo ""
echo "=== SUMMARY ==="
total_checked=0
total_passed=0
total_mismatch=0
for f in "$TMPDIR_RESULTS"/*; do
    line=$(cat "$f")
    checked=$(echo "$line" | grep -oE '[0-9]+ checked' | grep -oE '[0-9]+' || echo 0)
    passed=$(echo "$line" | grep -oE '[0-9]+ passed' | grep -oE '[0-9]+' || echo 0)
    mismatch=$(echo "$line" | grep -oE '[0-9]+ mismatches' | grep -oE '[0-9]+' || echo 0)
    total_checked=$((total_checked + checked))
    total_passed=$((total_passed + passed))
    total_mismatch=$((total_mismatch + mismatch))
done

rm -rf "$TMPDIR_RESULTS"
pct=0
if [ "$total_checked" -gt 0 ]; then
    pct=$(echo "scale=1; $total_passed * 100 / $total_checked" | bc)
fi
echo "Total: $total_passed/$total_checked = ${pct}% ($total_mismatch mismatches)"
