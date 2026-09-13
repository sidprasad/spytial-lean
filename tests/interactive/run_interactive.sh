#!/usr/bin/env bash

RUN_DIR=tests/interactive

TEST_DIR="$RUN_DIR/test-cases"
RUNNER="$RUN_DIR/test_single.sh"
PASS_COUNT=0
FAIL_COUNT=0
FAILED_TESTS=()

if [[ ! -x "$RUNNER" ]]; then
    echo "Error: Runner script '$RUNNER' not found or not executable."
    exit 1
fi

for test_file in "$TEST_DIR"/*.lean; do
    [[ -f "$test_file" ]] || continue

    echo -n "Running test: $(basename "$test_file")... "

    TEST_OUTPUT=$("$RUNNER" "$test_file" 2>&1)
    EXIT_CODE=$?

    if [ $EXIT_CODE -eq 0 ]; then
        echo "PASS"
        ((PASS_COUNT++))
    else
        echo "FAIL (Exit Code: $EXIT_CODE)"
        echo "--- FAILURE LOG: $(basename "$test_file") ---"
        echo "$TEST_OUTPUT"
        echo "-----------------------------------------------"

        ((FAIL_COUNT++))
        FAILED_TESTS+=("$(basename "$test_file")")
    fi
done

echo "LSP tests: $PASS_COUNT/$((PASS_COUNT + FAIL_COUNT)) passed"

if [[ $FAIL_COUNT -gt 0 ]]; then
    for failed in "${FAILED_TESTS[@]}"; do
        echo "  failed: $failed"
    done
    exit 1
fi
