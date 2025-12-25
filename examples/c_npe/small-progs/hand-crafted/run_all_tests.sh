#!/bin/bash

# Script to run Infer on all test cases
# Run from docker/repair directory: ../../examples/c_npe/run_all_tests.sh

echo "Running Infer on all null pointer test cases..."
echo "=============================================="

TOTAL=0
DETECTED=0

for filename in *c; do
    TEST_FILE=$filename
    if [ -f "$TEST_FILE" ]; then
        echo ""
        echo "Testing: $TEST_FILE"
        echo "-------------------"
        
        # Run infer and capture output
        OUTPUT=$(sudo ~/repos/infer/infer/bin/infer --keep-going --pulse-only -j 1 -- cc -c "$TEST_FILE" 2>&1)
        echo "$OUTPUT" 
        # Check if null dereference was detected
        if echo "$OUTPUT" | grep -q "Null Dereference"; then
            echo "✓ NULL DEREFERENCE DETECTED"
            ((DETECTED++))
        else
            echo "✗ No null dereference detected"
        fi
        
        ((TOTAL++))
    fi
done

echo ""
echo "=============================================="
echo "Summary: $DETECTED/$TOTAL null dereferences detected"
echo "=============================================="
