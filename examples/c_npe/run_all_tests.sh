#!/bin/bash

# Script to run Infer on all test cases
# Run from docker/repair directory: ../../examples/c_npe/run_all_tests.sh

echo "Running Infer on all null pointer test cases..."
echo "=============================================="

TOTAL=0
DETECTED=0

for i in {01..20}; do
    TEST_FILE=$(ls test${i}_*.c 2>/dev/null | head -1)
    if [ -f "$TEST_FILE" ]; then
        echo ""
        echo "Testing: $TEST_FILE"
        echo "-------------------"
        
        # Run infer and capture output
        OUTPUT=$(../../docker/repair/run-infer.sh "../../examples/c_npe/$TEST_FILE" 2>&1)
        
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