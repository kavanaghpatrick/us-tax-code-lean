#!/bin/bash
# Find all sections that fail to compile

echo "Finding broken sections..."
echo ""

BROKEN=()
WORKING=()
TOTAL=0

for file in src/TaxCode/Section[0-9]*.lean; do
    # Skip aristotle files
    if [[ $file == *"_aristotle"* ]]; then
        continue
    fi

    TOTAL=$((TOTAL + 1))

    # Try to compile
    if lean "$file" > /dev/null 2>&1; then
        WORKING+=("$file")
    else
        BROKEN+=("$file")
    fi

    # Progress indicator
    if (( TOTAL % 50 == 0 )); then
        echo "Checked $TOTAL sections..."
    fi
done

echo ""
echo "="*80
echo "COMPILATION RESULTS"
echo "="*80
echo "Total sections: $TOTAL"
echo "Working: ${#WORKING[@]}"
echo "Broken: ${#BROKEN[@]}"
echo ""

if [ ${#BROKEN[@]} -gt 0 ]; then
    echo "Broken sections:"
    printf '%s\n' "${BROKEN[@]}" | head -20
    if [ ${#BROKEN[@]} -gt 20 ]; then
        echo "... and $((${#BROKEN[@]} - 20)) more"
    fi
fi
