#!/bin/bash
# Fix the placeholder bug in all sections

echo "Fixing placeholder bug across all sections..."
echo ""

FIXED=0

for file in src/TaxCode/Section*.lean; do
    # Skip aristotle files
    if [[ $file == *"_aristotle"* ]]; then
        continue
    fi

    # Check if file has placeholder
    if grep -q "#check placeholder" "$file"; then
        # Replace with eval
        sed -i.bak 's/#check placeholder/#eval "Section loaded"/g' "$file"
        FIXED=$((FIXED + 1))

        if (( FIXED % 50 == 0 )); then
            echo "Fixed $FIXED files..."
        fi
    fi
done

echo ""
echo "="*80
echo "PLACEHOLDER FIX COMPLETE"
echo "="*80
echo "Fixed $FIXED files"
echo ""
echo "Backup files saved as *.bak (can delete with: rm src/TaxCode/*.bak)"
