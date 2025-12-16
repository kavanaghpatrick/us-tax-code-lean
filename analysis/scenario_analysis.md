# IRC Test Scenario Analysis

**Total Scenarios Generated**: 67

## Taxpayer Scenarios

Generated 50 diverse taxpayer scenarios covering:
- Income levels: $10K to $10M
- All filing statuses
- 0-5 dependents
- Ages 18-90

## Bond Scenarios (IRC §103, §141, §143, §144)

### Scenario 1: Standard state bond - should be tax-exempt

- **Issuer**: State
- **Interest**: $500
- **Proceeds**: $1,000,000
- **Private Use**: 0.0%
- **Expected Result**: Tax-exempt

### Scenario 2: Federal bond - NOT tax-exempt

- **Issuer**: Federal
- **Interest**: $400
- **Proceeds**: $1,000,000
- **Private Use**: 0.0%
- **Expected Result**: Taxable

### Scenario 3: Private activity bond, not qualified - NOT exempt

- **Issuer**: Local
- **Interest**: $600
- **Proceeds**: $1,000,000
- **Private Use**: 15.0%
- **Expected Result**: Taxable

### Scenario 4: Qualified private activity bond - IS exempt

- **Issuer**: Local
- **Interest**: $550
- **Proceeds**: $1,000,000
- **Private Use**: 20.0%
- **Expected Result**: Tax-exempt

### Scenario 5: Arbitrage bond - NOT exempt

- **Issuer**: State
- **Interest**: $700
- **Proceeds**: $1,000,000
- **Private Use**: 0.0%
- **Expected Result**: Taxable

### Scenario 6: Federally guaranteed - NOT exempt (§149(b))

- **Issuer**: State
- **Interest**: $450
- **Proceeds**: $1,000,000
- **Private Use**: 0.0%
- **Expected Result**: Taxable

### Scenario 7: Large bond with $6M private loan - triggers PAB status

- **Issuer**: State
- **Interest**: $1,500
- **Proceeds**: $200,000,000
- **Private Use**: 0.0%
- **Expected Result**: Taxable

### Scenario 8: Edge case - exactly 10% private use (at threshold, not over)

- **Issuer**: State
- **Interest**: $500
- **Proceeds**: $1,000,000
- **Private Use**: 10.0%
- **Expected Result**: Tax-exempt

### Scenario 9: Just over 10% private use threshold - NOT exempt

- **Issuer**: State
- **Interest**: $500
- **Proceeds**: $1,000,000
- **Private Use**: 11.0%
- **Expected Result**: Taxable

### Scenario 10: Unregistered bond when registration required - NOT exempt

- **Issuer**: State
- **Interest**: $500
- **Proceeds**: $1,000,000
- **Private Use**: 0.0%
- **Expected Result**: Taxable

## Expense Scenarios (IRC §162)

### Scenario 1: Reasonable salary for services rendered - fully deductible

- **Amount**: $100,000
- **Type**: Salary
- **Expected Deductible**: $100,000

### Scenario 2: Excessive salary - limited to reasonable amount

- **Amount**: $500,000
- **Type**: Salary
- **Expected Deductible**: $100,000

### Scenario 3: Illegal bribe - NOT deductible (§162(c))

- **Amount**: $50,000
- **Type**: Bribe
- **Expected Deductible**: $0

### Scenario 4: Government fine - NOT deductible (§162(f))

- **Amount**: $50,000
- **Type**: FineOrPenalty
- **Expected Deductible**: $0

### Scenario 5: Executive comp $2M for public company - capped at $1M (§162(m))

- **Amount**: $2,000,000
- **Type**: ExecutiveCompensation
- **Expected Deductible**: $1,000,000

### Scenario 6: Lobbying expense - NOT deductible (§162(e))

- **Amount**: $75,000
- **Type**: LobbyingExpense
- **Expected Deductible**: $0

### Scenario 7: Travel expense with lavish portion - deduct only reasonable part

- **Amount**: $10,000
- **Type**: Travel
- **Expected Deductible**: $7,000

