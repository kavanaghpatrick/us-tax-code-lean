# Proven Theorems Catalog

Auto-generated catalog of all proven properties in the US Tax Code formalization.

## Summary Statistics

- **Total Theorems**: 309
- **Total Lemmas**: 14
- **Sections with Proofs**: 45

### By Category

| Category | Count |
|----------|-------|
| Bounds | 93 |
| Other | 78 |
| Implications | 35 |
| Examples | 31 |
| Eligibility | 31 |
| Zero Conditions | 28 |
| Equivalence | 16 |
| Monotonicity | 8 |
| Linearity | 3 |

## Theorems by Category

### Bounds (93)

- **tax_nonnegative** (Section1)
  - `theorem tax_nonnegative (status : FilingStatus) (income : Currency) (h : income ≥ 0) : calculate_...`
- **gain_nonneg** (Section1001)
  - `theorem gain_nonneg (d : Disposition) : gain d ≥ 0`
- **loss_nonneg** (Section1001)
  - `theorem loss_nonneg (d : Disposition) : loss d ≥ 0`
- **gain_minus_loss_eq_realized_minus_basis** (Section1001)
  - `theorem gain_minus_loss_eq_realized_minus_basis (d : Disposition) : gain d - loss d = amountReali...`
- **exclusion_limited_by_transfer_for_value** (Section101)
  - `theorem exclusion_limited_by_transfer_for_value (payout : InsurancePayout) (transfer : PolicyTran...`
- **gift_basis_loss_le_gain** (Section1015)
  - `theorem gift_basis_loss_le_gain (info : GiftInfo) : (calc_basis_gift info).lossBasis ≤ (calc_basi...`
- **gift_tax_adjustment_capped_at_fmv** (Section1015)
  - `theorem gift_tax_adjustment_capped_at_fmv (basis fmv tax : Currency) (h : basis < fmv) : apply_gi...`
- **example_4_gift_tax_capped** (Section1015)
  - `theorem example_4_gift_tax_capped : calc_basis_gift { dateOfGift`
- **insolvency_exclusion_limit** (Section108)
  - `theorem insolvency_exclusion_limit (d : DischargeIndebtedness) (s : TaxpayerStatus) (e : Taxpayer...`
- **non_c_corp_qrpb_limited** (Section108)
  - `theorem non_c_corp_qrpb_limited (d : DischargeIndebtedness) (s : TaxpayerStatus) (e : TaxpayerEle...`
- **attributes_untouched_if_fully_absorbed_by_nol** (Section108)
  - `theorem attributes_untouched_if_fully_absorbed_by_nol (excluded : Currency) (s : TaxpayerStatus) ...`
- **exclusion_limit_nonneg** (Section121)
  - `theorem exclusion_limit_nonneg (filingStatus : FilingStatus) (t1 : Taxpayer) (t2 : Option Taxpaye...`
- **excluded_gain_le_total_gain** (Section121)
  - `theorem excluded_gain_le_total_gain (filingStatus : FilingStatus) (t1 : Taxpayer) (t2 : Option Ta...`
- **inventory_not_capital** (Section1221)
  - `theorem inventory_not_capital (p : PropertyInfo) (h : p.tp = PropertyType.Inventory) : isCapitalA...`
- **securities_are_capital_unless_dealer_exception** (Section1221)
  - `theorem securities_are_capital_unless_dealer_exception (p : PropertyInfo) (h_tp : p.tp = Property...`
- **real_property_generally_capital** (Section1221)
  - `theorem real_property_generally_capital (p : PropertyInfo) (h_tp : p.tp = PropertyType.Real) (h_b...`
- **lavish_travel_limited** (Section162)
  - `theorem lavish_travel_limited (e : Expense) (away : Bool) (lavish : Currency) (days : Nat) (fed :...`
- **salary_reasonable_limit** (Section162)
  - `theorem salary_reasonable_limit (e : Expense) (reasonable : Currency) (rendered : Bool) : e.type ...`
- **exec_comp_capped_at_1m** (Section162)
  - `theorem exec_comp_capped_at_1m : deductibleAmount example_exec_comp_capped = 1000000`
- **exec_comp_cap_enforced** (Section162)
  - `theorem exec_comp_cap_enforced (e : Expense) (amt : Currency) : e.type = ExpenseType.ExecutiveCom...`
- **exec_comp_no_cap_private** (Section162)
  - `theorem exec_comp_no_cap_private (e : Expense) (amt : Currency) : e.type = ExpenseType.ExecutiveC...`
- **exec_comp_no_cap_non_covered** (Section162)
  - `theorem exec_comp_no_cap_non_covered (e : Expense) (amt : Currency) : e.type = ExpenseType.Execut...`
- **lavish_travel_limited** (Section162)
  - `theorem lavish_travel_limited (e : Expense) (away : Bool) (lavish : Currency) (days : Nat) (fed :...`
- **salary_reasonable_limit** (Section162)
  - `theorem salary_reasonable_limit (e : Expense) (reasonable : Currency) (rendered : Bool) : e.type ...`
- **exec_comp_capped_at_1m** (Section162)
  - `theorem exec_comp_capped_at_1m : deductibleAmount example_exec_comp_capped = 1000000`
- **exec_comp_cap_enforced** (Section162)
  - `theorem exec_comp_cap_enforced (e : Expense) (amt : Currency) : e.type = ExpenseType.ExecutiveCom...`
- **exec_comp_no_cap_private** (Section162)
  - `theorem exec_comp_no_cap_private (e : Expense) (amt : Currency) : e.type = ExpenseType.ExecutiveC...`
- **exec_comp_no_cap_non_covered** (Section162)
  - `theorem exec_comp_no_cap_non_covered (e : Expense) (amt : Currency) : e.type = ExpenseType.Execut...`
- **imputed_interest_le_carrying_charges** (Section163)
  - `theorem imputed_interest_le_carrying_charges (c : Contract) (h_charges : 0 ≤ c.carrying_charges_a...`
- **imputed_interest_nonnegative** (Section163)
  - `theorem imputed_interest_nonnegative (c : Contract) (h_charges : 0 ≤ c.carrying_charges_attributa...`
- **investment_interest_limit_respects_net_income** (Section163)
  - `theorem investment_interest_limit_respects_net_income (ctx : InvestmentContext) : allowed_investm...`
- **investment_interest_limit_respects_total** (Section163)
  - `theorem investment_interest_limit_respects_total (ctx : InvestmentContext) : allowed_investment_i...`
- **carryforward_nonnegative** (Section163)
  - `theorem carryforward_nonnegative (ctx : InvestmentContext) : 0 ≤ disallowed_investment_interest_c...`
- **total_allowed_interest_deduction_nonnegative** (Section163)
  - `theorem total_allowed_interest_deduction_nonnegative (t : Taxpayer163) (h_contracts_charges : ∀ c...`
- **deduction_nonnegative** (Section164)
  - `theorem deduction_nonnegative (payments : List TaxPaymentInfo) (election : TaxpayerElection) (h_p...`
- **deduction_nonnegative** (Section166)
  - `theorem deduction_nonnegative (d : Debt) (h_basis : d.adjusted_basis ≥ 0) : (calculate_deduction ...`
- **nonbusiness_worthless_is_short_term_capital_loss** (Section166)
  - `theorem nonbusiness_worthless_is_short_term_capital_loss (d : Debt) (h_nonbusiness : ¬d.is_busine...`
- **partial_business_deduction_limit** (Section166)
  - `theorem partial_business_deduction_limit (d : Debt) (h_business : d.is_business_debt) (h_partial ...`
- **Rat** (Section168)
  - `theorem Rat.toCurrency_nonneg (r : Rat) (h : r ≥ 0) : Rat.toCurrency r ≥ 0`
- **getDepreciationRate_nonneg** (Section168)
  - `theorem getDepreciationRate_nonneg (m : DepreciationMethod) (r : Rat) (h : r > 0) : getDepreciati...`
- **getFirstYearFraction_nonneg** (Section168)
  - `theorem getFirstYearFraction_nonneg (c : Convention) (d : Date) (h_valid : d.month ≥ 1 ∧ d.month ...`
- **depreciationLoop_nonneg** (Section168)
  - `theorem depreciationLoop_nonneg (fuel : Nat) (yearIdx : Nat) (currentBasis : Rat) (accumulatedDep...`
- **depreciation_nonneg** (Section168)
  - `theorem depreciation_nonneg (p : Property) (yearProperties : List Property) (h_basis : p.basis ≥ ...`
- **depreciationLoop2_nonneg** (Section168)
  - `theorem depreciationLoop2_nonneg (fuel : Nat) (yearIdx : Nat) (currentBasis : Rat) (switchedToSL ...`
- **allowable_deduction_le_business_income** (Section179)
  - `theorem allowable_deduction_le_business_income (t : Taxpayer) : allowable_deduction t ≤ t.busines...`
- **allowable_deduction_le_dollar_limit** (Section179)
  - `theorem allowable_deduction_le_dollar_limit (t : Taxpayer) : allowable_deduction t ≤ calculated_d...`
- **suv_cost_le_limit** (Section179)
  - `theorem suv_cost_le_limit (p : Section179Property) (h : p.type = PropertyType.SportUtilityVehicle...`
- **example3_limit_correct** (Section179)
  - `theorem example3_limit_correct : calculated_dollar_limitation (total_cost_placed_in_service taxpa...`
- **section2001_b_computation_nonneg** (Section2001)
  - `theorem section2001_b_computation_nonneg (input : Section2001Input) : 0 ≤ section2001_b_computati...`
- **credit_nonneg** (Section21)
  - `theorem credit_nonneg (agi : Currency) (status : FilingStatus) (expenses : List Expense) (people ...`
- **allowance_nonnegative** (Section24)
  - `theorem allowance_nonnegative (t : Taxpayer) (year : TaxYear) : allowance_of_credit t year ≥ 0`
- **limitation_nonnegative** (Section24)
  - `theorem limitation_nonnegative (t : Taxpayer) (year : TaxYear) : limitation_based_on_agi t year ≥ 0`
- **credit_after_limitation_nonnegative** (Section24)
  - `theorem credit_after_limitation_nonnegative (t : Taxpayer) (year : TaxYear) : credit_after_agi_li...`
- **refundable_credit_nonnegative** (Section24)
  - `theorem refundable_credit_nonnegative (t : Taxpayer) (year : TaxYear) : refundable_credit t year ≥ 0`
- **refundable_le_allowable** (Section24)
  - `theorem refundable_le_allowable (t : Taxpayer) (year : TaxYear) : refundable_credit t year ≤ cred...`
- **final_credit_nonnegative** (Section24)
  - `theorem final_credit_nonnegative (t : Taxpayer) (year : TaxYear) (h_limit : t.tax_liability_limit...`
- **credit_nonneg_all_years** (Section24)
  - `theorem credit_nonneg_all_years (t : Taxpayer) (ty : TaxYear) : final_credit t ty ≥ 0`
- **credit_nonneg** (Section25)
  - `theorem credit_nonneg (mcc : MortgageCreditCertificate) (interestPaid : Currency) (ownershipInter...`
- **credit_limit_check** (Section25)
  - `theorem credit_limit_check (mcc : MortgageCreditCertificate) (interestPaid : Currency) (ownership...`
- **gift_limit_check** (Section274)
  - `theorem gift_limit_check (ctx : TaxContext) (e : Expense) (details : GiftDetails) : e.category = ...`
- **amountDistributed_nonneg** (Section301)
  - `theorem amountDistributed_nonneg (d : Distribution) : amountDistributed d ≥ 0`
- **gain_non_negative** (Section311)
  - `theorem gain_non_negative (input : CalculationInput) : calculateRecognizedGain input ≥ 0`
- **gain_formula_correct** (Section311)
  - `theorem gain_formula_correct (input : CalculationInput) (h_not_liq : ¬input.distribution.isComple...`
- **credit_nonnegative** (Section32)
  - `theorem credit_nonnegative (tp : TaxpayerProfile) (tax_year : TaxYear) : calculate_credit tp tax_...`
- **investment_limit_2024** (Section32)
  - `theorem investment_limit_2024 (ty : TaxYear) : ty.year ≥ 2024 → get_investment_income_limit ty = ...`
- **investment_limit_2023** (Section32)
  - `theorem investment_limit_2023 (ty : TaxYear) : ty.year = 2023 → get_investment_income_limit ty = ...`
- **investment_limit_2022** (Section32)
  - `theorem investment_limit_2022 (ty : TaxYear) : ty.year < 2023 → get_investment_income_limit ty = ...`
- **credit_nonnegative** (Section32)
  - `theorem credit_nonnegative (tp : TaxpayerProfile) (tax_year : TaxYear) : calculate_credit tp tax_...`
- **investment_limit_2024** (Section32)
  - `theorem investment_limit_2024 (ty : TaxYear) : ty.year ≥ 2024 → get_investment_income_limit ty = ...`
- **investment_limit_2023** (Section32)
  - `theorem investment_limit_2023 (ty : TaxYear) : ty.year = 2023 → get_investment_income_limit ty = ...`
- **investment_limit_2022** (Section32)
  - `theorem investment_limit_2022 (ty : TaxYear) : ty.year < 2023 → get_investment_income_limit ty = ...`
- **nondiscrimination_passed_if_no_hce** (Section401)
  - `theorem nondiscrimination_passed_if_no_hce (participants : List Employee) (contribution_map : Str...`
- **integrated_db_limit_non_negative** (Section401)
  - `theorem integrated_db_limit_non_negative (final_pay : Currency) (federal_benefit : Currency) : ca...`
- **nondiscrimination_passed_if_no_hce** (Section401)
  - `theorem nondiscrimination_passed_if_no_hce (participants : List Employee) (contribution_map : Str...`
- **integrated_db_limit_non_negative** (Section401)
  - `theorem integrated_db_limit_non_negative (final_pay : Currency) (federal_benefit : Currency) : ca...`
- **research_credit_nonneg** (Section41)
  - `theorem research_credit_nonneg (inputs : Section41Inputs) (h_wages : inputs.wages_qualified_servi...`
- **passive_loss_nonneg** (Section469)
  - `theorem passive_loss_nonneg (t : Taxpayer) (activities : List (Activity × ActivityContext)) : cal...`
- **passive_credit_nonneg** (Section469)
  - `theorem passive_credit_nonneg (t : Taxpayer) (activities : List (Activity × ActivityContext)) (ta...`
- **loss_is_zero_if_income_nonneg** (Section469)
  - `theorem loss_is_zero_if_income_nonneg (t : Taxpayer) (activities : List (Activity × ActivityConte...`
- **carryover_reduces_income** (Section469)
  - `theorem carryover_reduces_income (a : Activity) (loss : Currency) (h_loss : loss ≥ 0) : (applyCar...`
- **amt_nonnegative** (Section55)
  - `theorem amt_nonnegative (tmt : Currency) (reg_tax : Currency) (tax_59A : Currency) : alternative_...`
- **tmt_noncorporate_nonnegative** (Section55)
  - `theorem tmt_noncorporate_nonnegative (status : FilingStatus) (excess : Currency) (ftc : Currency)...`
- **mining_deduction_is_10_percent** (Section56)
  - `theorem mining_deduction_is_10_percent (mc : MiningCost) (year : Nat) : year >= mc.yearIncurred ∧...`
- **example_mining_deduction_check** (Section56)
  - `theorem example_mining_deduction_check : calculateAMTMiningDeduction exampleMiningCost 2024 = Nat...`
- **amt_foreign_tax_credit_nonneg** (Section59)
  - `theorem amt_foreign_tax_credit_nonneg (input : AMTForeignTaxCreditInput) (h_pre : input.preCredit...`
- **gross_income_nonneg** (Section61)
  - `theorem gross_income_nonneg (input : GrossIncomeInput) (h : ∀ s ∈ input.sources, s.amount ≥ 0) : ...`
- **agi_le_gross_income** (Section62)
  - `theorem agi_le_gross_income (data : TaxpayerData) (h : validDeductions data) : calculateAGI data ...`
- **educator_deduction_bounded** (Section62)
  - `theorem educator_deduction_bounded (data : TaxpayerData) : min data.educatorExpenses educatorExpe...`
- **taxable_le_agi** (Section63)
  - `theorem taxable_le_agi (input : TaxableIncomeInput) (h : input.adjustedGrossIncome ≥ 0) : calcula...`
- **taxable_nonneg** (Section63)
  - `theorem taxable_nonneg (input : TaxableIncomeInput) : calculateTaxableIncome input ≥ 0`
- **ordinary_income_nonnegative** (Section64)
  - `theorem ordinary_income_nonnegative (gains : List PropertyGain) (h : ∀ g ∈ gains, (g.amount : Int...`
- **ordinary_loss_nonpositive** (Section65)
  - `theorem ordinary_loss_nonpositive (losses : List PropertyLoss) (h : ∀ l ∈ losses, (l.amount : Int...`
- **noncapital_is_ordinary** (Section65)
  - `theorem noncapital_is_ordinary (l : PropertyLoss) (h : l.isCapitalAsset = false) : isOrdinaryLoss...`

### Eligibility (31)

- **qualified_private_activity_exempt** (Section103)
  - `theorem qualified_private_activity_exempt (b : Bond) (h_local : isStateOrLocal b) (h_pab : isPriv...`
- **qualified_private_activity_exempt** (Section103)
  - `theorem qualified_private_activity_exempt (b : Bond) (h_local : isStateOrLocal b) (h_pab : isPriv...`
- **qualified_private_activity_exempt** (Section103)
  - `theorem qualified_private_activity_exempt (b : Bond) (h_local : isStateOrLocal b) (h_pab : isPriv...`
- **qualified_private_activity_exempt** (Section103)
  - `theorem qualified_private_activity_exempt (b : Bond) (h_local : isStateOrLocal b) (h_pab : isPriv...`
- **c_corp_ineligible_qrpb** (Section108)
  - `theorem c_corp_ineligible_qrpb (d : DischargeIndebtedness) (s : TaxpayerStatus) (e : TaxpayerElec...`
- **excluded_gain_le_limit** (Section121)
  - `theorem excluded_gain_le_limit (filingStatus : FilingStatus) (t1 : Taxpayer) (t2 : Option Taxpaye...`
- **foreign_travel_exception_applies** (Section274)
  - `theorem foreign_travel_exception_applies (ctx : TaxContext) (e : Expense) (days business : Nat) :...`
- **ineligible_credit_zero** (Section32)
  - `theorem ineligible_credit_zero (tp : TaxpayerProfile) (tax_year : TaxYear) (h : ¬is_eligible_indi...`
- **excess_investment_income_ineligible** (Section32)
  - `theorem excess_investment_income_ineligible (tp : TaxpayerProfile) (ty : TaxYear) : tp.investment...`
- **investment_income_ok_may_qualify** (Section32)
  - `theorem investment_income_ok_may_qualify (tp : TaxpayerProfile) (ty : TaxYear) : tp.investment_in...`
- **mfs_always_ineligible** (Section32)
  - `theorem mfs_always_ineligible (tp : TaxpayerProfile) (ty : TaxYear) : tp.filing_status = FilingSt...`
- **non_mfs_may_qualify** (Section32)
  - `theorem non_mfs_may_qualify (tp : TaxpayerProfile) (ty : TaxYear) : tp.filing_status ≠ FilingStat...`
- **single_filer_may_qualify** (Section32)
  - `theorem single_filer_may_qualify : ∃ (tp : TaxpayerProfile) (ty : TaxYear), tp.filing_status = Fi...`
- **ineligible_implies_zero_credit** (Section32)
  - `theorem ineligible_implies_zero_credit (tp : TaxpayerProfile) (ty : TaxYear) : is_eligible_indivi...`
- **ineligible_credit_zero** (Section32)
  - `theorem ineligible_credit_zero (tp : TaxpayerProfile) (tax_year : TaxYear) (h : ¬is_eligible_indi...`
- **excess_investment_income_ineligible** (Section32)
  - `theorem excess_investment_income_ineligible (tp : TaxpayerProfile) (ty : TaxYear) : tp.investment...`
- **investment_income_ok_may_qualify** (Section32)
  - `theorem investment_income_ok_may_qualify (tp : TaxpayerProfile) (ty : TaxYear) : tp.investment_in...`
- **mfs_always_ineligible** (Section32)
  - `theorem mfs_always_ineligible (tp : TaxpayerProfile) (ty : TaxYear) : tp.filing_status = FilingSt...`
- **non_mfs_may_qualify** (Section32)
  - `theorem non_mfs_may_qualify (tp : TaxpayerProfile) (ty : TaxYear) : tp.filing_status ≠ FilingStat...`
- **non_mfs_may_qualify** (Section32)
  - `theorem non_mfs_may_qualify (tp : TaxpayerProfile) (ty : TaxYear) : tp.filing_status ≠ FilingStat...`
- **ineligible_implies_zero_credit** (Section32)
  - `theorem ineligible_implies_zero_credit (tp : TaxpayerProfile) (ty : TaxYear) : is_eligible_indivi...`
- **qualified_implies_coverage** (Section401)
  - `theorem qualified_implies_coverage (plan : Plan) (all_employees : List Employee) (contribution_ma...`
- **qualified_implies_coverage** (Section401)
  - `theorem qualified_implies_coverage (plan : Plan) (all_employees : List Employee) (contribution_ma...`
- **valid_ira_implies_written_instrument** (Section408)
  - `theorem valid_ira_implies_written_instrument (ira : IndividualRetirementAccount) (year : TaxYear)...`
- **valid_ira_contribution_limit** (Section408)
  - `theorem valid_ira_contribution_limit (ira : IndividualRetirementAccount) (year : TaxYear) (contri...`
- **valid_annuity_non_transferable** (Section408)
  - `theorem valid_annuity_non_transferable (annuity : IndividualRetirementAnnuity) (year : TaxYear) :...`
- **valid_employer_trust_nonforfeitable** (Section408)
  - `theorem valid_employer_trust_nonforfeitable (et : EmployerTrust) (year : TaxYear) (contributions ...`
- **capital_gains_excluded** (Section64)
  - `theorem capital_gains_excluded (g : PropertyGain) (h : g.propertyType = PropertyType.CapitalAsset...`
- **capital_losses_excluded** (Section65)
  - `theorem capital_losses_excluded (l : PropertyLoss) (h : l.isCapitalAsset = true) : isOrdinaryLoss...`
- **repeal_applies_post_2018** (Section71)
  - `theorem repeal_applies_post_2018 (instr : DivorceInstrument) (h : instr.executionDate > date_Dec_...`
- **repeal_applies_modification** (Section71)
  - `theorem repeal_applies_modification (instr : DivorceInstrument) (h_exec : instr.executionDate ≤ d...`

### Equivalence (16)

- **exclusion_eq_amount_received_for_simple_death_benefit** (Section101)
  - `theorem exclusion_eq_amount_received_for_simple_death_benefit (payout : InsurancePayout) (h_death...`
- **adjustedBasis_eq_general_of_not_charitable** (Section1011)
  - `theorem adjustedBasis_eq_general_of_not_charitable (prop : PropertyDisposition) (h : prop.isChari...`
- **adjustedBasis_bargain_eq_general_of_full_realization** (Section1011)
  - `theorem adjustedBasis_bargain_eq_general_of_full_realization (prop : PropertyDisposition) (h_char...`
- **trust_basis_gain_eq_loss** (Section1015)
  - `theorem trust_basis_gain_eq_loss (info : TrustInfo) : (calc_basis_trust info).gainBasis = (calc_b...`
- **gift_basis_eq_if_donor_eq_fmv** (Section1015)
  - `theorem gift_basis_eq_if_donor_eq_fmv (info : GiftInfo) (h : info.donorBasis = info.fmvAtGift) : ...`
- **taxable_eq_zero_of_exempt** (Section103)
  - `theorem taxable_eq_zero_of_exempt (b : Bond) (h : isTaxExempt b) : taxableInterest b = 0`
- **exempt_eq_zero_of_not_exempt** (Section103)
  - `theorem exempt_eq_zero_of_not_exempt (b : Bond) (h : ¬isTaxExempt b) : taxExemptInterest b = 0`
- **taxable_eq_zero_of_exempt** (Section103)
  - `theorem taxable_eq_zero_of_exempt (b : Bond) (h : isTaxExempt b) : taxableInterest b = 0`
- **exempt_eq_zero_of_not_exempt** (Section103)
  - `theorem exempt_eq_zero_of_not_exempt (b : Bond) (h : ¬isTaxExempt b) : taxExemptInterest b = 0`
- **life_tenant_deduction_eq_total** (Section167)
  - `theorem life_tenant_deduction_eq_total (d : Currency) (inc tot : Currency) : calculateDeductionAl...`
- **calculateDepreciationSchedule_eq_prime** (Section168)
  - `theorem calculateDepreciationSchedule_eq_prime (p : Property) (yearProperties : List Property) : ...`
- **calculateDepreciationSchedule_eq_calculateDepreciationSchedule2** (Section168)
  - `theorem calculateDepreciationSchedule_eq_calculateDepreciationSchedule2 (p : Property) (yearPrope...`
- **foldl_add_eq_sum_map** (Section174)
  - `lemma foldl_add_eq_sum_map {α : Type} (l : List α) (f : α → Currency) : l.foldl (fun s x => s + f...`
- **taxableAmount_sum_eq_amountDistributed** (Section301)
  - `theorem taxableAmount_sum_eq_amountDistributed (d : Distribution) (s : Stock) : let ta`
- **general_business_credit_eq_sum** (Section38)
  - `theorem general_business_credit_eq_sum (inputs : GeneralBusinessCreditInputs) : calc_general_busi...`
- **qre_eq_in_house_plus_contract** (Section41)
  - `theorem qre_eq_in_house_plus_contract (inputs : Section41Inputs) : calc_qualified_research_expens...`

### Examples (31)

- **example_tax_single_50k** (Section1)
  - `theorem example_tax_single_50k : calculate_tax FilingStatus.Single (dollars 50000) = dollars 11127`
- **example_tax_joint_100k** (Section1)
  - `theorem example_tax_joint_100k : calculate_tax FilingStatus.MarriedFilingJointly (dollars 100000)...`
- **exclusion_full_for_exception_to_transfer_for_value** (Section101)
  - `theorem exclusion_full_for_exception_to_transfer_for_value (payout : InsurancePayout) (transfer :...`
- **example1_correct** (Section1014)
  - `theorem example1_correct : calculateBasis example1_details = some 100000`
- **example2_correct** (Section1014)
  - `theorem example2_correct : calculateBasis example2_details = none`
- **example3_correct** (Section1014)
  - `theorem example3_correct : calculateBasis example3_details = some 95000`
- **example_1_gift_gain** (Section1015)
  - `theorem example_1_gift_gain : calc_basis_gift { dateOfGift`
- **example_2_gift_loss** (Section1015)
  - `theorem example_2_gift_loss : calc_basis_gift { dateOfGift`
- **example_3_gift_tax** (Section1015)
  - `theorem example_3_gift_tax : calc_basis_gift { dateOfGift`
- **example_5_trust** (Section1015)
  - `theorem example_5_trust : calc_basis_trust { dateOfTransfer`
- **nol_reduction_correct** (Section108)
  - `theorem nol_reduction_correct (excluded : Currency) (s : TaxpayerStatus) : (reduceAttributes excl...`
- **gbc_reduction_correct** (Section108)
  - `theorem gbc_reduction_correct (excluded : Currency) (s : TaxpayerStatus) : let rem_after_nol`
- **term_interest_disallowed_result_corrected** (Section167)
  - `theorem term_interest_disallowed_result_corrected (tr : TaxReturn167) (h_term : tr.property.isTer...`
- **deduction_sum_correct** (Section174)
  - `theorem deduction_sum_correct (e : Expenditure) (h_elig : is_foreign_research_or_experimental e) ...`
- **example1_correct** (Section179)
  - `theorem example1_correct : allowable_deduction taxpayer1 = 100000`
- **example2_correct** (Section179)
  - `theorem example2_correct : allowable_deduction taxpayer_suv = 25000`
- **example3_deduction_correct** (Section179)
  - `theorem example3_deduction_correct : allowable_deduction taxpayer_large = 2400000`
- **example4_deduction_correct** (Section179)
  - `theorem example4_deduction_correct : allowable_deduction taxpayer_low_income = 50000`
- **example4_carryover_correct** (Section179)
  - `theorem example4_carryover_correct : calculate_carryover taxpayer_low_income = 50000`
- **transportation_costs_independent_refiners_correct** (Section199)
  - `theorem transportation_costs_independent_refiners_correct (input : Section199Input) : let year`
- **total_w2_wages_correct** (Section199)
  - `theorem total_w2_wages_correct (input : Section199Input) : let year`
- **allowance_uses_correct_parameters** (Section24)
  - `theorem allowance_uses_correct_parameters (t : Taxpayer) (ty : TaxYear) : allowance_of_credit t t...`
- **threshold_uses_correct_parameters** (Section24)
  - `theorem threshold_uses_correct_parameters (status : FilingStatus) (ty : TaxYear) : threshold_amou...`
- **example_1_value** (Section32)
  - `theorem example_1_value : calculate_credit example_profile_1 example_tax_year = 1611`
- **example_2_value** (Section32)
  - `theorem example_2_value : calculate_credit example_profile_2 example_tax_year = 737`
- **example_1_value** (Section32)
  - `theorem example_1_value : calculate_credit example_profile_1 example_tax_year = 1611`
- **example_2_value** (Section32)
  - `theorem example_2_value : calculate_credit example_profile_2 example_tax_year = 737`
- **example_calculation_correct** (Section38)
  - `theorem example_calculation_correct : calc_general_business_credit example_inputs = 2000`
- **example_calculation_correct** (Section41)
  - `theorem example_calculation_correct : calc_research_credit example_inputs = 16300`
- **example_contract_income_check** (Section56)
  - `theorem example_contract_income_check : calculateAMTContractIncome exampleContract = Nat.toCurren...`
- **example_agi_correct** (Section62)
  - `theorem example_agi_correct : calculateAGI exampleTaxpayer = 8699750`

### Implications (35)

- **isTaxExempt_iff** (Section103)
  - `theorem isTaxExempt_iff (b : Bond) : isTaxExempt b = true ↔ (isStateOrLocal b = true) ∧ (isPrivat...`
- **private_loan_threshold_small_issue** (Section103)
  - `theorem private_loan_threshold_small_issue (proceeds : Rat) : proceeds ≤ 100000000 → min (5000000...`
- **private_loan_threshold_large_issue** (Section103)
  - `theorem private_loan_threshold_large_issue (proceeds : Rat) : proceeds > 100000000 → min (5000000...`
- **federally_guaranteed_not_exempt** (Section103)
  - `theorem federally_guaranteed_not_exempt (b : Bond) : isStateOrLocal b = true → b.isFederallyGuara...`
- **federal_guarantee_checked_first** (Section103)
  - `theorem federal_guarantee_checked_first (b : Bond) : b.isFederallyGuaranteed = true → isStateOrLo...`
- **isTaxExempt_iff** (Section103)
  - `theorem isTaxExempt_iff (b : Bond) : isTaxExempt b = true ↔ (isStateOrLocal b = true) ∧ (isPrivat...`
- **private_loan_threshold_small_issue** (Section103)
  - `theorem private_loan_threshold_small_issue (proceeds : Rat) : proceeds ≤ 100000000 → min (5000000...`
- **private_loan_threshold_large_issue** (Section103)
  - `theorem private_loan_threshold_large_issue (proceeds : Rat) : proceeds > 100000000 → min (5000000...`
- **federally_guaranteed_not_exempt** (Section103)
  - `theorem federally_guaranteed_not_exempt (b : Bond) : isStateOrLocal b = true → b.isFederallyGuara...`
- **federal_guarantee_checked_first** (Section103)
  - `theorem federal_guarantee_checked_first (b : Bond) : b.isFederallyGuaranteed = true → isStateOrLo...`
- **title11_exclusion_full** (Section108)
  - `theorem title11_exclusion_full (d : DischargeIndebtedness) (s : TaxpayerStatus) (e : TaxpayerElec...`
- **title11_precedence** (Section108)
  - `theorem title11_precedence (d : DischargeIndebtedness) (s : TaxpayerStatus) (e : TaxpayerElection...`
- **section_11_domestic_tax** (Section11)
  - `theorem section_11_domestic_tax (c : Corporation) (y : TaxYear) (i : Currency) : ¬c.is_foreign → ...`
- **section_11_foreign_corporation** (Section11)
  - `theorem section_11_foreign_corporation (c : Corporation) (y : TaxYear) (i : Currency) : c.is_fore...`
- **section_11_exception_594** (Section11)
  - `theorem section_11_exception_594 (c : Corporation) (y : TaxYear) (i : Currency) : c.subject_to_se...`
- **section_11_exception_subchapter_L** (Section11)
  - `theorem section_11_exception_subchapter_L (c : Corporation) (y : TaxYear) (i : Currency) : c.subj...`
- **section_11_exception_subchapter_M** (Section11)
  - `theorem section_11_exception_subchapter_M (c : Corporation) (y : TaxYear) (i : Currency) : c.subj...`
- **private_penalty_deductible_general** (Section162)
  - `theorem private_penalty_deductible_general (e : Expense) (amt : Currency) : e.type = ExpenseType....`
- **private_penalty_deductible_general** (Section162)
  - `theorem private_penalty_deductible_general (e : Expense) (amt : Currency) : e.type = ExpenseType....`
- **acquisition_disposition_exception** (Section164)
  - `theorem acquisition_disposition_exception (info : TaxPaymentInfo) (election : TaxpayerElection) :...`
- **int_mono_glue** (Section2001)
  - `lemma int_mono_glue {f g : Int → Int} {c : Int} (hf : ∀ x y, x ≤ y → y ≤ c → f x ≤ f y) (hg : ∀ x...`
- **tcja_parameters_2018_2025** (Section24)
  - `theorem tcja_parameters_2018_2025 (ty : TaxYear) : ty.year ≥ 2018 ∧ ty.year ≤ 2025 → let params`
- **pre_tcja_parameters** (Section24)
  - `theorem pre_tcja_parameters (ty : TaxYear) : ty.year < 2018 → let params`
- **post_tcja_parameters** (Section24)
  - `theorem post_tcja_parameters (ty : TaxYear) : ty.year > 2025 → let params`
- **tcja_doubles_credit** (Section24)
  - `theorem tcja_doubles_credit (ty_pre ty_tcja : TaxYear) : ty_pre.year < 2018 → ty_tcja.year ≥ 2018...`
- **tcja_higher_threshold_mfj** (Section24)
  - `theorem tcja_higher_threshold_mfj (ty_pre ty_tcja : TaxYear) : ty_pre.year < 2018 → ty_tcja.year ...`
- **tcja_lower_earned_income_threshold** (Section24)
  - `theorem tcja_lower_earned_income_threshold (ty_pre ty_tcja : TaxYear) : ty_pre.year < 2018 → ty_t...`
- **eligibility_requirements_complete** (Section32)
  - `theorem eligibility_requirements_complete (tp : TaxpayerProfile) (ty : TaxYear) : is_eligible_ind...`
- **eligibility_requirements_complete** (Section32)
  - `theorem eligibility_requirements_complete (tp : TaxpayerProfile) (ty : TaxYear) : is_eligible_ind...`
- **loss_is_magnitude_if_income_neg** (Section469)
  - `theorem loss_is_magnitude_if_income_neg (t : Taxpayer) (activities : List (Activity × ActivityCon...`
- **section482_authority** (Section482)
  - `theorem section482_authority (group : ControlGroup) (proposed : List Organization) (reason : Allo...`
- **allocation_preserves_total_income** (Section482)
  - `theorem allocation_preserves_total_income (group : ControlGroup) (proposed : List Organization) (...`
- **allocation_preserves_total_deductions** (Section482)
  - `theorem allocation_preserves_total_deductions (group : ControlGroup) (proposed : List Organizatio...`
- **allocation_preserves_total_credits** (Section482)
  - `theorem allocation_preserves_total_credits (group : ControlGroup) (proposed : List Organization) ...`
- **allocation_preserves_total_allowances** (Section482)
  - `theorem allocation_preserves_total_allowances (group : ControlGroup) (proposed : List Organizatio...`

### Linearity (3)

- **split_gift_tax_additive** (Section1015)
  - `theorem split_gift_tax_additive (t1 t2 : Currency) : calculate_split_gift_tax t1 t2 = t1 + t2`
- **additivity** (Section61)
  - `theorem additivity (sources1 sources2 : List IncomeSource) : calculateGrossIncome {sources`
- **agi_linear_gross_income** (Section62)
  - `theorem agi_linear_gross_income (data : TaxpayerData) (k : Currency) : calculateAGI { data with g...`

### Monotonicity (8)

- **calculate_percent_monotonic** (Section1)
  - `lemma calculate_percent_monotonic (r d : Int) (hr : 0 ≤ r) (hd : 0 < d) : Monotone (fun (i : Curr...`
- **tax_section1_a_monotonic** (Section1)
  - `lemma tax_section1_a_monotonic : Monotone tax_section1_a`
- **tax_section1_b_monotonic** (Section1)
  - `lemma tax_section1_b_monotonic : Monotone tax_section1_b`
- **tax_section1_c_monotonic** (Section1)
  - `lemma tax_section1_c_monotonic : Monotone tax_section1_c`
- **tax_section1_d_monotonic** (Section1)
  - `lemma tax_section1_d_monotonic : Monotone tax_section1_d`
- **tax_section1_e_monotonic** (Section1)
  - `lemma tax_section1_e_monotonic : Monotone tax_section1_e`
- **tax_monotonic** (Section1)
  - `theorem tax_monotonic (status : FilingStatus) (i1 i2 : Currency) (h1 : 0 ≤ i1) (h2 : i1 ≤ i2) : c...`
- **section2001_c_rate_schedule_monotone** (Section2001)
  - `theorem section2001_c_rate_schedule_monotone (a b : Currency) (h : a ≤ b) : section2001_c_rate_sc...`

### Other (78)

- **tax_section1_a_boundary_1_continuous** (Section1)
  - `theorem tax_section1_a_boundary_1_continuous : calculate_percent (dollars 36900) 15 100 = dollars...`
- **tax_section1_a_boundary_2_continuous** (Section1)
  - `theorem tax_section1_a_boundary_2_continuous : dollars 5535 + calculate_percent (dollars 89150 - ...`
- **tax_section1_a_boundary_3_continuous** (Section1)
  - `theorem tax_section1_a_boundary_3_continuous : dollars 20165 + calculate_percent (dollars 140000 ...`
- **tax_section1_a_boundary_4_continuous** (Section1)
  - `theorem tax_section1_a_boundary_4_continuous : dollars_and_cents 35928 50 + calculate_percent (do...`
- **tax_section1_b_boundary_1_continuous** (Section1)
  - `theorem tax_section1_b_boundary_1_continuous : calculate_percent (dollars 29600) 15 100 = dollars...`
- **tax_section1_b_boundary_2_continuous** (Section1)
  - `theorem tax_section1_b_boundary_2_continuous : dollars 4440 + calculate_percent (dollars 76400 - ...`
- **tax_section1_b_boundary_3_continuous** (Section1)
  - `theorem tax_section1_b_boundary_3_continuous : dollars 17544 + calculate_percent (dollars 127500 ...`
- **tax_section1_b_boundary_4_continuous** (Section1)
  - `theorem tax_section1_b_boundary_4_continuous : dollars 33385 + calculate_percent (dollars 250000 ...`
- **tax_section1_c_boundary_1_continuous** (Section1)
  - `theorem tax_section1_c_boundary_1_continuous : calculate_percent (dollars 22100) 15 100 = dollars...`
- **tax_section1_c_boundary_2_continuous** (Section1)
  - `theorem tax_section1_c_boundary_2_continuous : dollars 3315 + calculate_percent (dollars 53500 - ...`
- **tax_section1_c_boundary_3_continuous** (Section1)
  - `theorem tax_section1_c_boundary_3_continuous : dollars 12107 + calculate_percent (dollars 115000 ...`
- **tax_section1_c_boundary_4_continuous** (Section1)
  - `theorem tax_section1_c_boundary_4_continuous : dollars 31172 + calculate_percent (dollars 250000 ...`
- **tax_section1_d_boundary_1_continuous** (Section1)
  - `theorem tax_section1_d_boundary_1_continuous : calculate_percent (dollars 18450) 15 100 = dollars...`
- **tax_section1_d_boundary_2_continuous** (Section1)
  - `theorem tax_section1_d_boundary_2_continuous : dollars_and_cents 2767 50 + calculate_percent (dol...`
- **tax_section1_d_boundary_3_continuous** (Section1)
  - `theorem tax_section1_d_boundary_3_continuous : dollars_and_cents 10082 50 + calculate_percent (do...`
- **tax_section1_d_boundary_4_continuous** (Section1)
  - `theorem tax_section1_d_boundary_4_continuous : dollars_and_cents 17964 25 + calculate_percent (do...`
- **tax_section1_e_boundary_1_continuous** (Section1)
  - `theorem tax_section1_e_boundary_1_continuous : calculate_percent (dollars 1500) 15 100 = dollars 225`
- **tax_section1_e_boundary_2_continuous** (Section1)
  - `theorem tax_section1_e_boundary_2_continuous : dollars 225 + calculate_percent (dollars 3500 - do...`
- **tax_section1_e_boundary_3_continuous** (Section1)
  - `theorem tax_section1_e_boundary_3_continuous : dollars 785 + calculate_percent (dollars 5500 - do...`
- **tax_section1_e_boundary_4_continuous** (Section1)
  - `theorem tax_section1_e_boundary_4_continuous : dollars 1405 + calculate_percent (dollars 7500 - d...`
- **int_gain_loss_identity** (Section1001)
  - `lemma int_gain_loss_identity (a b : Int) : (if a > b then a - b else 0) - (if b > a then b - a el...`
- **interest_is_fully_included** (Section101)
  - `theorem interest_is_fully_included (agreement : InterestAgreement) (h_held : agreement.isHeldUnde...`
- **election_unifies_accounts** (Section1012)
  - `theorem election_unifies_accounts (acct : Account) (p1 p2 : Property) (h_stock1 : match p1.type w...`
- **drp_stock_allows_average_basis** (Section1012)
  - `theorem drp_stock_allows_average_basis (acct : Account) (p : Property) (h_drp : match p.type with...`
- **basis_none_if_disposed_before_death** (Section1014)
  - `theorem basis_none_if_disposed_before_death (details : PropertyDetails) (h_disposed : details.dis...`
- **basis_section2032_elected** (Section1014)
  - `theorem basis_section2032_elected (details : PropertyDetails) (h_not_disposed : details.dispositi...`
- **basis_section2032A_elected** (Section1014)
  - `theorem basis_section2032A_elected (details : PropertyDetails) (h_not_disposed : details.disposit...`
- **basis_default_fmv** (Section1014)
  - `theorem basis_default_fmv (details : PropertyDetails) (h_not_disposed : details.dispositionDate =...`
- **gift_tax_no_increase_if_basis_gt_fmv** (Section1015)
  - `theorem gift_tax_no_increase_if_basis_gt_fmv (basis fmv tax : Currency) (h : basis ≥ fmv) : apply...`
- **interest_partition** (Section103)
  - `theorem interest_partition (b : Bond) : taxableInterest b + taxExemptInterest b = b.interest`
- **private_activity_taxable** (Section103)
  - `theorem private_activity_taxable (b : Bond) (h_local : isStateOrLocal b) (h_pab : isPrivateActivi...`
- **arbitrage_taxable** (Section103)
  - `theorem arbitrage_taxable (b : Bond) (h_local : isStateOrLocal b) (h_arb : b.isArbitrage) : ¬isTa...`
- **registration_required_not_exempt** (Section103)
  - `theorem registration_required_not_exempt (b : Bond) (h_local : isStateOrLocal b) (h_req : b.isReg...`
- **non_fed_guaranteed_may_be_exempt** (Section103)
  - `theorem non_fed_guaranteed_may_be_exempt : let b`
- **large_bond_loan_triggers_pab** (Section103)
  - `theorem large_bond_loan_triggers_pab : let b`
- **loan_test_strictly_greater** (Section103)
  - `theorem loan_test_strictly_greater (b : Bond) : let loanThreshold`
- **exactly_at_threshold_not_pab** (Section103)
  - `theorem exactly_at_threshold_not_pab : let b : Bond`
- **interest_partition** (Section103)
  - `theorem interest_partition (b : Bond) : taxableInterest b + taxExemptInterest b = b.interest`
- **private_activity_taxable** (Section103)
  - `theorem private_activity_taxable (b : Bond) (h_local : isStateOrLocal b) (h_pab : isPrivateActivi...`
- **arbitrage_taxable** (Section103)
  - `theorem arbitrage_taxable (b : Bond) (h_local : isStateOrLocal b) (h_arb : b.isArbitrage) : ¬isTa...`
- **registration_required_not_exempt** (Section103)
  - `theorem registration_required_not_exempt (b : Bond) (h_local : isStateOrLocal b) (h_req : b.isReg...`
- **non_fed_guaranteed_may_be_exempt** (Section103)
  - `theorem non_fed_guaranteed_may_be_exempt : let b`
- **large_bond_loan_triggers_pab** (Section103)
  - `theorem large_bond_loan_triggers_pab : let b`
- **loan_test_strictly_greater** (Section103)
  - `theorem loan_test_strictly_greater (b : Bond) : let loanThreshold`
- **exactly_at_threshold_not_pab** (Section103)
  - `theorem exactly_at_threshold_not_pab : let b : Bond`
- **private_penalty_deductible** (Section162)
  - `theorem private_penalty_deductible : deductibleAmount example_private_penalty = 10000`
- **new_provisions_coverage** (Section162)
  - `theorem new_provisions_coverage : ∃ (e1 e2 e3 : Expense), (∃ govt amt, e1.type = ExpenseType.Fine...`
- **private_penalty_deductible** (Section162)
  - `theorem private_penalty_deductible : deductibleAmount example_private_penalty = 10000`
- **new_provisions_coverage** (Section162)
  - `theorem new_provisions_coverage : ∃ (e1 e2 e3 : Expense), (∃ govt amt, e1.type = ExpenseType.Fine...`
- **sales_tax_election_effect** (Section164)
  - `theorem sales_tax_election_effect : let election_income`
- **personal_property_not_depreciable** (Section167)
  - `theorem personal_property_not_depreciable (p : Property) (h : p.propType = PropertyType.Personal)...`
- **related_term_interest_not_depreciable** (Section167)
  - `theorem related_term_interest_not_depreciable (p : Property) (h1 : p.isTermInterest = true) (h2 :...`
- **section_273_bypass** (Section167)
  - `theorem section_273_bypass (p : Property) (ext : ExternalStatutes) (h_term : p.isTermInterest = t...`
- **depreciationSchedule_nonEmpty** (Section168)
  - `theorem depreciationSchedule_nonEmpty (p : Property) (yearProperties : List Property) (h_basis : ...`
- **int_affine_mono** (Section2001)
  - `lemma int_affine_mono {x y m d c : Int} (h : x ≤ y) (hm : 0 ≤ m) (hd : 0 < d) : c + x * m / d ≤ c...`
- **int_affine_mono_general** (Section2001)
  - `lemma int_affine_mono_general {x y m d k c : Int} (h : x ≤ y) (hm : 0 ≤ m) (hd : 0 < d) : c + (x ...`
- **int_affine_mono_specific** (Section2001)
  - `lemma int_affine_mono_specific {x y A B C D : Int} (h : x ≤ y) (hC : 0 ≤ C) (hD : 0 < D) : A + (x...`
- **applicable_percentage_bounds** (Section21)
  - `theorem applicable_percentage_bounds (agi : Currency) (status : FilingStatus) : let p`
- **credit_respects_year_parameters** (Section24)
  - `theorem credit_respects_year_parameters (t : Taxpayer) (ty : TaxYear) : ∃ params : CreditParamete...`
- **citizen_resident_taxable** (Section2501)
  - `theorem citizen_resident_taxable (t : Transfer) (h_status : isTreatedAsCitizen t.donor = true ∨ t...`
- **nonresident_intangible_exempt** (Section2501)
  - `theorem nonresident_intangible_exempt (t : Transfer) (h_nonresident : isTreatedAsNonresidentNotCi...`
- **expatriate_intangible_taxable** (Section2501)
  - `theorem expatriate_intangible_taxable (t : Transfer) (h_nonresident : isTreatedAsNonresidentNotCi...`
- **political_org_exempt** (Section2501)
  - `theorem political_org_exempt (t : Transfer) (h_political : t.toPoliticalOrg = true) : isTaxableTr...`
- **exempt_org_exempt** (Section2501)
  - `theorem exempt_org_exempt (t : Transfer) (h_exempt : t.toExemptOrg = true) : isTaxableTransfer t ...`
- **expatriate_stock_valuation** (Section2501)
  - `theorem expatriate_stock_valuation (t : Transfer) (info : ForeignCorpInfo) (h_stock : t.property....`
- **decomposition_lemma_v2** (Section301)
  - `lemma decomposition_lemma_v2 (amount div_portion basis pre1913 : Currency) : let dividend`
- **coverage_passed_if_all_benefit** (Section401)
  - `theorem coverage_passed_if_all_benefit (all_employees : List Employee) (h_non_empty : all_employe...`
- **coverage_passed_if_all_benefit** (Section401)
  - `theorem coverage_passed_if_all_benefit (all_employees : List Employee) (h_non_empty : all_employe...`
- **rental_real_estate_active_if_material_participation** (Section469)
  - `theorem rental_real_estate_active_if_material_participation (t : Taxpayer) (a : Activity) (ctx : ...`
- **rental_passive_if_not_rpb** (Section469)
  - `theorem rental_passive_if_not_rpb (t : Taxpayer) (a : Activity) (ctx : ActivityContext) (h_type :...`
- **adjustTransfer_is_commensurate** (Section482)
  - `theorem adjustTransfer_is_commensurate (t : Transfer) : isCommensurate (adjustTransfer t) = true`
- **valuation_requirement** (Section482)
  - `theorem valuation_requirement (aggregateReliable : Bool) (realisticReliable : Bool) : let method`
- **depreciation_schedule_length** (Section56)
  - `theorem depreciation_schedule_length (fuel : Nat) (basis : Currency) (switched : Bool) (p : Prope...`
- **amt_depreciation_length** (Section56)
  - `theorem amt_depreciation_length (p : Property) : (calculateAMTDepreciation p).length = p.recovery...`
- **gross_income_empty** (Section61)
  - `theorem gross_income_empty : calculateGrossIncome {sources`
- **standard_deduction_single_2024** (Section63)
  - `theorem standard_deduction_single_2024 : let input : TaxableIncomeInput`
- **repeal_does_not_apply_no_mod** (Section71)
  - `theorem repeal_does_not_apply_no_mod (instr : DivorceInstrument) (h_exec : instr.executionDate ≤ ...`
- **repeal_does_not_apply_mod_no_adopt** (Section71)
  - `theorem repeal_does_not_apply_mod_no_adopt (instr : DivorceInstrument) (h_exec : instr.executionD...`

### Zero Conditions (28)

- **gain_loss_exclusive** (Section1001)
  - `theorem gain_loss_exclusive (d : Disposition) : gain d > 0 → loss d = 0`
- **adjustedBasis_bargain_fmv_zero** (Section1011)
  - `theorem adjustedBasis_bargain_fmv_zero (prop : PropertyDisposition) (h_charitable : prop.isCharit...`
- **transfer_basis_zero_fees** (Section1012)
  - `theorem transfer_basis_zero_fees (b : Currency) : transfer_basis b 0 = b`
- **illegal_bribe_not_deductible** (Section162)
  - `theorem illegal_bribe_not_deductible (e : Expense) (h_illegal : Bool) : e.type = ExpenseType.Brib...`
- **not_ordinary_or_necessary_not_deductible** (Section162)
  - `theorem not_ordinary_or_necessary_not_deductible (e : Expense) : ¬(e.ordinary ∧ e.necessary) → de...`
- **govt_fine_not_deductible** (Section162)
  - `theorem govt_fine_not_deductible : deductibleAmount example_govt_fine = 0`
- **lobbying_not_deductible** (Section162)
  - `theorem lobbying_not_deductible : deductibleAmount example_lobbying = 0`
- **govt_fine_always_zero** (Section162)
  - `theorem govt_fine_always_zero (e : Expense) (amt : Currency) : e.type = ExpenseType.FineOrPenalty...`
- **lobbying_always_zero** (Section162)
  - `theorem lobbying_always_zero (e : Expense) (direct : Bool) (amt : Currency) : e.type = ExpenseTyp...`
- **lobbying_direct_and_grassroots_zero** (Section162)
  - `theorem lobbying_direct_and_grassroots_zero (e : Expense) (amt : Currency) : (e.type = ExpenseTyp...`
- **illegal_bribe_not_deductible** (Section162)
  - `theorem illegal_bribe_not_deductible (e : Expense) (h_illegal : Bool) : e.type = ExpenseType.Brib...`
- **not_ordinary_or_necessary_not_deductible** (Section162)
  - `theorem not_ordinary_or_necessary_not_deductible (e : Expense) : ¬(e.ordinary ∧ e.necessary) → de...`
- **govt_fine_not_deductible** (Section162)
  - `theorem govt_fine_not_deductible : deductibleAmount example_govt_fine = 0`
- **lobbying_not_deductible** (Section162)
  - `theorem lobbying_not_deductible : deductibleAmount example_lobbying = 0`
- **govt_fine_always_zero** (Section162)
  - `theorem govt_fine_always_zero (e : Expense) (amt : Currency) : e.type = ExpenseType.FineOrPenalty...`
- **lobbying_always_zero** (Section162)
  - `theorem lobbying_always_zero (e : Expense) (direct : Bool) (amt : Currency) : e.type = ExpenseTyp...`
- **lobbying_direct_and_grassroots_zero** (Section162)
  - `theorem lobbying_direct_and_grassroots_zero (e : Expense) (amt : Currency) : (e.type = ExpenseTyp...`
- **deduction_zero_if_no_payments** (Section164)
  - `theorem deduction_zero_if_no_payments (election : TaxpayerElection) : calculateTotalDeduction [] ...`
- **security_deduction_zero** (Section166)
  - `theorem security_deduction_zero (d : Debt) (h : d.is_security) : (calculate_deduction d).amount = 0`
- **tax_exempt_term_holder_no_basis_increase** (Section167)
  - `theorem tax_exempt_term_holder_no_basis_increase (adj : BasisAdjustment) (holder : TaxpayerProfil...`
- **telescoping_sum_list** (Section174)
  - `theorem telescoping_sum_list (f : Nat → Currency) (n : Nat) : ((List.range (n + 1)).map (fun i =>...`
- **yearly_deduction_simp** (Section174)
  - `lemma yearly_deduction_simp (e : Expenditure) (h_elig : is_foreign_research_or_experimental e) (h...`
- **entertainment_disallowed** (Section274)
  - `theorem entertainment_disallowed (ctx : TaxContext) (e : Expense) : e.category = ExpenseCategory....`
- **unsubstantiated_disallowed** (Section274)
  - `theorem unsubstantiated_disallowed (ctx : TaxContext) (e : Expense) : requiresSubstantiation e.ca...`
- **loss_is_always_zero** (Section311)
  - `theorem loss_is_always_zero (input : CalculationInput) : calculateRecognizedLoss input = 0`
- **credit_qre_zero_if_base_exceeds** (Section41)
  - `theorem credit_qre_zero_if_base_exceeds (inputs : Section41Inputs) (h_exceeds : inputs.base_amoun...`
- **amt_zero_if_regular_tax_exceeds_tmt** (Section55)
  - `theorem amt_zero_if_regular_tax_exceeds_tmt (tmt : Currency) (reg_tax : Currency) (tax_59A : Curr...`
- **writeoff_deduction_before_incurred** (Section59)
  - `theorem writeoff_deduction_before_incurred (exp : QualifiedExpenditure) (cy : TaxYear) (h : cy.ye...`

## Quick Reference by Section

| Section | Theorems | Lemmas |
|---------|----------|--------|
| Section1 | 24 | 6 |
| Section11 | 5 | 0 |
| Section21 | 2 | 0 |
| Section24 | 16 | 0 |
| Section25 | 2 | 0 |
| Section32 | 28 | 0 |
| Section38 | 2 | 0 |
| Section41 | 4 | 0 |
| Section55 | 3 | 0 |
| Section56 | 5 | 0 |
| Section59 | 2 | 0 |
| Section61 | 3 | 0 |
| Section62 | 4 | 0 |
| Section63 | 3 | 0 |
| Section64 | 2 | 0 |
| Section65 | 3 | 0 |
| Section71 | 4 | 0 |
| Section101 | 4 | 0 |
| Section103 | 34 | 0 |
| Section108 | 8 | 0 |
| Section121 | 3 | 0 |
| Section162 | 32 | 0 |
| Section163 | 6 | 0 |
| Section164 | 4 | 0 |
| Section166 | 4 | 0 |
| Section167 | 6 | 0 |
| Section168 | 9 | 0 |
| Section174 | 2 | 2 |
| Section179 | 9 | 0 |
| Section199 | 2 | 0 |
| Section274 | 4 | 0 |
| Section301 | 2 | 1 |
| Section311 | 3 | 0 |
| Section401 | 8 | 0 |
| Section408 | 4 | 0 |
| Section469 | 7 | 0 |
| Section482 | 7 | 0 |
| Section1001 | 4 | 1 |
| Section1011 | 3 | 0 |
| Section1012 | 3 | 0 |
| Section1014 | 7 | 0 |
| Section1015 | 11 | 0 |
| Section1221 | 3 | 0 |
| Section2001 | 2 | 4 |
| Section2501 | 6 | 0 |

---
*Generated by `tools/theorem_catalog.py`*