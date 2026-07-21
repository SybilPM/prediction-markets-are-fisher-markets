/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.Equilibrium
import FisherClearing.ReducedForm.LpRecovery
import FisherClearing.ReducedForm.WelfareGap

/-!
# Risk-Neutral Comparison for the Full Clearing Program

This file specializes the affine-envelope arguments to the actual fill,
net-demand, retail-welfare, and minting-cost definitions used by clearing.
It proves existence of a risk-neutral optimum, exact recovery when its MM
weighted fills lie below budget, and comparator welfare-gap bounds.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- Clearing welfare when every MM is valued at its affine, risk-neutral
    envelope (with its fill-independent constant removed). -/
noncomputable def FullInstance.riskNeutralObjective (b : ℝ) (fill : J → ℝ) : ℝ :=
  (∑ k : K, inst.mmUtil fill k) -
    logSumExp b (inst.netDemand fill) +
    inst.retailWelfare fill

theorem FullInstance.continuous_riskNeutralObjective (b : ℝ) :
    Continuous (inst.riskNeutralObjective b) := by
  unfold FullInstance.riskNeutralObjective
  have hmm : Continuous (fun fill => ∑ k : K, inst.mmUtil fill k) := by
    apply continuous_finsetSum
    intro k _
    exact inst.continuous_mmUtil k
  exact (hmm.sub ((continuous_logSumExp b).comp inst.continuous_netDemand)).add
    inst.continuous_retailWelfare

/-- The risk-neutral comparison program has an optimizer. -/
theorem FullInstance.exists_riskNeutral_optimal_fill (b : ℝ) :
    ∃ fill ∈ (boxFeasible : Set (J → ℝ)),
      IsMaxOn (inst.riskNeutralObjective b) boxFeasible fill :=
  isCompact_boxFeasible.exists_isMaxOn nonempty_boxFeasible
    (inst.continuous_riskNeutralObjective b).continuousOn

omit [Nonempty ι] in
/-- Exact affine-envelope decomposition of the full reduced-form objective. -/
theorem FullInstance.objective_eq_riskNeutral_sub_gap_add_const (b : ℝ) (fill : J → ℝ) :
    inst.objective b fill =
      inst.riskNeutralObjective b fill +
        ∑ k : K, (inst.budget k * Real.log (inst.budget k) - inst.budget k) -
        ∑ k : K, affineGap (inst.budget k) (inst.mmUtil fill k) := by
  have hmm :
      (∑ k : K, psiB (inst.budget k) (inst.mmUtil fill k)) =
        (∑ k : K, inst.mmUtil fill k) +
          ∑ k : K, (inst.budget k * Real.log (inst.budget k) - inst.budget k) -
          ∑ k : K, affineGap (inst.budget k) (inst.mmUtil fill k) := by
    calc
      (∑ k : K, psiB (inst.budget k) (inst.mmUtil fill k)) =
          ∑ k : K,
            ((inst.mmUtil fill k +
                (inst.budget k * Real.log (inst.budget k) - inst.budget k)) -
              affineGap (inst.budget k) (inst.mmUtil fill k)) := by
            apply Finset.sum_congr rfl
            intro k _
            unfold affineGap
            ring
      _ = (∑ k : K, inst.mmUtil fill k) +
            ∑ k : K, (inst.budget k * Real.log (inst.budget k) - inst.budget k) -
            ∑ k : K, affineGap (inst.budget k) (inst.mmUtil fill k) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [FullInstance.objective, FullInstance.riskNeutralObjective, hmm]
  ring

omit [Nonempty ι] in
/-- **Risk-Neutral Recovery.** A risk-neutral optimizer whose MM weighted
    fills all lie below budget is also an optimizer of reduced-form clearing. -/
theorem FullInstance.riskNeutral_recovery (b : ℝ) (fill : J → ℝ)
    (hbelow : ∀ k, inst.mmUtil fill k ≤ inst.budget k)
    (hopt : IsMaxOn (inst.riskNeutralObjective b) boxFeasible fill) :
    IsMaxOn (inst.objective b) boxFeasible fill := by
  intro other hother
  change inst.objective b other ≤ inst.objective b fill
  have hrecovery := FisherClearing.riskNeutral_recovery
    (S := (boxFeasible : Set (J → ℝ))) (B := inst.budget)
    (U := inst.mmUtil) (R := fun q => -logSumExp b (inst.netDemand q) + inst.retailWelfare q)
    (xRN := fill)
    inst.budget_pos hbelow
  have hresult := hrecovery (by
    intro q hq
    have h := hopt hq
    change inst.riskNeutralObjective b q ≤ inst.riskNeutralObjective b fill at h
    unfold FullInstance.riskNeutralObjective at h
    linarith) other hother
  unfold FullInstance.objective
  linarith

omit [Nonempty ι] in
/-- The paper's exact full-instance comparator bound.  The feasible comparator
    need not be a risk-neutral optimizer. -/
theorem FullInstance.comparator_welfare_gap (b : ℝ) (comparator ra : J → ℝ)
    (hcomparator_mem : comparator ∈ (boxFeasible : Set (J → ℝ)))
    (hra : IsMaxOn (inst.objective b) boxFeasible ra) :
    inst.riskNeutralObjective b comparator - inst.riskNeutralObjective b ra ≤
      ∑ k : K, welfareGap (inst.budget k)
        (budgetShortfall (inst.budget k) (inst.mmUtil comparator k)) := by
  apply optimization_comparator_gap
    (S := (boxFeasible : Set (J → ℝ))) (B := inst.budget)
    (U := inst.mmUtil) (F := inst.riskNeutralObjective b)
    (x := comparator) (xRA := ra)
    inst.budget_pos hcomparator_mem
  intro q hq
  have h := hra hq
  change inst.objective b q ≤ inst.objective b ra at h
  rw [inst.objective_eq_riskNeutral_sub_gap_add_const,
      inst.objective_eq_riskNeutral_sub_gap_add_const] at h
  linarith

omit [Nonempty ι] in
/-- Quadratic form of the full-instance comparator bound. -/
theorem FullInstance.comparator_welfare_gap_sq
    (b : ℝ) (comparator ra : J → ℝ)
    (hcomparator_mem : comparator ∈ (boxFeasible : Set (J → ℝ)))
    (hra : IsMaxOn (inst.objective b) boxFeasible ra) :
    inst.riskNeutralObjective b comparator - inst.riskNeutralObjective b ra ≤
      ∑ k : K,
        budgetShortfall (inst.budget k) (inst.mmUtil comparator k) ^ 2 /
          (2 * inst.budget k) := by
  apply optimization_comparator_gap_sq
    (S := (boxFeasible : Set (J → ℝ))) (B := inst.budget)
    (U := inst.mmUtil) (F := inst.riskNeutralObjective b)
    (x := comparator) (xRA := ra)
    inst.budget_pos hcomparator_mem
  intro q hq
  have h := hra hq
  change inst.objective b q ≤ inst.objective b ra at h
  rw [inst.objective_eq_riskNeutral_sub_gap_add_const,
      inst.objective_eq_riskNeutral_sub_gap_add_const] at h
  linarith

/-! ### Hard-budget benchmark -/

/-- Feasibility for the original hard-budget clearing problem: fills lie in
    the order box and every MM's expenditure at the endogenous softmax price
    is at most its budget. -/
def FullInstance.HardBudgetFeasible (b : ℝ) (fill : J → ℝ) : Prop :=
  fill ∈ (boxFeasible : Set (J → ℝ)) ∧
    ∀ k : K,
      inst.mmSpending (softmax b (inst.netDemand fill)) fill k ≤
        inst.budget k

/-- A positive-temperature reduced-form optimum is feasible for the original
    hard-budget program. -/
theorem FullInstance.hardBudgetFeasible_of_optimal
    {b : ℝ} (hb : 0 < b) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.objective b) boxFeasible fill) :
    inst.HardBudgetFeasible b fill := by
  refine ⟨hfill, ?_⟩
  intro k
  exact
    (inst.competitiveEquilibrium_of_optimal hb fill hfill hopt).mmSpending_le_budget
      inst k

/-- **Feasible Approximation of Hard-Budget Clearing (exact form).**
    Every hard-budget-feasible competitor has risk-neutral welfare at most the
    reduced-form solution plus the affine-envelope penalty at an unconstrained
    risk-neutral optimum.  Thus this pointwise statement also bounds the
    supremum of the hard-budget benchmark. -/
theorem FullInstance.hardBudget_welfare_gap
    {b : ℝ} (hb : 0 < b) (rn ra hard : J → ℝ)
    (hrn_mem : rn ∈ (boxFeasible : Set (J → ℝ)))
    (hra_mem : ra ∈ (boxFeasible : Set (J → ℝ)))
    (hrn : IsMaxOn (inst.riskNeutralObjective b) boxFeasible rn)
    (hra : IsMaxOn (inst.objective b) boxFeasible ra)
    (hhard : inst.HardBudgetFeasible b hard) :
    inst.HardBudgetFeasible b ra ∧
      inst.riskNeutralObjective b hard -
          inst.riskNeutralObjective b ra ≤
        ∑ k : K, welfareGap (inst.budget k)
          (budgetShortfall (inst.budget k) (inst.mmUtil rn k)) := by
  refine ⟨inst.hardBudgetFeasible_of_optimal hb ra hra_mem hra, ?_⟩
  have hhard_rn := hrn hhard.1
  change inst.riskNeutralObjective b hard ≤
    inst.riskNeutralObjective b rn at hhard_rn
  have hgap :=
    inst.comparator_welfare_gap b rn ra hrn_mem hra
  linarith

/-- Quadratic version of the hard-budget approximation guarantee. -/
theorem FullInstance.hardBudget_welfare_gap_sq
    {b : ℝ} (hb : 0 < b) (rn ra hard : J → ℝ)
    (hrn_mem : rn ∈ (boxFeasible : Set (J → ℝ)))
    (hra_mem : ra ∈ (boxFeasible : Set (J → ℝ)))
    (hrn : IsMaxOn (inst.riskNeutralObjective b) boxFeasible rn)
    (hra : IsMaxOn (inst.objective b) boxFeasible ra)
    (hhard : inst.HardBudgetFeasible b hard) :
    inst.HardBudgetFeasible b ra ∧
      inst.riskNeutralObjective b hard -
          inst.riskNeutralObjective b ra ≤
        ∑ k : K,
          budgetShortfall (inst.budget k) (inst.mmUtil rn k) ^ 2 /
            (2 * inst.budget k) := by
  refine ⟨inst.hardBudgetFeasible_of_optimal hb ra hra_mem hra, ?_⟩
  have hhard_rn := hrn hhard.1
  change inst.riskNeutralObjective b hard ≤
    inst.riskNeutralObjective b rn at hhard_rn
  have hgap :=
    inst.comparator_welfare_gap_sq b rn ra hrn_mem hra
  linarith

end FisherClearing
