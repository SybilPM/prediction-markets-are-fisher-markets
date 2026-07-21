/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.FullProgram

/-!
# Self-Enforcing Market-Maker Budgets

At arbitrary outcome prices, a market maker maximizing its reduced-form
quasilinear payoff spends no more than its budget.  The proof uses the feasible
radial direction toward the zero allocation and Fermat's theorem on a tangent
cone, avoiding an assumed KKT system.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- Price paid by MM `k`; for Arrow-Debreu orders the inner product is
    exactly `p_{ω(j)}` times full-fill quantity. -/
noncomputable def FullInstance.mmSpending (price : ι → ℝ) (fill : J → ℝ) (k : K) : ℝ :=
  ∑ j : J, if inst.owner j = some k then
    (∑ s : ι, price s * inst.payoff j s) * fill j
  else 0

/-- Price-taking payoff of one MM at fixed outcome prices. -/
noncomputable def FullInstance.mmPayoff (price : ι → ℝ) (k : K) (fill : J → ℝ) : ℝ :=
  psiB (inst.budget k) (inst.mmUtil fill k) - inst.mmSpending price fill k

omit [Fintype K] in theorem FullInstance.mmSpending_linear
    (price : ι → ℝ) (k : K) (f g : J → ℝ) (a c : ℝ) :
    inst.mmSpending price (a • f + c • g) k =
      a * inst.mmSpending price f k + c * inst.mmSpending price g k := by
  unfold FullInstance.mmSpending
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  trans ∑ j : J,
      (a * (if inst.owner j = some k then
          (∑ s : ι, price s * inst.payoff j s) * f j else 0) +
        c * (if inst.owner j = some k then
          (∑ s : ι, price s * inst.payoff j s) * g j else 0))
  · apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

omit [Fintype ι] [Fintype K] in theorem FullInstance.mmUtil_smul (t : ℝ) (fill : J → ℝ) (k : K) :
    inst.mmUtil (t • fill) k = t * inst.mmUtil fill k := by
  simpa using inst.mmUtil_linear k fill 0 t 0

omit [Fintype K] in theorem FullInstance.mmSpending_smul
    (price : ι → ℝ) (t : ℝ) (fill : J → ℝ) (k : K) :
    inst.mmSpending price (t • fill) k =
      t * inst.mmSpending price fill k := by
  unfold FullInstance.mmSpending
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

omit [Fintype J] in private theorem smul_mem_box
    (fill : J → ℝ) (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • fill ∈ (boxFeasible : Set (J → ℝ)) := by
  apply Set.mem_pi.mpr
  intro j _
  have hj := Set.mem_pi.mp hfill j trivial
  constructor
  · change 0 ≤ t * fill j
    exact mul_nonneg ht.1 hj.1
  · change t * fill j ≤ 1
    calc
      t * fill j ≤ 1 * fill j := mul_le_mul_of_nonneg_right ht.2 hj.1
      _ ≤ 1 := by simpa using hj.2

omit [Fintype K] in
/-- A price-taking optimum spends at most both its weighted fill and its budget. -/
theorem FullInstance.selfEnforcing_budget
    (price : ι → ℝ) (k : K) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.mmPayoff price k) boxFeasible fill) :
    inst.mmSpending price fill k ≤
      min (inst.mmUtil fill k) (inst.budget k) := by
  let U := inst.mmUtil fill k
  let P := inst.mmSpending price fill k
  let α := psiSlope (inst.budget k) U
  let g : ℝ → ℝ := fun t => psiB (inst.budget k) (t * U) - t * P
  have hU : 0 ≤ U := inst.mmUtil_nonneg fill hfill k
  have hmax : IsMaxOn g (Set.Icc (0 : ℝ) 1) 1 := by
    intro t ht
    change g t ≤ g 1
    have hs := smul_mem_box fill hfill ht
    have h := hopt hs
    change inst.mmPayoff price k (t • fill) ≤ inst.mmPayoff price k fill at h
    simp only [FullInstance.mmPayoff] at h
    rw [inst.mmUtil_smul, inst.mmSpending_smul] at h
    change
      psiB (inst.budget k) (t * U) - t * P ≤
        psiB (inst.budget k) U - P at h
    simpa only [g, one_mul] using h
  have hinner : HasDerivAt (fun t : ℝ => t * U) U 1 := by
    simpa using (hasDerivAt_id' (1 : ℝ)).mul_const U
  have hcost : HasDerivAt (fun t : ℝ => t * P) P 1 := by
    simpa using (hasDerivAt_id' (1 : ℝ)).mul_const P
  have hg : HasDerivAt g (α * U - P) 1 := by
    have hbase : HasDerivAt (psiB (inst.budget k)) α (1 * U) := by
      simpa only [α, one_mul] using
        hasDerivAt_psiB_nonneg (inst.budget_pos k) hU
    have hψ := hbase.comp 1 hinner
    simpa [g, Function.comp_def] using! hψ.sub hcost
  have hseg : segment ℝ (1 : ℝ) 0 ⊆ Set.Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1).segment_subset (by norm_num) (by norm_num)
  have hdir : (-1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 1 := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonpos := hmax.localize.hasFDerivWithinAt_nonpos
    (hasDerivWithinAt_iff_hasFDerivWithinAt.mp hg.hasDerivWithinAt) hdir
  have hspend : P ≤ α * U := by
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using hnonpos
  rw [psiSlope_mul_eq_min (inst.budget_pos k)] at hspend
  exact hspend

omit [Fintype K] in theorem FullInstance.selfEnforcing_budget_le
    (price : ι → ℝ) (k : K) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.mmPayoff price k) boxFeasible fill) :
    inst.mmSpending price fill k ≤ inst.budget k :=
  (inst.selfEnforcing_budget price k fill hfill hopt).trans (min_le_right _ _)

end FisherClearing
