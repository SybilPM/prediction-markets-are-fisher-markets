/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.ZeroTemperature

/-!
# Certified Shaded-LP Oracle

At zero temperature, the nonsmooth retail-and-minting part is kept exact while
each MM utility is replaced by its supporting tangent at the current fill.
Maximizing that surrogate is the paper's shaded matching LP.  Its improvement
is a rigorous upper certificate on continuous objective suboptimality.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- Retail welfare minus the zero-temperature minting epigraph value. -/
noncomputable def FullInstance.zeroResidual (fill : J → ℝ) : ℝ :=
  inst.retailWelfare fill - maxFin (inst.netDemand fill)

/-- The shaded-LP objective obtained by linearizing all MM utilities at
    `current`, while retaining the polyhedral residual exactly. -/
noncomputable def FullInstance.zeroLinearization (current candidate : J → ℝ) : ℝ :=
  inst.zeroResidual candidate +
    ∑ k : K,
      psiSlope (inst.budget k) (inst.mmUtil current k) *
        inst.mmUtil candidate k

/-- Improvement reported by one shaded matching-LP oracle call. -/
noncomputable def FullInstance.zeroOracleGap (current oracle : J → ℝ) : ℝ :=
  inst.zeroResidual oracle - inst.zeroResidual current +
    ∑ k : K,
      psiSlope (inst.budget k) (inst.mmUtil current k) *
        (inst.mmUtil oracle k - inst.mmUtil current k)

theorem FullInstance.objectiveZero_eq_sum_psi_add_residual (fill : J → ℝ) :
    inst.objectiveZero fill =
      (∑ k : K, psiB (inst.budget k) (inst.mmUtil fill k)) +
        inst.zeroResidual fill := by
  unfold FullInstance.objectiveZero FullInstance.zeroResidual
  ring

theorem FullInstance.zeroOracleGap_eq (current oracle : J → ℝ) :
    inst.zeroOracleGap current oracle =
      inst.zeroLinearization current oracle -
        inst.zeroLinearization current current := by
  unfold FullInstance.zeroOracleGap FullInstance.zeroLinearization
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- **LP-Oracle Certificate.** The shaded matching-LP improvement bounds the
    gap to every global zero-temperature optimum. -/
theorem FullInstance.zero_oracle_certificate (current oracle optimum : J → ℝ)
    (hcurrent : current ∈ (boxFeasible : Set (J → ℝ)))
    (hoptimum_mem : optimum ∈ (boxFeasible : Set (J → ℝ)))
    (hoptimum : IsMaxOn inst.objectiveZero boxFeasible optimum) (horacle :
      IsMaxOn (inst.zeroLinearization current) boxFeasible oracle) :
    0 ≤ inst.objectiveZero optimum - inst.objectiveZero current ∧
      inst.objectiveZero optimum - inst.objectiveZero current ≤
        inst.zeroOracleGap current oracle := by
  constructor
  · have h := hoptimum hcurrent
    change inst.objectiveZero current ≤ inst.objectiveZero optimum at h
    linarith
  · have htangent := sum_psiB_le_tangent
      inst.budget
      (fun k => inst.mmUtil current k)
      (fun k => inst.mmUtil optimum k)
      inst.budget_pos
      (fun k => inst.mmUtil_nonneg current hcurrent k)
      (fun k => inst.mmUtil_nonneg optimum hoptimum_mem k)
    simp_rw [mul_sub] at htangent
    rw [Finset.sum_sub_distrib] at htangent
    have horacle_bound := horacle hoptimum_mem
    change inst.zeroLinearization current optimum ≤
      inst.zeroLinearization current oracle at horacle_bound
    rw [inst.objectiveZero_eq_sum_psi_add_residual,
      inst.objectiveZero_eq_sum_psi_add_residual,
      inst.zeroOracleGap_eq]
    unfold FullInstance.zeroLinearization at horacle_bound ⊢
    linarith

/-- The oracle gap is itself nonnegative because the current point is a
    feasible candidate for its own linearized problem. -/
theorem FullInstance.zeroOracleGap_nonneg (current oracle : J → ℝ)
    (hcurrent : current ∈ (boxFeasible : Set (J → ℝ))) (horacle :
      IsMaxOn (inst.zeroLinearization current) boxFeasible oracle) :
    0 ≤ inst.zeroOracleGap current oracle := by
  have h := horacle hcurrent
  change inst.zeroLinearization current current ≤
    inst.zeroLinearization current oracle at h
  rw [inst.zeroOracleGap_eq]
  linarith

/-- Exact line search is monotone because the zero step is among its feasible
    candidates. -/
theorem FullInstance.exactLineSearch_nondecreasing (current oracle : J → ℝ) (γ : ℝ) (hline :
      IsMaxOn
        (fun t : ℝ =>
          inst.objectiveZero (AffineMap.lineMap current oracle t))
        (Set.Icc (0 : ℝ) 1) γ) :
    inst.objectiveZero current ≤
      inst.objectiveZero (AffineMap.lineMap current oracle γ) := by
  have h := hline (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
  change
    inst.objectiveZero (AffineMap.lineMap current oracle 0) ≤
      inst.objectiveZero (AffineMap.lineMap current oracle γ) at h
  simpa only [AffineMap.lineMap_apply_zero] using h

end FisherClearing
