/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import Mathlib

/-!
# Reduced-Form Market Maker Utility (Proposition 3)

This file defines the reduced-form utility function `ψ_B` that captures the market maker's
contribution to welfare in the clearing program. The function has two regimes:
- **Below budget** (`U ≤ B`): `ψ_B(U) = U + B log B − B` — affine, full welfare transfer
- **Above budget** (`U > B`): `ψ_B(U) = B log U` — logarithmic, diminishing returns

The function is:
- Concave on `(0, ∞)`
- C¹ at the join point `U = B` (value and derivative match)
- Has derivative `min(1, B/U)` for `U > 0`

## Main definitions

* `FisherClearing.psiB B U`: The reduced-form MM utility.

## Main results

* `FisherClearing.psiB_join`: Both branches agree at `U = B`.
* `FisherClearing.concaveOn_psiB`: `ψ_B` is concave on `(0, ∞)`.
* `FisherClearing.psiB_le_affine`: Affine envelope `ψ_B(U) ≤ U + B log B − B`.

## References

* Prediction Markets Are Fisher Markets, Proposition 3
-/

namespace FisherClearing

open Real

variable {B U : ℝ}

/-! ### Definition -/

/-- Reduced-form market maker utility:
    `ψ_B(U) = U + B log B − B` if `U ≤ B`, and `B log U` if `U > B`.
    Here `B > 0` is the MM's budget and `U > 0` is the MM's achieved utility. -/
noncomputable def psiB (B U : ℝ) : ℝ :=
  if U ≤ B then U + B * Real.log B - B else B * Real.log U

/-- Marginal reduced-form utility.  The branch definition is well behaved at `U = 0`,
    unlike the extension of `min 1 (B / U)` supplied by Lean's totalized division. -/
noncomputable def psiSlope (B U : ℝ) : ℝ :=
  if U < B then 1 else B / U

/-! ### Join continuity -/

/-- At `U = B`, both branches give `B log B`. -/
theorem psiB_join : psiB B B = B * Real.log B := by
  simp only [psiB, le_refl, ite_true]; ring

/-- Below budget, `ψ_B` is affine: `ψ_B(U) = U + B log B − B`. -/
theorem psiB_of_le (hU : U ≤ B) : psiB B U = U + B * Real.log B - B := by
  simp [psiB, hU]

/-- Above budget, `ψ_B` is logarithmic: `ψ_B(U) = B log U`. -/
theorem psiB_of_gt (hU : B < U) : psiB B U = B * Real.log U := by
  simp [psiB, not_le.mpr hU]

/-! ### Derivative -/

/-- The derivative of `ψ_B` below budget is 1. -/
theorem hasDerivAt_psiB_of_lt (hUB : U < B) :
    HasDerivAt (psiB B) 1 U := by
  -- Derivative of the affine branch is 1
  have hd : HasDerivAt (fun x : ℝ => x + (B * log B - B)) 1 U := by
    exact (hasDerivAt_id' U).add_const (B * log B - B)
  -- psiB B agrees with this branch near U
  refine hd.congr_of_eventuallyEq ?_
  apply Filter.eventuallyEq_of_mem (Iio_mem_nhds hUB)
  intro x (hx : x < B)
  change psiB B x = x + (B * log B - B)
  rw [psiB_of_le (le_of_lt hx)]; ring

/-- The derivative of `ψ_B` above budget is `B/U`. -/
theorem hasDerivAt_psiB_of_gt (hB : 0 < B) (hU : B < U) :
    HasDerivAt (psiB B) (B / U) U := by
  -- psiB B agrees with (fun U => B * log U) near U, since B < U
  have heq : psiB B =ᶠ[nhds U] (fun U => B * log U) := by
    apply Filter.eventuallyEq_of_mem (Ioi_mem_nhds hU)
    intro x (hx : B < x)
    simp [psiB, not_le.mpr hx]
  have hU_pos : (0 : ℝ) < U := lt_trans hB hU
  -- deriv of B * log U is B * U⁻¹ = B / U
  rw [div_eq_mul_inv]
  exact ((hasDerivAt_log (ne_of_gt hU_pos)).const_mul B).congr_of_eventuallyEq heq

/-! ### Derivative at boundary -/

/-- At `U = B`, the derivative is 1 (left = affine, right = B/B = 1). -/
theorem hasDerivAt_psiB_at_eq (hB : 0 < B) :
    HasDerivAt (psiB B) 1 B := by
  have hleft : HasDerivWithinAt (psiB B) 1 (Set.Iic B) B := by
    have hd : HasDerivAt (fun x : ℝ => x + (B * log B - B)) 1 B := by
      exact (hasDerivAt_id' B).add_const (B * log B - B)
    exact hd.hasDerivWithinAt.congr (fun y hy => by rw [psiB_of_le hy]; ring)
      (by rw [psiB_of_le le_rfl]; ring)
  have hright : HasDerivWithinAt (psiB B) 1 (Set.Ici B) B := by
    have hd : HasDerivAt (fun x : ℝ => B * log x) (B * B⁻¹) B :=
      (hasDerivAt_log (ne_of_gt hB)).const_mul B
    rw [mul_inv_cancel₀ (ne_of_gt hB)] at hd
    exact hd.hasDerivWithinAt.congr (fun y hy => by
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with rfl | hy'
      · rw [psiB_of_le le_rfl]; ring
      · exact psiB_of_gt hy') (by rw [psiB_of_le le_rfl]; ring)
  have hunion := hleft.union hright
  simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hunion

/-- `HasDerivAt (psiB B)` at any point `U > 0`. -/
theorem hasDerivAt_psiB (hB : 0 < B) (hU : 0 < U) :
    HasDerivAt (psiB B) (psiSlope B U) U := by
  unfold psiSlope
  by_cases hlt : U < B
  · simp only [if_pos hlt]; exact hasDerivAt_psiB_of_lt hlt
  · push Not at hlt; simp only [if_neg (not_lt.mpr hlt)]
    rcases eq_or_lt_of_le hlt with rfl | hgt
    · rw [div_self (ne_of_gt hB)]; exact hasDerivAt_psiB_at_eq hB
    · exact hasDerivAt_psiB_of_gt hB hgt

/-- The derivative formula also holds at `U = 0`, where the affine branch has slope one. -/
theorem hasDerivAt_psiB_nonneg (hB : 0 < B) (hU : 0 ≤ U) :
    HasDerivAt (psiB B) (psiSlope B U) U := by
  rcases hU.eq_or_lt with rfl | hU
  · simpa [psiSlope, hB] using hasDerivAt_psiB_of_lt hB
  · exact hasDerivAt_psiB hB hU

/-- The derivative formula holds on the whole real line.  Negative arguments
    lie in the affine branch; economically relevant weighted fills are
    nonnegative. -/
theorem hasDerivAt_psiB_all (hB : 0 < B) (U : ℝ) :
    HasDerivAt (psiB B) (psiSlope B U) U := by
  by_cases hU : 0 ≤ U
  · exact hasDerivAt_psiB_nonneg hB hU
  · have hUB : U < B := lt_trans (lt_of_not_ge hU) hB
    simpa [psiSlope, hUB] using hasDerivAt_psiB_of_lt hUB

/-- Marginal utility times weighted fill is exactly the smaller of fill value and budget. -/
theorem psiSlope_mul_eq_min (hB : 0 < B) :
    psiSlope B U * U = min U B := by
  by_cases hUB : U < B
  · simp [psiSlope, hUB, min_eq_left hUB.le]
  · have hBU : B ≤ U := le_of_not_gt hUB
    have hUpos : 0 < U := lt_of_lt_of_le hB hBU
    rw [psiSlope, if_neg hUB, div_mul_cancel₀ B hUpos.ne', min_eq_right hBU]

theorem continuous_psiB (hB : 0 < B) :
    Continuous (psiB B) := by
  rw [continuous_iff_continuousAt]
  intro U
  rcases lt_trichotomy U B with hUB | rfl | hBU
  · exact (hasDerivAt_psiB_of_lt hUB).continuousAt
  · exact (hasDerivAt_psiB_at_eq hB).continuousAt
  · exact (hasDerivAt_psiB_of_gt hB hBU).continuousAt

/-- The scarcity slope is continuous, including at `U = B` and `U = 0`. -/
theorem continuous_psiSlope (hB : 0 < B) :
    Continuous (psiSlope B) := by
  have hpiece :
      psiSlope B =
        fun U : ℝ => if U ≤ B then 1 else B / U := by
    funext U
    by_cases hUB : U < B
    · simp [psiSlope, hUB, hUB.le]
    · have hBU : B ≤ U := le_of_not_gt hUB
      rcases hBU.eq_or_lt with rfl | hBU
      · simp [psiSlope, hB.ne']
      · simp [psiSlope, not_lt.mpr hBU.le, not_le.mpr hBU]
  rw [hpiece]
  apply continuous_if_le continuous_id continuous_const
      continuousOn_const
  · exact continuousOn_const.div continuousOn_id fun U hBU hU0 => by
      have : 0 < U := lt_of_lt_of_le hB hBU
      exact (ne_of_gt this) hU0
  · intro U hUB
    change U = B at hUB
    subst U
    simp [hB.ne']

/-- The reduced-form utility is continuously differentiable. -/
theorem contDiff_one_psiB (hB : 0 < B) :
    ContDiff ℝ 1 (psiB B) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro U
    exact (hasDerivAt_psiB_all hB U).differentiableAt
  · have hderiv :
        deriv (psiB B) = psiSlope B := by
      funext U
      exact (hasDerivAt_psiB_all hB U).deriv
    rw [hderiv]
    exact continuous_psiSlope hB

/-! ### Concavity -/

/-- `ψ_B` is concave on `(0, ∞)`.

    **Proof**: The derivative `min(1, B/U)` is antitone on `(0, ∞)`,
    which implies concavity by `AntitoneOn.concaveOn_of_deriv`. -/
theorem concaveOn_psiB (hB : 0 < B) :
    ConcaveOn ℝ (Set.Ioi 0) (psiB B) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi 0)
  · -- ContinuousOn: follows from differentiability
    exact fun x hx => (hasDerivAt_psiB hB hx).continuousAt.continuousWithinAt
  · -- DifferentiableOn on interior (Ioi 0)
    rw [interior_Ioi]
    exact fun x hx => (hasDerivAt_psiB hB hx).differentiableAt.differentiableWithinAt
  · -- AntitoneOn of deriv on interior (Ioi 0)
    rw [interior_Ioi]
    intro u₁ hu₁ u₂ hu₂ h12
    -- deriv (psiB B) = if U < B then 1 else B / U
    rw [(hasDerivAt_psiB hB hu₁).deriv, (hasDerivAt_psiB hB hu₂).deriv]
    unfold psiSlope
    -- Case split on u₁, u₂ vs B
    by_cases h1 : u₁ < B <;> by_cases h2 : u₂ < B
    · -- Both below B: deriv = 1, 1 ≤ 1
      simp [h1, h2]
    · -- u₁ < B ≤ u₂: deriv₂ = B/u₂ ≤ 1 = deriv₁
      simp only [if_pos h1, if_neg h2]
      push Not at h2
      exact (div_le_one hu₂).mpr h2
    · -- u₂ < B ≤ u₁: impossible since u₁ ≤ u₂
      exact absurd (lt_of_le_of_lt h12 h2) (not_lt.mpr (not_lt.mp h1))
    · -- Both ≥ B: B/u₂ ≤ B/u₁
      simp only [if_neg h1, if_neg h2]
      exact (div_le_div_iff_of_pos_left hB hu₂ hu₁).mpr h12

/-! ### Affine envelope -/

/-- `ψ_B(U) ≤ U + B log B − B` for all `U`.
    Equality holds iff `U ≤ B` (the affine regime). -/
theorem psiB_le_affine (hB : 0 < B) :
    psiB B U ≤ U + B * Real.log B - B := by
  by_cases h : U ≤ B
  · rw [psiB_of_le h]
  · push Not at h
    rw [psiB_of_gt h]
    -- Need: B * log U ≤ U + B * log B - B
    -- Equivalently: B * (log U - log B) ≤ U - B
    -- Use: log(U/B) ≤ U/B - 1, then multiply by B
    have hUB_pos : 0 < U / B := div_pos (lt_trans hB h) hB
    have hlog : Real.log (U / B) ≤ U / B - 1 := Real.log_le_sub_one_of_pos hUB_pos
    have hlog' : Real.log U - Real.log B = Real.log (U / B) :=
      (Real.log_div (ne_of_gt (lt_trans hB h)) (ne_of_gt hB)).symm
    nlinarith [mul_le_mul_of_nonneg_left hlog (le_of_lt hB),
               mul_div_cancel₀ U (ne_of_gt hB)]

/-- The affine envelope is tight below budget. -/
theorem psiB_eq_affine_iff (hB : 0 < B) :
    psiB B U = U + B * Real.log B - B ↔ U ≤ B := by
  constructor
  · -- Forward: equality implies U ≤ B (strict ineq above budget)
    intro h
    by_contra hUB
    push Not at hUB -- hUB : B < U
    rw [psiB_of_gt hUB] at h
    -- h : B * log U = U + B * log B - B, i.e., B * (log U - log B) = U - B
    have hUB_pos : (0 : ℝ) < U / B := div_pos (lt_trans hB hUB) hB
    have hlog_pos : 0 < Real.log (U / B) := Real.log_pos ((one_lt_div hB).mpr hUB)
    -- Strict bound: log(U/B) + 1 < exp(log(U/B)) = U/B
    have h_strict := add_one_lt_exp hlog_pos.ne'
    rw [Real.exp_log hUB_pos] at h_strict
    -- h_strict : log(U/B) + 1 < U/B, i.e., log(U/B) < U/B - 1
    -- So B * log(U/B) < B * (U/B - 1) = U - B
    have hlog_div : Real.log (U / B) = Real.log U - Real.log B :=
      Real.log_div (ne_of_gt (lt_trans hB hUB)) (ne_of_gt hB)
    have h_eq : B * (Real.log U - Real.log B) = U - B := by linarith
    rw [← hlog_div] at h_eq
    -- But strict: B * log(U/B) < U - B
    nlinarith [mul_lt_mul_of_pos_left h_strict hB, mul_div_cancel₀ U (ne_of_gt hB)]
  · -- Backward: U ≤ B implies equality
    exact psiB_of_le

/-! ### Monotonicity -/

/-- `ψ_B` is nondecreasing on `[0, ∞)`. -/
theorem monotoneOn_psiB (hB : 0 < B) :
    MonotoneOn (psiB B) (Set.Ici 0) := by
  intro u₁ hu₁ u₂ hu₂ h12
  have h1 := Set.mem_Ici.mp hu₁  -- 0 ≤ u₁
  have h2 := Set.mem_Ici.mp hu₂  -- 0 ≤ u₂
  by_cases h1B : u₁ ≤ B <;> by_cases h2B : u₂ ≤ B
  · -- Both ≤ B: affine branch, psiB = U + const
    rw [psiB_of_le h1B, psiB_of_le h2B]; linarith
  · -- u₁ ≤ B < u₂: transition through boundary
    push Not at h2B
    rw [psiB_of_le h1B, psiB_of_gt h2B]
    -- u₁ + B*log B - B ≤ B + B*log B - B = B*log B ≤ B*log u₂
    have : u₁ + B * log B - B ≤ B * log B := by linarith
    linarith [mul_le_mul_of_nonneg_left (log_le_log hB h2B.le) hB.le]
  · -- u₂ ≤ B but u₁ > B: impossible since u₁ ≤ u₂
    push Not at h1B; linarith
  · -- Both > B: log branch, B * log u₁ ≤ B * log u₂
    push Not at h1B h2B
    rw [psiB_of_gt h1B, psiB_of_gt h2B]
    exact mul_le_mul_of_nonneg_left (log_le_log (lt_trans hB h1B) h12) hB.le

/-! ### Continuity -/

/-- `ψ_B` is continuous on `[0, ∞)`. -/
theorem continuousOn_psiB (hB : 0 < B) :
    ContinuousOn (psiB B) (Set.Ici 0) := by
  intro x hx
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with rfl | hx_pos
  · -- At x = 0: psiB B agrees with the continuous affine function near 0
    set f := fun U : ℝ => U + (B * log B - B)
    have hf : ContinuousWithinAt f (Set.Ici 0) 0 :=
      continuousWithinAt_id.add continuousWithinAt_const
    have heq : psiB B =ᶠ[nhdsWithin 0 (Set.Ici 0)] f := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hB)] with y hy
      change psiB B y = y + (B * log B - B)
      rw [psiB_of_le (le_of_lt hy)]; ring
    exact hf.congr_of_eventuallyEq heq (by simp only [f, psiB_of_le hB.le]; ring)
  · exact (hasDerivAt_psiB hB hx_pos).continuousAt.continuousWithinAt

/-- `ψ_B` is concave on `[0, ∞)`. -/
theorem concaveOn_psiB_Ici (hB : 0 < B) :
    ConcaveOn ℝ (Set.Ici 0) (psiB B) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
  · exact continuousOn_psiB hB
  · rw [interior_Ici]
    exact fun x hx => (hasDerivAt_psiB hB hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro u₁ hu₁ u₂ hu₂ h12
    rw [(hasDerivAt_psiB hB hu₁).deriv, (hasDerivAt_psiB hB hu₂).deriv]
    unfold psiSlope
    by_cases h1 : u₁ < B <;> by_cases h2 : u₂ < B
    · simp [h1, h2]
    · simp only [if_pos h1, if_neg h2]
      push Not at h2; exact (div_le_one hu₂).mpr h2
    · exact absurd (lt_of_le_of_lt h12 h2) (not_lt.mpr (not_lt.mp h1))
    · simp only [if_neg h1, if_neg h2]
      exact (div_le_div_iff_of_pos_left hB hu₂ hu₁).mpr h12

/-! ### Supporting tangent -/

/-- The derivative of the concave reduced-form utility gives a global
    supporting tangent on nonnegative weighted fills. -/
theorem psiB_le_tangent (hB : 0 < B) {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    psiB B V ≤ psiB B U + psiSlope B U * (V - U) := by
  rcases lt_trichotomy U V with hUV | rfl | hVU
  · have hslope := (concaveOn_psiB_Ici hB).slope_le_of_hasDerivAt
      (Set.mem_Ici.mpr hU) (Set.mem_Ici.mpr hV) hUV
      (hasDerivAt_psiB_nonneg hB hU)
    have hmul := (div_le_iff₀ (sub_pos.mpr hUV)).mp (by
      simpa only [slope, vsub_eq_sub, smul_eq_mul, inv_mul_eq_div] using hslope)
    linarith
  · simp
  · have hslope := (concaveOn_psiB_Ici hB).le_slope_of_hasDerivAt
      (Set.mem_Ici.mpr hV) (Set.mem_Ici.mpr hU) hVU
      (hasDerivAt_psiB_nonneg hB hU)
    have hmul := (le_div_iff₀ (sub_pos.mpr hVU)).mp (by
      simpa only [slope, vsub_eq_sub, smul_eq_mul, inv_mul_eq_div] using hslope)
    linarith

variable {κ : Type*} [Fintype κ]

/-- Summed supporting-tangent inequality for a finite family of reduced-form
    utilities.  This is the common engine behind the shaded matching oracle,
    budget decomposition, and the competitive-equilibrium proof. -/
theorem sum_psiB_le_tangent (budget current candidate : κ → ℝ) (hbudget : ∀ k, 0 < budget k)
    (hcurrent : ∀ k, 0 ≤ current k) (hcandidate : ∀ k, 0 ≤ candidate k) :
    (∑ k : κ, psiB (budget k) (candidate k)) ≤
      (∑ k : κ, psiB (budget k) (current k)) +
        ∑ k : κ, psiSlope (budget k) (current k) *
          (candidate k - current k) := by
  calc
    (∑ k : κ, psiB (budget k) (candidate k)) ≤
        ∑ k : κ,
          (psiB (budget k) (current k) +
            psiSlope (budget k) (current k) *
              (candidate k - current k)) :=
      Finset.sum_le_sum fun k _ =>
        psiB_le_tangent (hbudget k) (hcurrent k) (hcandidate k)
    _ = (∑ k : κ, psiB (budget k) (current k)) +
        ∑ k : κ, psiSlope (budget k) (current k) *
          (candidate k - current k) := by
      rw [Finset.sum_add_distrib]

/-- A maximizer at the left endpoint of `[0,1]` has nonpositive right
    derivative.  This packages the one-sided first-order argument shared by
    clearing and decomposition proofs. -/
theorem HasDerivAt.nonpos_of_isMaxOn_Icc
    {f : ℝ → ℝ} {d : ℝ} (hderiv : HasDerivAt f d 0)
    (hmax : IsMaxOn f (Set.Icc (0 : ℝ) 1) 0) :
    d ≤ 0 := by
  have hseg : segment ℝ (0 : ℝ) 1 ⊆ Set.Icc 0 1 :=
    (convex_Icc (0 : ℝ) 1).segment_subset (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hdir : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset hseg
  simpa [ContinuousLinearMap.toSpanSingleton_apply] using
    hmax.localize.hasFDerivWithinAt_nonpos
      (hasDerivWithinAt_iff_hasFDerivWithinAt.mp
        hderiv.hasDerivWithinAt) hdir

end FisherClearing
