/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import Mathlib
import FisherClearing.Convex.LogSumExp

/-!
# Softmax Function

This file defines the softmax function and proves it maps to the standard simplex.
Softmax is the gradient of log-sum-exp, and its output gives the clearing prices
in the LMSR market maker.

## Main definitions

* `FisherClearing.softmax b f k`: The function `exp(f k / b) / ∑ j, exp(f j / b)`.

## Main results

* `FisherClearing.softmax_nonneg`: Each softmax component is nonnegative.
* `FisherClearing.softmax_sum_eq_one`: Softmax components sum to 1.
* `FisherClearing.softmax_mem_stdSimplex`: Softmax output lies in the standard simplex.
* `FisherClearing.hasDerivAt_logSumExp_comp`: Softmax is the gradient of logSumExp.
-/

namespace FisherClearing

open scoped BigOperators
open Finset Real

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {b : ℝ}

/-! ### Softmax definition and basic properties -/

/-- Softmax with temperature `b`:
    `softmax b f k = exp(f k / b) / ∑ j, exp(f j / b)`.
    For `b > 0`, this gives a probability distribution over `ι`. -/
noncomputable def softmax (b : ℝ) (f : ι → ℝ) (k : ι) : ℝ :=
  Real.exp (f k / b) / sumExp b f

lemma softmax_nonneg (b : ℝ) (f : ι → ℝ) (k : ι) : 0 ≤ softmax b f k :=
  div_nonneg (le_of_lt (Real.exp_pos _)) (sumExp_nonneg b f)

lemma softmax_pos (b : ℝ) (f : ι → ℝ) (k : ι) : 0 < softmax b f k :=
  div_pos (Real.exp_pos _) (sumExp_pos b f)

lemma softmax_le_one (b : ℝ) (f : ι → ℝ) (k : ι) : softmax b f k ≤ 1 := by
  unfold softmax
  rw [div_le_one (sumExp_pos b f)]
  exact exp_div_le_sumExp b f k

/-! ### Softmax sums to one -/

/-- Softmax components sum to 1. -/
theorem softmax_sum_eq_one (b : ℝ) (f : ι → ℝ) :
    ∑ k : ι, softmax b f k = 1 := by
  simp only [softmax, ← Finset.sum_div]
  exact div_self (sumExp_ne_zero b f)

/-! ### Simplex membership -/

/-- Softmax output lies in the standard simplex `Δ = {p ≥ 0 | ∑ pᵢ = 1}`. -/
theorem softmax_mem_stdSimplex (b : ℝ) (f : ι → ℝ) :
    softmax b f ∈ stdSimplex ℝ ι :=
  ⟨fun k => softmax_nonneg b f k, softmax_sum_eq_one b f⟩

omit [Nonempty ι] in
/-- Softmax prices are unchanged by complete-set translations. -/
theorem softmax_add_const (b : ℝ) (f : ι → ℝ) (c : ℝ) :
    softmax b (fun i => f i + c) = softmax b f := by
  funext i
  unfold softmax
  rw [sumExp_add_const]
  have hnum :
      Real.exp ((f i + c) / b) =
        Real.exp (c / b) * Real.exp (f i / b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hnum]
  exact mul_div_mul_left
    (Real.exp (f i / b)) (sumExp b f)
      (Real.exp_ne_zero (c / b))

/-- Softmax is injective modulo translation by the all-ones direction. -/
theorem exists_add_const_of_softmax_eq (hb : 0 < b) {f g : ι → ℝ}
    (h : softmax b f = softmax b g) :
    ∃ c : ℝ, ∀ i : ι, f i = g i + c := by
  let c := b * (Real.log (sumExp b f) - Real.log (sumExp b g))
  refine ⟨c, ?_⟩
  intro i
  have hi := congrFun h i
  unfold softmax at hi
  have hcross :
      Real.exp (f i / b) * sumExp b g =
        Real.exp (g i / b) * sumExp b f := by
    exact (div_eq_div_iff (sumExp_ne_zero b f)
      (sumExp_ne_zero b g)).mp hi
  have hlog := congrArg Real.log hcross
  rw [Real.log_mul (Real.exp_ne_zero _) (sumExp_ne_zero b g),
    Real.log_mul (Real.exp_ne_zero _) (sumExp_ne_zero b f),
    Real.log_exp, Real.log_exp] at hlog
  have hscaled := congrArg (fun x : ℝ => b * x) hlog
  field_simp [ne_of_gt hb] at hscaled
  dsimp only [c]
  linarith

/-! ### Gradient relationship -/

/-- Softmax is the gradient of logSumExp: the partial derivative of `logSumExp b` with
    respect to the `k`-th component of `f` equals `softmax b f k`.

    **Proof sketch**: By the chain rule,
    `∂/∂fₖ [b · log(∑ exp(fᵢ/b))] = b · (1/∑ exp(fᵢ/b)) · exp(fₖ/b) · (1/b) = softmax_k`. -/
theorem hasDerivAt_logSumExp_comp [DecidableEq ι] (hb : 0 < b) (f : ι → ℝ) (k : ι) :
    HasDerivAt (fun t => logSumExp b (Function.update f k t))
      (softmax b f k) (f k) := by
  -- Decompose sumExp into the k-th exponential plus a constant
  set C := ∑ i ∈ Finset.univ.erase k, Real.exp (f i / b) with hC_def
  -- Key: sumExp (update f k t) = exp(t/b) + C for all t
  have hsplit : ∀ t, sumExp b (Function.update f k t) = Real.exp (t / b) + C := by
    intro t; unfold sumExp
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    simp only [Function.update_self]; congr 1
    exact Finset.sum_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  -- exp(f k / b) + C = sumExp b f
  have hsum_eq : Real.exp (f k / b) + C = sumExp b f := by
    have h := hsplit (f k); rw [Function.update_eq_self] at h; linarith
  have hpos : 0 < Real.exp (f k / b) + C := by linarith [sumExp_pos b f]
  -- Rewrite function to b * log(exp(t/b) + C)
  rw [show (fun t => logSumExp b (Function.update f k t)) =
      (fun t => b * Real.log (Real.exp (t / b) + C)) from
    funext fun t => by simp only [logSumExp, hsplit]]
  -- Chain rule step by step
  have h1 : HasDerivAt (fun t => Real.exp (t / b))
      (Real.exp (f k / b) * (1 / b)) (f k) := by
    have h := (Real.hasDerivAt_exp (f k / b)).comp (f k) ((hasDerivAt_id (f k)).div_const b)
    simp only [Function.comp_def, id] at h; exact h
  have h2 : HasDerivAt (fun t => Real.exp (t / b) + C)
      (Real.exp (f k / b) * (1 / b)) (f k) := by
    have h := h1.add (hasDerivAt_const (f k) C); rwa [add_zero] at h
  have h3 := h2.log (ne_of_gt hpos)
  have h4 := h3.const_mul b
  -- Simplify derivative to softmax
  have hderiv_eq : softmax b f k =
      b * (Real.exp (f k / b) * (1 / b) / (Real.exp (f k / b) + C)) := by
    simp only [softmax, ← hsum_eq]
    field_simp [ne_of_gt hb, ne_of_gt hpos]
  rw [hderiv_eq]; exact h4

/-- Directional derivative of log-sum-exp along the line from `f` to `g`.
    This is the finite-dimensional gradient formula in a basis-free form. -/
theorem hasDerivAt_logSumExp_line (hb : 0 < b) (f g : ι → ℝ) :
    HasDerivAt
      (fun t : ℝ => logSumExp b (AffineMap.lineMap f g t))
      (∑ i : ι, softmax b f i * (g i - f i)) 0 := by
  have hterm : ∀ i : ι,
      HasDerivAt
        (fun t : ℝ => Real.exp ((AffineMap.lineMap f g t) i / b))
        (Real.exp (f i / b) * ((g i - f i) / b)) 0 := by
    intro i
    have hline :
        HasDerivAt
          (fun t : ℝ => (AffineMap.lineMap f g t) i / b)
          ((g i - f i) / b) 0 := by
      simpa only [AffineMap.lineMap_apply_module', Pi.add_apply, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul, id_eq, one_mul] using
        ((((hasDerivAt_id (0 : ℝ)).mul_const (g i - f i)).add_const (f i)).div_const b)
    have hexp :
        HasDerivAt Real.exp (Real.exp (f i / b))
          ((AffineMap.lineMap f g (0 : ℝ)) i / b) := by
      simpa only [AffineMap.lineMap_apply_module', Pi.add_apply, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul, zero_mul, zero_add] using
        Real.hasDerivAt_exp (f i / b)
    simpa only [Function.comp_def] using hexp.comp 0 hline
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          ∑ i : ι, Real.exp ((AffineMap.lineMap f g t) i / b))
        (∑ i : ι, Real.exp (f i / b) * ((g i - f i) / b)) 0 :=
    HasDerivAt.fun_sum fun i _ => hterm i
  have hsum0 :
      (∑ i : ι, Real.exp ((AffineMap.lineMap f g (0 : ℝ)) i / b)) ≠ 0 := by
    simpa [sumExp, AffineMap.lineMap_apply_module'] using sumExp_ne_zero b f
  have htotal := (hsum.log hsum0).const_mul b
  have hderiv :
      b * ((∑ i : ι, Real.exp (f i / b) * ((g i - f i) / b)) /
        (∑ i : ι, Real.exp (f i / b))) =
        ∑ i : ι, softmax b f i * (g i - f i) := by
    have hsum_ne : (∑ i : ι, Real.exp (f i / b)) ≠ 0 := by
      simpa [sumExp] using sumExp_ne_zero b f
    unfold softmax sumExp
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt hb, hsum_ne]
  rw [← hderiv]
  simpa [logSumExp, sumExp] using htotal

/-- The softmax price is a subgradient of log-sum-exp. -/
theorem softmax_supports_logSumExp (hb : 0 < b) (f g : ι → ℝ) :
    ∑ i : ι, softmax b f i * (g i - f i) ≤
      logSumExp b g - logSumExp b f := by
  have hconv : ConvexOn ℝ Set.univ
      (fun t : ℝ => logSumExp b (AffineMap.lineMap f g t)) := by
    change ConvexOn ℝ Set.univ
      ((fun d : ι → ℝ => logSumExp b d) ∘ (AffineMap.lineMap f g))
    simpa only [Set.preimage_univ] using
      (convexOn_logSumExp hb).comp_affineMap (AffineMap.lineMap f g)
  have hslope := hconv.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) zero_lt_one (hasDerivAt_logSumExp_line hb f g)
  simpa [slope] using hslope

/-- Profit maximization of the smoothed minting sector at the softmax price. -/
theorem softmax_supply_optimal (hb : 0 < b) (demand other : ι → ℝ) :
    (∑ i : ι, softmax b demand i * other i) - logSumExp b other ≤
      (∑ i : ι, softmax b demand i * demand i) - logSumExp b demand := by
  have h := softmax_supports_logSumExp hb demand other
  have hsum :
      (∑ i : ι, softmax b demand i * (other i - demand i)) =
        (∑ i : ι, softmax b demand i * other i) -
          ∑ i : ι, softmax b demand i * demand i := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsum] at h
  linarith

end FisherClearing
