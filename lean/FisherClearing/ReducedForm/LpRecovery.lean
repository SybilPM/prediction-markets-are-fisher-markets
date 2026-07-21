/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import Mathlib
import FisherClearing.ReducedForm.Utility

/-!
# Risk-Neutral Recovery

If a risk-neutral optimum leaves every market maker below budget
(`U_k ≤ B_k`), the reduced-form objective has the same optimum. At the
risk-neutral solution every `ψ_B` meets its affine envelope, while everywhere
else the reduced-form objective is at most that envelope.

## Main results

* `FisherClearing.psiB_affine_regime`: Below budget, `ψ_B(U)` is affine in `U`.
* `FisherClearing.riskNeutral_recovery`: A risk-neutral optimum whose MM
  utilities are below budget also maximizes the reduced-form objective.

## References

* Prediction Markets Are Fisher Markets, Proposition 5
-/

namespace FisherClearing

open scoped BigOperators
open Real

variable {κ : Type*} [Fintype κ]
variable {X : Type*}

/-! ### LP Recovery -/

/-- If `U_k ≤ B_k` for all market makers `k`, then `∑ ψ_{B_k}(U_k)` is affine in `U`.
    Specifically: `∑ ψ_{B_k}(U_k) = ∑ U_k + ∑ (B_k log B_k − B_k)`. -/
theorem psiB_sum_affine_of_le (B U : κ → ℝ) (hle : ∀ k, U k ≤ B k) :
    ∑ k : κ, psiB (B k) (U k) =
      ∑ k : κ, U k + ∑ k : κ, (B k * Real.log (B k) - B k) := by
  have h : ∀ k, psiB (B k) (U k) = U k + (B k * Real.log (B k) - B k) :=
    fun k => by rw [psiB_of_le (hle k)]; ring
  simp_rw [h, Finset.sum_add_distrib]

/-- If every MM is below budget at two allocations, ordering their
    risk-neutral MM welfare also orders their reduced-form MM welfare. -/
theorem psiB_sum_mono_of_le (B U₁ U₂ : κ → ℝ) (h₁_le : ∀ k, U₁ k ≤ B k)
    (h₂_le : ∀ k, U₂ k ≤ B k) (hU : ∑ k : κ, U₁ k ≤ ∑ k : κ, U₂ k) :
    ∑ k : κ, psiB (B k) (U₁ k) ≤ ∑ k : κ, psiB (B k) (U₂ k) := by
  rw [psiB_sum_affine_of_le B U₁ h₁_le, psiB_sum_affine_of_le B U₂ h₂_le]
  linarith

/-- **Risk-neutral recovery**: let `R` collect all objective terms other than
    MM fill utility. If `xRN` maximizes `R(x) + ∑ U_k(x)` on `S` and every MM is
    below budget there, then `xRN` also maximizes
    `R(x) + ∑ ψ_{B_k}(U_k(x))`.

    This is the abstract optimization statement used by the paper's recovery
    proposition. -/
theorem riskNeutral_recovery
    (S : Set X) (B : κ → ℝ) (U : X → κ → ℝ) (R : X → ℝ) (xRN : X)
    (hB : ∀ k, 0 < B k)
    (hRN_le : ∀ k, U xRN k ≤ B k) (hRN_opt : ∀ x ∈ S,
      R x + ∑ k : κ, U x k ≤ R xRN + ∑ k : κ, U xRN k) :
    ∀ x ∈ S,
      R x + ∑ k : κ, psiB (B k) (U x k) ≤
        R xRN + ∑ k : κ, psiB (B k) (U xRN k) := by
  intro x hx
  have hψx : ∑ k : κ, psiB (B k) (U x k) ≤
      ∑ k : κ, U x k + ∑ k : κ, (B k * Real.log (B k) - B k) := by
    calc
      ∑ k : κ, psiB (B k) (U x k)
          ≤ ∑ k : κ, (U x k + B k * Real.log (B k) - B k) :=
            Finset.sum_le_sum fun k _ => psiB_le_affine (hB k)
      _ = ∑ k : κ, U x k + ∑ k : κ, (B k * Real.log (B k) - B k) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
  rw [psiB_sum_affine_of_le B (U xRN) hRN_le]
  linarith [hRN_opt x hx]

end FisherClearing
