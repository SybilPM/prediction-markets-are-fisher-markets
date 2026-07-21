/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Convex.Softmax
import FisherClearing.Duality.SandwichBound

/-!
# Structural Market Identities

This file proves the algebraic identities used by the paper's buy/sell
reduction and independent-group decomposition.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι κ : Type*}
variable [Fintype ι] [Nonempty ι]
variable [Fintype κ] [Nonempty κ]

/-! ### Buy/sell complement reduction -/

/-- Replacing a binary sell at limit `L` by a buy of the complementary
    outcome at limit `1 - L` leaves the positive-temperature objective
    unchanged.  The replacement adds `q` complete sets to demand. -/
theorem buySellReduction_logSumExp
    {b : ℝ} (hb : 0 < b) (demand : ι → ℝ)
    (limit quantity : ℝ) : (1 - limit) * quantity -
        logSumExp b (fun s => demand s + quantity) =
      -limit * quantity - logSumExp b demand := by
  rw [logSumExp_add_const hb]
  ring

/-- The same complement identity for zero-temperature minting. -/
theorem buySellReduction_maxFin (demand : ι → ℝ) (limit quantity : ℝ) :
    (1 - limit) * quantity -
        maxFin (fun s => demand s + quantity) =
      -limit * quantity - maxFin demand := by
  rw [maxFin_add_const]
  ring

/-! ### Independent market groups -/

private theorem exp_add_div (b x y : ℝ) :
    Real.exp ((x + y) / b) =
      Real.exp (x / b) * Real.exp (y / b) := by
  rw [← Real.exp_add]
  congr 1
  ring

omit [Nonempty ι] [Nonempty κ] in
/-- The exponential partition sum factorizes over independent groups. -/
theorem sumExp_product_add (b : ℝ) (f : ι → ℝ) (g : κ → ℝ) :
    sumExp b (fun z : ι × κ => f z.1 + g z.2) =
      sumExp b f * sumExp b g := by
  unfold sumExp
  rw [Fintype.sum_prod_type]
  simp_rw [exp_add_div, ← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- Log-sum-exp minting costs add across independent groups. -/
theorem logSumExp_product_add (b : ℝ) (f : ι → ℝ) (g : κ → ℝ) :
    logSumExp b (fun z : ι × κ => f z.1 + g z.2) =
      logSumExp b f + logSumExp b g := by
  unfold logSumExp
  rw [sumExp_product_add,
    Real.log_mul (sumExp_ne_zero b f) (sumExp_ne_zero b g)]
  ring

/-- Max minting costs add across independent groups. -/
theorem maxFin_product_add (f : ι → ℝ) (g : κ → ℝ) :
    maxFin (fun z : ι × κ => f z.1 + g z.2) =
      maxFin f + maxFin g := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro z _
    exact add_le_add (le_maxFin f z.1) (le_maxFin g z.2)
  · let joint : ι × κ → ℝ := fun z => f z.1 + g z.2
    have hi : ∀ i : ι,
        f i + maxFin g ≤ maxFin joint := by
      intro i
      have hg :
          maxFin g ≤ maxFin joint - f i := by
        apply Finset.sup'_le
        intro j _
        have hij := le_maxFin joint (i, j)
        dsimp only [joint] at hij
        linarith
      linarith
    have hf :
        maxFin f ≤ maxFin joint - maxFin g := by
      apply Finset.sup'_le
      intro i _
      linarith [hi i]
    change maxFin f + maxFin g ≤ maxFin joint
    linarith

omit [Nonempty ι] in
/-- The first-group marginal of a factorized joint softmax is the
    first-group softmax. -/
theorem softmax_product_fst_marginal (b : ℝ) (f : ι → ℝ) (g : κ → ℝ) (i : ι) :
    (∑ j : κ,
      softmax b (fun z : ι × κ => f z.1 + g z.2) (i, j)) =
      softmax b f i := by
  unfold softmax
  rw [sumExp_product_add, ← Finset.sum_div]
  simp_rw [exp_add_div]
  rw [← Finset.mul_sum]
  change
    (Real.exp (f i / b) * sumExp b g) /
        (sumExp b f * sumExp b g) =
      Real.exp (f i / b) / sumExp b f
  exact mul_div_mul_right
    (Real.exp (f i / b)) (sumExp b f)
      (sumExp_ne_zero b g)

omit [Nonempty κ] in
/-- The second-group marginal of a factorized joint softmax is the
    second-group softmax. -/
theorem softmax_product_snd_marginal
    (b : ℝ) (f : ι → ℝ) (g : κ → ℝ) (j : κ) : (∑ i : ι,
      softmax b (fun z : ι × κ => f z.1 + g z.2) (i, j)) =
      softmax b g j := by
  unfold softmax
  rw [sumExp_product_add, ← Finset.sum_div]
  simp_rw [exp_add_div]
  rw [← Finset.sum_mul]
  change
    (sumExp b f * Real.exp (g j / b)) /
        (sumExp b f * sumExp b g) =
      Real.exp (g j / b) / sumExp b g
  exact mul_div_mul_left
    (Real.exp (g j / b)) (sumExp b g)
      (sumExp_ne_zero b f)

end FisherClearing
