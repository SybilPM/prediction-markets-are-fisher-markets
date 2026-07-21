/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import FisherClearing.Convex.LogSumExp

/-!
# The Hard-Budget Computational Obstruction

This file formalizes the explicit two-market witness from the paper.  In each
independent binary market, one filled buy order consumes
`q * logistic(q / b)` units of capital.  For every `b > 0`, the two endpoint
fill plans `(2b, 9b)` and `(9b, 2b)` fit within budget `10.8b`, while their
midpoint `(5.5b, 5.5b)` does not.  Thus the hard-budget feasible set is
nonconvex at every positive temperature.
-/

namespace FisherClearing

/-- Logistic marginal price in a binary LMSR market. -/
noncomputable def logisticPrice (t : ℝ) : ℝ :=
  Real.exp t / (1 + Real.exp t)

/-- Capital consumed by one LMSR-priced buy fill. -/
noncomputable def binaryCapital (b q : ℝ) : ℝ :=
  logisticPrice (q / b) * q

/-- Capital consumed by the two independent orders in the witness. -/
noncomputable def twoMarketCapital (b : ℝ) (q : ℝ × ℝ) : ℝ :=
  binaryCapital b q.1 + binaryCapital b q.2

/-- The witness hard-budget feasible set, with budget `10.8 b`. -/
noncomputable def hardBudgetWitnessSet (b : ℝ) : Set (ℝ × ℝ) :=
  {q | twoMarketCapital b q ≤ (54 / 5 : ℝ) * b}

/-- The order-cap box used by the witness instance. -/
def hardBudgetWitnessBox (b : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ q.1 ≤ 9 * b ∧ 0 ≤ q.2 ∧ q.2 ≤ 9 * b}

/-- The actual bounded hard-budget feasible region: capital feasibility
    intersected with the order-cap box. -/
noncomputable def hardBudgetWitnessInstanceSet (b : ℝ) : Set (ℝ × ℝ) :=
  hardBudgetWitnessSet b ∩ hardBudgetWitnessBox b

noncomputable def hardBudgetWitnessX (b : ℝ) : ℝ × ℝ :=
  (2 * b, 9 * b)

noncomputable def hardBudgetWitnessY (b : ℝ) : ℝ × ℝ :=
  (9 * b, 2 * b)

noncomputable def hardBudgetWitnessMid (b : ℝ) : ℝ × ℝ :=
  ((11 / 2 : ℝ) * b, (11 / 2 : ℝ) * b)

theorem logisticPrice_lt_one (t : ℝ) :
    logisticPrice t < 1 := by
  unfold logisticPrice
  exact (div_lt_one (by positivity)).2 (by linarith)

theorem exp_two_lt_nine :
    Real.exp 2 < 9 := by
  have hpow :
      Real.exp (1 : ℝ) ^ 2 = Real.exp (2 : ℝ) := by
    simp
  rw [← hpow]
  nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]

theorem two_mul_logisticPrice_two_lt :
    2 * logisticPrice 2 < (9 / 5 : ℝ) := by
  unfold logisticPrice
  have hden : 0 < 1 + Real.exp 2 := by positivity
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hden).2
  nlinarith [exp_two_lt_nine]

theorem exp_five_lt_exp_eleven_halves :
    Real.exp 5 < Real.exp (11 / 2 : ℝ) :=
  Real.exp_lt_exp.mpr (by norm_num)

theorem fifty_four_lt_exp_eleven_halves : (54 : ℝ) < Real.exp (11 / 2 : ℝ) := by
  have hone : (5 / 2 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hpow :
      (5 / 2 : ℝ) ^ 5 < Real.exp 1 ^ 5 :=
    pow_lt_pow_left₀ hone (by norm_num) (by norm_num)
  calc
    (54 : ℝ) < (5 / 2 : ℝ) ^ 5 := by norm_num
    _ < Real.exp 1 ^ 5 := hpow
    _ = Real.exp 5 := Real.exp_one_pow 5
    _ < Real.exp (11 / 2 : ℝ) :=
      exp_five_lt_exp_eleven_halves

theorem fifty_four_over_fifty_five_lt_logisticPrice :
    (54 / 55 : ℝ) < logisticPrice (11 / 2 : ℝ) := by
  unfold logisticPrice
  have hden : 0 < 1 + Real.exp (11 / 2 : ℝ) := by positivity
  apply (lt_div_iff₀ hden).2
  nlinarith [fifty_four_lt_exp_eleven_halves]

theorem twoMarketCapital_scaled
    {b : ℝ} (hb : 0 < b) (x y : ℝ) :
    twoMarketCapital b (b * x, b * y) =
      b * (logisticPrice x * x + logisticPrice y * y) := by
  unfold twoMarketCapital binaryCapital
  have hb0 : b ≠ 0 := ne_of_gt hb
  rw [mul_div_cancel_left₀ x hb0, mul_div_cancel_left₀ y hb0]
  ring

theorem hardBudgetWitnessX_mem
    {b : ℝ} (hb : 0 < b) :
    hardBudgetWitnessX b ∈ hardBudgetWitnessSet b := by
  change twoMarketCapital b (2 * b, 9 * b) ≤ (54 / 5 : ℝ) * b
  rw [show (2 * b, 9 * b) = (b * 2, b * 9) by
    ext <;> ring, twoMarketCapital_scaled hb]
  have hnine : 9 * logisticPrice 9 < 9 := by
    nlinarith [logisticPrice_lt_one 9]
  have hbase :
      logisticPrice 2 * 2 + logisticPrice 9 * 9 <
        (54 / 5 : ℝ) := by
    nlinarith [two_mul_logisticPrice_two_lt]
  nlinarith

theorem hardBudgetWitnessY_mem
    {b : ℝ} (hb : 0 < b) :
    hardBudgetWitnessY b ∈ hardBudgetWitnessSet b := by
  change twoMarketCapital b (9 * b, 2 * b) ≤ (54 / 5 : ℝ) * b
  rw [show (9 * b, 2 * b) = (b * 9, b * 2) by
    ext <;> ring, twoMarketCapital_scaled hb]
  have hnine : 9 * logisticPrice 9 < 9 := by
    nlinarith [logisticPrice_lt_one 9]
  have hbase :
      logisticPrice 9 * 9 + logisticPrice 2 * 2 <
        (54 / 5 : ℝ) := by
    nlinarith [two_mul_logisticPrice_two_lt]
  nlinarith

theorem hardBudgetWitnessMid_not_mem
    {b : ℝ} (hb : 0 < b) :
    hardBudgetWitnessMid b ∉ hardBudgetWitnessSet b := by
  change ¬ twoMarketCapital b
    ((11 / 2 : ℝ) * b, (11 / 2 : ℝ) * b) ≤
      (54 / 5 : ℝ) * b
  rw [show
      ((11 / 2 : ℝ) * b, (11 / 2 : ℝ) * b) =
        (b * (11 / 2 : ℝ), b * (11 / 2 : ℝ)) by
    ext <;> ring, twoMarketCapital_scaled hb]
  have hbase :
      (54 / 5 : ℝ) <
        logisticPrice (11 / 2 : ℝ) * (11 / 2 : ℝ) +
          logisticPrice (11 / 2 : ℝ) * (11 / 2 : ℝ) := by
    nlinarith [fifty_four_over_fifty_five_lt_logisticPrice]
  nlinarith

theorem hardBudgetWitnessMid_eq_average (b : ℝ) :
    hardBudgetWitnessMid b =
      (1 / 2 : ℝ) • hardBudgetWitnessX b +
        (1 / 2 : ℝ) • hardBudgetWitnessY b := by
  ext <;>
    simp [hardBudgetWitnessMid, hardBudgetWitnessX,
      hardBudgetWitnessY] <;>
    ring

/-- Both witness endpoints obey the order caps. -/
theorem hardBudgetWitnessX_mem_box
    {b : ℝ} (hb : 0 < b) :
    hardBudgetWitnessX b ∈ hardBudgetWitnessBox b := by
  simp only [hardBudgetWitnessX, hardBudgetWitnessBox, Set.mem_setOf_eq]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · positivity
  · exact le_rfl

theorem hardBudgetWitnessY_mem_box
    {b : ℝ} (hb : 0 < b) :
    hardBudgetWitnessY b ∈ hardBudgetWitnessBox b := by
  simp only [hardBudgetWitnessY, hardBudgetWitnessBox, Set.mem_setOf_eq]
  constructor
  · positivity
  constructor
  · exact le_rfl
  constructor
  · positivity
  · nlinarith

theorem hardBudgetWitnessX_mem_instance
    {b : ℝ} (hb : 0 < b) :
    hardBudgetWitnessX b ∈ hardBudgetWitnessInstanceSet b :=
  ⟨hardBudgetWitnessX_mem hb, hardBudgetWitnessX_mem_box hb⟩

theorem hardBudgetWitnessY_mem_instance
    {b : ℝ} (hb : 0 < b) :
    hardBudgetWitnessY b ∈ hardBudgetWitnessInstanceSet b :=
  ⟨hardBudgetWitnessY_mem hb, hardBudgetWitnessY_mem_box hb⟩

theorem hardBudgetWitnessMid_not_mem_instance
    {b : ℝ} (hb : 0 < b) :
    hardBudgetWitnessMid b ∉ hardBudgetWitnessInstanceSet b := by
  intro hmid
  exact hardBudgetWitnessMid_not_mem hb hmid.1

/-- The unbounded capital sublevel set is already nonconvex. -/
theorem not_convex_hardBudgetWitnessSet
    {b : ℝ} (hb : 0 < b) :
    ¬ Convex ℝ (hardBudgetWitnessSet b) := by
  intro hconv
  have havg :=
    hconv (hardBudgetWitnessX_mem hb)
      (hardBudgetWitnessY_mem hb)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [← hardBudgetWitnessMid_eq_average b] at havg
  exact hardBudgetWitnessMid_not_mem hb havg

/-- **Computational obstruction.**  For every positive temperature, the
    hard-budget feasible region of an explicit bounded two-market instance is
    nonconvex.  Thus the obstruction survives intersection with the paper's
    order-cap box. -/
theorem not_convex_hardBudgetWitnessInstanceSet
    {b : ℝ} (hb : 0 < b) :
    ¬ Convex ℝ (hardBudgetWitnessInstanceSet b) := by
  intro hconv
  have havg :=
    hconv (hardBudgetWitnessX_mem_instance hb)
      (hardBudgetWitnessY_mem_instance hb)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [← hardBudgetWitnessMid_eq_average b] at havg
  exact hardBudgetWitnessMid_not_mem_instance hb havg

end FisherClearing
