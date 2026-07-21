/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.MaximumEntropy

/-!
# The Paper's Three-Order Worked Example

This file instantiates the abstract clearing model with the numerical example
from the paper and verifies its displayed allocation, price, scarcity factor,
and capital use.
-/

namespace FisherClearing

open scoped BigOperators

inductive WorkedOutcome
  | yes
  | no
  deriving DecidableEq, Fintype, Nonempty

inductive WorkedOrder
  | highMM
  | lowMM
  | retailNo
  deriving DecidableEq, Fintype

theorem sum_workedOutcome (f : WorkedOutcome → ℝ) : (∑ s : WorkedOutcome, f s) =
      f .yes + f .no := by
  rw [show (Finset.univ : Finset WorkedOutcome) =
      {.yes, .no} by decide]
  simp

theorem sum_workedOrder (f : WorkedOrder → ℝ) : (∑ j : WorkedOrder, f j) =
      f .highMM + f .lowMM + f .retailNo := by
  rw [show (Finset.univ : Finset WorkedOrder) =
      {.highMM, .lowMM, .retailNo} by decide]
  simp
  ring

/-- The worked order book, with fills normalized to fractions of each order's
    cap.  Thus coefficients already include the order sizes 100, 100, and 200. -/
noncomputable def workedInstance :
    FullInstance WorkedOutcome WorkedOrder Unit where
  limitPrice
    | .highMM => 70
    | .lowMM => 55
    | .retailNo => 120
  payoff
    | .highMM, .yes => 100
    | .highMM, .no => 0
    | .lowMM, .yes => 100
    | .lowMM, .no => 0
    | .retailNo, .yes => 0
    | .retailNo, .no => 200
  budget _ := 50
  budget_pos _ := by norm_num
  limitPrice_pos
    | .highMM => by norm_num
    | .lowMM => by norm_num
    | .retailNo => by norm_num
  owner
    | .highMM => some ()
    | .lowMM => some ()
    | .retailNo => none

/-- Full fill of the high MM bid, rejection of the low MM bid, and half fill
    of the retail No bid. -/
noncomputable def workedFill : WorkedOrder → ℝ
  | .highMM => 1
  | .lowMM => 0
  | .retailNo => 1 / 2

/-- The supporting zero-temperature outcome price `(0.4, 0.6)`. -/
noncomputable def workedPrice : WorkedOutcome → ℝ
  | .yes => 2 / 5
  | .no => 3 / 5

/-- The budget-blind LP fill from the worked example. -/
noncomputable def workedRiskNeutralFill : WorkedOrder → ℝ
  | _ => 1

/-- Risk-neutral zero-temperature welfare for this order book. -/
noncomputable def workedRiskNeutralZeroObjective (fill : WorkedOrder → ℝ) : ℝ :=
  workedInstance.mmUtil fill () +
    workedInstance.retailWelfare fill -
    maxFin (workedInstance.netDemand fill)

theorem workedFill_mem_box :
    workedFill ∈
      (boxFeasible : Set (WorkedOrder → ℝ)) := by
  apply Set.mem_pi.mpr
  intro j _
  cases j <;> norm_num [workedFill]

theorem workedPrice_mem_simplex :
    workedPrice ∈ stdSimplex ℝ WorkedOutcome := by
  constructor
  · intro s
    cases s <;> norm_num [workedPrice]
  · rw [sum_workedOutcome]
    norm_num [workedPrice]

theorem worked_mmUtil (fill : WorkedOrder → ℝ) :
    workedInstance.mmUtil fill () =
      70 * fill .highMM + 55 * fill .lowMM := by
  unfold FullInstance.mmUtil
  rw [sum_workedOrder]
  simp only [workedInstance, ↓reduceIte, reduceCtorEq, add_zero]

theorem worked_mmSpending (fill : WorkedOrder → ℝ) :
    workedInstance.mmSpending workedPrice fill () =
      40 * fill .highMM + 40 * fill .lowMM := by
  unfold FullInstance.mmSpending
  rw [sum_workedOrder]
  simp only [workedInstance, ↓reduceIte, reduceCtorEq, add_zero]
  rw [sum_workedOutcome, sum_workedOutcome]
  norm_num [workedPrice]

theorem worked_retailWelfare (fill : WorkedOrder → ℝ) :
    workedInstance.retailWelfare fill =
      120 * fill .retailNo := by
  unfold FullInstance.retailWelfare
  rw [sum_workedOrder]
  simp [workedInstance]

theorem worked_demandPayment (fill : WorkedOrder → ℝ) :
    outcomeDot workedPrice (workedInstance.netDemand fill) =
      40 * fill .highMM + 40 * fill .lowMM +
        120 * fill .retailNo := by
  rw [workedInstance.demandPayment_eq_agentSpending]
  rw [show (∑ k : Unit,
      workedInstance.mmSpending workedPrice fill k) =
        workedInstance.mmSpending workedPrice fill () by simp,
    worked_mmSpending]
  unfold FullInstance.retailSpending outcomeDot
  rw [sum_workedOrder]
  simp only [workedInstance, reduceCtorEq, ↓reduceIte, add_zero, zero_add,
    add_right_inj, mul_eq_mul_right_iff]
  rw [sum_workedOutcome]
  norm_num [workedPrice]

theorem worked_mmPayoff (fill : WorkedOrder → ℝ) :
    workedInstance.mmPayoff workedPrice () fill =
      psiB 50 (70 * fill .highMM + 55 * fill .lowMM) -
        (40 * fill .highMM + 40 * fill .lowMM) := by
  unfold FullInstance.mmPayoff
  rw [worked_mmUtil, worked_mmSpending]
  rfl

theorem worked_netDemand :
    workedInstance.netDemand workedFill =
      fun _ : WorkedOutcome => 100 := by
  funext s
  unfold FullInstance.netDemand
  rw [sum_workedOrder]
  cases s <;> norm_num [workedInstance, workedFill]

theorem worked_supply_support :
    outcomeDot workedPrice
        (workedInstance.netDemand workedFill) =
      maxFin (workedInstance.netDemand workedFill) := by
  rw [worked_netDemand]
  have hmax :
      maxFin (fun _ : WorkedOutcome => (100 : ℝ)) = 100 := by
    simpa using
      maxFin_add_const (0 : WorkedOutcome → ℝ) 100
  rw [hmax]
  unfold outcomeDot
  rw [sum_workedOutcome]
  norm_num [workedPrice]

/-- The budget-blind fill creates 200 units of demand in either outcome. -/
theorem workedRiskNeutral_netDemand :
    workedInstance.netDemand workedRiskNeutralFill =
      fun _ : WorkedOutcome => 200 := by
  funext s
  unfold FullInstance.netDemand
  rw [sum_workedOrder]
  cases s <;> norm_num [workedInstance, workedRiskNeutralFill]

theorem workedRiskNeutral_maxFin :
    maxFin (workedInstance.netDemand workedRiskNeutralFill) = 200 := by
  rw [workedRiskNeutral_netDemand]
  simpa using maxFin_add_const (0 : WorkedOutcome → ℝ) 200

theorem worked_mm_optimal :
    IsMaxOn
      (workedInstance.mmPayoff workedPrice ())
      boxFeasible workedFill := by
  intro other hother
  change
    workedInstance.mmPayoff workedPrice () other ≤
      workedInstance.mmPayoff workedPrice () workedFill
  rw [worked_mmPayoff, worked_mmPayoff]
  have hU :
      0 ≤ 70 * other .highMM + 55 * other .lowMM := by
    rw [← worked_mmUtil]
    exact workedInstance.mmUtil_nonneg other hother ()
  have htangent :=
    psiB_le_tangent (B := (50 : ℝ)) (U := (70 : ℝ))
      (V := 70 * other .highMM + 55 * other .lowMM)
      (by norm_num) (by norm_num) hU
  norm_num [psiSlope] at htangent
  rcases Set.mem_pi.mp hother WorkedOrder.highMM trivial with
    ⟨hhighLower, hhighUpper⟩
  rcases Set.mem_pi.mp hother WorkedOrder.lowMM trivial with
    ⟨hlowLower, hlowUpper⟩
  norm_num [workedFill]
  nlinarith

theorem worked_retail_optimal :
    IsMaxOn
      (workedInstance.retailOrderPayoff
        workedPrice .retailNo)
      (Set.Icc 0 1) (workedFill .retailNo) := by
  intro quantity _
  change
    workedInstance.retailOrderPayoff
        workedPrice .retailNo quantity ≤
      workedInstance.retailOrderPayoff
        workedPrice .retailNo (workedFill .retailNo)
  unfold FullInstance.retailOrderPayoff outcomeDot
  rw [sum_workedOutcome]
  norm_num [workedInstance, workedPrice, workedFill]

/-- The displayed allocation and price form an agent-by-agent competitive
    equilibrium. -/
theorem worked_zeroAgentCompetitiveEquilibrium :
    workedInstance.ZeroAgentCompetitiveEquilibrium
      workedFill workedPrice where
  fill_mem := workedFill_mem_box
  price_mem := workedPrice_mem_simplex
  supply_optimal :=
    zeroSupply_optimal_of_support workedPrice
      (workedInstance.netDemand workedFill)
      workedPrice_mem_simplex worked_supply_support
  mm_optimal := by
    intro k
    cases k
    exact worked_mm_optimal
  retail_optimal := by
    intro j howner
    cases j with
    | highMM => simp [workedInstance] at howner
    | lowMM => simp [workedInstance] at howner
    | retailNo => exact worked_retail_optimal

/-- The paper's worked fill is globally optimal for the zero-temperature
    reduced-form clearing program. -/
theorem workedFill_isOptimal :
    IsMaxOn workedInstance.objectiveZero boxFeasible workedFill :=
  worked_zeroAgentCompetitiveEquilibrium.isOptimal workedInstance

/-- The paper's budget-blind LP allocation (all three orders filled) is
    globally risk-neutral optimal. -/
theorem workedRiskNeutralFill_isOptimal :
    IsMaxOn workedRiskNeutralZeroObjective boxFeasible
      workedRiskNeutralFill := by
  intro other hother
  change workedRiskNeutralZeroObjective other ≤
    workedRiskNeutralZeroObjective workedRiskNeutralFill
  have hmint :=
    outcomeDot_le_maxFin workedPrice
      (workedInstance.netDemand other)
      workedPrice_mem_simplex
  have hhigh :=
    (Set.mem_pi.mp hother WorkedOrder.highMM trivial).2
  have hlow :=
    (Set.mem_pi.mp hother WorkedOrder.lowMM trivial).2
  unfold workedRiskNeutralZeroObjective
  rw [worked_mmUtil, worked_retailWelfare,
    worked_mmUtil, worked_retailWelfare, workedRiskNeutral_maxFin]
  rw [worked_demandPayment] at hmint
  norm_num [workedRiskNeutralFill]
  nlinarith

theorem workedRiskNeutral_welfare_value :
    workedRiskNeutralZeroObjective workedRiskNeutralFill = 45 := by
  unfold workedRiskNeutralZeroObjective
  rw [worked_mmUtil, worked_retailWelfare, workedRiskNeutral_maxFin]
  norm_num [workedRiskNeutralFill]

theorem worked_reducedFill_riskNeutralWelfare_value :
    workedRiskNeutralZeroObjective workedFill = 30 := by
  unfold workedRiskNeutralZeroObjective
  rw [worked_mmUtil, worked_retailWelfare, worked_netDemand]
  have hmax :
      maxFin (fun _ : WorkedOutcome => (100 : ℝ)) = 100 := by
    simpa using
      maxFin_add_const (0 : WorkedOutcome → ℝ) 100
  rw [hmax]
  norm_num [workedFill]

theorem worked_welfare_gap_value :
    workedRiskNeutralZeroObjective workedRiskNeutralFill -
        workedRiskNeutralZeroObjective workedFill =
      15 := by
  rw [workedRiskNeutral_welfare_value,
    worked_reducedFill_riskNeutralWelfare_value]
  norm_num

theorem worked_mmUtil_value :
    workedInstance.mmUtil workedFill () = 70 := by
  rw [worked_mmUtil]
  norm_num [workedFill]

theorem worked_scarcity_value :
    capitalScarcity 50
      (workedInstance.mmUtil workedFill ()) = 5 / 7 := by
  rw [worked_mmUtil_value]
  norm_num [capitalScarcity]

theorem worked_spending_value :
    workedInstance.mmSpending workedPrice workedFill () = 40 := by
  rw [worked_mmSpending]
  norm_num [workedFill]

end FisherClearing
