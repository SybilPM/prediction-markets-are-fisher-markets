/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.FullProgram
import FisherClearing.Duality.SandwichBound

/-!
# Zero-Temperature Clearing

This file gives the `b = 0` counterpart of the log-sum-exp clearing program.
The minting cost is the finite maximum of net demand.  We prove continuity,
concavity, and existence of an optimum on the fill box.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- Reduced-form clearing objective at zero temperature. -/
noncomputable def FullInstance.objectiveZero (fill : J → ℝ) : ℝ :=
  (∑ k : K, psiB (inst.budget k) (inst.mmUtil fill k)) -
  maxFin (inst.netDemand fill) +
  inst.retailWelfare fill

theorem FullInstance.continuous_objectiveZero :
    Continuous inst.objectiveZero := by
  unfold FullInstance.objectiveZero
  exact (inst.continuous_mmWelfare.sub
    (continuous_maxFin.comp inst.continuous_netDemand)).add
      inst.continuous_retailWelfare

omit [Fintype K] [DecidableEq K] in theorem FullInstance.concaveOn_neg_zero_minting :
    ConcaveOn ℝ boxFeasible
      (fun fill => -maxFin (inst.netDemand fill)) := by
  constructor
  · exact convex_boxFeasible
  · intro f _ g _ a c ha hc hac
    simp only [smul_eq_mul]
    have hlin :
        inst.netDemand (a • f + c • g) =
          a • inst.netDemand f + c • inst.netDemand g := by
      ext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact inst.netDemand_linear s f g a c
    rw [hlin]
    have hconv := convexOn_maxFin.2
      (Set.mem_univ (inst.netDemand f)) (Set.mem_univ (inst.netDemand g))
      ha hc hac
    simp only [smul_eq_mul] at hconv
    linarith

theorem FullInstance.concaveOn_objectiveZero :
    ConcaveOn ℝ boxFeasible inst.objectiveZero := by
  constructor
  · exact convex_boxFeasible
  · intro f hf g hg a c ha hc hac
    have hMM := inst.concaveOn_mmWelfare.2 hf hg ha hc hac
    have hMint := inst.concaveOn_neg_zero_minting.2 hf hg ha hc hac
    have hRetail := inst.concaveOn_retailWelfare.2 hf hg ha hc hac
    simp only [FullInstance.objectiveZero, smul_eq_mul] at *
    linarith

/-- The positive-temperature objective uniformly approximates the
    zero-temperature objective, with the same `b log |ι|` error as the
    log-sum-exp approximation to the maximum. -/
theorem FullInstance.objective_sandwich_zero
    {b : ℝ} (hb : 0 < b) (fill : J → ℝ) :
    inst.objectiveZero fill -
        b * Real.log (Fintype.card ι) ≤
      inst.objective b fill ∧
    inst.objective b fill ≤ inst.objectiveZero fill := by
  have hsandwich :=
    logSumExp_sandwich hb (inst.netDemand fill)
  unfold FullInstance.objective FullInstance.objectiveZero
  constructor <;> linarith

/-- The zero-temperature reduced-form clearing program has an optimizer. -/
theorem FullInstance.exists_optimal_fill_zero :
    ∃ fill ∈ (boxFeasible : Set (J → ℝ)),
      IsMaxOn inst.objectiveZero boxFeasible fill := by
  exact isCompact_boxFeasible.exists_isMaxOn nonempty_boxFeasible
    inst.continuous_objectiveZero.continuousOn

end FisherClearing
