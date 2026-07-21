/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.PriceDual

/-!
# Unique Positive-Temperature Observables

At positive temperature, different optimal order-level fills may remain, but
the clearing price, each MM's deployed value and scarcity factor, every
strictly capital-constrained MM's weighted fill, and net demand modulo a
complete-set shift are unique.
-/

namespace FisherClearing

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- Across positive-temperature optima, each MM's deployed value is unique. -/
theorem FullInstance.deployedValue_unique
    {b : ℝ} (hb : 0 < b)
    (fill₁ fill₂ : J → ℝ) (hfill₁ : fill₁ ∈ (boxFeasible : Set (J → ℝ)))
    (hfill₂ : fill₂ ∈ (boxFeasible : Set (J → ℝ)))
    (hopt₁ : IsMaxOn (inst.objective b) boxFeasible fill₁)
    (hopt₂ : IsMaxOn (inst.objective b) boxFeasible fill₂) (k : K) :
    deployedValue (inst.budget k) (inst.mmUtil fill₁ k) =
      deployedValue (inst.budget k) (inst.mmUtil fill₂ k) := by
  let price₁ := softmax b (inst.netDemand fill₁)
  let price₂ := softmax b (inst.netDemand fill₂)
  have hprice : price₁ = price₂ := by
    exact inst.softmax_price_unique hb fill₁ fill₂
      hfill₁ hfill₂ hopt₁ hopt₂
  have heq₁ :=
    inst.competitiveEquilibrium_of_optimal hb fill₁ hfill₁ hopt₁
  have heq₂ :=
    inst.competitiveEquilibrium_of_optimal hb fill₂ hfill₂ hopt₂
  have hopt₂' :
      IsMaxOn (inst.mmPayoff price₁ k) boxFeasible fill₂ := by
    simpa only [price₁, price₂, hprice] using heq₂.mmOptimal inst k
  have h₁₂ :=
    inst.mmDirectional_nonpos_of_optimal price₁ k fill₁ fill₂
      hfill₁ hfill₂ (heq₁.mmOptimal inst k)
  have h₂₁ :=
    inst.mmDirectional_nonpos_of_optimal price₁ k fill₂ fill₁
      hfill₂ hfill₁ hopt₂'
  by_cases hU :
      inst.mmUtil fill₁ k ≤ inst.mmUtil fill₂ k
  · have hslope :
        psiSlope (inst.budget k) (inst.mmUtil fill₁ k) ≤
          psiSlope (inst.budget k) (inst.mmUtil fill₂ k) := by
      rcases hU.eq_or_lt with hEq | hlt
      · rw [hEq]
      · nlinarith
    exact deployedValue_eq_of_le_of_psiSlope_le
      (inst.budget_pos k) hU hslope
  · have hU' : inst.mmUtil fill₂ k ≤ inst.mmUtil fill₁ k :=
      le_of_not_ge hU
    have hslope :
        psiSlope (inst.budget k) (inst.mmUtil fill₂ k) ≤
          psiSlope (inst.budget k) (inst.mmUtil fill₁ k) := by
      have hlt : inst.mmUtil fill₂ k < inst.mmUtil fill₁ k :=
        lt_of_not_ge hU
      nlinarith
    exact (deployedValue_eq_of_le_of_psiSlope_le
      (inst.budget_pos k) hU' hslope).symm

/-- Consequently each MM's capital-scarcity factor is unique. -/
theorem FullInstance.capitalScarcity_unique
    {b : ℝ} (hb : 0 < b)
    (fill₁ fill₂ : J → ℝ) (hfill₁ : fill₁ ∈ (boxFeasible : Set (J → ℝ)))
    (hfill₂ : fill₂ ∈ (boxFeasible : Set (J → ℝ)))
    (hopt₁ : IsMaxOn (inst.objective b) boxFeasible fill₁)
    (hopt₂ : IsMaxOn (inst.objective b) boxFeasible fill₂) (k : K) :
    capitalScarcity (inst.budget k) (inst.mmUtil fill₁ k) =
      capitalScarcity (inst.budget k) (inst.mmUtil fill₂ k) := by
  have hV := inst.deployedValue_unique hb fill₁ fill₂
    hfill₁ hfill₂ hopt₁ hopt₂ k
  unfold capitalScarcity
  simpa only [deployedValue] using congrArg
    (fun V : ℝ => inst.budget k / V) hV

/-- If an MM is strictly capital-constrained at one optimum, its weighted fill
    itself (not merely its deployed value) is unique across all optima. -/
theorem FullInstance.mmUtil_unique_of_budget_lt
    {b : ℝ} (hb : 0 < b)
    (fill₁ fill₂ : J → ℝ) (hfill₁ : fill₁ ∈ (boxFeasible : Set (J → ℝ)))
    (hfill₂ : fill₂ ∈ (boxFeasible : Set (J → ℝ)))
    (hopt₁ : IsMaxOn (inst.objective b) boxFeasible fill₁)
    (hopt₂ : IsMaxOn (inst.objective b) boxFeasible fill₂)
    (k : K) (hbinding : inst.budget k < inst.mmUtil fill₁ k) :
    inst.mmUtil fill₁ k = inst.mmUtil fill₂ k := by
  have hV := inst.deployedValue_unique hb fill₁ fill₂
    hfill₁ hfill₂ hopt₁ hopt₂ k
  have hright : inst.budget k < inst.mmUtil fill₂ k := by
    by_contra h
    have hle : inst.mmUtil fill₂ k ≤ inst.budget k := le_of_not_gt h
    rw [deployedValue, max_eq_left hbinding.le,
      deployedValue, max_eq_right hle] at hV
    linarith
  simpa only [deployedValue, max_eq_left hbinding.le,
    max_eq_left hright.le] using hV

/-- Net demand is unique modulo adding one common complete-set quantity to
    every outcome. -/
theorem FullInstance.exists_netDemand_add_const
    {b : ℝ} (hb : 0 < b)
    (fill₁ fill₂ : J → ℝ) (hfill₁ : fill₁ ∈ (boxFeasible : Set (J → ℝ)))
    (hfill₂ : fill₂ ∈ (boxFeasible : Set (J → ℝ)))
    (hopt₁ : IsMaxOn (inst.objective b) boxFeasible fill₁)
    (hopt₂ : IsMaxOn (inst.objective b) boxFeasible fill₂) :
    ∃ c : ℝ, ∀ s : ι,
      inst.netDemand fill₁ s = inst.netDemand fill₂ s + c := by
  apply exists_add_const_of_softmax_eq hb
  exact inst.softmax_price_unique hb fill₁ fill₂
    hfill₁ hfill₂ hopt₁ hopt₂

end FisherClearing
