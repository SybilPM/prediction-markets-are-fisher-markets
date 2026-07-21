/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.FullProgram

/-!
# Demand-Space Value Function

We project the fill box through the linear net-demand map and define the inner
reduced-form welfare as an attained maximum on each fiber.  The resulting value
function is concave on the feasible demand set.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- Welfare before subtracting the minting cost. -/
noncomputable def FullInstance.innerWelfare (fill : J → ℝ) : ℝ :=
  (∑ k : K, psiB (inst.budget k) (inst.mmUtil fill k)) +
  inst.retailWelfare fill

/-- Net demands obtainable from feasible fills. -/
def FullInstance.feasibleDemands : Set (ι → ℝ) :=
  inst.netDemand '' (boxFeasible : Set (J → ℝ))

/-- Feasible fills producing exactly demand `D`. -/
def FullInstance.demandFiber (D : ι → ℝ) : Set (J → ℝ) :=
  (boxFeasible : Set (J → ℝ)) ∩ inst.netDemand ⁻¹' {D}

/-- Maximum inner welfare at fixed demand.  It is used only on `feasibleDemands`,
    where compactness proves that the supremum is attained. -/
noncomputable def FullInstance.demandValue (D : ι → ℝ) : ℝ :=
  sSup (inst.innerWelfare '' inst.demandFiber D)

/-- Clearing after projection to net-demand space. -/
noncomputable def FullInstance.demandObjective (b : ℝ) (D : ι → ℝ) : ℝ :=
  inst.demandValue D - logSumExp b D

omit [Fintype ι] in theorem FullInstance.continuous_innerWelfare :
    Continuous inst.innerWelfare := by
  unfold FullInstance.innerWelfare
  exact inst.continuous_mmWelfare.add inst.continuous_retailWelfare

omit [Fintype ι] in theorem FullInstance.concaveOn_innerWelfare :
    ConcaveOn ℝ boxFeasible inst.innerWelfare := by
  constructor
  · exact convex_boxFeasible
  · intro f hf g hg a c ha hc hac
    have hMM := inst.concaveOn_mmWelfare.2 hf hg ha hc hac
    have hRetail := inst.concaveOn_retailWelfare.2 hf hg ha hc hac
    simp only [FullInstance.innerWelfare, smul_eq_mul] at *
    linarith

omit [Fintype ι] [Fintype K] [DecidableEq K] in theorem FullInstance.convex_feasibleDemands :
    Convex ℝ inst.feasibleDemands := by
  intro D₁ hD₁ D₂ hD₂ a c ha hc hac
  rcases hD₁ with ⟨f, hf, rfl⟩
  rcases hD₂ with ⟨g, hg, rfl⟩
  refine ⟨a • f + c • g, convex_boxFeasible hf hg ha hc hac, ?_⟩
  ext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact inst.netDemand_linear s f g a c

omit [Fintype ι] [Fintype K] [DecidableEq K] in
theorem FullInstance.isCompact_demandFiber (D : ι → ℝ) :
    IsCompact (inst.demandFiber D) := by
  unfold FullInstance.demandFiber
  exact isCompact_boxFeasible.inter_right
    (isClosed_singleton.preimage inst.continuous_netDemand)

omit [Fintype ι] [Fintype K] [DecidableEq K] in
theorem FullInstance.demandFiber_nonempty {D : ι → ℝ} (hD : D ∈ inst.feasibleDemands) :
    (inst.demandFiber D).Nonempty := by
  rcases hD with ⟨fill, hfill, hDemand⟩
  refine ⟨fill, hfill, ?_⟩
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hDemand

omit [Fintype ι] in
/-- Every feasible demand has a fill attaining `demandValue`. -/
theorem FullInstance.exists_demandValue_eq {D : ι → ℝ} (hD : D ∈ inst.feasibleDemands) :
    ∃ fill ∈ inst.demandFiber D,
      inst.demandValue D = inst.innerWelfare fill ∧
      ∀ other ∈ inst.demandFiber D,
        inst.innerWelfare other ≤ inst.innerWelfare fill := by
  simpa only [FullInstance.demandValue] using
    (inst.isCompact_demandFiber D).exists_sSup_image_eq_and_ge
      (inst.demandFiber_nonempty hD)
      inst.continuous_innerWelfare.continuousOn

omit [Fintype ι] [Fintype K] [DecidableEq K] in theorem FullInstance.netDemand_mem_feasibleDemands
    (fill : J → ℝ) (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    inst.netDemand fill ∈ inst.feasibleDemands :=
  ⟨fill, hfill, rfl⟩

omit [Fintype ι] [Fintype K] [DecidableEq K] in theorem FullInstance.mem_demandFiber_netDemand
    (fill : J → ℝ) (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    fill ∈ inst.demandFiber (inst.netDemand fill) :=
  ⟨hfill, by simp⟩

omit [Fintype ι] in
/-- `demandValue` really is an upper bound for every fill on its fiber. -/
theorem FullInstance.innerWelfare_le_demandValue
    (fill : J → ℝ) (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    inst.innerWelfare fill ≤ inst.demandValue (inst.netDemand fill) := by
  have hD := inst.netDemand_mem_feasibleDemands fill hfill
  rcases inst.exists_demandValue_eq hD with ⟨best, _hbestFiber, hvalue, hbest⟩
  calc
    inst.innerWelfare fill ≤ inst.innerWelfare best :=
      hbest fill (inst.mem_demandFiber_netDemand fill hfill)
    _ = inst.demandValue (inst.netDemand fill) := hvalue.symm

theorem FullInstance.objective_eq_innerWelfare_sub_cost (b : ℝ) (fill : J → ℝ) :
    inst.objective b fill =
      inst.innerWelfare fill - logSumExp b (inst.netDemand fill) := by
  unfold FullInstance.objective FullInstance.innerWelfare
  ring

/-- A globally optimal fill must maximize inner welfare among all fills
    producing the same net demand. -/
theorem FullInstance.demandValue_eq_innerWelfare_of_optimal (b : ℝ) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.objective b) boxFeasible fill) :
    inst.demandValue (inst.netDemand fill) = inst.innerWelfare fill := by
  have hD := inst.netDemand_mem_feasibleDemands fill hfill
  rcases inst.exists_demandValue_eq hD with
    ⟨best, hbestFiber, hvalue, _hbest⟩
  have h := hopt hbestFiber.1
  change inst.objective b best ≤ inst.objective b fill at h
  rw [inst.objective_eq_innerWelfare_sub_cost,
      inst.objective_eq_innerWelfare_sub_cost] at h
  have hbestDemand : inst.netDemand best = inst.netDemand fill := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hbestFiber.2
  rw [hbestDemand] at h
  linarith [inst.innerWelfare_le_demandValue fill hfill]

/-- Projection of a fill-space optimum is a demand-space optimum. -/
theorem FullInstance.demandOptimal_of_fillOptimal (b : ℝ) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.objective b) boxFeasible fill) :
    IsMaxOn (inst.demandObjective b) inst.feasibleDemands
      (inst.netDemand fill) := by
  intro D hD
  change inst.demandObjective b D ≤
    inst.demandObjective b (inst.netDemand fill)
  rcases inst.exists_demandValue_eq hD with
    ⟨best, hbestFiber, hvalue, _hbest⟩
  have h := hopt hbestFiber.1
  change inst.objective b best ≤ inst.objective b fill at h
  rw [inst.objective_eq_innerWelfare_sub_cost,
      inst.objective_eq_innerWelfare_sub_cost] at h
  have hbestDemand : inst.netDemand best = D := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hbestFiber.2
  rw [hbestDemand, ← hvalue,
      ← inst.demandValue_eq_innerWelfare_of_optimal b fill hfill hopt] at h
  unfold FullInstance.demandObjective
  exact h

/-- A demand-space optimum, lifted by a fiber maximizer, is a fill-space optimum. -/
theorem FullInstance.fillOptimal_of_demandOptimal (b : ℝ) (fill : J → ℝ)
    (_hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hfiber : inst.demandValue (inst.netDemand fill) =
      inst.innerWelfare fill)
    (hopt : IsMaxOn (inst.demandObjective b) inst.feasibleDemands
      (inst.netDemand fill)) :
    IsMaxOn (inst.objective b) boxFeasible fill := by
  intro other hother
  change inst.objective b other ≤ inst.objective b fill
  have hdemand := hopt (inst.netDemand_mem_feasibleDemands other hother)
  change
    inst.demandValue (inst.netDemand other) -
        logSumExp b (inst.netDemand other) ≤
      inst.demandValue (inst.netDemand fill) -
        logSumExp b (inst.netDemand fill) at hdemand
  rw [hfiber] at hdemand
  rw [inst.objective_eq_innerWelfare_sub_cost,
      inst.objective_eq_innerWelfare_sub_cost]
  exact (sub_le_sub_right
    (inst.innerWelfare_le_demandValue other hother)
    (logSumExp b (inst.netDemand other))).trans hdemand

/-- Exact optimizer correspondence between fill space and demand space. -/
theorem FullInstance.fillOptimal_iff_fiber_and_demandOptimal (b : ℝ) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    IsMaxOn (inst.objective b) boxFeasible fill ↔
      inst.demandValue (inst.netDemand fill) = inst.innerWelfare fill ∧
      IsMaxOn (inst.demandObjective b) inst.feasibleDemands
        (inst.netDemand fill) := by
  constructor
  · intro hopt
    exact ⟨inst.demandValue_eq_innerWelfare_of_optimal b fill hfill hopt,
      inst.demandOptimal_of_fillOptimal b fill hfill hopt⟩
  · rintro ⟨hfiber, hdemand⟩
    exact inst.fillOptimal_of_demandOptimal b fill hfill hfiber hdemand

omit [Fintype ι] in
/-- The paper's inner demand-space value function is concave. -/
theorem FullInstance.concaveOn_demandValue :
    ConcaveOn ℝ inst.feasibleDemands inst.demandValue := by
  constructor
  · exact inst.convex_feasibleDemands
  · intro D₁ hD₁ D₂ hD₂ a c ha hc hac
    rcases inst.exists_demandValue_eq hD₁ with
      ⟨f, hfFiber, hfValue, _⟩
    rcases inst.exists_demandValue_eq hD₂ with
      ⟨g, hgFiber, hgValue, _⟩
    have hDmix :
        a • D₁ + c • D₂ ∈ inst.feasibleDemands :=
      inst.convex_feasibleDemands hD₁ hD₂ ha hc hac
    rcases inst.exists_demandValue_eq hDmix with
      ⟨best, hbestFiber, hbestValue, hbest⟩
    have hmixBox :
        a • f + c • g ∈ (boxFeasible : Set (J → ℝ)) :=
      convex_boxFeasible hfFiber.1 hgFiber.1 ha hc hac
    have hmixDemand :
        inst.netDemand (a • f + c • g) = a • D₁ + c • D₂ := by
      ext s
      have hfD : inst.netDemand f = D₁ := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hfFiber.2
      have hgD : inst.netDemand g = D₂ := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hgFiber.2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        inst.netDemand (a • f + c • g) s =
            a * inst.netDemand f s + c * inst.netDemand g s :=
          inst.netDemand_linear s f g a c
        _ = a * D₁ s + c * D₂ s := by rw [hfD, hgD]
    have hmixFiber :
        a • f + c • g ∈ inst.demandFiber (a • D₁ + c • D₂) :=
      ⟨hmixBox, by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hmixDemand⟩
    have hinner :=
      inst.concaveOn_innerWelfare.2 hfFiber.1 hgFiber.1 ha hc hac
    have hupper := hbest (a • f + c • g) hmixFiber
    simp only [smul_eq_mul] at hinner ⊢
    rw [hfValue, hgValue, hbestValue]
    exact hinner.trans hupper

end FisherClearing
