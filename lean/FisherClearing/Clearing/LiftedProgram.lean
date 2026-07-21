/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.FullProgram

/-!
# Deployed-Value Lift of the Full Clearing Program

This file lifts every reduced-form term `ψ_B(U)` to
`B log V - V + U` under `V ≥ U`.  It proves both directions of the
optimization equivalence, not only the scalar identity.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- A lifted point consists of fill fractions and one positive deployed value per MM. -/
def FullInstance.liftedFeasible : Set ((J → ℝ) × (K → ℝ)) :=
  {z | z.1 ∈ (boxFeasible : Set (J → ℝ)) ∧
    ∀ k, 0 < z.2 k ∧ inst.mmUtil z.1 k ≤ z.2 k}

/-- The canonical lift uses the pointwise optimizer `V_k = max(U_k, B_k)`. -/
noncomputable def FullInstance.deployedLift (fill : J → ℝ) : (J → ℝ) × (K → ℝ) :=
  (fill, fun k => deployedValue (inst.budget k) (inst.mmUtil fill k))

/-- Positive-temperature objective in deployed-value variables. -/
noncomputable def FullInstance.liftedObjective (b : ℝ) (z : (J → ℝ) × (K → ℝ)) : ℝ :=
  (∑ k : K, liftedMM (inst.budget k) (z.2 k) (inst.mmUtil z.1 k)) -
  logSumExp b (inst.netDemand z.1) +
  inst.retailWelfare z.1

omit [Fintype ι] [Nonempty ι] [Fintype K] in theorem FullInstance.deployedLift_mem (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    inst.deployedLift fill ∈ inst.liftedFeasible := by
  refine ⟨hfill, fun k => ⟨deployedValue_pos (inst.budget_pos k), ?_⟩⟩
  exact deployedValue_ge_U

omit [Nonempty ι] in theorem FullInstance.liftedObjective_deployedLift (b : ℝ) (fill : J → ℝ) :
    inst.liftedObjective b (inst.deployedLift fill) = inst.objective b fill := by
  unfold FullInstance.liftedObjective FullInstance.deployedLift FullInstance.objective
  simp only
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  exact liftedMM_eq_psiB

omit [Nonempty ι] in theorem FullInstance.liftedObjective_le_reduced (b : ℝ)
    (z : (J → ℝ) × (K → ℝ)) (hz : z ∈ inst.liftedFeasible) :
    inst.liftedObjective b z ≤ inst.objective b z.1 := by
  have hMM :
      ∑ k : K, liftedMM (inst.budget k) (z.2 k) (inst.mmUtil z.1 k) ≤
        ∑ k : K, psiB (inst.budget k) (inst.mmUtil z.1 k) := by
    apply Finset.sum_le_sum
    intro k _
    exact liftedMM_le_psiB (inst.budget_pos k) (hz.2 k).1 (hz.2 k).2
  unfold FullInstance.liftedObjective FullInstance.objective
  linarith

omit [Nonempty ι] in
/-- A reduced-form optimizer canonically lifts to a lifted-program optimizer. -/
theorem FullInstance.IsOptimal.deployedLift
    {b : ℝ} {fill : J → ℝ}
    (hopt : IsMaxOn (inst.objective b) boxFeasible fill) :
    IsMaxOn (inst.liftedObjective b) inst.liftedFeasible (inst.deployedLift fill) := by
  intro z hz
  calc
    inst.liftedObjective b z ≤ inst.objective b z.1 :=
      inst.liftedObjective_le_reduced b z hz
    _ ≤ inst.objective b fill := hopt hz.1
    _ = inst.liftedObjective b (inst.deployedLift fill) :=
      (inst.liftedObjective_deployedLift b fill).symm

omit [Nonempty ι] in
/-- Optimality of the canonical deployed lift implies reduced-form optimality. -/
theorem FullInstance.IsLiftedOptimal.reduced
    {b : ℝ} {fill : J → ℝ}
    (hopt : IsMaxOn (inst.liftedObjective b) inst.liftedFeasible
      (inst.deployedLift fill)) :
    IsMaxOn (inst.objective b) boxFeasible fill := by
  intro fill' hfill'
  calc
    inst.objective b fill' =
        inst.liftedObjective b (inst.deployedLift fill') :=
      (inst.liftedObjective_deployedLift b fill').symm
    _ ≤ inst.liftedObjective b (inst.deployedLift fill) :=
      hopt (inst.deployedLift_mem fill' hfill')
    _ = inst.objective b fill :=
      inst.liftedObjective_deployedLift b fill

omit [Nonempty ι] in theorem FullInstance.isOptimal_iff_isLiftedOptimal
    {b : ℝ} {fill : J → ℝ} :
    IsMaxOn (inst.objective b) boxFeasible fill ↔
      IsMaxOn (inst.liftedObjective b) inst.liftedFeasible
        (inst.deployedLift fill) :=
  ⟨fun h => FullInstance.IsOptimal.deployedLift inst h,
    fun h => FullInstance.IsLiftedOptimal.reduced inst h⟩

end FisherClearing
