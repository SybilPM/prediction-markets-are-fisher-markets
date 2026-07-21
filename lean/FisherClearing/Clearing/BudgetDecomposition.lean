/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.ReducedForm.Utility
import FisherClearing.Clearing.DeployedValue

/-!
# Exact Budget Decomposition

This file isolates the separable mathematical core of the paper's component
decomposition theorem.  A component has a convex feasible set, linear
per-market-maker weighted fills, and a concave residual objective.  At a point
where the reduced-form utilities have common scarcity slopes, nonlinear
optimality is equivalent to optimality of the ordinary matching objective with
all of one market maker's values shaded by that common slope.  This proves both
directions of exact decomposition.
-/

namespace FisherClearing

open scoped BigOperators

variable {M K X : Type*}
variable [Fintype M] [Fintype K]
variable [AddCommGroup X] [Module ℝ X]

/-- Abstract data of a clearing program that separates by components. -/
structure SeparableProgram (M K X : Type*) [Fintype M] [Fintype K]
    [AddCommGroup X] [Module ℝ X] where
  feasible : M → Set X
  utility : K → M → X →ₗ[ℝ] ℝ
  residual : M → X → ℝ
  residual_concave : ∀ m, ConcaveOn ℝ (feasible m) (residual m)
  utility_nonneg : ∀ k m x, x ∈ feasible m → 0 ≤ utility k m x

variable (program : SeparableProgram M K X)

/-- Objective of one component under its allocated MM budgets. -/
noncomputable def SeparableProgram.componentObjective (budget : K → ℝ) (m : M) (x : X) : ℝ :=
  (∑ k : K, psiB (budget k) (program.utility k m x)) +
    program.residual m x

/-- Matching objective obtained by shading each MM's linear value by a
    scarcity factor. -/
noncomputable def SeparableProgram.shadedObjective (scarcity : K → ℝ) (m : M) (x : X) : ℝ :=
  (∑ k : K, scarcity k * program.utility k m x) +
    program.residual m x

/-- A component objective with fixed utility supplied by all other
    components. -/
noncomputable def SeparableProgram.offsetObjective
    (budget offset : K → ℝ) (m : M) (x : X) : ℝ :=
  (∑ k : K,
    psiB (budget k) (offset k + program.utility k m x)) +
    program.residual m x

/-- Feasibility of an assembled component allocation. -/
def SeparableProgram.assemblyFeasible : Set (M → X) :=
  {x | ∀ m, x m ∈ program.feasible m}

/-- Total weighted fill of one MM across all components. -/
noncomputable def SeparableProgram.totalUtility (x : M → X) (k : K) : ℝ :=
  ∑ m : M, program.utility k m (x m)

/-- The monolithic separable clearing objective. -/
noncomputable def SeparableProgram.monolithicObjective (budget : K → ℝ) (x : M → X) : ℝ :=
  (∑ k : K, psiB (budget k) (program.totalUtility x k)) +
    ∑ m : M, program.residual m (x m)

theorem SeparableProgram.totalUtility_nonneg
    (x : M → X) (hx : x ∈ program.assemblyFeasible) (k : K) :
    0 ≤ program.totalUtility x k := by
  unfold SeparableProgram.totalUtility
  exact Finset.sum_nonneg fun m _ =>
    program.utility_nonneg k m (x m) (hx m)

theorem SeparableProgram.hasDerivAt_utility_line (k : K) (m : M) (x y : X) :
    HasDerivAt
      (fun t : ℝ =>
        program.utility k m (AffineMap.lineMap x y t))
      (program.utility k m y - program.utility k m x) 0 := by
  convert (((hasDerivAt_id (0 : ℝ)).mul_const
    (program.utility k m y - program.utility k m x)).add_const
      (program.utility k m x)) using 1 <;> try rfl
  · funext t
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
    simp only [smul_eq_mul, id_eq]
    ring
  · ring

/-- At a point with the displayed scarcity slopes, nonlinear component
    optimality is equivalent to optimality of the scarcity-shaded matching
    objective.  The `offset` allows the same lemma to be used for one
    component inside a monolithic program. -/
theorem SeparableProgram.isMaxOn_offsetObjective_iff_shaded
    (budget offset scarcity : K → ℝ) (m : M) (x : X) (hx : x ∈ program.feasible m)
    (hbudget : ∀ k, 0 < budget k) (hoffset_nonneg :
      ∀ k y, y ∈ program.feasible m →
        0 ≤ offset k + program.utility k m y)
    (hslope : ∀ k,
      psiSlope (budget k) (offset k + program.utility k m x) =
        scarcity k) :
    IsMaxOn (program.offsetObjective budget offset m)
        (program.feasible m) x ↔
      IsMaxOn (program.shadedObjective scarcity m)
        (program.feasible m) x := by
  constructor
  · intro hopt y hy
    change program.shadedObjective scarcity m y ≤
      program.shadedObjective scarcity m x
    let line : ℝ → X := AffineMap.lineMap x y
    let chordResidual : ℝ → ℝ := fun t =>
      (1 - t) * program.residual m x +
        t * program.residual m y
    let psiPath : ℝ → ℝ :=
      ∑ k : K, fun t =>
        psiB (budget k)
          (offset k + program.utility k m (line t))
    let lowerPath : ℝ → ℝ := psiPath + chordResidual
    have hlineMem :
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          line t ∈ program.feasible m := by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      change AffineMap.lineMap x y t ∈ program.feasible m
      rw [AffineMap.lineMap_apply_module]
      exact (program.residual_concave m).1 hx hy
        (by linarith) ht0 (by linarith)
    have hlowerMax :
        IsMaxOn lowerPath (Set.Icc (0 : ℝ) 1) 0 := by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hnonlinear := hopt (hlineMem t ht)
      change program.offsetObjective budget offset m (line t) ≤
        program.offsetObjective budget offset m x at hnonlinear
      have hresidual :=
        (program.residual_concave m).2 hx hy
          (by linarith : 0 ≤ (1 : ℝ) - t) ht0
          (by linarith : (1 : ℝ) - t + t = 1)
      simp only [smul_eq_mul] at hresidual
      have hlineEq :
          line t = (1 - t) • x + t • y := by
        simp only [line, AffineMap.lineMap_apply_module]
      rw [← hlineEq] at hresidual
      change lowerPath t ≤ lowerPath 0
      simp only [lowerPath, psiPath, chordResidual, line,
        Pi.add_apply, Finset.sum_apply,
          AffineMap.lineMap_apply_zero, one_mul, zero_mul, sub_zero]
      unfold SeparableProgram.offsetObjective at hnonlinear
      linarith
    have hpsi :
        HasDerivAt
          psiPath
          (∑ k : K,
            psiSlope (budget k)
                (offset k + program.utility k m x) *
              (program.utility k m y -
                program.utility k m x)) 0 := by
      let A : K → ℝ → ℝ := fun k t =>
        psiB (budget k)
          (offset k + program.utility k m (line t))
      let A' : K → ℝ := fun k =>
        psiSlope (budget k)
            (offset k + program.utility k m x) *
          (program.utility k m y -
            program.utility k m x)
      have hA : ∀ k ∈ Finset.univ,
          HasDerivAt (A k) (A' k) 0 := by
        intro k _
        have hinner :
            HasDerivAt
              (fun t : ℝ =>
                offset k + program.utility k m (line t))
              (program.utility k m y -
                program.utility k m x) 0 := by
          simpa only [line] using
            (program.hasDerivAt_utility_line k m x y).const_add
              (offset k)
        have houter :=
          hasDerivAt_psiB_nonneg (hbudget k)
            (hoffset_nonneg k x hx)
        have houter' :
            HasDerivAt (psiB (budget k))
              (psiSlope (budget k)
                (offset k + program.utility k m x))
              (offset k + program.utility k m (line 0)) := by
          simpa only [line, AffineMap.lineMap_apply_zero] using houter
        exact houter'.comp 0 hinner
      simpa only [psiPath, A, A'] using
        HasDerivAt.sum hA
    have hchord :
        HasDerivAt chordResidual
          (program.residual m y - program.residual m x) 0 := by
      have hfun :
          chordResidual =
            fun t : ℝ =>
              t * (program.residual m y - program.residual m x) +
                program.residual m x := by
        funext t
        simp only [chordResidual]
        ring
      rw [hfun]
      simpa using
        (((hasDerivAt_id (0 : ℝ)).mul_const
          (program.residual m y -
            program.residual m x)).add_const
              (program.residual m x))
    have hlowerDeriv :
        HasDerivAt lowerPath
          ((∑ k : K,
            psiSlope (budget k)
                (offset k + program.utility k m x) *
              (program.utility k m y -
                program.utility k m x)) +
            (program.residual m y -
              program.residual m x)) 0 := by
      exact hpsi.add hchord
    have hdirection :
        (∑ k : K,
          scarcity k *
            (program.utility k m y -
              program.utility k m x)) +
          (program.residual m y -
            program.residual m x) ≤ 0 := by
      simpa only [hslope] using
        HasDerivAt.nonpos_of_isMaxOn_Icc hlowerDeriv hlowerMax
    have hsumdiff :
        (∑ k : K, scarcity k *
          (program.utility k m y -
            program.utility k m x)) =
        (∑ k : K, scarcity k * program.utility k m y) -
          ∑ k : K, scarcity k * program.utility k m x := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
    rw [hsumdiff] at hdirection
    unfold SeparableProgram.shadedObjective
    linarith
  · intro hlinear y hy
    change program.offsetObjective budget offset m y ≤
      program.offsetObjective budget offset m x
    have hlinear' := hlinear hy
    change program.shadedObjective scarcity m y ≤
      program.shadedObjective scarcity m x at hlinear'
    have hpsi :
        (∑ k : K, psiB (budget k)
          (offset k + program.utility k m y)) ≤
        (∑ k : K, psiB (budget k)
          (offset k + program.utility k m x)) +
          ∑ k : K, scarcity k *
            (program.utility k m y -
              program.utility k m x) := by
      have htangent := sum_psiB_le_tangent
        budget
        (fun k => offset k + program.utility k m x)
        (fun k => offset k + program.utility k m y)
        hbudget
        (fun k => hoffset_nonneg k x hx)
        (fun k => hoffset_nonneg k y hy)
      simpa only [hslope, add_sub_add_left_eq_sub] using htangent
    unfold SeparableProgram.shadedObjective at hlinear'
    unfold SeparableProgram.offsetObjective
    have hsumdiff :
        (∑ k : K, scarcity k *
          (program.utility k m y -
            program.utility k m x)) =
        (∑ k : K, scarcity k * program.utility k m y) -
          ∑ k : K, scarcity k * program.utility k m x := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
    rw [hsumdiff] at hpsi
    linarith

/-- The zero-offset specialization used by independent component programs. -/
theorem SeparableProgram.isMaxOn_componentObjective_iff_shaded
    (budget scarcity : K → ℝ) (m : M) (x : X) (hx : x ∈ program.feasible m)
    (hbudget : ∀ k, 0 < budget k) (hslope : ∀ k,
      psiSlope (budget k) (program.utility k m x) = scarcity k) :
    IsMaxOn (program.componentObjective budget m)
        (program.feasible m) x ↔
      IsMaxOn (program.shadedObjective scarcity m)
        (program.feasible m) x := by
  have heq :
      program.componentObjective budget m =
        program.offsetObjective budget 0 m := by
    funext y
    simp [SeparableProgram.componentObjective,
      SeparableProgram.offsetObjective]
  rw [heq]
  exact program.isMaxOn_offsetObjective_iff_shaded
      budget 0 scarcity m x hx hbudget
      (fun k y hy => by
        simpa using program.utility_nonneg k m y hy)
      (fun k => by simpa using hslope k)

/-! ### Assembly and exact decomposition -/

/-- Replace one component of an assembled allocation. -/
noncomputable def replaceComponent (x : M → X) (m : M) (y : X) (n : M) : X := by
  classical
  exact if n = m then y else x n

/-- Utility supplied by all components except `m`. -/
noncomputable def SeparableProgram.otherUtility (x : M → X) (m : M) (k : K) : ℝ := by
  classical
  exact ∑ n ∈ Finset.univ.erase m, program.utility k n (x n)

/-- Residual objective supplied by all components except `m`. -/
noncomputable def SeparableProgram.otherResidual (x : M → X) (m : M) : ℝ := by
  classical
  exact ∑ n ∈ Finset.univ.erase m, program.residual n (x n)

theorem SeparableProgram.replaceComponent_mem (x : M → X) (hx : x ∈ program.assemblyFeasible)
    (m : M) (y : X) (hy : y ∈ program.feasible m) :
    replaceComponent x m y ∈ program.assemblyFeasible := by
  classical
  intro n
  by_cases hnm : n = m
  · subst n
    simpa [replaceComponent] using hy
  · simpa [replaceComponent, hnm] using hx n

theorem SeparableProgram.totalUtility_replaceComponent (x : M → X) (m : M) (y : X) (k : K) :
    program.totalUtility (replaceComponent x m y) k =
      program.otherUtility x m k + program.utility k m y := by
  classical
  unfold SeparableProgram.totalUtility SeparableProgram.otherUtility
    replaceComponent
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ m)]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro n hn
    have hnm : n ≠ m := (Finset.mem_erase.mp hn).1
    simp [hnm]
  · simp

theorem SeparableProgram.totalUtility_eq_other_add (x : M → X) (m : M) (k : K) :
    program.totalUtility x k =
      program.otherUtility x m k + program.utility k m (x m) := by
  classical
  unfold SeparableProgram.totalUtility SeparableProgram.otherUtility
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ m)).symm

theorem SeparableProgram.sum_residual_replaceComponent (x : M → X) (m : M) (y : X) : (∑ n : M,
      program.residual n (replaceComponent x m y n)) =
      program.otherResidual x m + program.residual m y := by
  classical
  unfold SeparableProgram.otherResidual
    replaceComponent
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ m)]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro n hn
    have hnm : n ≠ m := (Finset.mem_erase.mp hn).1
    simp [hnm]
  · simp

theorem SeparableProgram.sum_residual_eq_other_add (x : M → X) (m : M) :
    (∑ n : M, program.residual n (x n)) =
      program.otherResidual x m + program.residual m (x m) := by
  classical
  unfold SeparableProgram.otherResidual
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ m)).symm

theorem SeparableProgram.monolithic_replaceComponent
    (budget : K → ℝ) (x : M → X) (m : M) (y : X) :
    program.monolithicObjective budget
        (replaceComponent x m y) =
      program.offsetObjective budget (program.otherUtility x m) m y +
        program.otherResidual x m := by
  unfold SeparableProgram.monolithicObjective
    SeparableProgram.offsetObjective
  simp_rw [program.totalUtility_replaceComponent x m y]
  rw [program.sum_residual_replaceComponent x m y]
  ring

theorem SeparableProgram.monolithic_eq_offset (budget : K → ℝ) (x : M → X) (m : M) :
    program.monolithicObjective budget x =
      program.offsetObjective budget (program.otherUtility x m) m (x m) +
        program.otherResidual x m := by
  unfold SeparableProgram.monolithicObjective
    SeparableProgram.offsetObjective
  simp_rw [program.totalUtility_eq_other_add x m]
  rw [program.sum_residual_eq_other_add x m]
  ring

theorem SeparableProgram.sum_shadedObjective (scarcity : K → ℝ) (x : M → X) :
    (∑ m : M, program.shadedObjective scarcity m (x m)) =
      (∑ k : K, scarcity k * program.totalUtility x k) +
        ∑ m : M, program.residual m (x m) := by
  unfold SeparableProgram.shadedObjective
    SeparableProgram.totalUtility
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  apply congrArg₂ (· + ·) ?_ rfl
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]

/-- If positive component budgets add to the monolithic budget and every
    component has the same scarcity slope, then the monolithic utility has
    that slope as well.  This discharges a formerly separate hypothesis in
    exact budget decomposition. -/
theorem SeparableProgram.monolithicSlope_of_componentSlopes
    [Nonempty M]
    (budget : K → ℝ) (componentBudget : M → K → ℝ) (scarcity : K → ℝ) (x : M → X)
    (hx : x ∈ program.assemblyFeasible) (hbudget : ∀ k, 0 < budget k)
    (hcomponentBudget : ∀ m k, 0 < componentBudget m k)
    (hbudgetSum : ∀ k, ∑ m : M, componentBudget m k = budget k)
    (hcomponentSlope : ∀ m k,
      psiSlope (componentBudget m k)
        (program.utility k m (x m)) = scarcity k) :
    ∀ k,
      psiSlope (budget k) (program.totalUtility x k) = scarcity k := by
  intro k
  by_cases hone : scarcity k = 1
  · rw [hone, psiSlope_eq_capitalScarcity (hbudget k),
      capitalScarcity_eq_one_iff (hbudget k)]
    rw [← hbudgetSum k]
    unfold SeparableProgram.totalUtility
    apply Finset.sum_le_sum
    intro m _
    have hslope := hcomponentSlope m k
    rw [psiSlope_eq_capitalScarcity (hcomponentBudget m k)] at hslope
    exact (capitalScarcity_eq_one_iff (hcomponentBudget m k)).mp
      (hslope.trans hone)
  · have hbudgetUtility :
        ∀ m, componentBudget m k =
          scarcity k * program.utility k m (x m) := by
      intro m
      have hslope := hcomponentSlope m k
      by_cases hlt :
          program.utility k m (x m) < componentBudget m k
      · simp only [psiSlope, if_pos hlt] at hslope
        exact absurd hslope.symm hone
      · have hutilityPos :
            0 < program.utility k m (x m) :=
          lt_of_lt_of_le (hcomponentBudget m k) (le_of_not_gt hlt)
        simp only [psiSlope, if_neg hlt] at hslope
        calc
          componentBudget m k =
              (componentBudget m k / program.utility k m (x m)) *
                program.utility k m (x m) := by
                  rw [div_mul_cancel₀ _ (ne_of_gt hutilityPos)]
          _ = scarcity k * program.utility k m (x m) := by rw [hslope]
    have hbudgetAsProduct :
        budget k = scarcity k * program.totalUtility x k := by
      rw [← hbudgetSum k]
      unfold SeparableProgram.totalUtility
      calc
        (∑ m : M, componentBudget m k) =
            ∑ m : M, scarcity k * program.utility k m (x m) :=
          Finset.sum_congr rfl fun m _ => hbudgetUtility m
        _ = scarcity k * ∑ m : M, program.utility k m (x m) := by
          rw [Finset.mul_sum]
    have htotalPos : 0 < program.totalUtility x k := by
      obtain ⟨m⟩ := ‹Nonempty M›
      unfold SeparableProgram.totalUtility
      exact lt_of_lt_of_le
        (lt_of_lt_of_le (hcomponentBudget m k)
          (le_of_not_gt (fun hlt =>
            hone (by
              have hslope := hcomponentSlope m k
              simpa [psiSlope, hlt] using hslope.symm))))
        (Finset.single_le_sum
          (fun n _ => program.utility_nonneg k n (x n) (hx n))
          (Finset.mem_univ m))
    have hbudgetLe : budget k ≤ program.totalUtility x k := by
      rw [← hbudgetSum k]
      unfold SeparableProgram.totalUtility
      exact Finset.sum_le_sum fun m _ =>
        le_of_not_gt (fun hlt =>
          hone (by
            have hslope := hcomponentSlope m k
            simpa [psiSlope, hlt] using hslope.symm))
    rw [psiSlope, if_neg (not_lt.mpr hbudgetLe), hbudgetAsProduct]
    exact mul_div_cancel_right₀ (scarcity k) (ne_of_gt htotalPos)

/-- **Exact budget decomposition.**  If the monolithic and component budgets
    induce the same scarcity factor for every MM at an assembled feasible
    point, then monolithic optimality is equivalent to independent component
    optimality. -/
theorem SeparableProgram.exactBudgetDecomposition
    (budget : K → ℝ) (componentBudget : M → K → ℝ) (scarcity : K → ℝ) (x : M → X)
    (hx : x ∈ program.assemblyFeasible) (hbudget : ∀ k, 0 < budget k)
    (hcomponentBudget : ∀ m k, 0 < componentBudget m k) (hmonolithicSlope : ∀ k,
      psiSlope (budget k) (program.totalUtility x k) = scarcity k)
    (hcomponentSlope : ∀ m k,
      psiSlope (componentBudget m k)
        (program.utility k m (x m)) = scarcity k) :
    IsMaxOn (program.monolithicObjective budget)
        program.assemblyFeasible x ↔
      ∀ m, IsMaxOn
        (program.componentObjective (componentBudget m) m)
        (program.feasible m) (x m) := by
  classical
  constructor
  · intro hmonolithic m
    have hoffsetNonneg :
        ∀ k y, y ∈ program.feasible m →
          0 ≤ program.otherUtility x m k +
            program.utility k m y := by
      intro k y hy
      unfold SeparableProgram.otherUtility
      exact add_nonneg
        (Finset.sum_nonneg fun n hn =>
          program.utility_nonneg k n (x n)
            (hx n))
        (program.utility_nonneg k m y hy)
    have hoffsetSlope :
        ∀ k,
          psiSlope (budget k)
              (program.otherUtility x m k +
                program.utility k m (x m)) =
            scarcity k := by
      intro k
      rw [← program.totalUtility_eq_other_add x m k]
      exact hmonolithicSlope k
    have hoffsetOptimal :
        IsMaxOn
          (program.offsetObjective budget
            (program.otherUtility x m) m)
          (program.feasible m) (x m) := by
      intro y hy
      change program.offsetObjective budget
          (program.otherUtility x m) m y ≤
        program.offsetObjective budget
          (program.otherUtility x m) m (x m)
      have h := hmonolithic
        (program.replaceComponent_mem x hx m y hy)
      change program.monolithicObjective budget
          (replaceComponent x m y) ≤
        program.monolithicObjective budget x at h
      rw [program.monolithic_replaceComponent budget x m y,
        program.monolithic_eq_offset budget x m] at h
      linarith
    have hshaded :
        IsMaxOn (program.shadedObjective scarcity m)
          (program.feasible m) (x m) :=
      (program.isMaxOn_offsetObjective_iff_shaded
        budget (program.otherUtility x m) scarcity m (x m)
        (hx m) hbudget hoffsetNonneg hoffsetSlope).1
        hoffsetOptimal
    exact
      (program.isMaxOn_componentObjective_iff_shaded
        (componentBudget m) scarcity m (x m) (hx m)
        (hcomponentBudget m) (hcomponentSlope m)).2 hshaded
  · intro hcomponents y hy
    change program.monolithicObjective budget y ≤
      program.monolithicObjective budget x
    have hshaded :
        ∀ m, IsMaxOn (program.shadedObjective scarcity m)
          (program.feasible m) (x m) := by
      intro m
      exact
        (program.isMaxOn_componentObjective_iff_shaded
          (componentBudget m) scarcity m (x m) (hx m)
          (hcomponentBudget m) (hcomponentSlope m)).1
          (hcomponents m)
    have hshadedSum :
        (∑ m : M, program.shadedObjective scarcity m (y m)) ≤
          ∑ m : M, program.shadedObjective scarcity m (x m) :=
      Finset.sum_le_sum fun m _ => hshaded m (hy m)
    rw [program.sum_shadedObjective scarcity y,
      program.sum_shadedObjective scarcity x] at hshadedSum
    have hpsi :
        (∑ k : K, psiB (budget k) (program.totalUtility y k)) ≤
          (∑ k : K, psiB (budget k) (program.totalUtility x k)) +
            ∑ k : K, scarcity k *
              (program.totalUtility y k -
                program.totalUtility x k) := by
      simpa only [hmonolithicSlope] using
        sum_psiB_le_tangent
          budget
          (program.totalUtility x)
          (program.totalUtility y)
          hbudget
          (program.totalUtility_nonneg x hx)
          (program.totalUtility_nonneg y hy)
    have hsumdiff :
        (∑ k : K, scarcity k *
          (program.totalUtility y k -
            program.totalUtility x k)) =
        (∑ k : K, scarcity k * program.totalUtility y k) -
          ∑ k : K, scarcity k * program.totalUtility x k := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
    rw [hsumdiff] at hpsi
    unfold SeparableProgram.monolithicObjective
    linarith

/-- Exact budget decomposition with the monolithic slope derived from the
    component budget sum and common component slopes. -/
theorem SeparableProgram.exactBudgetDecomposition_of_sum
    [Nonempty M]
    (budget : K → ℝ) (componentBudget : M → K → ℝ) (scarcity : K → ℝ) (x : M → X)
    (hx : x ∈ program.assemblyFeasible) (hbudget : ∀ k, 0 < budget k)
    (hcomponentBudget : ∀ m k, 0 < componentBudget m k)
    (hbudgetSum : ∀ k, ∑ m : M, componentBudget m k = budget k)
    (hcomponentSlope : ∀ m k,
      psiSlope (componentBudget m k)
        (program.utility k m (x m)) = scarcity k) :
    IsMaxOn (program.monolithicObjective budget)
        program.assemblyFeasible x ↔
      ∀ m, IsMaxOn
        (program.componentObjective (componentBudget m) m)
        (program.feasible m) (x m) := by
  classical
  apply program.exactBudgetDecomposition
    budget componentBudget scarcity x hx hbudget hcomponentBudget
  · exact program.monolithicSlope_of_componentSlopes
      budget componentBudget scarcity x hx hbudget hcomponentBudget
        hbudgetSum hcomponentSlope
  · exact hcomponentSlope

omit [Fintype K] in
/-- Budget shares proportional to deployed values add back to the monolithic
    budget. -/
theorem proportionalComponentBudgets_sum (budget scarcity : K → ℝ) (deployed : M → K → ℝ)
    (hbudget : ∀ k,
      budget k = scarcity k * ∑ m : M, deployed m k) :
    ∀ k, (∑ m : M, scarcity k * deployed m k) = budget k := by
  intro k
  rw [← Finset.mul_sum, ← hbudget k]

omit [Fintype K] in
/-- The proportional shares sum to the budget when scarcity is defined as
    total budget divided by total deployed value. -/
theorem proportionalComponentBudgets_sum_of_total (budget : K → ℝ) (deployed : M → K → ℝ)
    (htotal : ∀ k, 0 < ∑ m : M, deployed m k) :
    ∀ k,
      (∑ m : M,
        (budget k / ∑ n : M, deployed n k) * deployed m k) =
        budget k := by
  intro k
  rw [← Finset.mul_sum]
  exact div_mul_cancel₀ (budget k) (ne_of_gt (htotal k))

/-- Component deployed value is canonical under a common scarcity factor and
    retained-cash complementarity.  This is the arithmetic bridge used when
    splitting a monolithic optimum's retained cash among active components. -/
theorem deployedValue_eq_of_common_scarcity (scarcity budget utility cash deployed : ℝ)
    (hscarcity_pos : 0 < scarcity) (hscarcity_le : scarcity ≤ 1)
    (hutility : 0 ≤ utility) (hcash : 0 ≤ cash) (hdeployed : deployed = utility + cash)
    (hbudget : budget = scarcity * deployed) (hcomplementarity : (1 - scarcity) * cash = 0) :
    deployedValue budget utility = deployed := by
  by_cases hone : scarcity = 1
  · subst scarcity
    have hbudgetDeployed : budget = deployed := by
      simpa using hbudget
    have hutilityBudget : utility ≤ budget := by
      rw [hbudgetDeployed, hdeployed]
      linarith
    unfold deployedValue
    rw [max_eq_right hutilityBudget, hbudgetDeployed]
  · have hfactor : 1 - scarcity ≠ 0 := sub_ne_zero.mpr (Ne.symm hone)
    have hcashZero : cash = 0 :=
      (mul_eq_zero.mp hcomplementarity).resolve_left hfactor
    have hdeployedUtility : deployed = utility := by
      rw [hdeployed, hcashZero, add_zero]
    have hbudgetUtility : budget ≤ utility := by
      rw [hbudget, hdeployedUtility]
      nlinarith
    unfold deployedValue
    rw [max_eq_left hbudgetUtility, hdeployedUtility]

omit [Fintype M] [Fintype K] in
/-- If displayed deployed values are the canonical `max(U,B)` values and
    budget shares equal scarcity times deployed value, then every component
    has exactly the displayed common scarcity slope. -/
theorem commonSlope_of_proportional_deployed (componentBudget : M → K → ℝ)
    (scarcity : K → ℝ) (utility deployed : M → K → ℝ)
    (hbudget : ∀ m k, 0 < componentBudget m k)
    (hdeployed : ∀ m k,
      deployed m k =
        deployedValue (componentBudget m k) (utility m k))
    (hproportional : ∀ m k,
      componentBudget m k = scarcity k * deployed m k) :
    ∀ m k,
      psiSlope (componentBudget m k) (utility m k) = scarcity k := by
  intro m k
  have hVpos : 0 < deployed m k := by
    rw [hdeployed m k]
    exact deployedValue_pos (hbudget m k)
  have hmax :
      max (utility m k) (componentBudget m k) =
        deployed m k := by
    simpa only [deployedValue] using (hdeployed m k).symm
  rw [psiSlope_eq_capitalScarcity
      (hbudget m k),
    capitalScarcity, hmax, hproportional m k]
  exact mul_div_cancel_right₀ (scarcity k) (ne_of_gt hVpos)

omit [Fintype M] [Fintype K] in
/-- The paper's retained-cash split conditions imply the common component
    scarcity slopes required by exact decomposition. -/
theorem commonSlope_of_retainedCash_split
    (componentBudget : M → K → ℝ) (scarcity : K → ℝ)
    (utility cash deployed : M → K → ℝ) (hcomponentBudget : ∀ m k, 0 < componentBudget m k)
    (hscarcity_pos : ∀ k, 0 < scarcity k) (hscarcity_le : ∀ k, scarcity k ≤ 1)
    (hutility : ∀ m k, 0 ≤ utility m k) (hcash : ∀ m k, 0 ≤ cash m k)
    (hdeployed : ∀ m k,
      deployed m k = utility m k + cash m k)
    (hbudget : ∀ m k,
      componentBudget m k = scarcity k * deployed m k)
    (hcomplementarity : ∀ m k,
      (1 - scarcity k) * cash m k = 0) :
    ∀ m k,
      psiSlope (componentBudget m k) (utility m k) =
        scarcity k := by
  apply commonSlope_of_proportional_deployed
    componentBudget scarcity utility deployed
      hcomponentBudget
  · intro m k
    exact (deployedValue_eq_of_common_scarcity
      (scarcity k) (componentBudget m k)
      (utility m k) (cash m k) (deployed m k)
      (hscarcity_pos k) (hscarcity_le k)
      (hutility m k) (hcash m k)
      (hdeployed m k) (hbudget m k)
      (hcomplementarity m k)).symm
  · exact hbudget

end FisherClearing
