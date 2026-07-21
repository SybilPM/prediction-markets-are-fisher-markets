/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.LiftedProgram
import FisherClearing.Clearing.ZeroTemperature

/-!
# Zero-Temperature Exponential-Cone Reformulation

The minting maximum is represented by one LP epigraph variable, while every
logarithm is represented by a single exponential-cone slice
`exp(tₖ) ≤ Vₖ`.  The resulting objective is linear in all displayed variables.
This file proves exact pointwise and optimizer equivalence with reduced-form
zero-temperature clearing.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- Variables of the zero-temperature exponential-cone program. -/
structure FullInstance.ZeroConicPoint where
  fill : J → ℝ
  deployed : K → ℝ
  logValue : K → ℝ
  mintEpigraph : ℝ

/-- LP constraints together with one exponential-cone slice per MM. -/
def FullInstance.zeroConicFeasible :
    Set (FullInstance.ZeroConicPoint (J := J) (K := K)) :=
  {z |
    z.fill ∈ (boxFeasible : Set (J → ℝ)) ∧
    (∀ k : K,
      0 < z.deployed k ∧
      inst.mmUtil z.fill k ≤ z.deployed k ∧
      Real.exp (z.logValue k) ≤ z.deployed k) ∧
    ∀ s : ι, inst.netDemand z.fill s ≤ z.mintEpigraph}

/-- Linear objective of the conic formulation. -/
noncomputable def FullInstance.zeroConicObjective
    (z : FullInstance.ZeroConicPoint (J := J) (K := K)) : ℝ :=
  (∑ k : K,
    (inst.budget k * z.logValue k - z.deployed k +
      inst.mmUtil z.fill k)) +
    inst.retailWelfare z.fill - z.mintEpigraph

/-- Canonical epigraph lift of a reduced-form fill. -/
noncomputable def FullInstance.zeroConicLift (fill : J → ℝ) :
      FullInstance.ZeroConicPoint (J := J) (K := K) where
  fill := fill
  deployed := fun k =>
    deployedValue (inst.budget k) (inst.mmUtil fill k)
  logValue := fun k =>
    Real.log (deployedValue (inst.budget k) (inst.mmUtil fill k))
  mintEpigraph := maxFin (inst.netDemand fill)

/-- The exponential-cone slice at homogeneous coordinate one is exactly the
    logarithm hypograph. -/
theorem expConeAtOne_iff {t V : ℝ} (hV : 0 < V) :
    Real.exp t ≤ V ↔ t ≤ Real.log V :=
  (Real.le_log_iff_exp_le hV).symm

private theorem isMaxOn_iff_isMaxOn_lift
    {X Z : Type*} (f : X → ℝ) (g : Z → ℝ) (S : Set X) (T : Set Z)
    (project : Z → X) (lift : X → Z) (x : X) (hlift : ∀ y ∈ S, lift y ∈ T)
    (hproject : ∀ z ∈ T, project z ∈ S) (hbound : ∀ z ∈ T, g z ≤ f (project z))
    (hvalue : ∀ y, g (lift y) = f y) :
    IsMaxOn f S x ↔ IsMaxOn g T (lift x) := by
  constructor
  · intro hopt z hz
    calc
      g z ≤ f (project z) := hbound z hz
      _ ≤ f x := hopt (hproject z hz)
      _ = g (lift x) := (hvalue x).symm
  · intro hopt y hy
    change f y ≤ f x
    rw [← hvalue y, ← hvalue x]
    exact hopt (hlift y hy)

omit [Fintype ι] [Nonempty ι] in theorem FullInstance.conicMMObjective_le_reduced
    (fill : J → ℝ) (deployed logValue : K → ℝ) (hcone : ∀ k, 0 < deployed k ∧
      inst.mmUtil fill k ≤ deployed k ∧
      Real.exp (logValue k) ≤ deployed k) :
    (∑ k : K, (inst.budget k * logValue k - deployed k +
      inst.mmUtil fill k)) ≤
      ∑ k : K, psiB (inst.budget k) (inst.mmUtil fill k) := by
  apply Finset.sum_le_sum
  intro k _
  have hlog := (Real.le_log_iff_exp_le (hcone k).1).mpr (hcone k).2.2
  calc
    inst.budget k * logValue k - deployed k + inst.mmUtil fill k ≤
        liftedMM (inst.budget k) (deployed k) (inst.mmUtil fill k) := by
      unfold liftedMM
      nlinarith [inst.budget_pos k]
    _ ≤ psiB (inst.budget k) (inst.mmUtil fill k) :=
      liftedMM_le_psiB (inst.budget_pos k) (hcone k).1 (hcone k).2.1

omit [Fintype ι] [Nonempty ι] in theorem FullInstance.sum_liftedMM_deployedValue (fill : J → ℝ) :
    (∑ k : K, liftedMM (inst.budget k)
      (deployedValue (inst.budget k) (inst.mmUtil fill k))
      (inst.mmUtil fill k)) =
      ∑ k : K, psiB (inst.budget k) (inst.mmUtil fill k) :=
  Finset.sum_congr rfl fun _ _ => liftedMM_eq_psiB

omit [Fintype K] in theorem FullInstance.zeroConicLift_mem (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    inst.zeroConicLift fill ∈ inst.zeroConicFeasible := by
  refine ⟨hfill, ?_, ?_⟩
  · intro k
    let V := deployedValue (inst.budget k) (inst.mmUtil fill k)
    have hV : 0 < V := deployedValue_pos (inst.budget_pos k)
    refine ⟨hV, deployedValue_ge_U, ?_⟩
    change Real.exp (Real.log V) ≤ V
    rw [Real.exp_log hV]
  · intro s
    exact le_maxFin (inst.netDemand fill) s

omit [Fintype K] in theorem FullInstance.maxFin_le_mintEpigraph
    (z : FullInstance.ZeroConicPoint (J := J) (K := K)) (hz : z ∈ inst.zeroConicFeasible) :
    maxFin (inst.netDemand z.fill) ≤ z.mintEpigraph := by
  apply Finset.sup'_le
  intro s _
  exact hz.2.2 s

/-- Every conic-feasible point is bounded above by the reduced-form objective
    of its projected fill. -/
theorem FullInstance.zeroConicObjective_le_reduced
    (z : FullInstance.ZeroConicPoint (J := J) (K := K)) (hz : z ∈ inst.zeroConicFeasible) :
    inst.zeroConicObjective z ≤ inst.objectiveZero z.fill := by
  have hMM := inst.conicMMObjective_le_reduced
    z.fill z.deployed z.logValue hz.2.1
  have hmint := inst.maxFin_le_mintEpigraph z hz
  unfold FullInstance.zeroConicObjective FullInstance.objectiveZero
  linarith

/-- The canonical conic lift has exactly the reduced-form value. -/
theorem FullInstance.zeroConicObjective_lift (fill : J → ℝ) :
    inst.zeroConicObjective (inst.zeroConicLift fill) =
      inst.objectiveZero fill := by
  unfold FullInstance.zeroConicObjective FullInstance.zeroConicLift
    FullInstance.objectiveZero
  change
    (∑ k : K,
      liftedMM (inst.budget k)
        (deployedValue (inst.budget k) (inst.mmUtil fill k))
        (inst.mmUtil fill k)) +
        inst.retailWelfare fill - maxFin (inst.netDemand fill) =
      (∑ k : K, psiB (inst.budget k) (inst.mmUtil fill k)) -
        maxFin (inst.netDemand fill) + inst.retailWelfare fill
  rw [inst.sum_liftedMM_deployedValue]
  ring

theorem FullInstance.isZeroOptimal_iff_isZeroConicOptimal
    {fill : J → ℝ} :
    IsMaxOn inst.objectiveZero boxFeasible fill ↔
      IsMaxOn inst.zeroConicObjective inst.zeroConicFeasible
        (inst.zeroConicLift fill) :=
  isMaxOn_iff_isMaxOn_lift
    inst.objectiveZero inst.zeroConicObjective boxFeasible
    inst.zeroConicFeasible ZeroConicPoint.fill inst.zeroConicLift fill
    inst.zeroConicLift_mem (fun _ hz => hz.1)
    inst.zeroConicObjective_le_reduced inst.zeroConicObjective_lift

/-- A reduced-form zero-temperature optimizer canonically lifts to a conic
    optimizer. -/
theorem FullInstance.IsZeroOptimal.zeroConicLift
    {fill : J → ℝ}
    (hopt : IsMaxOn inst.objectiveZero boxFeasible fill) :
    IsMaxOn inst.zeroConicObjective inst.zeroConicFeasible
      (inst.zeroConicLift fill) :=
  (inst.isZeroOptimal_iff_isZeroConicOptimal).mp hopt

/-- Optimality of the canonical conic lift projects back to reduced-form
    optimality. -/
theorem FullInstance.IsZeroConicOptimal.reduced
    {fill : J → ℝ}
    (hopt : IsMaxOn inst.zeroConicObjective inst.zeroConicFeasible
      (inst.zeroConicLift fill)) :
    IsMaxOn inst.objectiveZero boxFeasible fill :=
  (inst.isZeroOptimal_iff_isZeroConicOptimal).mpr hopt

/-! ### Positive-temperature formulation -/

/-- Sum of the shifted exponential-cone slices used in the log-sum-exp
    epigraph. -/
noncomputable def shiftedExpSum (b : ℝ) (demand : ι → ℝ) (mintEpigraph : ℝ) : ℝ :=
  ∑ s : ι, Real.exp ((demand s - mintEpigraph) / b)

omit [Nonempty ι] in theorem shiftedExpSum_eq
    {b : ℝ} (hb : 0 < b) (demand : ι → ℝ) (mintEpigraph : ℝ) :
    shiftedExpSum b demand mintEpigraph =
      sumExp b demand / Real.exp (mintEpigraph / b) := by
  unfold shiftedExpSum sumExp
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  have harg :
      (demand s - mintEpigraph) / b =
        demand s / b - mintEpigraph / b := by
    field_simp [ne_of_gt hb]
  rw [harg, Real.exp_sub]

/-- The standard `O(|ι|)` exponential-cone epigraph for log-sum-exp. -/
theorem logSumExp_le_iff_shiftedExpSum_le_one
    {b : ℝ} (hb : 0 < b) (demand : ι → ℝ) (mintEpigraph : ℝ) :
    logSumExp b demand ≤ mintEpigraph ↔
      shiftedExpSum b demand mintEpigraph ≤ 1 := by
  rw [shiftedExpSum_eq hb]
  have hsum : 0 < sumExp b demand := sumExp_pos b demand
  have hexp : 0 < Real.exp (mintEpigraph / b) :=
    Real.exp_pos _
  constructor
  · intro hcost
    have hlog :
        Real.log (sumExp b demand) ≤ mintEpigraph / b := by
      apply (le_div_iff₀ hb).2
      unfold logSumExp at hcost
      nlinarith
    have hsumExp :
        sumExp b demand ≤ Real.exp (mintEpigraph / b) :=
      (Real.log_le_iff_le_exp hsum).mp hlog
    exact (div_le_one hexp).2 hsumExp
  · intro hshift
    have hsumExp :
        sumExp b demand ≤ Real.exp (mintEpigraph / b) :=
      (div_le_one hexp).1 hshift
    have hlog :
        Real.log (sumExp b demand) ≤ mintEpigraph / b :=
      (Real.log_le_iff_le_exp hsum).2 hsumExp
    unfold logSumExp
    calc
      b * Real.log (sumExp b demand) ≤
          b * (mintEpigraph / b) :=
        mul_le_mul_of_nonneg_left hlog hb.le
      _ = mintEpigraph := by field_simp [ne_of_gt hb]

/-- Variables of the positive-temperature exponential-cone program.  Besides
    one cone per MM, it uses one shifted exponential slice per outcome. -/
structure FullInstance.PositiveConicPoint where
  fill : J → ℝ
  deployed : K → ℝ
  logValue : K → ℝ
  mintEpigraph : ℝ
  mintWeight : ι → ℝ

/-- Linear and exponential-cone constraints for positive temperature. -/
def FullInstance.positiveConicFeasible (b : ℝ) :
    Set (FullInstance.PositiveConicPoint
      (ι := ι) (J := J) (K := K)) :=
  {z |
    z.fill ∈ (boxFeasible : Set (J → ℝ)) ∧
    (∀ k : K,
      0 < z.deployed k ∧
      inst.mmUtil z.fill k ≤ z.deployed k ∧
      Real.exp (z.logValue k) ≤ z.deployed k) ∧
    (∀ s : ι,
      Real.exp ((inst.netDemand z.fill s - z.mintEpigraph) / b) ≤
        z.mintWeight s) ∧
    (∑ s : ι, z.mintWeight s) ≤ 1}

/-- Linear objective of the positive-temperature conic formulation. -/
noncomputable def FullInstance.positiveConicObjective (z : FullInstance.PositiveConicPoint
      (ι := ι) (J := J) (K := K)) : ℝ :=
  (∑ k : K,
    (inst.budget k * z.logValue k - z.deployed k +
      inst.mmUtil z.fill k)) +
    inst.retailWelfare z.fill - z.mintEpigraph

/-- Canonical positive-temperature conic lift. -/
noncomputable def FullInstance.positiveConicLift (b : ℝ) (fill : J → ℝ) :
      FullInstance.PositiveConicPoint
        (ι := ι) (J := J) (K := K) where
  fill := fill
  deployed := fun k =>
    deployedValue (inst.budget k) (inst.mmUtil fill k)
  logValue := fun k =>
    Real.log (deployedValue (inst.budget k) (inst.mmUtil fill k))
  mintEpigraph := logSumExp b (inst.netDemand fill)
  mintWeight := fun s =>
    Real.exp ((inst.netDemand fill s -
      logSumExp b (inst.netDemand fill)) / b)

omit [Fintype K] in theorem FullInstance.positiveConicLift_mem
    {b : ℝ} (hb : 0 < b) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    inst.positiveConicLift b fill ∈ inst.positiveConicFeasible b := by
  refine ⟨hfill, ?_, ?_, ?_⟩
  · intro k
    let V := deployedValue (inst.budget k) (inst.mmUtil fill k)
    have hV : 0 < V := deployedValue_pos (inst.budget_pos k)
    refine ⟨hV, deployedValue_ge_U, ?_⟩
    change Real.exp (Real.log V) ≤ V
    rw [Real.exp_log hV]
  · intro s
    exact le_rfl
  · exact (logSumExp_le_iff_shiftedExpSum_le_one hb
      (inst.netDemand fill)
      (logSumExp b (inst.netDemand fill))).1 le_rfl

omit [Fintype K] in theorem FullInstance.logSumExp_le_mintEpigraph
    {b : ℝ} (hb : 0 < b)
    (z : FullInstance.PositiveConicPoint
      (ι := ι) (J := J) (K := K))
    (hz : z ∈ inst.positiveConicFeasible b) :
    logSumExp b (inst.netDemand z.fill) ≤ z.mintEpigraph := by
  apply (logSumExp_le_iff_shiftedExpSum_le_one hb
    (inst.netDemand z.fill) z.mintEpigraph).2
  unfold shiftedExpSum
  calc
    (∑ s : ι,
        Real.exp ((inst.netDemand z.fill s - z.mintEpigraph) / b)) ≤
        ∑ s : ι, z.mintWeight s :=
      Finset.sum_le_sum fun s _ => hz.2.2.1 s
    _ ≤ 1 := hz.2.2.2

/-- Every positive-conic feasible point is bounded above by the corresponding
    reduced-form objective. -/
theorem FullInstance.positiveConicObjective_le_reduced
    {b : ℝ} (hb : 0 < b)
    (z : FullInstance.PositiveConicPoint
      (ι := ι) (J := J) (K := K))
    (hz : z ∈ inst.positiveConicFeasible b) :
    inst.positiveConicObjective z ≤ inst.objective b z.fill := by
  have hMM := inst.conicMMObjective_le_reduced
    z.fill z.deployed z.logValue hz.2.1
  have hmint := inst.logSumExp_le_mintEpigraph hb z hz
  unfold FullInstance.positiveConicObjective FullInstance.objective
  linarith

omit [Nonempty ι] in theorem FullInstance.positiveConicObjective_lift
    (b : ℝ) (fill : J → ℝ) :
    inst.positiveConicObjective (inst.positiveConicLift b fill) =
      inst.objective b fill := by
  unfold FullInstance.positiveConicObjective
    FullInstance.positiveConicLift FullInstance.objective
  change
    (∑ k : K,
      liftedMM (inst.budget k)
        (deployedValue (inst.budget k) (inst.mmUtil fill k))
        (inst.mmUtil fill k)) +
        inst.retailWelfare fill -
          logSumExp b (inst.netDemand fill) =
      (∑ k : K, psiB (inst.budget k) (inst.mmUtil fill k)) -
        logSumExp b (inst.netDemand fill) +
          inst.retailWelfare fill
  rw [inst.sum_liftedMM_deployedValue]
  ring

theorem FullInstance.isOptimal_iff_isPositiveConicOptimal
    {b : ℝ} (hb : 0 < b) {fill : J → ℝ} :
    IsMaxOn (inst.objective b) boxFeasible fill ↔
      IsMaxOn inst.positiveConicObjective
        (inst.positiveConicFeasible b)
        (inst.positiveConicLift b fill) :=
  isMaxOn_iff_isMaxOn_lift
    (inst.objective b) inst.positiveConicObjective boxFeasible
    (inst.positiveConicFeasible b) PositiveConicPoint.fill
    (inst.positiveConicLift b) fill (inst.positiveConicLift_mem hb)
    (fun _ hz => hz.1) (inst.positiveConicObjective_le_reduced hb)
    (inst.positiveConicObjective_lift b)

theorem FullInstance.IsOptimal.positiveConicLift
    {b : ℝ} (hb : 0 < b) {fill : J → ℝ}
    (hopt : IsMaxOn (inst.objective b) boxFeasible fill) :
    IsMaxOn inst.positiveConicObjective (inst.positiveConicFeasible b)
      (inst.positiveConicLift b fill) :=
  (inst.isOptimal_iff_isPositiveConicOptimal hb).mp hopt

theorem FullInstance.IsPositiveConicOptimal.reduced
    {b : ℝ} (hb : 0 < b) {fill : J → ℝ}
    (hopt : IsMaxOn inst.positiveConicObjective
      (inst.positiveConicFeasible b) (inst.positiveConicLift b fill)) :
    IsMaxOn (inst.objective b) boxFeasible fill :=
  (inst.isOptimal_iff_isPositiveConicOptimal hb).mpr hopt

end FisherClearing
