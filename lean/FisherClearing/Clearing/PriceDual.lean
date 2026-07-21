/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.Equilibrium
import FisherClearing.Clearing.PriceUniqueness

/-!
# Risk-Averse Price Dual

The trader-side price potential is the attained maximum of aggregate trader
surplus on the fill box.  It is convex in prices.  Adding the log-sum-exp
conjugate `b * negEntropy` gives the paper's price dual.  At positive
temperature, the softmax price extracted from any primal optimum minimizes this
dual and is unique.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- The paper's trader-side price potential `Φ_RA(p)`. -/
noncomputable def FullInstance.pricePotential (price : ι → ℝ) : ℝ :=
  sSup (inst.traderSurplus price '' (boxFeasible : Set (J → ℝ)))

theorem FullInstance.continuous_traderSurplus (price : ι → ℝ) :
    Continuous (inst.traderSurplus price) := by
  unfold FullInstance.traderSurplus outcomeDot
  exact inst.continuous_innerWelfare.sub (by
    apply continuous_finsetSum
    intro s _
    exact continuous_const.mul
      ((continuous_apply s).comp inst.continuous_netDemand))

/-- Joint continuity in prices and fills. -/
theorem FullInstance.continuous_uncurry_traderSurplus :
    Continuous ↿inst.traderSurplus := by
  unfold FullInstance.traderSurplus outcomeDot
  have hinner :
      Continuous (fun z : (ι → ℝ) × (J → ℝ) =>
        inst.innerWelfare z.2) :=
    inst.continuous_innerWelfare.comp continuous_snd
  have hpayment :
      Continuous (fun z : (ι → ℝ) × (J → ℝ) =>
        ∑ s : ι, z.1 s * inst.netDemand z.2 s) := by
    apply continuous_finsetSum
    intro s _
    exact ((continuous_apply s).comp continuous_fst).mul
      ((continuous_apply s).comp
        (inst.continuous_netDemand.comp continuous_snd))
  exact hinner.sub hpayment

/-- The trader-side price potential is continuous.  This is the compact
    maximum theorem specialized to the fixed fill box. -/
theorem FullInstance.continuous_pricePotential :
    Continuous inst.pricePotential := by
  unfold FullInstance.pricePotential
  exact isCompact_boxFeasible.continuous_sSup
    inst.continuous_uncurry_traderSurplus

/-- The price potential is attained by a feasible fill. -/
theorem FullInstance.exists_pricePotential_eq (price : ι → ℝ) :
    ∃ fill ∈ (boxFeasible : Set (J → ℝ)),
      inst.pricePotential price = inst.traderSurplus price fill ∧
      IsMaxOn (inst.traderSurplus price) boxFeasible fill := by
  rcases isCompact_boxFeasible.exists_sSup_image_eq_and_ge
      nonempty_boxFeasible
      (inst.continuous_traderSurplus price).continuousOn with
    ⟨fill, hfill, hvalue, hbest⟩
  refine ⟨fill, hfill, ?_, ?_⟩
  · exact hvalue
  · intro other hother
    change inst.traderSurplus price other ≤ inst.traderSurplus price fill
    exact hbest other hother

theorem FullInstance.traderSurplus_le_pricePotential (price : ι → ℝ) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    inst.traderSurplus price fill ≤ inst.pricePotential price := by
  rcases inst.exists_pricePotential_eq price with
    ⟨best, _hbestMem, hvalue, hbest⟩
  rw [hvalue]
  exact hbest hfill

theorem FullInstance.pricePotential_eq_of_isMaxOn (price : ι → ℝ) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.traderSurplus price) boxFeasible fill) :
    inst.pricePotential price = inst.traderSurplus price fill := by
  rcases inst.exists_pricePotential_eq price with
    ⟨best, hbestMem, hvalue, hbest⟩
  rw [hvalue]
  exact le_antisymm (hopt hbestMem) (hbest hfill)

theorem outcomeDot_price_linear (p q demand : ι → ℝ) (a c : ℝ) :
    outcomeDot (a • p + c • q) demand =
      a * outcomeDot p demand + c * outcomeDot q demand := by
  unfold outcomeDot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem FullInstance.traderSurplus_price_combo
    (p q : ι → ℝ) (fill : J → ℝ) (a c : ℝ) (hac : a + c = 1) :
    inst.traderSurplus (a • p + c • q) fill =
      a * inst.traderSurplus p fill + c * inst.traderSurplus q fill := by
  unfold FullInstance.traderSurplus
  rw [outcomeDot_price_linear]
  calc
    inst.innerWelfare fill -
          (a * outcomeDot p (inst.netDemand fill) +
            c * outcomeDot q (inst.netDemand fill)) =
        (a + c) * inst.innerWelfare fill -
          (a * outcomeDot p (inst.netDemand fill) +
            c * outcomeDot q (inst.netDemand fill)) := by rw [hac]; ring
    _ = a * (inst.innerWelfare fill -
          outcomeDot p (inst.netDemand fill)) +
        c * (inst.innerWelfare fill -
          outcomeDot q (inst.netDemand fill)) := by ring

/-- `Φ_RA` is convex as the pointwise supremum of affine price functions. -/
theorem FullInstance.convexOn_pricePotential :
    ConvexOn ℝ Set.univ inst.pricePotential := by
  constructor
  · exact convex_univ
  · intro p _hp q _hq a c ha hc hac
    rcases inst.exists_pricePotential_eq (a • p + c • q) with
      ⟨fill, hfill, hvalue, _hbest⟩
    have hpBound := inst.traderSurplus_le_pricePotential p fill hfill
    have hqBound := inst.traderSurplus_le_pricePotential q fill hfill
    simp only [smul_eq_mul]
    rw [hvalue, inst.traderSurplus_price_combo p q fill a c hac]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hpBound ha)
      (mul_le_mul_of_nonneg_left hqBound hc)

/-- The fill-space potential has exactly the demand-space representation
    `max_D {W_RA(D) - ⟨p,D⟩}` from the paper. -/
theorem FullInstance.exists_pricePotential_demand_representation (price : ι → ℝ) :
    ∃ demand ∈ inst.feasibleDemands,
      inst.pricePotential price =
        inst.demandValue demand - outcomeDot price demand ∧
      ∀ other ∈ inst.feasibleDemands,
        inst.demandValue other - outcomeDot price other ≤
          inst.demandValue demand - outcomeDot price demand := by
  rcases inst.exists_pricePotential_eq price with
    ⟨fill, hfill, hvalue, hopt⟩
  let demand := inst.netDemand fill
  have hdemand : demand ∈ inst.feasibleDemands :=
    inst.netDemand_mem_feasibleDemands fill hfill
  have hfiber : inst.demandValue demand = inst.innerWelfare fill := by
    rcases inst.exists_demandValue_eq hdemand with
      ⟨best, hbestFiber, hbestValue, _⟩
    have h := hopt hbestFiber.1
    change inst.traderSurplus price best ≤
      inst.traderSurplus price fill at h
    have hnet : inst.netDemand best = demand := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hbestFiber.2
    unfold FullInstance.traderSurplus at h
    rw [hnet] at h
    linarith [inst.innerWelfare_le_demandValue fill hfill]
  refine ⟨demand, hdemand, ?_, ?_⟩
  · rw [hvalue, FullInstance.traderSurplus, hfiber]
  · intro other hother
    rcases inst.exists_demandValue_eq hother with
      ⟨otherFill, hotherFiber, hotherValue, _⟩
    have h := hopt hotherFiber.1
    change inst.traderSurplus price otherFill ≤
      inst.traderSurplus price fill at h
    have hnet : inst.netDemand otherFill = other := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hotherFiber.2
    unfold FullInstance.traderSurplus at h
    rw [hnet, ← hotherValue, ← hfiber] at h
    exact h

/-- Fenchel--Young inequality for log-sum-exp, in real-valued form. -/
theorem logSumExp_fenchel_inequality
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (price : ι → ℝ)
    (hprice : price ∈ stdSimplex ℝ ι) (demand : ι → ℝ) :
    outcomeDot price demand - logSumExp b demand ≤
      b * negEntropy price := by
  have h := le_fenchelConjugate (logSumExp b) price demand
  rw [fenchelConjugate_logSumExp_simplex hb hprice] at h
  exact_mod_cast h

/-- Fenchel equality at the softmax gradient. -/
theorem softmax_fenchel_equality
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (demand : ι → ℝ) :
    outcomeDot (softmax b demand) demand - logSumExp b demand =
      b * negEntropy (softmax b demand) := by
  set price := softmax b demand
  set S := sumExp b demand
  have hS : 0 < S := sumExp_pos b demand
  have hlog : ∀ s : ι,
      Real.log (price s) = demand s / b - Real.log S := by
    intro s
    simp only [price, softmax, S]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hS),
      Real.log_exp]
  have hprod :
      ∑ s : ι, price s * (b * Real.log S) = b * Real.log S := by
    rw [show ∑ s : ι, price s * (b * Real.log S) =
        (b * Real.log S) * ∑ s : ι, price s from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring]
    rw [show (∑ s : ι, price s) = 1 by
      exact softmax_sum_eq_one b demand, mul_one]
  unfold outcomeDot negEntropy logSumExp
  simp_rw [hlog]
  rw [Finset.mul_sum]
  have hterm : ∀ s : ι,
      b * (price s * (demand s / b - Real.log S)) =
        price s * demand s - price s * (b * Real.log S) := by
    intro s
    field_simp [ne_of_gt hb]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, hprod]

/-- The real-valued risk-averse price-dual objective. -/
noncomputable def FullInstance.priceDualObjective (b : ℝ) (price : ι → ℝ) : ℝ :=
  inst.pricePotential price + b * negEntropy price

/-- Weak duality between any feasible fill and any simplex price. -/
theorem FullInstance.clearing_le_priceDual
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (price : ι → ℝ) (hprice : price ∈ stdSimplex ℝ ι) :
    inst.objective b fill ≤ inst.priceDualObjective b price := by
  have htrader := inst.traderSurplus_le_pricePotential price fill hfill
  have hcost :=
    logSumExp_fenchel_inequality hb price hprice (inst.netDemand fill)
  rw [inst.objective_eq_innerWelfare_sub_cost]
  unfold FullInstance.traderSurplus at htrader
  unfold FullInstance.priceDualObjective
  linarith

/-- Strong duality and dual attainment at the extracted softmax price. -/
theorem FullInstance.softmax_minimizes_priceDual
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.objective b) boxFeasible fill) :
    let price := softmax b (inst.netDemand fill)
    inst.priceDualObjective b price = inst.objective b fill ∧
      ∀ other ∈ stdSimplex ℝ ι,
        inst.priceDualObjective b price ≤ inst.priceDualObjective b other := by
  let price := softmax b (inst.netDemand fill)
  have heq := inst.competitiveEquilibrium_of_optimal hb fill hfill hopt
  have hpotential :
      inst.pricePotential price = inst.traderSurplus price fill :=
    inst.pricePotential_eq_of_isMaxOn price fill hfill heq.traders_optimal
  have hfenchel := softmax_fenchel_equality hb (inst.netDemand fill)
  change outcomeDot price (inst.netDemand fill) -
      logSumExp b (inst.netDemand fill) =
    b * negEntropy price at hfenchel
  have hequality :
      inst.priceDualObjective b price = inst.objective b fill := by
    rw [FullInstance.priceDualObjective, hpotential,
      inst.objective_eq_innerWelfare_sub_cost]
    unfold FullInstance.traderSurplus
    linarith
  refine ⟨hequality, ?_⟩
  intro other hother
  rw [hequality]
  exact inst.clearing_le_priceDual hb fill hfill other hother

/-- Positive-temperature clearing prices are unique. -/
theorem FullInstance.softmax_price_unique
    [Nonempty ι] {b : ℝ} (hb : 0 < b)
    (fill₁ fill₂ : J → ℝ) (hfill₁ : fill₁ ∈ (boxFeasible : Set (J → ℝ)))
    (hfill₂ : fill₂ ∈ (boxFeasible : Set (J → ℝ)))
    (hopt₁ : IsMaxOn (inst.objective b) boxFeasible fill₁)
    (hopt₂ : IsMaxOn (inst.objective b) boxFeasible fill₂) :
    softmax b (inst.netDemand fill₁) =
      softmax b (inst.netDemand fill₂) := by
  have hdual₁ := (inst.softmax_minimizes_priceDual hb fill₁ hfill₁ hopt₁).2
  have hdual₂ := (inst.softmax_minimizes_priceDual hb fill₂ hfill₂ hopt₂).2
  have hconv :
      ConvexOn ℝ (stdSimplex ℝ ι) inst.pricePotential :=
    inst.convexOn_pricePotential.subset (Set.subset_univ _)
      (convex_stdSimplex ℝ ι)
  apply price_unique hb inst.pricePotential hconv
    _ _
    (softmax_mem_stdSimplex b (inst.netDemand fill₁))
    (softmax_mem_stdSimplex b (inst.netDemand fill₂))
  · simpa only [FullInstance.priceDualObjective, shannonEntropy,
      neg_neg] using hdual₁
  · simpa only [FullInstance.priceDualObjective, shannonEntropy,
      neg_neg] using hdual₂

end FisherClearing
