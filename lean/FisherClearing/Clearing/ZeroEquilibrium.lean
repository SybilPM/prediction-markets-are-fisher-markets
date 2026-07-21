/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.OracleCertificate
import FisherClearing.Clearing.PriceDual

/-!
# Zero-Temperature Equilibrium and Price Dual

This file characterizes zero-temperature equilibrium at a supporting price,
including aggregate and agent-by-agent trader optimality, supply support,
primal-dual equality, budget absorption, and limit-order exactness.
`MaximumEntropy.lean` proves that every zero-temperature optimum has such a
supporting price.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- Profit of the zero-temperature complete-set minting sector. -/
noncomputable def zeroSupplyProfit (price demand : ι → ℝ) : ℝ :=
  outcomeDot price demand - maxFin demand

/-- A simplex-weighted average never exceeds the largest coordinate. -/
theorem outcomeDot_le_maxFin (price demand : ι → ℝ) (hprice : price ∈ stdSimplex ℝ ι) :
    outcomeDot price demand ≤ maxFin demand := by
  unfold outcomeDot
  calc
    (∑ s : ι, price s * demand s) ≤
        ∑ s : ι, price s * maxFin demand := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (le_maxFin demand s) (hprice.1 s)
    _ = maxFin demand * ∑ s : ι, price s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = maxFin demand := by rw [hprice.2, mul_one]

/-- A simplex price supports zero-temperature supply exactly when it yields
    zero minting profit at the displayed demand. -/
theorem zeroSupply_optimal_of_support (price demand : ι → ℝ)
    (hprice : price ∈ stdSimplex ℝ ι) (hsupport : outcomeDot price demand = maxFin demand) :
    IsMaxOn (zeroSupplyProfit price) Set.univ demand := by
  intro other _
  have hother := outcomeDot_le_maxFin price other hprice
  change zeroSupplyProfit price other ≤ zeroSupplyProfit price demand
  rw [zeroSupplyProfit, zeroSupplyProfit, hsupport]
  linarith

theorem support_of_zeroSupply_optimal (price demand : ι → ℝ)
    (hprice : price ∈ stdSimplex ℝ ι)
    (hopt : IsMaxOn (zeroSupplyProfit price) Set.univ demand) :
    outcomeDot price demand = maxFin demand := by
  have hle := outcomeDot_le_maxFin price demand hprice
  have hzero := hopt (Set.mem_univ (0 : ι → ℝ))
  change zeroSupplyProfit price 0 ≤ zeroSupplyProfit price demand at hzero
  simp only [zeroSupplyProfit, outcomeDot, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, maxFin_zero, sub_self] at hzero
  change 0 ≤ outcomeDot price demand - maxFin demand at hzero
  apply le_antisymm hle
  linarith

/-- Aggregate competitive-equilibrium conditions for max-cost minting. -/
structure FullInstance.ZeroCompetitiveEquilibrium
    (fill : J → ℝ) (price : ι → ℝ) : Prop where
  fill_mem : fill ∈ (boxFeasible : Set (J → ℝ))
  price_mem : price ∈ stdSimplex ℝ ι
  traders_optimal : IsMaxOn (inst.traderSurplus price) boxFeasible fill
  supply_optimal : IsMaxOn (zeroSupplyProfit price) Set.univ
    (inst.netDemand fill)

theorem FullInstance.ZeroCompetitiveEquilibrium.supply_support
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) :
    outcomeDot price (inst.netDemand fill) =
      maxFin (inst.netDemand fill) :=
  support_of_zeroSupply_optimal price (inst.netDemand fill)
    heq.price_mem heq.supply_optimal

/-- Zero-temperature competitive-equilibrium conditions certify clearing
    optimality. -/
theorem FullInstance.ZeroCompetitiveEquilibrium.isOptimal
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) :
    IsMaxOn inst.objectiveZero boxFeasible fill := by
  intro other hother
  change inst.objectiveZero other ≤ inst.objectiveZero fill
  have htrader := heq.traders_optimal hother
  change inst.traderSurplus price other ≤
    inst.traderSurplus price fill at htrader
  have hsupply := heq.supply_optimal
    (Set.mem_univ (inst.netDemand other))
  change zeroSupplyProfit price (inst.netDemand other) ≤
    zeroSupplyProfit price (inst.netDemand fill) at hsupply
  rw [inst.objectiveZero_eq_sum_psi_add_residual,
    inst.objectiveZero_eq_sum_psi_add_residual]
  unfold FullInstance.traderSurplus FullInstance.innerWelfare
    zeroSupplyProfit FullInstance.zeroResidual at *
  linarith

theorem FullInstance.ZeroCompetitiveEquilibrium.mmOptimal
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) (k : K) :
    IsMaxOn (inst.mmPayoff price k) boxFeasible fill :=
  inst.mmOptimal_of_tradersOptimal price fill heq.fill_mem
    heq.traders_optimal k

theorem FullInstance.ZeroCompetitiveEquilibrium.retailOptimal
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) (j : J) (howner : inst.owner j = none) :
    IsMaxOn (inst.retailOrderPayoff price j) (Set.Icc 0 1)
      (fill j) :=
  inst.retailOptimal_of_tradersOptimal price fill heq.fill_mem
    heq.traders_optimal j howner

theorem FullInstance.ZeroCompetitiveEquilibrium.retail_full
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) (j : J) (howner : inst.owner j = none)
    (hprice : outcomeDot price (inst.payoff j) < inst.limitPrice j) :
    fill j = 1 :=
  inst.retailOrder_full_of_optimal price fill heq.fill_mem j
    (heq.retailOptimal inst j howner) hprice

theorem FullInstance.ZeroCompetitiveEquilibrium.retail_zero
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) (j : J) (howner : inst.owner j = none)
    (hprice : inst.limitPrice j < outcomeDot price (inst.payoff j)) :
    fill j = 0 :=
  inst.retailOrder_zero_of_optimal price fill heq.fill_mem j
    (heq.retailOptimal inst j howner) hprice

theorem FullInstance.ZeroCompetitiveEquilibrium.retail_price_eq_limit
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) (j : J) (howner : inst.owner j = none)
    (hpositive : 0 < fill j) (hpartial : fill j < 1) :
    outcomeDot price (inst.payoff j) = inst.limitPrice j :=
  inst.retailOrder_price_eq_limit_of_partial price fill j
    (heq.retailOptimal inst j howner) hpositive hpartial

/-- Zero-temperature competitive equilibrium stated agent by agent. -/
structure FullInstance.ZeroAgentCompetitiveEquilibrium
    (fill : J → ℝ) (price : ι → ℝ) : Prop where
  fill_mem : fill ∈ (boxFeasible : Set (J → ℝ))
  price_mem : price ∈ stdSimplex ℝ ι
  supply_optimal : IsMaxOn (zeroSupplyProfit price) Set.univ
    (inst.netDemand fill)
  mm_optimal : ∀ k,
    IsMaxOn (inst.mmPayoff price k) boxFeasible fill
  retail_optimal : ∀ j, inst.owner j = none →
    IsMaxOn (inst.retailOrderPayoff price j) (Set.Icc 0 1)
      (fill j)

theorem FullInstance.ZeroCompetitiveEquilibrium.toAgent
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) :
    inst.ZeroAgentCompetitiveEquilibrium fill price where
  fill_mem := heq.fill_mem
  price_mem := heq.price_mem
  supply_optimal := heq.supply_optimal
  mm_optimal := heq.mmOptimal inst
  retail_optimal := heq.retailOptimal inst

theorem FullInstance.ZeroAgentCompetitiveEquilibrium.toAggregate
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroAgentCompetitiveEquilibrium fill price) :
    inst.ZeroCompetitiveEquilibrium fill price where
  fill_mem := heq.fill_mem
  price_mem := heq.price_mem
  traders_optimal :=
    inst.tradersOptimal_of_agentsOptimal price fill
      heq.mm_optimal heq.retail_optimal
  supply_optimal := heq.supply_optimal

theorem FullInstance.ZeroAgentCompetitiveEquilibrium.isOptimal
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroAgentCompetitiveEquilibrium fill price) :
    IsMaxOn inst.objectiveZero boxFeasible fill :=
  (heq.toAggregate inst).isOptimal inst

theorem FullInstance.ZeroCompetitiveEquilibrium.mmSpending_le_budget
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) (k : K) :
    inst.mmSpending price fill k ≤ inst.budget k :=
  inst.selfEnforcing_budget_le price k fill heq.fill_mem
    (heq.mmOptimal inst k)

theorem FullInstance.ZeroCompetitiveEquilibrium.mmSpending_add_retainedCash_le_budget
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) (k : K) :
    inst.mmSpending price fill k +
        retainedCash (inst.budget k) (inst.mmUtil fill k) ≤
      inst.budget k := by
  exact add_retainedCash_le_of_le_min
    (inst.selfEnforcing_budget price k fill heq.fill_mem
      (heq.mmOptimal inst k))

theorem FullInstance.ZeroCompetitiveEquilibrium.mm_limitPrice_exact
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price)
    (j : J) (k : K) (howner : inst.owner j = some k)
    (hfilled : 0 < fill j) :
    outcomeDot price (inst.payoff j) ≤
      psiSlope (inst.budget k) (inst.mmUtil fill k) *
        inst.limitPrice j :=
  inst.mm_limitPrice_exact_of_optimal heq.fill_mem k
    (heq.mmOptimal inst k) j howner hfilled

theorem FullInstance.ZeroCompetitiveEquilibrium.mm_price_le_limitPrice
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price)
    (j : J) (k : K) (howner : inst.owner j = some k)
    (hfilled : 0 < fill j) :
    outcomeDot price (inst.payoff j) ≤ inst.limitPrice j := by
  have hexact := heq.mm_limitPrice_exact inst j k howner hfilled
  rw [psiSlope_eq_capitalScarcity (inst.budget_pos k)] at hexact
  nlinarith [inst.limitPrice_pos j,
    capitalScarcity_le_one (B := inst.budget k)
      (U := inst.mmUtil fill k) (inst.budget_pos k)]

/-- Weak zero-temperature price duality. -/
theorem FullInstance.clearingZero_le_pricePotential (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (price : ι → ℝ) (hprice : price ∈ stdSimplex ℝ ι) :
    inst.objectiveZero fill ≤ inst.pricePotential price := by
  have htrader := inst.traderSurplus_le_pricePotential price fill hfill
  have hsupply :=
    outcomeDot_le_maxFin price (inst.netDemand fill) hprice
  rw [inst.objectiveZero_eq_sum_psi_add_residual]
  unfold FullInstance.traderSurplus FullInstance.innerWelfare
    FullInstance.zeroResidual at *
  linarith

/-- A zero-temperature equilibrium price attains the price dual, with no
    duality gap, and minimizes the trader potential over the simplex. -/
theorem FullInstance.ZeroCompetitiveEquilibrium.strongDuality
    {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.ZeroCompetitiveEquilibrium fill price) :
    inst.pricePotential price = inst.objectiveZero fill ∧
      ∀ other ∈ stdSimplex ℝ ι,
        inst.pricePotential price ≤ inst.pricePotential other := by
  have hpotential :
      inst.pricePotential price = inst.traderSurplus price fill :=
    inst.pricePotential_eq_of_isMaxOn price fill heq.fill_mem
      heq.traders_optimal
  have hsupport := heq.supply_support inst
  have hequality :
      inst.pricePotential price = inst.objectiveZero fill := by
    rw [hpotential, inst.objectiveZero_eq_sum_psi_add_residual]
    unfold FullInstance.traderSurplus FullInstance.innerWelfare
      FullInstance.zeroResidual
    linarith
  refine ⟨hequality, ?_⟩
  intro other hother
  rw [hequality]
  exact inst.clearingZero_le_pricePotential fill heq.fill_mem other hother

/-- Primal-dual equality is exactly the missing supporting-price certificate:
    it reconstructs a zero-temperature competitive equilibrium. -/
theorem FullInstance.zeroCompetitiveEquilibrium_of_primalDualEquality (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (price : ι → ℝ) (hprice : price ∈ stdSimplex ℝ ι)
    (hequality : inst.pricePotential price = inst.objectiveZero fill) :
    inst.ZeroCompetitiveEquilibrium fill price := by
  have htrader_le :=
    inst.traderSurplus_le_pricePotential price fill hfill
  have hsupply_le :=
    outcomeDot_le_maxFin price (inst.netDemand fill) hprice
  have hpotential_eq :
      inst.pricePotential price = inst.traderSurplus price fill := by
    rw [inst.objectiveZero_eq_sum_psi_add_residual] at hequality
    unfold FullInstance.traderSurplus FullInstance.innerWelfare
      FullInstance.zeroResidual at *
    linarith
  have hsupport :
      outcomeDot price (inst.netDemand fill) =
        maxFin (inst.netDemand fill) := by
    rw [inst.objectiveZero_eq_sum_psi_add_residual] at hequality
    unfold FullInstance.traderSurplus FullInstance.innerWelfare
      FullInstance.zeroResidual at *
    linarith
  refine ⟨hfill, hprice, ?_, zeroSupply_optimal_of_support
    price (inst.netDemand fill) hprice hsupport⟩
  intro other hother
  change inst.traderSurplus price other ≤
    inst.traderSurplus price fill
  rw [← hpotential_eq]
  exact inst.traderSurplus_le_pricePotential price other hother

/-! ### Zero-temperature price set -/

/-- The zero-temperature clearing-price set in dual form: minimizers of the
    trader potential over the outcome simplex. -/
def FullInstance.zeroPriceSet : Set (ι → ℝ) :=
  {price |
    price ∈ stdSimplex ℝ ι ∧
      ∀ other ∈ stdSimplex ℝ ι,
        inst.pricePotential price ≤ inst.pricePotential other}

theorem FullInstance.zeroPriceSet_nonempty :
    inst.zeroPriceSet.Nonempty := by
  rcases exists_optimal_price inst.pricePotential
      inst.continuous_pricePotential.continuousOn with
    ⟨price, hprice, hopt⟩
  exact ⟨price, hprice, hopt⟩

omit [Nonempty ι] in theorem FullInstance.convex_zeroPriceSet :
    Convex ℝ inst.zeroPriceSet := by
  intro p hp q hq a c ha hc hac
  have hsimplex :
      a • p + c • q ∈ stdSimplex ℝ ι :=
    (convex_stdSimplex ℝ ι) hp.1 hq.1 ha hc hac
  refine ⟨hsimplex, ?_⟩
  intro other hother
  have hconv := inst.convexOn_pricePotential.2
    (Set.mem_univ p) (Set.mem_univ q) ha hc hac
  have hpother := hp.2 other hother
  have hqother := hq.2 other hother
  simp only [smul_eq_mul] at hconv
  calc
    inst.pricePotential (a • p + c • q) ≤
        a * inst.pricePotential p + c * inst.pricePotential q := hconv
    _ ≤ a * inst.pricePotential other +
        c * inst.pricePotential other :=
      add_le_add (mul_le_mul_of_nonneg_left hpother ha)
        (mul_le_mul_of_nonneg_left hqother hc)
    _ = inst.pricePotential other := by rw [← add_mul, hac, one_mul]

omit [Nonempty ι] in theorem FullInstance.isCompact_zeroPriceSet :
    IsCompact inst.zeroPriceSet := by
  have hclosedMin :
      IsClosed {price : ι → ℝ |
        ∀ other ∈ stdSimplex ℝ ι,
          inst.pricePotential price ≤ inst.pricePotential other} := by
    rw [show {price : ι → ℝ |
        ∀ other ∈ stdSimplex ℝ ι,
          inst.pricePotential price ≤ inst.pricePotential other} =
        ⋂ other ∈ stdSimplex ℝ ι,
          {price | inst.pricePotential price ≤
            inst.pricePotential other} by
      ext price
      simp]
    exact isClosed_biInter fun other _ =>
      isClosed_le inst.continuous_pricePotential continuous_const
  apply (isCompact_stdSimplex ℝ ι).of_isClosed_subset
  · exact (isClosed_stdSimplex ℝ ι).inter hclosedMin
  · intro price hprice
    exact hprice.1

/-- The zero-price set has a unique maximum-entropy element. -/
theorem FullInstance.existsUnique_maxEntropy_zeroPrice :
    ∃! price : ι → ℝ,
      price ∈ inst.zeroPriceSet ∧
        IsMaxOn shannonEntropy inst.zeroPriceSet price := by
  rcases inst.isCompact_zeroPriceSet.exists_isMaxOn
      inst.zeroPriceSet_nonempty
      continuous_shannonEntropy.continuousOn with
    ⟨price, hprice, hmax⟩
  refine ⟨price, ⟨hprice, hmax⟩, ?_⟩
  intro other hother
  have hstrictSimplex :
      StrictConcaveOn ℝ (stdSimplex ℝ ι) shannonEntropy := by
    have h := (strictConvexOn_negEntropy_simplex (ι := ι)).neg
    rw [show -(fun q : ι → ℝ => -shannonEntropy q) =
        shannonEntropy by
      funext q
      simp] at h
    exact h
  have hstrict :
      StrictConcaveOn ℝ inst.zeroPriceSet shannonEntropy :=
    hstrictSimplex.subset (fun p hp => hp.1) inst.convex_zeroPriceSet
  exact hstrict.eq_of_isMaxOn hother.2 hmax hother.1 hprice

end FisherClearing
