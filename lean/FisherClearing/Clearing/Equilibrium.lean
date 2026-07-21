/-
Copyright (c) 2024 FisherClearing Contributors. All rights reserved.
Licensed under CC BY 4.0 as described in the repository LICENSE.
Authors: Valeriy Cherepanov
-/
import FisherClearing.Clearing.DemandSpace
import FisherClearing.Clearing.SelfEnforcing
import FisherClearing.Convex.Softmax

/-!
# Positive-Temperature Clearing Equilibrium

For positive temperature, the softmax of optimal net demand supports both
sides of the market: the minting sector maximizes profit and the aggregate
trader sector maximizes welfare minus expenditure.  Conversely, these two
price-taking optimality conditions certify a clearing optimum.
-/

namespace FisherClearing

open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {J : Type*} [Fintype J]
variable {K : Type*} [Fintype K] [DecidableEq K]

variable (inst : FullInstance ι J K)

/-- Inner product of an outcome price with net demand. -/
noncomputable def outcomeDot (price demand : ι → ℝ) : ℝ :=
  ∑ s : ι, price s * demand s

/-- Aggregate price-taking payoff of all traders. -/
noncomputable def FullInstance.traderSurplus (price : ι → ℝ) (fill : J → ℝ) : ℝ :=
  inst.innerWelfare fill - outcomeDot price (inst.netDemand fill)

/-- Profit of the endogenous minting sector. -/
noncomputable def supplyProfit (b : ℝ) (price demand : ι → ℝ) : ℝ :=
  outcomeDot price demand - logSumExp b demand

/-- Directional derivative of inner welfare along a fill segment. -/
noncomputable def FullInstance.innerDirectional (fill other : J → ℝ) : ℝ :=
  (∑ k : K,
    psiSlope (inst.budget k) (inst.mmUtil fill k) *
      (inst.mmUtil other k - inst.mmUtil fill k)) +
  (inst.retailWelfare other - inst.retailWelfare fill)

omit [Fintype ι] [Fintype K] in theorem FullInstance.hasDerivAt_mmUtil_line
    (fill other : J → ℝ) (k : K) :
    HasDerivAt
      (fun t : ℝ => inst.mmUtil (AffineMap.lineMap fill other t) k)
      (inst.mmUtil other k - inst.mmUtil fill k) 0 := by
  convert (((hasDerivAt_id (0 : ℝ)).mul_const
    (inst.mmUtil other k - inst.mmUtil fill k)).add_const
      (inst.mmUtil fill k)) using 1 <;> try rfl
  · funext t
    rw [AffineMap.lineMap_apply_module,
      inst.mmUtil_linear k fill other (1 - t) t]
    simp only [id_eq]
    ring
  · ring

omit [Fintype K] in theorem FullInstance.hasDerivAt_mmSpending_line
    (price : ι → ℝ) (fill other : J → ℝ) (k : K) :
    HasDerivAt
      (fun t : ℝ =>
        inst.mmSpending price (AffineMap.lineMap fill other t) k)
      (inst.mmSpending price other k - inst.mmSpending price fill k) 0 := by
  convert (((hasDerivAt_id (0 : ℝ)).mul_const
    (inst.mmSpending price other k -
      inst.mmSpending price fill k)).add_const
        (inst.mmSpending price fill k)) using 1 <;> try rfl
  · funext t
    rw [AffineMap.lineMap_apply_module,
      inst.mmSpending_linear price k fill other (1 - t) t]
    simp only [id_eq]
    ring
  · ring

omit [Fintype ι] [Fintype K] [DecidableEq K] in theorem FullInstance.hasDerivAt_retailWelfare_line
    (fill other : J → ℝ) :
    HasDerivAt
      (fun t : ℝ => inst.retailWelfare (AffineMap.lineMap fill other t))
      (inst.retailWelfare other - inst.retailWelfare fill) 0 := by
  convert (((hasDerivAt_id (0 : ℝ)).mul_const
    (inst.retailWelfare other - inst.retailWelfare fill)).add_const
      (inst.retailWelfare fill)) using 1 <;> try rfl
  · funext t
    rw [AffineMap.lineMap_apply_module,
      inst.retailWelfare_linear fill other (1 - t) t]
    simp only [id_eq]
    ring
  · ring

omit [Fintype ι] in theorem FullInstance.hasDerivAt_innerWelfare_line (fill other : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    HasDerivAt
      (fun t : ℝ => inst.innerWelfare (AffineMap.lineMap fill other t))
      (inst.innerDirectional fill other) 0 := by
  have hmm : ∀ k : K,
      HasDerivAt
        (fun t : ℝ =>
          psiB (inst.budget k)
            (inst.mmUtil (AffineMap.lineMap fill other t) k))
        (psiSlope (inst.budget k) (inst.mmUtil fill k) *
          (inst.mmUtil other k - inst.mmUtil fill k)) 0 := by
    intro k
    have houter :
        HasDerivAt (psiB (inst.budget k))
          (psiSlope (inst.budget k) (inst.mmUtil fill k))
          (inst.mmUtil (AffineMap.lineMap fill other (0 : ℝ)) k) := by
      simpa only [AffineMap.lineMap_apply_zero] using
        hasDerivAt_psiB_nonneg (inst.budget_pos k)
          (inst.mmUtil_nonneg fill hfill k)
    exact houter.comp 0 (inst.hasDerivAt_mmUtil_line fill other k)
  have hmmsum :
      HasDerivAt
        (fun t : ℝ => ∑ k : K,
          psiB (inst.budget k)
            (inst.mmUtil (AffineMap.lineMap fill other t) k))
        (∑ k : K,
          psiSlope (inst.budget k) (inst.mmUtil fill k) *
            (inst.mmUtil other k - inst.mmUtil fill k)) 0 :=
    HasDerivAt.fun_sum fun k _ => hmm k
  have hretail := inst.hasDerivAt_retailWelfare_line fill other
  simpa only [FullInstance.innerWelfare, FullInstance.innerDirectional,
    Pi.add_apply] using!
    hmmsum.add hretail

omit [Fintype ι] [Fintype K] [DecidableEq K] in theorem FullInstance.netDemand_line
    (fill other : J → ℝ) (t : ℝ) :
    inst.netDemand (AffineMap.lineMap fill other t) =
      AffineMap.lineMap (inst.netDemand fill) (inst.netDemand other) t := by
  ext s
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module,
    inst.netDemand_linear s fill other (1 - t) t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

omit [Fintype K] [DecidableEq K] in theorem FullInstance.hasDerivAt_minting_line
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (fill other : J → ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        logSumExp b (inst.netDemand (AffineMap.lineMap fill other t)))
      (∑ s : ι, softmax b (inst.netDemand fill) s *
        (inst.netDemand other s - inst.netDemand fill s)) 0 := by
  simpa only [inst.netDemand_line fill other] using
    hasDerivAt_logSumExp_line hb (inst.netDemand fill) (inst.netDemand other)

omit [Fintype J] in private theorem lineMap_mem_box (fill other : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hother : other ∈ (boxFeasible : Set (J → ℝ)))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap fill other t ∈ (boxFeasible : Set (J → ℝ)) := by
  rw [AffineMap.lineMap_apply_module]
  exact convex_boxFeasible hfill hother (sub_nonneg.mpr ht.2) ht.1 (by linarith)

/-- At a positive-temperature clearing optimum, softmax prices make the
    aggregate trader allocation price-taking optimal. -/
theorem FullInstance.traderSurplus_optimal_of_fillOptimal
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.objective b) boxFeasible fill) :
    IsMaxOn
      (inst.traderSurplus (softmax b (inst.netDemand fill)))
      boxFeasible fill := by
  intro other hother
  change
    inst.traderSurplus (softmax b (inst.netDemand fill)) other ≤
      inst.traderSurplus (softmax b (inst.netDemand fill)) fill
  let line : ℝ → J → ℝ := AffineMap.lineMap fill other
  let dinner := inst.innerDirectional fill other
  let dcost :=
    ∑ s : ι, softmax b (inst.netDemand fill) s *
      (inst.netDemand other s - inst.netDemand fill s)
  have hinner :
      HasDerivAt (fun t : ℝ => inst.innerWelfare (line t)) dinner 0 := by
    simpa only [line, dinner] using
      inst.hasDerivAt_innerWelfare_line fill other hfill
  have hcost :
      HasDerivAt
        (fun t : ℝ => logSumExp b (inst.netDemand (line t))) dcost 0 := by
    simpa only [line, dcost] using
      inst.hasDerivAt_minting_line hb fill other
  have hobjective :
      HasDerivAt (fun t : ℝ => inst.objective b (line t))
        (dinner - dcost) 0 := by
    simpa only [inst.objective_eq_innerWelfare_sub_cost, Pi.sub_apply] using!
      hinner.sub hcost
  have hlineMax :
      IsMaxOn (fun t : ℝ => inst.objective b (line t))
        (Set.Icc (0 : ℝ) 1) 0 := by
    intro t ht
    change inst.objective b (line t) ≤ inst.objective b (line 0)
    have h := hopt (lineMap_mem_box fill other hfill hother ht)
    change inst.objective b (line t) ≤ inst.objective b fill at h
    simpa only [line, AffineMap.lineMap_apply_zero] using h
  have hobjective_nonpos :=
    HasDerivAt.nonpos_of_isMaxOn_Icc hobjective hlineMax
  have hline_subset :
      Set.Icc (0 : ℝ) 1 ⊆
        (AffineMap.lineMap fill other) ⁻¹'
          (boxFeasible : Set (J → ℝ)) :=
    fun _ ht => lineMap_mem_box fill other hfill hother ht
  have hconcave :
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
        (fun t : ℝ => inst.innerWelfare (line t)) := by
    simpa only [line, Function.comp_apply] using!
      (inst.concaveOn_innerWelfare.comp_affineMap
        (AffineMap.lineMap fill other)).subset hline_subset
          (convex_Icc (0 : ℝ) 1)
  have hslope := hconcave.slope_le_of_hasDerivAt
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
    zero_lt_one hinner
  have hinner_diff :
      inst.innerWelfare other - inst.innerWelfare fill ≤ dinner := by
    simpa [line, slope] using hslope
  have hpayment_diff :
      dcost =
        outcomeDot (softmax b (inst.netDemand fill))
            (inst.netDemand other) -
          outcomeDot (softmax b (inst.netDemand fill))
            (inst.netDemand fill) := by
    unfold dcost outcomeDot
    simp only [mul_sub, Finset.sum_sub_distrib]
  unfold FullInstance.traderSurplus
  rw [hpayment_diff] at hobjective_nonpos
  linarith

/-- Softmax prices make optimal demand profit-maximizing for the minting sector. -/
theorem supply_optimal_at_softmax
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (demand : ι → ℝ) :
    IsMaxOn
      (supplyProfit b (softmax b demand))
      Set.univ demand := by
  intro other _
  change supplyProfit b (softmax b demand) other ≤
    supplyProfit b (softmax b demand) demand
  simpa only [supplyProfit, outcomeDot] using
    softmax_supply_optimal hb demand other

/-- Aggregate competitive-equilibrium conditions at a common outcome price. -/
structure FullInstance.CompetitiveEquilibrium
    (b : ℝ) (fill : J → ℝ) (price : ι → ℝ) : Prop where
  fill_mem : fill ∈ (boxFeasible : Set (J → ℝ))
  price_mem : price ∈ stdSimplex ℝ ι
  traders_optimal : IsMaxOn (inst.traderSurplus price) boxFeasible fill
  supply_optimal : IsMaxOn (supplyProfit b price) Set.univ
    (inst.netDemand fill)

/-- Every positive-temperature optimum induces a competitive equilibrium. -/
theorem FullInstance.competitiveEquilibrium_of_optimal
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.objective b) boxFeasible fill) :
    inst.CompetitiveEquilibrium b fill
      (softmax b (inst.netDemand fill)) where
  fill_mem := hfill
  price_mem := softmax_mem_stdSimplex b (inst.netDemand fill)
  traders_optimal :=
    inst.traderSurplus_optimal_of_fillOptimal hb fill hfill hopt
  supply_optimal := supply_optimal_at_softmax hb (inst.netDemand fill)

/-- Competitive-equilibrium conditions certify a clearing optimum. -/
theorem FullInstance.CompetitiveEquilibrium.isOptimal
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price) :
    IsMaxOn (inst.objective b) boxFeasible fill := by
  intro other hother
  change inst.objective b other ≤ inst.objective b fill
  have htrader := heq.traders_optimal hother
  change inst.traderSurplus price other ≤
    inst.traderSurplus price fill at htrader
  have hsupply := heq.supply_optimal (Set.mem_univ (inst.netDemand other))
  change supplyProfit b price (inst.netDemand other) ≤
    supplyProfit b price (inst.netDemand fill) at hsupply
  rw [inst.objective_eq_innerWelfare_sub_cost,
      inst.objective_eq_innerWelfare_sub_cost]
  unfold FullInstance.traderSurplus outcomeDot at htrader
  unfold supplyProfit outcomeDot at hsupply
  linarith

/-! ### Agent-by-agent decomposition -/

/-- Retail-order spending at outcome prices. -/
noncomputable def FullInstance.retailSpending (price : ι → ℝ) (fill : J → ℝ) : ℝ :=
  ∑ j : J, if inst.owner j = none then
    outcomeDot price (inst.payoff j) * fill j
  else 0

/-- Aggregate price-taking retail surplus. -/
noncomputable def FullInstance.retailSurplus (price : ι → ℝ) (fill : J → ℝ) : ℝ :=
  inst.retailWelfare fill - inst.retailSpending price fill

/-- Price-taking payoff of one retail order at a scalar fill. -/
noncomputable def FullInstance.retailOrderPayoff
    (price : ι → ℝ) (j : J) (quantity : ℝ) : ℝ :=
  (inst.limitPrice j - outcomeDot price (inst.payoff j)) * quantity

omit [Fintype K] [DecidableEq K] in
/-- Retail surplus separates order by order. -/
theorem FullInstance.retailSurplus_eq_sum_orderPayoffs (price : ι → ℝ) (fill : J → ℝ) :
    inst.retailSurplus price fill =
      ∑ j : J, if inst.owner j = none then
        inst.retailOrderPayoff price j (fill j) else 0 := by
  unfold FullInstance.retailSurplus FullInstance.retailWelfare
    FullInstance.retailSpending FullInstance.retailOrderPayoff
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases howner : inst.owner j = none
  · simp [howner]
    ring
  · simp [howner]

/-- Replace one order's scalar fill. -/
noncomputable def orderPatch (fill : J → ℝ) (j : J) (quantity : ℝ) : J → ℝ := by
  classical
  exact Function.update fill j quantity

omit [Fintype J] in theorem orderPatch_mem_box (fill : J → ℝ) (j : J) (quantity : ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hquantity : quantity ∈ Set.Icc (0 : ℝ) 1) :
    orderPatch fill j quantity ∈
      (boxFeasible : Set (J → ℝ)) := by
  classical
  apply Set.mem_pi.mpr
  intro l _
  by_cases hlj : l = j
  · subst l
    simpa [orderPatch] using hquantity
  · simpa [orderPatch, hlj] using
      Set.mem_pi.mp hfill l trivial

omit [Fintype K] in theorem FullInstance.mmPayoff_orderPatch_retail
    (price : ι → ℝ) (fill : J → ℝ) (j : J)
    (quantity : ℝ) (howner : inst.owner j = none) (k : K) :
    inst.mmPayoff price k (orderPatch fill j quantity) =
      inst.mmPayoff price k fill := by
  have hutil :
      inst.mmUtil (orderPatch fill j quantity) k =
        inst.mmUtil fill k := by
    unfold FullInstance.mmUtil
    apply Finset.sum_congr rfl
    intro l _
    by_cases hlj : l = j
    · subst l
      simp [howner]
    · simp [orderPatch, hlj]
  have hspending :
      inst.mmSpending price (orderPatch fill j quantity) k =
        inst.mmSpending price fill k := by
    unfold FullInstance.mmSpending
    apply Finset.sum_congr rfl
    intro l _
    by_cases hlj : l = j
    · subst l
      simp [howner]
    · simp [orderPatch, hlj]
  unfold FullInstance.mmPayoff
  rw [hutil, hspending]

omit [Fintype K] [DecidableEq K] in theorem FullInstance.retailSurplus_orderPatch
    (price : ι → ℝ) (fill : J → ℝ) (j : J)
    (quantity : ℝ) (howner : inst.owner j = none) :
    inst.retailSurplus price (orderPatch fill j quantity) =
      inst.retailSurplus price fill -
        inst.retailOrderPayoff price j (fill j) +
        inst.retailOrderPayoff price j quantity := by
  classical
  rw [inst.retailSurplus_eq_sum_orderPayoffs,
    inst.retailSurplus_eq_sum_orderPayoffs]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hrest :
      (∑ l ∈ Finset.univ.erase j,
        if inst.owner l = none then
          inst.retailOrderPayoff price l
            (orderPatch fill j quantity l) else 0) =
      ∑ l ∈ Finset.univ.erase j,
        if inst.owner l = none then
          inst.retailOrderPayoff price l (fill l) else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    simp [orderPatch, hlj]
  rw [hrest]
  simp [orderPatch, howner]

theorem FullInstance.demandPayment_eq_agentSpending (price : ι → ℝ) (fill : J → ℝ) :
    outcomeDot price (inst.netDemand fill) =
      (∑ k : K, inst.mmSpending price fill k) +
        inst.retailSpending price fill := by
  have hdot :
      outcomeDot price (inst.netDemand fill) =
        ∑ j : J, outcomeDot price (inst.payoff j) * fill j := by
    unfold outcomeDot FullInstance.netDemand
    calc
      (∑ s : ι, price s * ∑ j : J, fill j * inst.payoff j s) =
          ∑ s : ι, ∑ j : J, price s * (fill j * inst.payoff j s) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
      _ = ∑ j : J, ∑ s : ι, price s * (fill j * inst.payoff j s) :=
        Finset.sum_comm
      _ = ∑ j : J, (∑ s : ι, price s * inst.payoff j s) * fill j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        ring
  rw [hdot]
  unfold FullInstance.mmSpending FullInstance.retailSpending outcomeDot
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases howner : inst.owner j with
  | none =>
      simp
  | some k =>
      simp

/-- Trader surplus is the sum of each MM's payoff and retail surplus. -/
theorem FullInstance.traderSurplus_eq_sum_agentPayoffs (price : ι → ℝ) (fill : J → ℝ) :
    inst.traderSurplus price fill =
      (∑ k : K, inst.mmPayoff price k fill) +
        inst.retailSurplus price fill := by
  rw [FullInstance.traderSurplus, FullInstance.innerWelfare,
    FullInstance.retailSurplus, inst.demandPayment_eq_agentSpending]
  unfold FullInstance.mmPayoff
  rw [Finset.sum_sub_distrib]
  ring

theorem FullInstance.traderSurplus_orderPatch_retail (price : ι → ℝ) (fill : J → ℝ) (j : J)
    (quantity : ℝ) (howner : inst.owner j = none) :
    inst.traderSurplus price (orderPatch fill j quantity) =
      inst.traderSurplus price fill -
        inst.retailOrderPayoff price j (fill j) +
        inst.retailOrderPayoff price j quantity := by
  rw [inst.traderSurplus_eq_sum_agentPayoffs,
    inst.traderSurplus_eq_sum_agentPayoffs,
    inst.retailSurplus_orderPatch price fill j quantity howner]
  have hMM :
      (∑ k : K,
        inst.mmPayoff price k (orderPatch fill j quantity)) =
      ∑ k : K, inst.mmPayoff price k fill := by
    apply Finset.sum_congr rfl
    intro k _
    exact inst.mmPayoff_orderPatch_retail
      price fill j quantity howner k
  rw [hMM]
  ring

/-- Replace precisely the coordinates owned by one MM. -/
noncomputable def FullInstance.ownerPatch (k : K) (base alternative : J → ℝ) (j : J) : ℝ :=
  if inst.owner j = some k then alternative j else base j

omit [Fintype ι] [Fintype J] [Fintype K] in theorem FullInstance.ownerPatch_mem_box
    (k : K) (base alternative : J → ℝ) (hbase : base ∈ (boxFeasible : Set (J → ℝ)))
    (halt : alternative ∈ (boxFeasible : Set (J → ℝ))) :
    inst.ownerPatch k base alternative ∈
      (boxFeasible : Set (J → ℝ)) := by
  apply Set.mem_pi.mpr
  intro j _
  by_cases howner : inst.owner j = some k
  · simpa [FullInstance.ownerPatch, howner] using
      Set.mem_pi.mp halt j trivial
  · simpa [FullInstance.ownerPatch, howner] using
      Set.mem_pi.mp hbase j trivial

omit [Fintype ι] [Fintype K] in theorem FullInstance.mmUtil_ownerPatch_self
    (k : K) (base alternative : J → ℝ) :
    inst.mmUtil (inst.ownerPatch k base alternative) k =
      inst.mmUtil alternative k := by
  unfold FullInstance.mmUtil FullInstance.ownerPatch
  apply Finset.sum_congr rfl
  intro j _
  by_cases howner : inst.owner j = some k <;> simp [howner]

omit [Fintype K] in theorem FullInstance.mmSpending_ownerPatch_self
    (price : ι → ℝ) (k : K) (base alternative : J → ℝ) :
    inst.mmSpending price (inst.ownerPatch k base alternative) k =
      inst.mmSpending price alternative k := by
  unfold FullInstance.mmSpending FullInstance.ownerPatch
  apply Finset.sum_congr rfl
  intro j _
  by_cases howner : inst.owner j = some k <;> simp [howner]

omit [Fintype K] in theorem FullInstance.mmPayoff_ownerPatch_self
    (price : ι → ℝ) (k : K) (base alternative : J → ℝ) :
    inst.mmPayoff price k (inst.ownerPatch k base alternative) =
      inst.mmPayoff price k alternative := by
  unfold FullInstance.mmPayoff
  rw [inst.mmUtil_ownerPatch_self, inst.mmSpending_ownerPatch_self]

omit [Fintype ι] [Fintype K] in theorem FullInstance.mmUtil_ownerPatch_other
    (k l : K) (hkl : l ≠ k) (base alternative : J → ℝ) :
    inst.mmUtil (inst.ownerPatch k base alternative) l =
      inst.mmUtil base l := by
  unfold FullInstance.mmUtil FullInstance.ownerPatch
  apply Finset.sum_congr rfl
  intro j _
  by_cases hownerl : inst.owner j = some l
  · simp [hownerl, hkl]
  · simp [hownerl]

omit [Fintype K] in theorem FullInstance.mmSpending_ownerPatch_other
    (price : ι → ℝ) (k l : K) (hkl : l ≠ k) (base alternative : J → ℝ) :
    inst.mmSpending price (inst.ownerPatch k base alternative) l =
      inst.mmSpending price base l := by
  unfold FullInstance.mmSpending FullInstance.ownerPatch
  apply Finset.sum_congr rfl
  intro j _
  by_cases hownerl : inst.owner j = some l
  · simp [hownerl, hkl]
  · simp [hownerl]

omit [Fintype K] in theorem FullInstance.mmPayoff_ownerPatch_other
    (price : ι → ℝ) (k l : K) (hkl : l ≠ k) (base alternative : J → ℝ) :
    inst.mmPayoff price l (inst.ownerPatch k base alternative) =
      inst.mmPayoff price l base := by
  unfold FullInstance.mmPayoff
  rw [inst.mmUtil_ownerPatch_other k l hkl,
    inst.mmSpending_ownerPatch_other price k l hkl]

omit [Fintype K] in theorem FullInstance.retailSurplus_ownerPatch
    (price : ι → ℝ) (k : K) (base alternative : J → ℝ) :
    inst.retailSurplus price (inst.ownerPatch k base alternative) =
      inst.retailSurplus price base := by
  unfold FullInstance.retailSurplus FullInstance.retailWelfare
    FullInstance.retailSpending FullInstance.ownerPatch
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro j _ <;>
    cases howner : inst.owner j with
    | none => simp
    | some l => simp

/-- Aggregate trader optimality implies each MM's price-taking optimality. -/
theorem FullInstance.mmOptimal_of_tradersOptimal (price : ι → ℝ) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (htraders : IsMaxOn (inst.traderSurplus price) boxFeasible fill)
    (k : K) :
    IsMaxOn (inst.mmPayoff price k) boxFeasible fill := by
  intro alternative halt
  change inst.mmPayoff price k alternative ≤ inst.mmPayoff price k fill
  let patched := inst.ownerPatch k fill alternative
  have h := htraders (inst.ownerPatch_mem_box k fill alternative hfill halt)
  change inst.traderSurplus price patched ≤
    inst.traderSurplus price fill at h
  rw [inst.traderSurplus_eq_sum_agentPayoffs,
    inst.traderSurplus_eq_sum_agentPayoffs] at h
  have hsum :
      (∑ l : K, inst.mmPayoff price l patched) -
          ∑ l : K, inst.mmPayoff price l fill =
        inst.mmPayoff price k alternative -
          inst.mmPayoff price k fill := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ l : K,
          (inst.mmPayoff price l patched -
            inst.mmPayoff price l fill)) =
          ∑ l : K, if l = k then
            inst.mmPayoff price k alternative -
              inst.mmPayoff price k fill
          else 0 := by
            apply Finset.sum_congr rfl
            intro l _
            by_cases hlk : l = k
            · subst l
              simp [patched, inst.mmPayoff_ownerPatch_self]
            · simp only [if_neg hlk, patched,
                inst.mmPayoff_ownerPatch_other price k l hlk, sub_self]
      _ = inst.mmPayoff price k alternative -
            inst.mmPayoff price k fill := by simp
  have hretail :
      inst.retailSurplus price patched =
        inst.retailSurplus price fill := by
    exact inst.retailSurplus_ownerPatch price k fill alternative
  linarith

/-- Aggregate trader optimality implies price-taking optimality of every
    individual retail order. -/
theorem FullInstance.retailOptimal_of_tradersOptimal (price : ι → ℝ) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (htraders : IsMaxOn (inst.traderSurplus price) boxFeasible fill)
    (j : J) (howner : inst.owner j = none) :
    IsMaxOn (inst.retailOrderPayoff price j) (Set.Icc 0 1)
      (fill j) := by
  intro quantity hquantity
  change inst.retailOrderPayoff price j quantity ≤
    inst.retailOrderPayoff price j (fill j)
  have h := htraders
    (orderPatch_mem_box fill j quantity hfill hquantity)
  change inst.traderSurplus price (orderPatch fill j quantity) ≤
    inst.traderSurplus price fill at h
  rw [inst.traderSurplus_orderPatch_retail
    price fill j quantity howner] at h
  linarith

omit [Fintype J] [Fintype K] [DecidableEq K] in
/-- A retail order whose limit value strictly exceeds its outcome price is
    filled completely at every price-taking optimum. -/
theorem FullInstance.retailOrder_full_of_optimal (price : ι → ℝ) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) (j : J)
    (hopt : IsMaxOn (inst.retailOrderPayoff price j) (Set.Icc 0 1)
      (fill j))
    (hprice : outcomeDot price (inst.payoff j) < inst.limitPrice j) :
    fill j = 1 := by
  rcases Set.mem_pi.mp hfill j trivial with ⟨hfillLower, hfillUpper⟩
  have hone := hopt (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
  change inst.retailOrderPayoff price j 1 ≤
    inst.retailOrderPayoff price j (fill j) at hone
  unfold FullInstance.retailOrderPayoff at hone
  nlinarith

omit [Fintype J] [Fintype K] [DecidableEq K] in
/-- A retail order whose outcome price strictly exceeds its limit value is
    rejected at every price-taking optimum. -/
theorem FullInstance.retailOrder_zero_of_optimal (price : ι → ℝ) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) (j : J)
    (hopt : IsMaxOn (inst.retailOrderPayoff price j) (Set.Icc 0 1)
      (fill j))
    (hprice : inst.limitPrice j < outcomeDot price (inst.payoff j)) :
    fill j = 0 := by
  rcases Set.mem_pi.mp hfill j trivial with ⟨hfillLower, hfillUpper⟩
  have hzero := hopt (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
  change inst.retailOrderPayoff price j 0 ≤
    inst.retailOrderPayoff price j (fill j) at hzero
  unfold FullInstance.retailOrderPayoff at hzero
  nlinarith

omit [Fintype J] [Fintype K] [DecidableEq K] in
/-- A partially filled retail order clears exactly at its limit value. -/
theorem FullInstance.retailOrder_price_eq_limit_of_partial
    (price : ι → ℝ) (fill : J → ℝ) (j : J)
    (hopt : IsMaxOn (inst.retailOrderPayoff price j) (Set.Icc 0 1)
      (fill j))
    (hpositive : 0 < fill j) (hpartial : fill j < 1) :
    outcomeDot price (inst.payoff j) = inst.limitPrice j := by
  have hzero := hopt (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
  have hone := hopt (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
  change inst.retailOrderPayoff price j 0 ≤
    inst.retailOrderPayoff price j (fill j) at hzero
  change inst.retailOrderPayoff price j 1 ≤
    inst.retailOrderPayoff price j (fill j) at hone
  unfold FullInstance.retailOrderPayoff at hzero hone
  nlinarith

/-- Agent-by-agent MM and retail optimality reassembles into aggregate trader
    optimality. -/
theorem FullInstance.tradersOptimal_of_agentsOptimal (price : ι → ℝ) (fill : J → ℝ)
    (hMM : ∀ k,
      IsMaxOn (inst.mmPayoff price k) boxFeasible fill)
    (hretail : ∀ j, inst.owner j = none →
      IsMaxOn (inst.retailOrderPayoff price j) (Set.Icc 0 1)
        (fill j)) :
    IsMaxOn (inst.traderSurplus price) boxFeasible fill := by
  intro other hother
  change inst.traderSurplus price other ≤
    inst.traderSurplus price fill
  have hMMSum :
      (∑ k : K, inst.mmPayoff price k other) ≤
        ∑ k : K, inst.mmPayoff price k fill :=
    Finset.sum_le_sum fun k _ => hMM k hother
  have hretailSum :
      inst.retailSurplus price other ≤
        inst.retailSurplus price fill := by
    rw [inst.retailSurplus_eq_sum_orderPayoffs,
      inst.retailSurplus_eq_sum_orderPayoffs]
    apply Finset.sum_le_sum
    intro j _
    by_cases howner : inst.owner j = none
    · simp only [howner, if_true]
      exact hretail j howner
        (Set.mem_pi.mp hother j trivial)
    · simp [howner]
  rw [inst.traderSurplus_eq_sum_agentPayoffs,
    inst.traderSurplus_eq_sum_agentPayoffs]
  linarith

theorem FullInstance.CompetitiveEquilibrium.mmOptimal
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price) (k : K) :
    IsMaxOn (inst.mmPayoff price k) boxFeasible fill :=
  inst.mmOptimal_of_tradersOptimal price fill heq.fill_mem
    heq.traders_optimal k

theorem FullInstance.CompetitiveEquilibrium.retailOptimal
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price) (j : J) (howner : inst.owner j = none) :
    IsMaxOn (inst.retailOrderPayoff price j) (Set.Icc 0 1)
      (fill j) :=
  inst.retailOptimal_of_tradersOptimal price fill heq.fill_mem
    heq.traders_optimal j howner

theorem FullInstance.CompetitiveEquilibrium.retail_full
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price) (j : J) (howner : inst.owner j = none)
    (hprice : outcomeDot price (inst.payoff j) < inst.limitPrice j) :
    fill j = 1 :=
  inst.retailOrder_full_of_optimal price fill heq.fill_mem j
    (heq.retailOptimal inst j howner) hprice

theorem FullInstance.CompetitiveEquilibrium.retail_zero
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price) (j : J) (howner : inst.owner j = none)
    (hprice : inst.limitPrice j < outcomeDot price (inst.payoff j)) :
    fill j = 0 :=
  inst.retailOrder_zero_of_optimal price fill heq.fill_mem j
    (heq.retailOptimal inst j howner) hprice

theorem FullInstance.CompetitiveEquilibrium.retail_price_eq_limit
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price) (j : J) (howner : inst.owner j = none)
    (hpositive : 0 < fill j) (hpartial : fill j < 1) :
    outcomeDot price (inst.payoff j) = inst.limitPrice j :=
  inst.retailOrder_price_eq_limit_of_partial price fill j
    (heq.retailOptimal inst j howner) hpositive hpartial

/-- Competitive equilibrium stated exactly agent by agent, as in the paper. -/
structure FullInstance.AgentCompetitiveEquilibrium
    (b : ℝ) (fill : J → ℝ) (price : ι → ℝ) : Prop where
  fill_mem : fill ∈ (boxFeasible : Set (J → ℝ))
  price_mem : price ∈ stdSimplex ℝ ι
  supply_optimal : IsMaxOn (supplyProfit b price) Set.univ
    (inst.netDemand fill)
  mm_optimal : ∀ k,
    IsMaxOn (inst.mmPayoff price k) boxFeasible fill
  retail_optimal : ∀ j, inst.owner j = none →
    IsMaxOn (inst.retailOrderPayoff price j) (Set.Icc 0 1)
      (fill j)

theorem FullInstance.CompetitiveEquilibrium.toAgent
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price) :
    inst.AgentCompetitiveEquilibrium b fill price where
  fill_mem := heq.fill_mem
  price_mem := heq.price_mem
  supply_optimal := heq.supply_optimal
  mm_optimal := heq.mmOptimal inst
  retail_optimal := heq.retailOptimal inst

theorem FullInstance.AgentCompetitiveEquilibrium.toAggregate
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.AgentCompetitiveEquilibrium b fill price) :
    inst.CompetitiveEquilibrium b fill price where
  fill_mem := heq.fill_mem
  price_mem := heq.price_mem
  traders_optimal :=
    inst.tradersOptimal_of_agentsOptimal price fill
      heq.mm_optimal heq.retail_optimal
  supply_optimal := heq.supply_optimal

theorem FullInstance.AgentCompetitiveEquilibrium.isOptimal
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.AgentCompetitiveEquilibrium b fill price) :
    IsMaxOn (inst.objective b) boxFeasible fill :=
  (heq.toAggregate inst).isOptimal inst

theorem FullInstance.agentCompetitiveEquilibrium_of_optimal
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.objective b) boxFeasible fill) :
    inst.AgentCompetitiveEquilibrium b fill
      (softmax b (inst.netDemand fill)) :=
  (inst.competitiveEquilibrium_of_optimal hb fill hfill hopt).toAgent inst

/-- Exact positive-temperature equivalence between clearing optimality and the
    paper's agent-by-agent competitive-equilibrium conditions. -/
theorem FullInstance.isOptimal_iff_exists_agentCompetitiveEquilibrium
    [Nonempty ι] {b : ℝ} (hb : 0 < b) (fill : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    IsMaxOn (inst.objective b) boxFeasible fill ↔
      ∃ price : ι → ℝ,
        inst.AgentCompetitiveEquilibrium b fill price := by
  constructor
  · intro hopt
    exact ⟨softmax b (inst.netDemand fill),
      inst.agentCompetitiveEquilibrium_of_optimal hb fill hfill hopt⟩
  · rintro ⟨price, heq⟩
    exact heq.isOptimal inst

omit [Fintype K] in
/-- First-order condition for one MM along every feasible fill segment. -/
theorem FullInstance.mmDirectional_nonpos_of_optimal
    (price : ι → ℝ) (k : K) (fill other : J → ℝ)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ)))
    (hother : other ∈ (boxFeasible : Set (J → ℝ)))
    (hopt : IsMaxOn (inst.mmPayoff price k) boxFeasible fill) :
    psiSlope (inst.budget k) (inst.mmUtil fill k) *
          (inst.mmUtil other k - inst.mmUtil fill k) -
        (inst.mmSpending price other k -
          inst.mmSpending price fill k) ≤ 0 := by
  let line : ℝ → J → ℝ := AffineMap.lineMap fill other
  let derivative :=
    psiSlope (inst.budget k) (inst.mmUtil fill k) *
          (inst.mmUtil other k - inst.mmUtil fill k) -
        (inst.mmSpending price other k -
          inst.mmSpending price fill k)
  have hU : 0 ≤ inst.mmUtil fill k :=
    inst.mmUtil_nonneg fill hfill k
  have hψ :
      HasDerivAt
        (fun t : ℝ =>
          psiB (inst.budget k) (inst.mmUtil (line t) k))
        (psiSlope (inst.budget k) (inst.mmUtil fill k) *
          (inst.mmUtil other k - inst.mmUtil fill k)) 0 := by
    have houter :
        HasDerivAt (psiB (inst.budget k))
          (psiSlope (inst.budget k) (inst.mmUtil fill k))
          (inst.mmUtil (line 0) k) := by
      simpa only [line, AffineMap.lineMap_apply_zero] using
        hasDerivAt_psiB_nonneg (inst.budget_pos k) hU
    exact houter.comp 0 (inst.hasDerivAt_mmUtil_line fill other k)
  have hspending :
      HasDerivAt
        (fun t : ℝ => inst.mmSpending price (line t) k)
        (inst.mmSpending price other k -
          inst.mmSpending price fill k) 0 := by
    simpa only [line] using
      inst.hasDerivAt_mmSpending_line price fill other k
  have hpayoff :
      HasDerivAt (fun t : ℝ => inst.mmPayoff price k (line t))
        derivative 0 := by
    simpa only [FullInstance.mmPayoff, derivative] using!
      hψ.sub hspending
  have hlineMax :
      IsMaxOn (fun t : ℝ => inst.mmPayoff price k (line t))
        (Set.Icc (0 : ℝ) 1) 0 := by
    intro t ht
    change inst.mmPayoff price k (line t) ≤
      inst.mmPayoff price k (line 0)
    have h := hopt (lineMap_mem_box fill other hfill hother ht)
    change inst.mmPayoff price k (line t) ≤
      inst.mmPayoff price k fill at h
    simpa only [line, AffineMap.lineMap_apply_zero] using h
  simpa only [derivative] using
    HasDerivAt.nonpos_of_isMaxOn_Icc hpayoff hlineMax

private noncomputable def eraseFill
    (fill : J → ℝ) (j : J) : J → ℝ := by
  classical
  exact Function.update fill j 0

omit [Fintype J] in private theorem eraseFill_mem_box (fill : J → ℝ) (j : J)
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) :
    eraseFill fill j ∈ (boxFeasible : Set (J → ℝ)) := by
  classical
  apply Set.mem_pi.mpr
  intro l _
  by_cases hlj : l = j
  · subst l
    simp [eraseFill]
  · simpa [eraseFill, hlj] using
      Set.mem_pi.mp hfill l trivial

omit [Fintype ι] [Fintype K] in private theorem mmUtil_eraseFill (fill : J → ℝ) (j : J) (k : K)
    (howner : inst.owner j = some k) :
    inst.mmUtil (eraseFill fill j) k =
      inst.mmUtil fill k - inst.limitPrice j * fill j := by
  classical
  unfold FullInstance.mmUtil
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hrest :
      (∑ x ∈ Finset.univ.erase j,
          if inst.owner x = some k then
            inst.limitPrice x * eraseFill fill j x else 0) =
        ∑ x ∈ Finset.univ.erase j,
          if inst.owner x = some k then
            inst.limitPrice x * fill x else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    simp [eraseFill, Function.update, hlj]
  rw [hrest]
  simp [eraseFill, howner]

omit [Fintype K] in private theorem mmSpending_eraseFill
    (price : ι → ℝ) (fill : J → ℝ) (j : J) (k : K) (howner : inst.owner j = some k) :
    inst.mmSpending price (eraseFill fill j) k =
      inst.mmSpending price fill k -
        outcomeDot price (inst.payoff j) * fill j := by
  classical
  unfold FullInstance.mmSpending outcomeDot
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hrest :
      (∑ x ∈ Finset.univ.erase j,
          if inst.owner x = some k then
            (∑ s : ι, price s * inst.payoff x s) *
              eraseFill fill j x else 0) =
        ∑ x ∈ Finset.univ.erase j,
          if inst.owner x = some k then
            (∑ s : ι, price s * inst.payoff x s) * fill x else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    simp [eraseFill, Function.update, hlj]
  rw [hrest]
  simp [eraseFill, howner]

omit [Fintype K] in
/-- **Exact limit-order condition at any price-taking MM optimum.** If an
    MM-owned order receives positive fill, its outcome price is at most its
    limit value shaded by that MM's common scarcity factor. -/
theorem FullInstance.mm_limitPrice_exact_of_optimal
    {fill : J → ℝ} {price : ι → ℝ}
    (hfill : fill ∈ (boxFeasible : Set (J → ℝ))) (k : K)
    (hopt : IsMaxOn (inst.mmPayoff price k) boxFeasible fill)
    (j : J) (howner : inst.owner j = some k)
    (hfilled : 0 < fill j) :
    outcomeDot price (inst.payoff j) ≤
      psiSlope (inst.budget k) (inst.mmUtil fill k) *
        inst.limitPrice j := by
  let other := eraseFill fill j
  have hdir := inst.mmDirectional_nonpos_of_optimal price k fill other
    hfill (eraseFill_mem_box fill j hfill) hopt
  rw [mmUtil_eraseFill inst fill j k howner,
    mmSpending_eraseFill inst price fill j k howner] at hdir
  nlinarith

/-- **Exact limit-order condition.** If an MM-owned order receives positive
    fill at equilibrium, its outcome price is at most its limit value shaded
    by that MM's common scarcity factor. -/
theorem FullInstance.CompetitiveEquilibrium.mm_limitPrice_exact
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price)
    (j : J) (k : K) (howner : inst.owner j = some k)
    (hfilled : 0 < fill j) :
    outcomeDot price (inst.payoff j) ≤
      psiSlope (inst.budget k) (inst.mmUtil fill k) *
        inst.limitPrice j :=
  inst.mm_limitPrice_exact_of_optimal heq.fill_mem k
    (heq.mmOptimal inst k) j howner hfilled

/-- The scarcity factor never exceeds one, so a positively filled MM order
    can never clear above its unshaded limit price. -/
theorem FullInstance.CompetitiveEquilibrium.mm_price_le_limitPrice
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price)
    (j : J) (k : K) (howner : inst.owner j = some k)
    (hfilled : 0 < fill j) :
    outcomeDot price (inst.payoff j) ≤ inst.limitPrice j := by
  have hexact := heq.mm_limitPrice_exact inst j k howner hfilled
  rw [psiSlope_eq_capitalScarcity (inst.budget_pos k)] at hexact
  nlinarith [inst.limitPrice_pos j,
    capitalScarcity_le_one (B := inst.budget k)
      (U := inst.mmUtil fill k) (inst.budget_pos k)]

/-- Consequently every MM in a competitive equilibrium respects its budget. -/
theorem FullInstance.CompetitiveEquilibrium.mmSpending_le_budget
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price) (k : K) :
  inst.mmSpending price fill k ≤ inst.budget k :=
  inst.selfEnforcing_budget_le price k fill heq.fill_mem
    (heq.mmOptimal inst k)

/-- Budget absorption including retained cash: expenditure on fills plus the
    undeployed cash option is at most the MM's budget. -/
theorem FullInstance.CompetitiveEquilibrium.mmSpending_add_retainedCash_le_budget
    {b : ℝ} {fill : J → ℝ} {price : ι → ℝ}
    (heq : inst.CompetitiveEquilibrium b fill price) (k : K) :
    inst.mmSpending price fill k +
        retainedCash (inst.budget k) (inst.mmUtil fill k) ≤
      inst.budget k := by
  exact add_retainedCash_le_of_le_min
    (inst.selfEnforcing_budget price k fill heq.fill_mem
      (heq.mmOptimal inst k))

end FisherClearing
