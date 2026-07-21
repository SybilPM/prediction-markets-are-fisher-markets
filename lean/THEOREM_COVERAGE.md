# Paper-to-Lean theorem coverage

This map tracks the main paper `paper.typ`. Names are fully qualified by the
`FisherClearing` namespace unless shown otherwise.

| Paper result | Principal Lean declaration(s) | File |
|---|---|---|
| Minting–Simplex Duality | `fenchelConjugate_mintingCost_eq` | `Duality/MintingSimplex.lean` |
| LMSR–Entropy Duality | `fenchelConjugate_logSumExp_eq` | `Duality/LmsrEntropy.lean` |
| LSE–Max Sandwich | `logSumExp_sandwich` | `Duality/SandwichBound.lean` |
| LMSR = Smoothed Batch Clearing | `hasDerivAt_logSumExp_comp`, `softmax_mem_stdSimplex`, `FullInstance.competitiveEquilibrium_of_optimal` | `Convex/Softmax.lean`, `Clearing/Equilibrium.lean` |
| UCP execution rules | `FullInstance.CompetitiveEquilibrium.retail_full`, `.retail_zero`, `.retail_price_eq_limit` | `Clearing/Equilibrium.lean` |
| Unconstrained Price Uniqueness | `price_unique`; the stronger budgeted result is `FullInstance.softmax_price_unique` | `Clearing/PriceUniqueness.lean`, `Clearing/PriceDual.lean` |
| Computational Obstruction | `not_convex_hardBudgetWitnessInstanceSet` (capital sublevel intersected with the finite order-cap box) | `Clearing/ComputationalObstruction.lean` |
| Reduced-Form MM Utility | `psiB_of_le`, `psiB_of_gt`, `hasDerivAt_psiB_all`, `contDiff_one_psiB`, `concaveOn_psiB_Ici`, `psiB_le_affine`, `psiB_eq_affine_iff`; the retained-cash maximum is `liftedMM_eq_psiB` and `liftedMM_le_psiB` | `ReducedForm/Utility.lean`, `Clearing/DeployedValue.lean` |
| Self-Enforcing Budgets | `FullInstance.selfEnforcing_budget` | `Clearing/SelfEnforcing.lean` |
| Deployed-Value Lift | `FullInstance.isOptimal_iff_isLiftedOptimal` | `Clearing/LiftedProgram.lean` |
| Reduced-Form Clearing with Budgeted MMs | `FullInstance.concaveOn_objective`, `.exists_optimal_fill`, `.concaveOn_objectiveZero`, `.exists_optimal_fill_zero`, equilibrium budget and exact-limit theorems | `Clearing/FullProgram.lean`, `Clearing/ZeroTemperature.lean`, `Clearing/Equilibrium.lean`, `Clearing/ZeroEquilibrium.lean` |
| Demand-Space Concavity | `FullInstance.concaveOn_demandValue`, `.fillOptimal_iff_fiber_and_demandOptimal` | `Clearing/DemandSpace.lean` |
| Clearing = Competitive Equilibrium | `FullInstance.isOptimal_iff_exists_agentCompetitiveEquilibrium`, `.isZeroOptimal_iff_exists_agentCompetitiveEquilibrium` | `Clearing/Equilibrium.lean`, `Clearing/MaximumEntropy.lean` |
| Risk-Averse Price Dual | `FullInstance.clearing_le_priceDual`, `.softmax_minimizes_priceDual`; zero-temperature strong duality is `.ZeroCompetitiveEquilibrium.strongDuality` | `Clearing/PriceDual.lean`, `Clearing/ZeroEquilibrium.lean` |
| Maximum-Entropy Price Selection | `FullInstance.tendsto_regularized_prices_to_maxEntropy`, `.tendsto_softmax_prices_to_maxEntropy` | `Clearing/MaximumEntropy.lean` |
| Unique Observables | `FullInstance.deployedValue_unique`, `.capitalScarcity_unique`, `.mmUtil_unique_of_budget_lt`, `.exists_netDemand_add_const` | `Clearing/UniqueObservables.lean` |
| Risk-Neutral Recovery | `FullInstance.riskNeutral_recovery` | `Clearing/RiskNeutral.lean` |
| Welfare Gap Bound | `FullInstance.comparator_welfare_gap`, `.comparator_welfare_gap_sq` (any feasible comparator, with risk-neutral optima as a corollary) | `Clearing/RiskNeutral.lean` |
| Feasible Approximation of Hard-Budget Clearing | `FullInstance.hardBudgetFeasible_of_optimal`, `.hardBudget_welfare_gap`, `.hardBudget_welfare_gap_sq` | `Clearing/RiskNeutral.lean` |
| Conic Reformulation | `FullInstance.isZeroOptimal_iff_isZeroConicOptimal`, `.isOptimal_iff_isPositiveConicOptimal` | `Clearing/ConicReformulation.lean` |
| LP-Oracle Certificate | `FullInstance.zero_oracle_certificate`, `.zeroOracleGap_nonneg`, `.exactLineSearch_nondecreasing` | `Clearing/OracleCertificate.lean` |
| Exact Budget Decomposition | `SeparableProgram.exactBudgetDecomposition_of_sum`, `.monolithicSlope_of_componentSlopes`, `commonSlope_of_retainedCash_split`, `proportionalComponentBudgets_sum_of_total` | `Clearing/BudgetDecomposition.lean` |

## Checked unnumbered claims

- Positive-temperature objectives uniformly approximate the zero-temperature
  objective: `FullInstance.objective_sandwich_zero`.
- Every cluster point of positive-temperature optimal fills as `b → 0⁺` is
  zero-temperature optimal:
  `FullInstance.clusterPoint_of_optimal_fills_is_zeroOptimal`.
- Prices converge to uniform as `b → ∞`, even when feasible fills vary with
  temperature: `FullInstance.tendsto_softmax_prices_to_uniform`.
- MM capital plus retained cash is at most budget at both temperatures:
  `CompetitiveEquilibrium.mmSpending_add_retainedCash_le_budget` and its
  `ZeroCompetitiveEquilibrium` counterpart.
- Buy/sell complement reduction:
  `buySellReduction_logSumExp`, `buySellReduction_maxFin`.
- The shared supporting-tangent engine used by the LP oracle and
  decomposition: `sum_psiB_le_tangent`.
- Independent-group minting factorization and price marginals:
  `logSumExp_product_add`, `maxFin_product_add`,
  `softmax_product_fst_marginal`, `softmax_product_snd_marginal`.
- The numerical worked example, including both optima, welfare values,
  scarcity `5/7`, and spending `40`: declarations prefixed `worked` in
  `Clearing/WorkedExample.lean`.

## Scope boundary

The formal model is finite-dimensional and proves the exact optimization,
duality, equilibrium, welfare, conic-reduction, and decomposition statements.
The following portions of the paper are intentionally not represented as Lean
theorems:

- held-out benchmark observations and figures;
- literature attribution and open problems;
- the generic theorem that a third-party exponential-cone implementation runs
  in polynomial time; and
- external probabilistic-inference complexity classifications.

The exact exponential-cone encodings and their optimizer equivalences are
proved, but a verified implementation and bit-complexity analysis of a conic
interior-point solver are not part of this repository.
