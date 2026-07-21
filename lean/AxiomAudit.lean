import FisherClearing

/-!
This file is an executable audit of representative top-level paper results.
Run `lake env lean AxiomAudit.lean` and verify that no result reports
`sorryAx`.  The remaining axioms are mathlib's standard classical/foundational
axioms.
-/

#print axioms FisherClearing.fenchelConjugate_mintingCost_eq
#print axioms FisherClearing.fenchelConjugate_logSumExp_eq
#print axioms FisherClearing.logSumExp_sandwich
#print axioms FisherClearing.not_convex_hardBudgetWitnessInstanceSet
#print axioms FisherClearing.contDiff_one_psiB
#print axioms FisherClearing.FullInstance.isOptimal_iff_isLiftedOptimal
#print axioms FisherClearing.FullInstance.isOptimal_iff_exists_agentCompetitiveEquilibrium
#print axioms FisherClearing.FullInstance.isZeroOptimal_iff_exists_agentCompetitiveEquilibrium
#print axioms FisherClearing.FullInstance.softmax_minimizes_priceDual
#print axioms FisherClearing.FullInstance.tendsto_softmax_prices_to_maxEntropy
#print axioms FisherClearing.FullInstance.hardBudget_welfare_gap_sq
#print axioms FisherClearing.FullInstance.comparator_welfare_gap_sq
#print axioms FisherClearing.FullInstance.isZeroOptimal_iff_isZeroConicOptimal
#print axioms FisherClearing.FullInstance.isOptimal_iff_isPositiveConicOptimal
#print axioms FisherClearing.FullInstance.zero_oracle_certificate
#print axioms FisherClearing.SeparableProgram.exactBudgetDecomposition_of_sum
#print axioms FisherClearing.workedFill_isOptimal
