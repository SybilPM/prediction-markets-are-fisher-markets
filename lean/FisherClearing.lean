-- FisherClearing: Lean 4 formalization of "Prediction Markets Are Fisher Markets"
--
-- This umbrella imports the complete machine-checked mathematical
-- formalization of the main paper.  See THEOREM_COVERAGE.md for the
-- paper-to-Lean theorem map and scope boundary.

import FisherClearing.Convex.LogSumExp
import FisherClearing.Convex.Softmax
import FisherClearing.Duality.SandwichBound
import FisherClearing.Convex.FenchelConjugate
import FisherClearing.Duality.MintingSimplex
import FisherClearing.Duality.LmsrEntropy
import FisherClearing.ReducedForm.Utility
import FisherClearing.ReducedForm.LpRecovery
import FisherClearing.ReducedForm.WelfareGap
import FisherClearing.Clearing.PriceUniqueness
import FisherClearing.Clearing.DeployedValue
import FisherClearing.Clearing.DemandSpace
import FisherClearing.Clearing.Equilibrium
import FisherClearing.Clearing.FullProgram
import FisherClearing.Clearing.ConicReformulation
import FisherClearing.Clearing.ComputationalObstruction
import FisherClearing.Clearing.BudgetDecomposition
import FisherClearing.Clearing.LiftedProgram
import FisherClearing.Clearing.MarketIdentities
import FisherClearing.Clearing.MaximumEntropy
import FisherClearing.Clearing.OracleCertificate
import FisherClearing.Clearing.PriceDual
import FisherClearing.Clearing.RiskNeutral
import FisherClearing.Clearing.SelfEnforcing
import FisherClearing.Clearing.UniqueObservables
import FisherClearing.Clearing.ZeroEquilibrium
import FisherClearing.Clearing.ZeroTemperature
import FisherClearing.Clearing.WorkedExample
