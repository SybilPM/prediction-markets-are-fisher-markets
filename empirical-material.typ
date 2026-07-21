#set document(title: "Empirical Material for Prediction Markets Are Fisher Markets")
#set text(font: "New Computer Modern", size: 10pt)
#set page(margin: (x: 1.25in, y: 1.05in), numbering: "1")
#set par(justify: true, leading: 0.55em)
#set heading(numbering: "1.")
#show heading.where(level: 1): it => block(above: 1.4em, below: 0.7em)[#it]
#show heading.where(level: 2): it => block(above: 1.1em, below: 0.5em)[#it]
#show figure.caption: set text(size: 9pt)

#let caveat(body) = block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("fff7ed"),
  stroke: (left: 1.5pt + rgb("c2410c")),
)[#text(weight: "bold")[Reporting constraint. ]#body]

#let recommendation(body) = block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("eff6ff"),
  stroke: (left: 1.5pt + rgb("1d4ed8")),
)[#text(weight: "bold")[Recommended paper treatment. ]#body]

#let header-cell(body) = table.cell(fill: rgb("f3f4f6"), [#text(weight: "bold")[#body]])

#align(center)[
  #text(size: 15pt, weight: "bold")[
    Empirical Material for _Prediction Markets Are Fisher Markets_
  ]
  #v(0.45em)
  #text(size: 10.5pt)[Preregistered solver evaluation, negative results, and integration draft]
  #v(0.3em)
  #text(size: 9pt, style: "italic")[Standalone research note — 13 July 2026]
]

#v(0.8em)

#block(inset: (x: 1.5em))[
  #text(weight: "bold")[Status.]
  This is integration material, not part of the paper and not a polished empirical section.
  It records the complete first preregistered experiment before any solver tuning prompted by
  its results. It is intentionally more conservative than the current preliminary-validation
  paragraph in `paper.typ`. Its LP-default recommendation is now historical: the replacement
  retained-cash solver and the complete held-out v2 evaluation are documented separately in
  `empirical-retained-cash-v2.typ`. V1 remains unchanged evidence about the implementations it
  actually measured.
]

= Executive finding

The new experiment supports the _mathematical relevance_ of the retained-cash
quasilinear-Fisher objective, but not the _operational robustness_ of its current conic
implementation. Conditional on returning a valid result, the conic quasilinear-Fisher solver
often lies very close to the production LP: its median LP-relative welfare shortfall is
$0.034%$ over all 123 successful observations. But it fails numerically in 35 of 158 declared
runs. Those failures are part of the result, not an implementation detail that may be omitted.

The budget sweep also overturns the previous single-book headline. At the tightest budget
multiplier, $0.1 times$, all ten conic runs succeed but the mean LP-relative shortfall is
$3.488%$ with a paired bootstrap 95% interval of $[2.288%, 4.753%]$. The shortfall falls to
$0.031%$ at the default multiplier and to numerical zero among successful observations at
$1.5 times$ and $3 times$, consistent with qualitative LP recovery as budgets become slack.
It is not correct to claim a gap below $0.7%$ over the full sweep.

#caveat[
  Every welfare and runtime statistic below that is not a count is conditional on solver
  success. A conditional quality estimate may be optimistic when hard instances are more
  likely to fail. Every such statistic must therefore be printed with its
  successful/declared denominator.
]

= Provenance and anti-selection protocol

The implementation was frozen before measurement at Sybil revision
#link("https://github.com/MetaB0y/sybil/tree/831dda777e1bc11fb66a13d335401284868a3f03")[
  `831dda777e1bc11fb66a13d335401284868a3f03`
]. Protocol `solver-evaluation-v1` declares every scenario family, seed, budget point, solver,
iteration limit, time limit, metric, and exclusion rule. The complete retained run contains
675 rows over 158 independently generated scenario groups.

The runner writes one row for every declaration, including panics, numerical failures, empty
results, verifier failures, iteration limits, and timeouts. The analysis rejects missing,
duplicate, or unexpected keys and rejects a scenario group unless every solver receives the
same problem fingerprint. The retained run has 675/675 observations, no missing or duplicate
keys, no unexpected keys, and no cross-solver fingerprint mismatches.

Research solvers do not silently substitute LP. This is a substantive difference from the
historical prototype: a failed conic or EG request now remains a failed conic or EG observation.
Explicit delegation is allowed only when the requested mathematical objective reduces to LP,
for example Conic Linear mode or a problem with no market-maker orders.

Solver order rotates within scenario groups, and a declared warm-up precedes timing. Welfare is
recomputed by the integer verifier after the signed complete-set mint/burn adjustment; backend
floating objectives are not used for ranking. The run took 242 seconds on an AMD Ryzen 7 5800X
with 32 GB RAM under Linux 6.6.144 and Rust 1.97.0. The protocol BLAKE3, host metadata, raw
JSONL, generated summaries, and analysis-script SHA-256 are checked into result revision
#link("https://github.com/MetaB0y/sybil/tree/bd47c8d9cb30e48894854c411a45e1bdd40d5211/benchmarks/solver/results/2026-07-13-v1")[
  `bd47c8d9cb30e48894854c411a45e1bdd40d5211`
]. The distinct frozen revision identifies the exact runner and solver code used to create the
observations; the result revision adds the immutable raw data, deterministic analysis, report,
and a post-run conformance-diagnostic correction without rerunning or rewriting the observations.

== Declared suites

- _Quality:_ balanced, concentrated-liquidity, asymmetric-depth, and buy-heavy stress books;
  12 medium-scale seeds per profile.
- _Scaling:_ 300, 3,000, 10,000, and 30,000 declared retail orders; respectively 8, 8, 8,
  and 5 seeds.
- _Budget:_ ten paired medium books at MM budget multipliers 0.1, 0.3, 0.5, 1, 1.5, and 3.
- _Decomposition:_ monolithic and decomposed LP/quasilinear-Fisher on balanced and asymmetric
  books; eight seeds per profile.
- _Exact reference:_ five small books with LP, conic quasilinear-Fisher, and a three-second
  SCIP MILP limit.

The generator varies heavy-tailed order size, buy/sell imbalance, hot-market concentration,
liquidity depth and dispersion, market-group incidence, and MM market coverage. These are
structural synthetic stresses. They are not calibrated samples of production order flow.

= Questions and estimands

The experiment addresses five narrower questions than “does the theorem work?”

+ _Validity and reliability._ Does a solver return a non-empty candidate that passes the
  independent integer verifier, and what termination state does it report?
+ _Operational welfare._ How far is each valid result from the monolithic production LP on the
  identical book? LP is a deployed reference, not asserted to be the hard-budget global optimum.
+ _Budget recovery._ Does the quasilinear-Fisher solution approach the LP solution as MM budgets
  become slack, and what happens under severe scarcity?
+ _Scaling._ How do successful-run wall times and failure rates change with the declared order
  count on one machine?
+ _Exactness and decomposition._ On tiny instances, how often does MILP prove an optimum and how
  closely does LP track it? On separable books, what do decomposition and its coordination cap
  cost?

The experiment does _not_ yet test the instance-wise quadratic guarantee
$sum_k Delta_k^2 / (2 B_k)$. It does not record the bound for each instance, so the budget sweep
is evidence about qualitative recovery, not quantitative verification of the theorem's bound.

= Main results

== Reliability, termination, and runtime

#figure(
  table(
    columns: (1.7fr, 0.85fr, 0.8fr, 0.65fr, 0.9fr, 0.9fr),
    inset: 4.5pt,
    align: (left, center, center, center, right, right),
    header-cell[Solver], header-cell[Valid / declared], header-cell[At cap],
    header-cell[Failed], header-cell[Median time], header-cell[Median LP gap],
    [LP], [158/158], [0], [0], [0.0269 s], [0.000%],
    [IterLP], [137/137], [10], [0], [0.2548 s], [0.295%],
    [EG Frank–Wolfe], [137/137], [92], [0], [0.5710 s], [0.681%],
    [Conic quasi-Fisher], [123/158], [0], [35], [0.0868 s], [0.034%],
    [Conic Fisher], [46/48], [0], [2], [0.1026 s], [0.053%],
    [Decomposed LP], [16/16], [11], [0], [0.5894 s], [0.000%],
    [Decomposed quasi], [13/16], [8], [3], [1.3275 s], [1.918%],
    [MILP reference], [4/5], [0], [1], [0.0529 s], [0.000%],
  ),
  caption: [All declared observations. Runtime and welfare columns use successful observations;
  the denominator and iteration-cap columns prevent those conditional summaries from being
  read as unconditional reliability.],
) <tab-reliability>

All 634 returned candidates passed the independent verifier. The remaining 41 declarations
were 40 numerical failures and one MILP timeout. A valid result is not necessarily converged:
EG reached its iteration limit in 92/137 observations, IterLP in 10/137, decomposed LP in 11/16,
and decomposed quasi-Fisher in 8/16.

The production LP is the only evaluated method combining perfect return rate, reported
convergence, verifier validity, and the lowest overall median time. IterLP is approximately
9.5 times slower and EG approximately 21 times slower by the mixed-suite medians. The successful
conic median is approximately 3.2 times the LP median, but this comparison conditions away 35
conic failures and must not be presented alone.

== Heterogeneous quality profiles

#figure(
  table(
    columns: (1.65fr, 0.85fr, 0.85fr, 1fr, 0.85fr, 0.85fr),
    inset: 4.5pt,
    align: (left, right, right, right, center, center),
    header-cell[Profile], header-cell[IterLP], header-cell[EG],
    header-cell[Quasi-Fisher], header-cell[Quasi success], header-cell[Fisher success],
    [Asymmetric depth], [0.491%], [0.309%], [0.000%], [11/12], [11/12],
    [Balanced], [0.219%], [0.446%], [0.467%], [10/12], [12/12],
    [Buy-heavy stress], [0.659%], [1.125%], [0.000%], [9/12], [12/12],
    [Concentrated], [0.290%], [0.957%], [0.034%], [9/12], [11/12],
  ),
  caption: [Median LP-relative welfare shortfall among successful quality-suite observations.
  LP is zero by construction. Fisher quality is omitted from the gap columns to keep the table
  compact; its profile medians are respectively 0.032%, 0.467%, 0.065%, and 0.045%.],
) <tab-quality>

The quasilinear-Fisher solver exactly or nearly recovers LP on many asymmetric and buy-heavy
books. The balanced profile is a useful counterexample to a universal near-identity statement,
and numerical failures appear in every quality profile except none is privileged as an
exclusion. EG's larger gaps and high cap rate show that returning a valid allocation alone is
not enough to validate the no-cash algorithm empirically.

== Paired budget sweep

#figure(
  table(
    columns: (0.85fr, 1fr, 1fr, 1.1fr, 1fr, 1.45fr),
    inset: 4.5pt,
    align: (right, right, right, right, center, center),
    header-cell[Budget], header-cell[IterLP mean], header-cell[EG mean],
    header-cell[Quasi mean], header-cell[Quasi success], header-cell[Quasi bootstrap 95%],
    [0.1×], [0.191%], [3.993%], [3.488%], [10/10], [[2.288%, 4.753%]],
    [0.3×], [0.268%], [3.335%], [1.660%], [8/10], [[0.849%, 2.524%]],
    [0.5×], [0.280%], [2.000%], [0.733%], [8/10], [[0.264%, 1.319%]],
    [1×], [0.301%], [0.637%], [0.031%], [9/10], [[0.001%, 0.073%]],
    [1.5×], [0.301%], [0.689%], [0.000%], [7/10], [[−0.000%, 0.000%]],
    [3×], [0.305%], [0.227%], [0.000%], [8/10], [[0.000%, 0.000%]],
  ),
  caption: [Mean LP-relative welfare shortfall on ten paired books at each MM budget multiplier.
  Intervals use 10,000 seed-level bootstrap resamples with a fixed seed. Quasi-Fisher means and
  intervals condition on success; the success column remains part of the result.],
) <tab-budget>

This is the cleanest qualitative evidence for the paper's recovery story. Quasilinear-Fisher
welfare approaches LP welfare when budgets are slack, while severe scarcity creates a visible
cost. The result is stronger scientifically than the old claim because it shows both where
recovery occurs and where it does not. Numerical reliability is non-monotone in the multiplier,
so the retained-cash variable cannot yet be said to make the implementation uniformly
well-conditioned.

== Scaling and numerical fragility

#figure(
  table(
    columns: (1.2fr, 0.9fr, 0.9fr, 0.9fr, 1.7fr),
    inset: 4.5pt,
    align: (right, right, right, right, center),
    header-cell[Retail orders], header-cell[LP], header-cell[IterLP], header-cell[EG],
    header-cell[Quasi valid / median valid time],
    [300], [0.0033 s], [0.0271 s], [0.0684 s], [8/8 / 0.0093 s],
    [3,000], [0.0260 s], [0.2354 s], [0.5549 s], [2/8 / 0.0819 s],
    [10,000], [0.1097 s], [1.0823 s], [2.6138 s], [3/8 / 0.3422 s],
    [30,000], [0.4649 s], [4.7761 s], [5.0078 s], [2/5 / 1.2923 s],
  ),
  caption: [Successful-run median wall time on the scaling suite. Conic failure counts are a
  first-class scaling outcome; the apparently competitive conic times do not characterize a
  reliable exchange-scale method.],
) <tab-scaling>

LP scales regularly and succeeds throughout. IterLP and EG also return verifier-valid candidates
throughout, although EG is often capped. Conic quasi-Fisher succeeds in only 7 of the 21 declared
medium-to-xlarge scaling runs. This directly contradicts the current paper's unqualified phrase
“retained cash keeps the cone well-conditioned” and weakens “practical at exchange scale” from an
empirical claim to an implementation goal.

== Decomposition and exact reference

Decomposed LP reproduces monolithic LP welfare and allocation in all 16 separable-book runs, but
is slower and reaches its coordination cap in 11. On balanced books its median is 0.575 seconds
versus 0.026 seconds for monolithic LP; on asymmetric books, 0.886 versus 0.047 seconds.
Decomposed quasi-Fisher succeeds in 13/16 runs, reaches its cap in eight, and has a 1.918% overall
median LP-relative shortfall. Three asymmetric component solves fail numerically, and the runner
propagates those failures rather than assembling a partial result.

This is a negative operational result on independent single-market groups, not a test of the
paper's intended combinatorial regime. No experiment here varies bundle-coupling treewidth or
compares full joint-state enumeration with component inference. The asymptotic decomposition
claim therefore remains theoretically motivated and empirically open.

SCIP proves four of the five tiny MILP references optimal and times out at three seconds on one.
LP agrees with the four proven optima to integer-rounding precision. This validates a small
regression stratum only. It does not establish global LP exactness, and the timeout incumbent is
not relabeled as an optimum.

= What the paper may and may not claim

#recommendation[
  Replace the current preliminary-validation paragraph. Present the experiment as a transparent
  first evaluation with a positive conditional recovery result, a negative numerical-reliability
  result, and a negative independent-market decomposition result. Do not use the experiment to
  claim direct validation of the quadratic bound, production readiness of the conic solver, or a
  decomposition speedup.
]

Supported statements:

- On a preregistered synthetic suite, valid quasilinear-Fisher solutions are often close to the
  production LP, with a 0.034% median shortfall over 123 valid observations.
- Paired budget sweeps show qualitative LP recovery as MM budgets become slack, and materially
  larger gaps under severe scarcity.
- All returned allocations pass the independent integer verifier.
- The current conic implementation is numerically fragile: 35/158 declarations fail, with
  reliability deteriorating outside the small scaling stratum.
- Monolithic LP is the best current production choice on these workloads.
- Decomposition adds overhead on already separable independent-market books; the bundle-order
  regime remains unmeasured.

Unsupported statements:

- “The gap is below 0.7% at all budget scales.”
- “Retained cash keeps the conic program well-conditioned” without qualification.
- “The conic solve is practical at exchange scale” as an empirical conclusion.
- “The experiment verifies the quadratic welfare guarantee.”
- “Decomposition preserves 98–99% of welfare” without current denominators, failure counts, and
  an explicit workload definition.
- “LP is the exact hard-budget optimum” beyond the four tiny proven MILP instances.

== Insert-ready replacement for the validation paragraph

#block(inset: (x: 1em), stroke: (left: 1pt + luma(170)))[
  _Empirical evaluation._ We preregistered a synthetic evaluation spanning 675 solver runs over
  158 independently generated order books, retaining every numerical failure, iteration cap,
  timeout, and verifier rejection. Every solver in a comparison received an identical
  fingerprint-checked problem, and welfare was recomputed in integer arithmetic by an independent
  verifier. Conditional on success, the quasilinear-Fisher conic program often closely tracks the
  production LP: across 123 successful observations its median LP-relative welfare shortfall is
  0.034%. A paired budget sweep shows the predicted qualitative recovery as MM budgets become
  slack—mean shortfall falls from 3.488% at a 0.1× multiplier to 0.031% at 1× and numerical zero
  among successful observations at 1.5× and 3×. These conditional quality results come with an
  important negative result: the conic implementation fails numerically in 35 of 158 declarations
  and succeeds in only 7 of 21 medium-to-xlarge scaling runs. Thus the experiment supports the
  economic recovery pattern but not yet a claim of numerically robust exchange-scale conic
  clearing. The monolithic LP remains the production solver; it returns a converged,
  verifier-valid result in all 158 declarations and has a 26.9 ms overall median wall time.
]

== Suggested abstract and open-problem edits

In the abstract, replace “Exponential-cone formulations make clearing practical at exchange
scale” with:

#block(inset: (x: 1em), stroke: (left: 1pt + luma(170)))[
  The clearing program admits a standard exponential-cone formulation; developing a numerically
  robust exchange-scale implementation remains an engineering and empirical question.
]

Replace the open-problem sentence asserting gaps below 0.7% with:

#block(inset: (x: 1em), stroke: (left: 1pt + luma(170)))[
  A preregistered synthetic budget sweep exhibits the predicted recovery as budgets become slack,
  but mean LP-relative shortfall rises to 3.488% at the tightest tested multiplier. Measuring the
  instance-wise ratio between observed shortfall and the quadratic bound—on both frozen replay
  data and adversarial books—remains open.
]

= Limitations and next experiment

This is a solver-only experiment on one machine. It does not measure end-to-end sequencer latency,
peak resident memory, CPU cycles, concurrency interference, or deployed traffic. Timing varies
books and rotates order, but uses only one timed observation per solver/book. All books are
synthetic, and all orders are single-market; there are no spreads, conditional bundles, or
joint-state inference workloads.

Version 2 should be preregistered under a new protocol ID rather than editing version 1. It should
freeze the following before running:

+ A replay corpus derived from anonymized production data or frozen public-market statistics,
  kept separate from synthetic stress strata.
+ Peak RSS, CPU time, iteration count, primal and dual residuals, objective traces, conditioning
  diagnostics, and end-to-end sequencer latency.
+ The theorem's per-instance quadratic bound and a primary statistic for measured-gap/bound ratio.
+ Numerical-scale adversaries and near-zero deployed-value cases for the conic formulation.
+ A difficulty-stratified exact-reference suite that produces both proven MILP optima and honest
  timeouts.
+ Bundle-coupling strata varying connected-component size, treewidth, and cross-group order
  density, so the decomposition claim is tested in its intended regime.
+ Held-out seeds or a new frozen corpus for every tuning decision prompted by version 1. Reusing
  version 1 after tuning is a regression check, not an unbiased performance estimate.

= Artifact-to-paper checklist

Before integrating these paragraphs into `paper.typ`:

- cite Sybil result commit `bd47c8d9cb30e48894854c411a45e1bdd40d5211`, not only the frozen
  runner revision;
- preserve successful/declared denominators in every table and caption;
- publish the raw JSONL, protocol, machine metadata, and analysis hash;
- distinguish verifier validity from convergence and from global optimality;
- label LP as the operational comparator and MILP as exact only on proven-optimal rows;
- state that bootstrap intervals condition on solver success and synthetic-book variation;
- retain the numerical-failure and timeout rows in the main text or an immediately adjacent table;
  and
- do not tune the current solver and then present the same protocol as confirmatory evidence.

The most valuable empirical contribution is not a uniformly positive performance claim. It is a
reproducible map of where the Fisher-market formulation already behaves as predicted, where the
implementation fails, and what a genuinely confirmatory next experiment must measure.
