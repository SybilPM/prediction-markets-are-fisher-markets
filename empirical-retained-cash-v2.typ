#set document(title: "Retained-Cash Clearing: Empirical Material for Prediction Markets Are Fisher Markets")
#set text(font: "New Computer Modern", size: 10pt)
#set page(margin: (x: 1.2in, y: 1.0in), numbering: "1")
#set par(justify: true, leading: 0.55em)
#set heading(numbering: "1.")
#show heading.where(level: 1): it => block(above: 1.4em, below: 0.7em)[#it]
#show heading.where(level: 2): it => block(above: 1.1em, below: 0.5em)[#it]
#show figure.caption: set text(size: 9pt)

#let header-cell(body) = table.cell(
  fill: rgb("f3f4f6"),
  [#text(weight: "bold")[#body]],
)

#let evidence(body) = block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("eff6ff"),
  stroke: (left: 1.5pt + rgb("1d4ed8")),
)[#text(weight: "bold")[Empirical conclusion. ]#body]

#let caveat(body) = block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("fff7ed"),
  stroke: (left: 1.5pt + rgb("c2410c")),
)[#text(weight: "bold")[Reporting constraint. ]#body]

#let revision(body) = block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("f5f3ff"),
  stroke: (left: 1.5pt + rgb("7c3aed")),
)[#text(weight: "bold")[Suggested paper revision. ]#body]

#align(center)[
  #text(size: 15pt, weight: "bold")[
    Retained-Cash Clearing: Empirical Material for
    _Prediction Markets Are Fisher Markets_
  ]
  #v(0.4em)
  #text(size: 10.5pt)[Certified oracle solving, adversarial flash liquidity, and honest negative results]
  #v(0.3em)
  #text(size: 9pt, style: "italic")[Standalone integration note — 13 July 2026]
]

#v(0.8em)

#block(inset: (x: 1.5em))[
  #text(weight: "bold")[Status.]
  This is material for later integration, not a silently edited empirical section of
  `paper.typ`. It supersedes the implementation recommendation in `empirical-material.typ`
  while preserving that document as the complete v1 negative result. V2 was specified and
  frozen before its held-out seeds were run.
]

= Executive result

The implementation now follows the paper's retained-cash objective directly. It applies
generalized Frank–Wolfe to the zero-temperature concave program, using a HiGHS matching LP
as its linear oracle and exact one-dimensional concave line search. The method has a
computable upper bound on continuous objective suboptimality. It replaces two historical
implementations that did not have the convergence semantics their names suggested: a
damped IterLP fixed point and a forced-step no-cash EG loop.

On the complete held-out evaluation, retained-cash Frank–Wolfe (RC-FW) returns a
verifier-valid, hard-budget-feasible landed allocation in 135 of 135 declared problems.
It meets the configured certificate tolerance in 110 and reaches the fixed 100-update cap
in 25. Its median wall time is 37.5 ms; its 95th percentile is 2.13 s. The median relative
certificate gap is zero, the 95th percentile is $0.0374%$, and the maximum is $0.1159%$ on
a deliberately heavy-tailed numerical-range stress.

#evidence[
  The experiment supports the paper's algorithmic structure: a convergent,
  certificate-bearing LP-oracle method is reliable where a generic exponential-cone
  implementation is not. It does not support claiming uniformly LP-like latency or
  claiming that the configured 100-update product policy converges on every book.
]

The independent Clarabel QuasiFisher formulation succeeds in 114/135 declarations and
fails with `InsufficientProgress` in 21. Conditional on success it is fast (5.9 ms median)
and extremely close to the best observed retained-cash objective. The failures are part of
the result. Clarabel is useful corroboration, not the supported production algorithm.

#caveat[
  Every failure, verifier rejection, iteration limit, and timeout remains in its declared
  denominator. Runtime and quality summaries are conditional on verifier-valid success and
  must be printed with that denominator. “Observed-best objective gap” is a comparison among
  returned landed allocations, not an optimality certificate.
]

= Algorithm evaluated

== Shifted retained-cash objective

For MM $k$, let $U_k(q)$ be the total value of its fills after applying the paper's
buy/sell reduction: an ask at limit $L$ is a complementary-outcome buy with value $1-L$.
Let $B_k$ be its shared capital. Constants that do not affect the allocation are removed,
giving

$
psi_B(U) = cases(
  U & "if" U <= B,
  B (1 + ln(U/B)) & "if" U > B.
)
$

With $H(q)$ denoting retail surplus, the linear correction introduced by the ask reduction,
and negative zero-temperature minting cost, the implemented objective is

$ F(q) = H(q) + sum_k psi_(B_k)(U_k(q)). $

$H$ is concave polyhedral and each $psi_B circle U_k$ is concave. At iterate $q_t$, MM $k$
has pacing factor

$ alpha_(k,t) = min(1, B_k / U_k(q_t)). $

The linear oracle returns

$
s_t in arg max_(s in Q)\
  { H(s) + sum_k alpha_(k,t) U_k(s) },
$

where $Q$ contains order bounds and matching/minting constraints but no bilinear MM budget
row. This is an ordinary matching LP. The update is

$ q_(t+1) = (1-gamma_t) q_t + gamma_t s_t, $

with $gamma_t in [0,1]$ chosen by bisection on the exact monotone directional derivative.
The implementation guards objective monotonicity against floating-point line-search noise.

== Certificate

Define

$
G(q_t) = H(s_t) - H(q_t)
  + sum_k alpha_(k,t) (U_k(s_t)-U_k(q_t)).
$

Concavity of the smooth MM terms and optimality of $s_t$ in the generalized oracle imply

$ 0 <= F(q^*) - F(q_t) <= G(q_t). $

Thus $G(q_t)$ is an instance-specific upper bound, unlike a difference between consecutive
pacing multipliers. The configured stop is

$ G(q_t) <= max(\$0.001, 10^(-5) abs(F(q_t))). $

The implementation allows 100 allocation updates and makes a final oracle call to certify
the returned iterate at the cap. Capped rows are labeled `iteration_limit` and preserve
$G(q_t)$.

== Integer landing and verification

The continuous allocation cannot be settled directly because protocol quantities and prices
are integers. Each order is capped by the ceiling of its continuous fill; a welfare LP inside
those caps then finds uniform prices supported by the landed fills. It cannot introduce more
quantity than the continuous solution allowed. The independent verifier checks order limits,
market/group price identities, minting, and exact MM capital. This landing LP is a declared
epilogue of RC-FW, not a hidden substitution of the LP-SLP algorithm.

= Evaluation design and anti-selection rules

The Sybil implementation and protocol were frozen at revision
`0f0824ac892d1b9268fa45fded2004f7f9777ff7` before evaluation. Protocol
`solver-evaluation-v2-retained-cash` has BLAKE3
`1f85a07b0588618911577dadb4044182d651b3870dd834182f59a3c0f7276e2c`.
It declares 545 rows over 135 problem groups. The retained artifact has 545/545 rows,
zero missing, duplicate, or unexpected keys, and zero cross-solver problem-fingerprint
mismatches. The analysis script SHA-256 is
`ab19d98c885e96323fd593fbff5c24b63f3c349ad44e79ae1ae0ce3299f71b9b`.

Development smoke seeds are below 30000. Held-out evaluation seeds begin at 50000 and were
not used during algorithm and numerical repair. Solver order rotates within problem groups
after a declared warm-up. The run took 50 seconds on an AMD Ryzen 7 5800X with 32 GB RAM,
Linux 6.6.144, and Rust 1.97.0.

The later artifact/report revision adds the raw and derived outputs, interpretation, and one
semantics-preserving Rust 1.97 lint cleanup in the generator (`rank % 2 == 0` to
`rank.is_multiple_of(2)`). It does not rerun or rewrite an observation. The frozen revision
above remains the exact executable source used for `results.jsonl`.

The suite contains:

+ neutral random controls at tight, baseline, and slack budgets;
+ concentrated tight random books;
+ two-sided flash-liquidity ladders at six budget ratios and ten paired seeds;
+ flash scaling at 48, 400, and 2,000 total orders;
+ heavy-tailed quantity and wide-budget numerical stress;
+ 15 tiny original hard-budget MIQCQPs solved to proven SCIP optimality; and
+ retained-cash versus forced-spend Fisher ablations.

The two-sided flash generator is the theory-aligned adversary. A single MM posts both bids
and asks across markets against one shared budget. Retail crosses alternate between the two
sides, so capital is consumed through both $p q$ and $(1-p)q$. An ordinary LP sees profitable
orders independently but cannot represent the endogenous price–quantity capital coupling.

= Full-denominator results

== Reliability, termination, and runtime

#figure(
  table(
    columns: (1.65fr, 0.85fr, 0.95fr, 0.8fr, 0.95fr, 0.9fr),
    inset: 4.2pt,
    align: (left, center, center, right, right, right),
    header-cell[Method], header-cell[Valid / declared], header-cell[Termination],
    header-cell[Median time], header-cell[Median retained gap], header-cell[P95 certificate],
    [RC-FW], [135/135], [110 conv.; 25 cap], [37.5 ms], [0.0000%], [0.0374%],
    [LP-SLP], [125/125], [106 conv.; 19 cap], [4.0 ms], [0.0080%], [—],
    [Clarabel quasi], [114/135], [21 numerical failures], [5.9 ms], [0.000017%], [0.0000089%],
    [LP, no budget], [52/125], [73 verifier-invalid], [2.3 ms#footnote[Successful rows only.]], [0.0000%], [—],
    [SCIP hard budget], [15/15], [15 proven optima], [43.9 ms], [0.8078%], [different objective],
  ),
  caption: [All applicable held-out declarations. Retained gaps are relative to the best
  verifier-valid landed retained-cash objective observed on the same problem. Certificate
  columns report each backend's own continuous-objective bound.],
) <tab-v2-overall>

No returned RC-FW, LP-SLP, QuasiFisher, or SCIP candidate fails the independent verifier.
The budget-blind LP is deliberately allowed to fail: it exceeds capital in 73/125 rows and
reaches 7.448 times budget in the worst case. This is direct evidence that ordinary LP
clearing is not a feasible substitute when flash liquidity shares capital.

RC-FW integer landing loss has median \$0, 95th percentile \$0.00033, and maximum \$0.4893.
Its absolute certificate gap has median \$0, 95th percentile \$9.25, and maximum \$430.70;
the corresponding relative values are 0%, 0.0374%, and 0.1159%.

== Adversarial flash budget sweep

#figure(
  table(
    columns: (0.75fr, 1fr, 1fr, 0.9fr, 0.75fr, 0.75fr),
    inset: 4.2pt,
    align: (center, right, right, center, center, center),
    header-cell[Budget / limit value], header-cell[RC-FW mean gap],
    header-cell[LP-SLP mean gap], header-cell[No-budget LP valid],
    header-cell[RC-FW valid], header-cell[Quasi valid],
    [0.10×], [0.0091%], [0.1284%], [0/10], [10/10], [9/10],
    [0.25×], [0.0000%], [0.2783%], [0/10], [10/10], [7/10],
    [0.50×], [0.0003%], [1.9862%], [0/10], [10/10], [10/10],
    [1.00×], [0.0000%], [0.0000%], [10/10], [10/10], [7/10],
    [2.00×], [0.0000%], [0.0000%], [10/10], [10/10], [10/10],
    [10.0×], [0.0000%], [0.0000%], [10/10], [10/10], [8/10],
  ),
  caption: [Mean observed-best retained-objective gap over ten paired held-out seeds.
  Failures remain in the validity columns and are not imputed into conditional means.],
) <tab-v2-budget>

At $0.5 times$, LP-SLP's mean retained-objective gap is $1.9862%$, with a paired
bootstrap interval $[1.9164%, 2.0464%]$. RC-FW's is $0.0003%$ with interval
$[0.0001%, 0.0004%]$. At $0.25 times$, LP-SLP has $0.2783%$
$[0.2317%, 0.3172%]$ versus zero for RC-FW at displayed precision. These are the clearest
empirical examples of the theoretical approach outperforming a normal LP heuristic.

The non-monotone LP-SLP pattern is informative. At $0.1 times$ almost all MM liquidity is
suppressed; at $0.5 times$ the budget is just loose enough that a single price-linearization
chooses materially wrong shared-capital allocation; at $1 times$ and above capital is slack
for these ladders. The adversary targets the boundary where endogenous prices matter, rather
than simply choosing the smallest budget.

Clarabel's 0.25× result is conditional on only 7/10 successful runs. It also fails in 2/10
fully slack 10× cases. Cone robustness therefore does not vary monotonically with economic
difficulty.

== Scaling

#figure(
  table(
    columns: (0.75fr, 1.35fr, 1.35fr, 1.05fr),
    inset: 4.2pt,
    align: (center, left, left, left),
    header-cell[Orders], header-cell[RC-FW], header-cell[LP-SLP], header-cell[Clarabel quasi],
    [48], [6/6; 27.7 ms; 0.0001%], [6/6; 1.7 ms; 0.3701%], [6/6; 1.5 ms],
    [400], [6/6; 48.3 ms; 0.0000%], [6/6; 4.6 ms; 0.3611%], [4/6; 5.7 ms],
    [2,000], [4/4; 224.9 ms; 0.0000%], [4/4; 38.5 ms; 0.2907%], [2/4; 34.2 ms],
  ),
  caption: [Valid/declared; median successful wall time; median observed-best retained gap
  where applicable.],
) <tab-v2-scaling>

RC-FW scales less favorably than one LP solve because it invokes the LP oracle repeatedly,
but it remains below 250 ms at the median for 2,000-order flash books on this machine.
This suite is too small to justify “exchange scale” without qualification. It supports
“practical on the tested synthetic scales, with visible long tails.”

== Iteration-cap anatomy

The 25 RC-FW caps occur in five tight neutral books, five of six concentrated books, four
flash-sweep points, one small scaling book, all five tight numerical-range books, and all
five tight no-cash-ablation books. The worst five certificate gaps all come from the
heavy-tailed tight numerical suite. The worst capped landed allocation is $0.0818%$ behind
the observed best retained objective despite its conservative $0.1159%$ certificate.

#caveat[
  The certificate controls the continuous retained-cash objective. It does not certify that
  the integer landing is globally optimal, nor does an observed-best landed comparison
  tighten the certificate. Both quantities should be reported separately.
]

= Theorem-aligned consistency checks

== Welfare bound

For each applicable problem the runner evaluates the first instance-specific bound using
the unconstrained LP allocation,

$ sum_k [Delta_k - B_k ln(1 + Delta_k/B_k)], $

and divides the observed hard-budget welfare shortfall by it. For RC-FW the ratio has median
$0.321$ and maximum $0.402$ where defined. No observed RC-FW row exceeds one.

This is a much better empirical target than a generic “welfare gap below one percent” claim:
the theorem predicts an instance-scaled absolute loss, not a universal percentage. The
experiment is consistent with the bound but cannot validate a theorem already proved
analytically, and synthetic coverage does not establish a production distribution.

== Exact hard-budget reference

SCIP proves all 15 tiny MIQCQPs optimal with zero backend gap. Its median linear-welfare
improvement over LP-SLP is $0.2604%$, so one-pass SLP is not exact even on these small books.
SCIP's median retained-objective gap is $0.8078%$, whereas RC-FW's is zero at displayed
precision. Conversely, RC-FW's median linear welfare is $4.7205%$ below LP-SLP in this suite.

There is no contradiction: SCIP maximizes linear welfare subject to the original hard
budget, while RC-FW maximizes the retained-cash reduced-form objective. The paper should
not call one the exact optimizer of the other's objective. The value of the comparison is
that it separates the approximation theorem's two economic formulations.

== Retained-cash ablation

On five small tight-budget books, forced-spend Fisher and QuasiFisher both have median
observed-best retained gap $0.0008%$ and succeed 5/5; RC-FW has median zero but reaches its
cap in all five. With 4× slack budget all three are effectively identical and converge.
This small ablation does not by itself demonstrate a material allocation advantage from
retained cash. Its contribution is numerical/modeling hygiene: the no-cash objective has a
log singularity and is not the economic program proved in the paper.

= Negative results and limitations

+ _RC-FW has a tail._ It is roughly 9.4 times slower than LP-SLP at the overall median and
  reaches the fixed cap in 18.5% of applicable rows. A convergence theorem does not remove
  product latency limits.
+ _Clarabel is not reliable enough._ Its 21 `InsufficientProgress` failures comprise one
  neutral, two concentrated, nine budget-sweep, two medium-scaling, two large-scaling, and
  five numerical-stress declarations. Conditional quality statistics are optimistic if
  difficult books fail selectively.
+ _The exact suite is tiny._ Fifteen SCIP optima are useful unit-scale references, not
  evidence that MIQCQP scales to production.
+ _The order books are synthetic._ They vary the structural mechanisms of interest but are
  not calibrated or anonymized production replays.
+ _Timing is single-host and warm._ Solver order rotation reduces, but cannot remove, cache,
  CPU-frequency, allocator, and shared-machine effects.
+ _The largest flash book has 2,000 orders._ The present data do not establish hundred-
  thousand-order performance.
+ _Observed-best is not true optimum._ It can understate every method's landed objective
  gap. Only the RC-FW continuous gap and backend conic/MILP gaps are certificates for their
  respective formulations.

= Recommended integration into the paper

#revision[
  Replace “one convex solve replaces heuristic iteration” with “one convex program replaces
  the non-convex hard-budget formulation; we solve its zero-temperature form by a certified
  generalized Frank–Wolfe method whose iterations are ordinary matching LPs.” The current
  wording confuses mathematical formulation with the number of backend calls.
]

#revision[
  Replace the unqualified abstract claim “Exponential-cone formulations make clearing
  practical at exchange scale.” A defensible sentence is: “The retained-cash program admits
  both an exponential-cone formulation and a generalized Frank–Wolfe LP-oracle algorithm.
  In held-out synthetic tests the oracle algorithm returned verifier-valid allocations in
  135/135 cases; a Clarabel reference failed numerically in 21/135.”
]

The empirical section should be organized around four claims:

+ _Feasibility:_ RC-FW is verifier-valid and respects shared capital in 135/135; ordinary
  budget-blind LP is invalid in 73/125.
+ _Theory-aligned advantage:_ on adversarial two-sided flash ladders, RC-FW reduces the
  retained-objective gap from LP-SLP's $1.9862%$ to $0.0003%$ at the 0.5× boundary.
+ _Certification:_ 110/135 meet tolerance; all 25 capped rows expose their residual gap,
  with overall 95th percentile $0.0374%$ and maximum $0.1159%$.
+ _Trade-off:_ RC-FW's median is 37.5 ms versus 4.0 ms for LP-SLP; Clarabel is faster when
  successful but has 21/135 numerical failures.

The paper should include at least three figures from the deterministic Sybil artifacts:

+ retained-objective gap versus budget ratio, with validity denominators;
+ runtime versus flash order count, with Clarabel failures visible; and
+ the full termination-outcome counts plus RC-FW certificate-gap distribution.

Do not use a figure that drops numerical failures or places SCIP and RC-FW in one
objective-quality ranking without labeling their different objectives.

= Reproducibility and artifact map

The Sybil result directory is
`benchmarks/solver/results/2026-07-13-v2/`. It contains:

+ `results.jsonl`: immutable row-level evidence;
+ `protocol.json`: the frozen declaration copied into the run;
+ `metadata.json`: source revision, hashes, host, toolchain, and elapsed time;
+ `summary.json`, `summary.csv`, and `summary.md`: deterministic derived tables; and
+ six SVGs covering quality, budget response, scaling, termination, capital utilization,
  and certificate gaps.

The runner command is:

```bash
cargo run --release -p matching-sim --bin solver-experiments -- \
  --protocol benchmarks/solver/protocol-v2.json \
  --source-revision 0f0824ac892d1b9268fa45fded2004f7f9777ff7 \
  --output-dir benchmarks/solver/results/2026-07-13-v2
```

The analyzer command is:

```bash
python3 scripts/benchmarks/analyze_solver_experiments.py \
  benchmarks/solver/results/2026-07-13-v2
```

No evaluation row was rerun, removed, imputed, or selected after inspecting outcomes.
