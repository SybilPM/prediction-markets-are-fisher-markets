#set document(title: "Post-Evaluation Solver Engineering for Retained-Cash Clearing")
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

#let boundary(body) = block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("fff7ed"),
  stroke: (left: 1.5pt + rgb("c2410c")),
)[#text(weight: "bold")[Evidence boundary. ]#body]

#let implication(body) = block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("eff6ff"),
  stroke: (left: 1.5pt + rgb("1d4ed8")),
)[#text(weight: "bold")[Paper implication. ]#body]

#align(center)[
  #text(size: 15pt, weight: "bold")[
    Post-Evaluation Solver Engineering for Retained-Cash Clearing
  ]
  #v(0.4em)
  #text(size: 10.5pt)[LP-oracle reuse, a better-conditioned cone model, and a pacing-dual research path]
  #v(0.3em)
  #text(size: 9pt, style: "italic")[Standalone integration note — 13 July 2026]
]

#v(0.8em)

#block(inset: (x: 1.5em))[
  #text(weight: "bold")[Status.]
  This note records engineering performed after the frozen v2 experiment in
  `empirical-retained-cash-v2.typ`. It is material for a later paper revision, not a new
  empirical result. It leaves every v2 row and headline unchanged.
]

#block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("fef2f2"),
  stroke: (left: 1.5pt + rgb("b91c1c")),
)[
  #text(weight: "bold")[Subsequent model correction.]
  The later pacing-bundle work found that the “reduced mint equations” below
  imposed equality of outcome demands, whereas the paper requires the
  epigraph $M >= D_omega$. Current Clarabel code restores that epigraph. The
  historical 97/100 development count below therefore describes a superseded
  supply model and is not corrected-objective availability evidence. See
  `pacing-bundle-development.typ`; the LP-oracle reuse result is unaffected.
]

= Executive assessment

The generalized Frank–Wolfe retained-cash solver remains the right supported algorithm.
Its appeal is structural rather than accidental: it optimizes the paper's concave
retained-cash objective; every iteration calls the exchange's ordinary matching LP; and
the Frank–Wolfe gap is an instance-specific upper bound on continuous suboptimality. The
frozen held-out result—135/135 verifier-valid returns, with 110 meeting the configured
certificate tolerance—therefore remains the strongest basis for a production choice.

The main implementation inefficiency was not inherent to the algorithm. Only the matching
LP's objective changes between iterations, but the implementation rebuilt the sparse model
and cold-started HiGHS on every call. Reusing the model and its simplex basis reduced the
median time on a nine-book development smoke set from 141.9 ms to 31.9 ms. Among the six
capped rows, the median fell from 951.5 ms to 153.1 ms. This preserves the feasible region,
oracle optimum, line search, and certificate.

The independent Clarabel implementation also had two avoidable formulation problems. It
used a poorly scaled representation of the logarithm and retained redundant free mint
variables. Replacing these with the canonical perspective exponential cone and eliminating
per-market mint variables increased success on a 100-row adversarial development sweep
from 92/100 to 97/100 after conservative step-size tuning. The three remaining
`InsufficientProgress` outcomes stay failures; Clarabel is still a reference, not a silent
fallback.

#boundary[
  All numbers in this note use development seeds below 30000. No v2 evaluation seed at or
  above 50000 was rerun or used for tuning. These measurements may motivate a frozen v3
  protocol, but must not be merged into the held-out v2 tables or described as confirmatory.
]

= Reusing the matching-LP oracle

At iterate $q_t$, the retained-cash solver calls

$
s_t in arg max_(s in cal(Q))\
  R(s) + sum_k alpha_(k,t) U_k(s),
  quad alpha_(k,t) = min(1, B_k / U_k(q_t)).
$

The polytope $cal(Q)$, variable bounds, market-balance matrix, minting columns, and row
bounds do not depend on $t$. Only fill-variable objective costs depend on the pacing factors.
The revised oracle therefore builds one HiGHS model, changes its column costs, solves, and
converts the solved model back to a live model for the next call. HiGHS can re-optimize from
the previous basis instead of repeating matrix construction and a cold simplex start.

This is a semantics-preserving optimization in the sense relevant to the theorem: each
call still returns an optimum of the same linear oracle. It need not return the identical
primal vector. A matching LP can have an optimal face, and a warm basis may select another
point on it. That can change a capped Frank–Wolfe trajectory without changing an individual
oracle's optimum. The regression test consequently compares warm and cold objective optima
after repeated cost changes rather than requiring byte-identical allocations.

#figure(
  table(
    columns: (2.1fr, 1fr, 1fr),
    inset: 4.5pt,
    align: (left, right, right),
    header-cell[Development-smoke statistic], header-cell[Cold oracle], header-cell[Reused oracle],
    [Median time, all nine RC-FW rows], [141.9 ms], [31.9 ms],
    [Median time, six capped rows], [951.5 ms], [153.1 ms],
    [Median paired speedup, all rows], [—], [5.18×],
    [Median paired speedup, capped rows], [—], [6.50×],
    [Capped-row speedup range], [—], [4.44×–8.53×],
  ),
  caption: [Paired post-evaluation development timings. Termination classes and oracle counts
  were unchanged. The smallest 16-order problem regressed slightly, from 3.59 ms to 3.88 ms.],
) <tab-oracle-reuse>

The optimization attacks cost per iteration, not iteration complexity. Rows that reached
the 100-update cap still do so and still expose their certificate gaps. This distinction
should remain explicit if a later paper version reports lower latency.

#implication[
  The paper can describe RC-FW as a repeated matching-LP method without implying repeated
  cold solves. A reusable simplex basis makes the theoretical oracle abstraction a good
  implementation boundary: algorithmic clarity and low latency point in the same direction.
]

= A cleaner exponential-cone reference

== Canonical perspective cone

For a market maker with capital $B_k$, deployed value $U_k$, and retained cash $s_k$, the
logarithmic contribution can be represented with one cone triple

$
(t_k, B_k, U_k+s_k) in cal(K)_"exp",
$

where

$
cal(K)_"exp" = { (x,y,z) : y > 0,\ y exp(x/y) <= z }.
$

It follows that

$ t_k <= B_k ln((U_k+s_k)/B_k). $

Maximizing $t_k-s_k$ differs from $B_k ln(U_k+s_k)-s_k$ only by the
allocation-independent constant $-B_k ln B_k$. The previous model instead expressed
$exp(t_k/B_k) <= U_k+s_k$, putting $1/B_k$ on a structural row. The perspective form is
both the canonical conic lift and better scaled across wide budget ranges.

== Eliminating free mint variables

For binary market $m$, let $a^Y_(m i)$ and $a^N_(m i)$ be order $i$'s YES and NO payoff
coefficients. With a per-market complete-set mint $z_m$, the original balances are

$
sum_i a^Y_(m i) q_i - z_m - g_m = 0,
quad
sum_i a^N_(m i) q_i - z_m = 0,
$

where $g_m$ is the relevant group mint when present. The second equality gives
$z_m = sum_i a^N_(m i) q_i$. Substitution leaves the single equality

$
sum_i (a^Y_(m i)-a^N_(m i)) q_i - g_m = 0.
$

The minting objective is adjusted by the same substitution. This removes one free variable
and one equality per market from Clarabel's KKT system. It does not alter the allocation;
the integer landing LP still recovers both market-price duals.

== Complete development tuning audit

Every row below used the same 100 declared QuasiFisher development problems. Reporting all
variants prevents a successful setting from being presented without its search history.

#figure(
  table(
    columns: (2.35fr, 0.65fr, 0.85fr, 0.85fr),
    inset: 4.0pt,
    align: (left, center, right, right),
    header-cell[Variant], header-cell[Solved], header-cell[Median], header-cell[P95],
    [Perspective cone, default step], [92/100], [6.95 ms], [105.7 ms],
    [Wider equilibration range], [92/100], [6.97 ms], [100.9 ms],
    [Reduced mint equations], [92/100], [6.88 ms], [97.6 ms],
    [Presolve disabled], [92/100], [7.04 ms], [99.0 ms],
    [Static regularization $10^(-6)$], [86/100], [7.93 ms], [101.3 ms],
    [Static regularization $10^(-10)$], [91/100], [7.46 ms], [83.5 ms],
    [Maximum step 0.95], [96/100], [6.09 ms], [92.1 ms],
    [Maximum step 0.90], [96/100], [6.80 ms], [90.6 ms],
    [Maximum step 0.80], [#text(weight: "bold")[97/100]], [7.16 ms], [96.2 ms],
    [Maximum step 0.70], [96/100], [7.57 ms], [112.4 ms],
    [Faer factorization, step 0.80], [97/100], [7.34 ms], [103.8 ms],
  ),
  caption: [Post-evaluation development audit. Step 0.80 and the reduced equations were kept.
  Faer added 37 transitive dependencies without improving success and was rejected.],
) <tab-conic-audit>

The final failures comprise one slack neutral book and two slack heavy-tailed numerical-range
books. This is useful negative evidence: numerical difficulty is not monotone in economic
budget tightness. Failure records now preserve iteration counts, objective values, primal and
dual gaps, and residuals, so a future robustness study can model failure rather than erase it.

#implication[
  A later paper revision may present the perspective-cone derivation as the canonical conic
  formulation. It must continue to distinguish mathematical representability from backend
  robustness. The 97/100 figure is development evidence, not a replacement for Clarabel's
  frozen 114/135 held-out result.
]

= Is Frank–Wolfe the final algorithm?

RC-FW is the right current implementation, but the reduced-form utility exposes a promising
lower-dimensional dual. For $U >= 0$,

$
psi_B(U) = min_(0 < alpha <= 1) { alpha U - B ln alpha }.
$

Indeed, the unconstrained stationary point is $alpha=B/U$; clipping it at one recovers the
affine branch for $U <= B$ and the logarithmic branch for $U>B$. Inserting this identity into
the retained-cash objective and exchanging max and min under the usual convexity conditions
yields a convex pacing problem with one scalar $alpha_k$ per market maker. Evaluating its
nonsmooth objective or a cutting plane again requires the same shaded matching LP.

This suggests a stabilized bundle or cutting-plane method. Its dimension depends on the
number of market makers rather than the number of orders, so it may need fewer oracle calls
when a small number of makers posts a large flash-liquidity ladder. It is also naturally
adversarial against one-pass LP-SLP: the hard cases are changes of the optimal LP face near a
shared-capital boundary, precisely where one price linearization is least informative.

The approach is not yet a safe replacement. A credible implementation must:

+ recover a primal allocation from the bundle model's mixture of oracle vertices;
+ report a valid primal–dual gap for the returned allocation;
+ remain stable at nonsmooth LP face changes and at $alpha_k=1$;
+ preserve integer landing and independent verification; and
+ beat basis-reusing RC-FW on a protocol frozen before untouched evaluation seeds are run.

Plain BFGS on pacing factors or an uncertified projected subgradient method would be shorter,
but would discard the convergence evidence that motivates the theoretical solver. The right
comparison is therefore certified RC-FW versus a certified pacing-dual bundle method.

= Proposed next experiment

A new protocol should be preregistered after the pacing-dual implementation and metrics are
frozen. The primary comparison should include RC-FW with oracle reuse, the pacing-dual bundle
method, LP-SLP, and Clarabel QuasiFisher. Every declaration should retain failures and caps.

The stress axes should include:

+ number of retail orders at fixed small MM count, to test the dual's dimensional advantage;
+ MM count at fixed order count, to expose where that advantage disappears;
+ budget ratios concentrated around the endogenous binding boundary;
+ nearly degenerate ladders that repeatedly change the matching LP's optimal face;
+ heavy-tailed values and quantities across several numerical scales;
+ sparse bundle-coupling graphs of controlled treewidth; and
+ anonymized production replays once a defensible calibration corpus exists.

Report wall time, LP-oracle time, model-update time, line-search time, oracle count, simplex
iterations, peak memory, termination class, continuous certificate, integer landing loss,
verifier result, capital utilization, and objective gap to the best valid landed candidate.
Tail summaries should include P50, P90, P95, P99, and maximum with declared denominators.

The preregistered hypotheses should be narrow: basis reuse reduces RC-FW oracle time without
changing oracle optima; the pacing-dual method reduces oracle count on low-MM flash books;
neither method has an unconditional advantage as MM dimension grows; and Clarabel remains an
independent objective check whose failures are reported rather than imputed.

= Integration guidance

The frozen v2 section already supports the central paper claim and should not be rewritten as
though these changes preceded it. A later empirical update can add a clearly labeled
post-evaluation paragraph stating that model/basis reuse removed much of RC-FW's implementation
tail, followed by a new held-out result only after a v3 freeze. The cone derivation can be
corrected immediately as mathematics, while its development success rate belongs in a footnote
or future-work note until independently evaluated.

The clean scientific story is stronger than a universal winner claim:

+ retained-cash geometry supplies both a reliable certified LP-oracle method and a canonical
  conic reference;
+ adversarial shared-capital books reveal why an ordinary one-pass LP approximation can fail;
+ engineering the oracle boundary closes much of the practical latency gap without changing
  the algorithm; and
+ the pacing dual offers a principled route to fewer oracle calls, with certification—not
  benchmark selection—as the acceptance criterion.
