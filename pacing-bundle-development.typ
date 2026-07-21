#set document(title: "A Fully Corrective Pacing Bundle for Retained-Cash Clearing")
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

#let correction(body) = block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("fef2f2"),
  stroke: (left: 1.5pt + rgb("b91c1c")),
)[#text(weight: "bold")[Model correction. ]#body]

#let implication(body) = block(
  width: 100%,
  inset: (x: 0.9em, y: 0.65em),
  fill: rgb("eff6ff"),
  stroke: (left: 1.5pt + rgb("1d4ed8")),
)[#text(weight: "bold")[Paper implication. ]#body]

#align(center)[
  #text(size: 15pt, weight: "bold")[
    A Fully Corrective Pacing Bundle for Retained-Cash Clearing
  ]
  #v(0.35em)
  #text(size: 10.5pt)[Derivation, development evidence, landing limits, and integration material]
  #v(0.3em)
  #text(size: 9pt, style: "italic")[Standalone paper-development note — revised 14 July 2026]
]

#v(0.8em)

#boundary[
  Every empirical number here uses development seeds 16000–18403 that were
  observed while the implementation was changing. All 555 declared rows—111
  books by five methods—are retained, but this is not held-out or confirmatory
  evidence. The generated books are structural stresses, not calibrated
  production replay. The frozen v2 experiment remains unchanged. A publishable
  comparison requires a frozen implementation and a new untouched protocol.
]

= Executive assessment

The pacing dual suggested in `solver-engineering-followup.typ` now has a
certificate-bearing implementation. It is a fully corrective bundle, or
equivalently a simplicial-decomposition method, whose atoms are optima of the
exchange's ordinary matching LP. The continuous algorithm is elegant: one
pacing scalar per market maker, a reusable LP oracle, a convex mixture of
retained primal atoms, and a valid global upper gap. In the complete development
matrix it returned verifier-valid results in 110/111 declarations and met its
strict continuous stopping criterion in 105, with five iteration caps and one
explicit integer price-support failure. Generalized Frank–Wolfe had 82
convergences, 28 iteration caps, and one landing failure. The
corrected-epigraph Clarabel formulation was the fastest theoretical method and
a strong quality reference conditional on success, but returned
`InsufficientProgress` on 2 of 111 declarations. Thus the evidence supports the
retained-cash formulation and the bundle's robustness; it does not establish
one universally best implementation.

The most alarming earlier result—a 67.9% bundle landing loss—was a real bug,
not rounding noise. A final supporting LP had a degenerate optimal face and
returned a distant vertex instead of the certified atom mixture. Landing now
uses a lexicographic second LP: remain on the primary supporting face, then
minimize L1 distance to the certified point, while publishing only the primary
LP's market duals. A price-support gate then compares the already available
nearest-face, primary-basis, and certified-target integer candidates under
those prices. The maximum bundle landing loss falls to 0.5344% and its maximum
retained-objective gap to 0.4936%. The method is still not an automatic
production replacement: its 10,000-order median is 1.786 seconds and its
overall maximum is 2.313 seconds, while the evidence is development-exposed
and synthetic.

= Variational pacing representation

For the shifted retained-cash utility

$
psi_B(U) = cases(
  U, & U <= B,
  B(1 + ln(U/B)), & U > B,
),
$

one has, for $B>0$,

$ psi_B(U) = min_(0 < alpha <= 1) {alpha U - B ln alpha}. $

The stationary point is $alpha=B/U$; clipping at one gives the affine branch.
Let

$ F(bold(q)) = R(bold(q)) + sum_k psi_(B_k)(U_k(bold(q))), $

where $R$ contains retail value, the exact MM-sell correction, and the negative
zero-temperature minting cost. For fixed $bold(alpha)$ the inner problem is

$ h(bold(alpha)) = max_(bold(q) in cal(Q)) {R(bold(q)) + sum_k alpha_k U_k(bold(q))}, $

which is precisely a matching LP with all orders of MM $k$ shaded by one
$alpha_k$. The pacing dual is

$ min_(bold(alpha) in (0,1]^K) {h(bold(alpha)) - sum_k B_k ln alpha_k}. $

Each LP optimum is both a cutting plane for this convex dual and a feasible
primal atom. If retained atoms are $bold(q)^1, dots, bold(q)^r$ and
$bold(lambda)$ lies on the simplex, then

$ bold(q)(bold(lambda)) = sum_a lambda_a bold(q)^a $

remains in $cal(Q)$. The restricted master maximizes
$F(bold(q)(bold(lambda)))$ over that simplex. The implementation performs
pairwise exact line searches: mass moves from one active atom to another, so
feasibility is automatic and the active set can shrink as well as grow.

== Certificate

At the current mixture $bold(q)$, set
$alpha_k=psi'_(B_k)(U_k(bold(q)))$. Concavity gives

$ F(bold(q)^*) - F(bold(q)) <= h(bold(alpha)) - [R(bold(q)) + sum_k alpha_k U_k(bold(q))]. $

The right side is the generalized Frank–Wolfe gap, now evaluated at a fully
corrected primal mixture. Importantly, the implementation does not treat the
LP backend's returned primal value as an exact oracle maximum. Finite
analytical column bounds, row duals, and reduced costs produce a conservative
Lagrangian upper bound. This remains valid under floating-point LP residuals.
The best global upper bound seen so far minus the current primal objective is
the reported certificate.

#implication[
  This derivation is suitable for a later algorithm subsection. It makes the
  theoretical advantage precise without claiming that low-dimensional pacing
  alone guarantees low wall time: the restricted master can still have a long
  correction tail as the number of market makers grows.
]

= Corrections required before comparing algorithms

Implementing the bundle falsified several assumptions in the earlier
engineering and benchmark stack. They must be recorded because leaving them in
place would artificially strengthen the empirical story.

== Minting is an epigraph

At zero temperature, complete-set supply costs
$C_0(bold(D))=max_omega D_omega$. The LP representation is

$ M >= D_omega quad "for every" omega, $

not equality balance. The matching LP used equality rows. The Clarabel model
then went further and eliminated the mint variable using those equalities. Both
implementations are now corrected. Independent binaries retain the two
epigraph inequalities. For a mutually exclusive group, translation
equivariance gives

$ sum_m D^N_m + max(0, max_m(D^Y_m-D^N_m)), $

represented by one nonnegative group epigraph and one inequality per member.

#correction[
  The 97/100 Clarabel development result in
  `solver-engineering-followup.typ` used the superseded equality-reduced supply
  model. It is not availability evidence for an independent implementation of
  the corrected paper objective. The perspective exponential-cone scaling and
  conservative-step findings remain useful, but same-objective Clarabel
  robustness must be rerun under a future frozen protocol.
]

== A landed objective is settlement-valued

Earlier analysis evaluated landed fills with the continuous $C_0$ expression
even after post-price fill trimming. That can make a mutated allocation appear
to beat its own continuous upper certificate. The landed retained objective
now uses signed mint/burn cash from actual uniform fill prices. The experiment
also reports the supply-support diagnostic

$ abs(C_0(bold(D)) - sum_omega p_omega D_omega). $

The final development matrix had P95 residuals of
$3.48 times 10^(-8)$ dollars for RC-FW, $1.06 times 10^(-8)$ for the bundle,
and $1.45 times 10^(-6)$ for Clarabel QuasiFisher. Their maxima were
$5.7 times 10^(-8)$, $0.000160$, and $0.000155$, respectively. The five-step
LP-SLP baseline instead reached $28.02$ dollars at P95 and $62.75$ at maximum,
despite every returned row passing the current verifier. This is why the
diagnostic belongs next to, not inside or instead of, the verifier.

== Post-price fill trimming is not equilibrium preservation

Blindly reducing an MM fill after price discovery changes demand without
re-solving the supply and consumer optimality conditions. The revised
retained-cash landing checks rounded quantities at discovered prices, adds
linearized hard-budget rows, and re-solves. It finalizes only when prices and
integer quantities form a budget-consistent fixed point. Exhaustion is an
explicit post-processing failure.

== NO-side capital prices must not be complemented twice

The final 1,024-case conformance pass exposed an API mismatch that the original
matrix did not isolate. `MmSide::capital_needed` assumed every caller supplied
the YES price, while verification, post-processing, and benchmark reporting
supplied the order's actual outcome fill price. A NO order was therefore
complemented twice. The engine contract now takes the traded outcome price:
either buy consumes its fill price and either sell consumes one minus its fill
price. LP code that starts from $p_("YES")$ converts a NO order explicitly.

The minimized billion-unit case also made HiGHS choose different degenerate
bases across processes. The retained run therefore pins one thread, parallel
mode off, and random seed zero, and sorts MM objective indices before floating
accumulation. Five fresh-process repetitions of the minimized case and the full
conformance pass succeeded. A complete fresh-process matrix replay then matched
all 555 non-timing solver outputs exactly. It also exposed nondeterministic
scenario hashes from direct `HashMap` serialization; the benchmark now hashes a
canonical market/MM-side encoding, and the final replay matched those hashes as
well. The current synthetic families mostly quote YES, so this is correctness
evidence, not strong empirical coverage of NO-side parity; a frozen follow-up
should add paired YES/NO metamorphic books.

== Lexicographic landing and the rejected utility band

A final pacing-supported LP may have many primal optima. Constraining each MM's
weighted fill to a narrow band around the continuous bundle point greatly
reduced landing loss in the development matrix. But these constraints
introduce new dual multipliers. Extracting only the market-row duals then omits
part of stationarity. A property-based conformance case filled a buyer at price
$1.00$ despite a limit of $0.901073144$. Widening the band would hide rather
than repair the issue, so the rows were removed.

The implemented repair is lexicographic. First solve the original
pacing-supported matching LP and retain its market duals. Then constrain the
allocation to the primary optimal face and minimize L1 distance to the
certified continuous target. The auxiliary distance-row duals are never
published as prices. Normally scaled books use the exact face with an explicit
activity check. Deliberately wide billion-unit books use a $10^(-8)$ relative
near-face band directly because HiGHS can report an exact auxiliary optimum
there while materially violating the face row.

Before budget projection, landing evaluates the nearest-face, primary-basis,
and certified-target integer candidates under the primary prices and chooses
the smallest minting-duality residual, failing explicitly above $0.05$. No
other solver is called. This repair removed the 67.9% outlier. Its worst bundle
row is now the 80-order two-MM book at seed 17003: the support gate rejects the
nearest candidate, then accepts a candidate with 7.4923% allocation movement,
$2.8937$ objective loss, and 0.5344% relative landing loss. The next tail is an
eight-MM book with 0.3052% movement and 0.0523% loss. A relaxed-only version
produced a cosmetically smaller objective gap but a $21.14$ minting-duality
residual. The final implementation therefore chooses price support over the
most flattering observed-best score.

= Complete development matrix

#figure(
  table(
    columns: (1.65fr, 0.85fr, 1.05fr, 0.9fr, 1fr),
    inset: 3.2pt,
    align: (left, right, right, right, right),
    header-cell[Metric], header-cell[LP-SLP], header-cell[RC-FW],
    header-cell[Bundle], header-cell[Clarabel],
    [Successful / declared], [111 / 111], [110 / 111], [110 / 111], [109 / 111],
    [Core termination], [87 / 24 cap], [82 / 28 cap + 1 fail], [105 / 5 cap + 1 support fail], [109 / 2 fail],
    [Verifier-invalid returns], [0], [0], [0], [0],
    [Median wall time], [15.19 ms], [74.88 ms], [74.75 ms], [30.85 ms],
    [P95 wall time], [282.76 ms], [513.18 ms], [578.48 ms], [151.02 ms],
    [P99 wall time], [434.86 ms], [1,423.79 ms], [2,185.52 ms], [311.87 ms],
    [Retained gap mean / P50 / P95 / max], [1.0599 / 0.1395 / 2.5373 / 21.7429%], [0.5294 / 0.0002 / 0.0804 / 20.8714%], [0.00545 / 0 / 0.000615 / 0.4936%], [0.0379 / 0 / 0.4138 / 0.5357%],
    [Welfare gap mean / P50 / P95 / max], [1.2750 / 0 / 0.0840 / 37.5938%], [2.8054 / 0.9588 / 6.6082 / 37.1955%], [1.8249 / 0.4693 / 6.0563 / 7.2036%], [2.1237 / 1.6237 / 6.0729 / 11.5312%],
    [Landing loss P95 / max], [--], [0.0208 / 20.8685%], [0.00271 / 0.53439%], [--],
    [Landing L1 P95 / max], [--], [0.3651 / 41.5304%], [0.08825 / 7.4923%], [--],
    [Mint duality P95 / max], [\$28.0197 / \$62.7453], [\$3.48e-8 / \$5.7e-8], [\$1.06e-8 / \$0.000160], [\$1.45e-6 / \$0.000155],
  ),
  caption: [Four feasible methods from the complete 555-row development
  comparison. Runtime and quality statistics condition on successful
  verifier-valid rows; success retains the full declared denominator. Welfare
  is shown separately from the retained-cash objective.],
) <tab-pacing-development>

The bundle retained two active atoms at the median and 14 at the maximum. The
restricted master used 48 pairwise correction steps at the median. Its tail and
the exact landing LP both become visible at larger order or MM dimension. This
is a concrete target for a dedicated small convex master and a cheaper
lexicographic landing implementation.

All four failed declarations remain visible. RC-FW failed integer recovery on
one 16-MM tight-flash book after its core reached the update cap. The bundle
failed wide-range seed 16203 after its converged continuous point could not be
integerized under the primary prices: the best candidate's minting-duality
discrepancy was \$2,090.58 against \$769,328.56 of minting cost (0.272%).
Accepting that row would hide the price/allocation inconsistency rather than
solve it. Clarabel
returned `InsufficientProgress` on one neutral high-budget book and one
heavy-range high-budget book. No result from another solver replaces them.

The fifth method is a deliberately budget-blind LP negative control. It passes
verification on only 35/111 rows, violates MM budgets on 76, and reaches 7.353
times available capital. Its superficially excellent conditional objective is
therefore not included as a feasible competitor.

== Orthogonal scaling

#figure(
  table(
    columns: (0.6fr, 1.15fr, 1.15fr, 1.15fr, 1.15fr),
    inset: 3.8pt,
    align: (right, right, right, right, right),
    header-cell[Orders], header-cell[LP-SLP], header-cell[RC-FW],
    header-cell[Bundle], header-cell[Clarabel],
    [80], [1.74 / 21.0049%], [11.11 / 18.1420%], [3.94 / 0.0000%], [3.02 / 0.0000%],
    [400], [7.75 / 0.2379%], [17.93 / 0.0032%], [9.17 / 0.0000%], [6.58 / 0.0085%],
    [2,000], [25.20 / 0.3475%], [81.33 / 0.0005%], [80.94 / 0.0000%], [32.80 / 0.0000%],
    [10,000], [315.10 / 0.3414%], [1,374.26 / 0.0046%], [1,786.34 / 0.0000%], [309.64 / 0.0001%],
  ),
  caption: [Fixed-two-MM order-count scaling, shown as median milliseconds /
  median observed-best retained-objective gap. The gap is to the best
  verifier-valid landed result on the same book, not to a proven optimum.],
) <tab-order-scaling>

The 80-order rows are structurally adversarial to a short LP-SLP pass and
vanilla Frank--Wolfe: their median gaps were 21.00% and 18.14%. The bundle's
median is zero, but seed 17003 has a 0.4936% gap after the support gate rejects
a closer unsupported candidate; its four-row mean is 0.1234%. Corrected
Clarabel's maximum is below 0.000001%. This demonstrates an
advantage for the retained-cash objective and convergent methods, not a unique
advantage for the bundle implementation.

At fixed order count, bundle median time rose from 78.17 ms with one MM to
222.45 ms with 16 MMs. At 16 MMs RC-FW's conditional median was 153.31 ms but
succeeded on only three of four rows; the bundle succeeded on all four with no
displayed observed-best gap. Clarabel remained near 37.03 ms with a 0.0664%
gap. Thus the bundle's practical dimension is the MM count, as the variational
derivation predicts, and its pairwise restricted master is not the right
high-dimensional implementation.

== Adversarial flash budgets

At budget ratios 0.10, 0.25, and 0.50 the bundle has no displayed mean
observed-best retained gap after lexicographic landing. RC-FW records 0.0299%,
0.0047%, and 0.0012%; LP-SLP records 0.2794%, 0.3568%, and 1.9538%; Clarabel
records 0.3462%, 0.0114%, and 0.0008%. All methods match at slack budgets. These
five-seed development comparisons are useful diagnostics but far too exposed
and small for an inferential paper claim.

= What belongs in a later paper revision

The paper can eventually add the pacing variational identity, the
bundle/primal-atom interpretation, and the conservative certificate derivation
independently of performance claims. The implementation also strengthens the
empirical methodology: report welfare and retained objective separately,
oracle work, restricted-master work, active atoms, P50/P95/P99/max latency,
integer landing loss and movement, and minting duality rather than one median
runtime.

The current numerical table should remain outside the main paper or be labeled
unambiguously as development evidence. A confirmatory experiment should be
frozen before untouched instances are generated and should include:

+ RC-FW with the reused HiGHS oracle;
+ the fully corrective pacing bundle;
+ LP-SLP as the theory-aligned adversarial baseline;
+ corrected-epigraph Clarabel QuasiFisher as an independent reference;
+ order-count scaling at fixed MM count;
+ MM-count scaling at fixed order count;
+ budget ratios concentrated around the endogenous binding boundary;
+ nearly degenerate LP faces and heavy-tailed numerical ranges; and
+ every cap, numerical failure, landing failure, and verifier failure in its
  declared denominator.

A serious empirical section needs three distinct layers: a preregistered
synthetic corpus for controlled coverage; simulation calibrated to frozen
descriptive depth, spread, order-size, imbalance, and correlation statistics;
and consented production replay with complete batch and shared-MM identity
reconstruction. The present experiment supplies only the first layer's
development design, not its untouched result.

#implication[
  The honest conclusion is not “a new solver is faster.” The pacing formulation
  has much better retained-objective tails and cap behavior on the adversarial
  books, while Clarabel is materially faster conditional on success and the
  lexicographic LP dominates 10,000-order bundle latency. The theorem-to-system
  bridge now has three separately measured parts: continuous certificate,
  price-supported face selection, and integer budget landing.
]

= Reproducibility map

The implementation and development protocol live in the Sybil repository:

+ `crates/matching-solver/src/pacing_bundle_solver.rs` — atoms, restricted
  master, primal recovery, and global gap;
+ `crates/matching-solver/src/lp_solver.rs` — minting epigraph, reusable oracle,
  dual upper bound, and lexicographic nearest-face projection;
+ `crates/matching-solver/src/conic_solver.rs` — corrected Clarabel minting
  epigraph;
+ `benchmarks/solver/protocol-pacing-development.json` — all declared
  development rows; and
+ `scripts/benchmarks/analyze_solver_experiments.py` — integrity checks,
  tail/work/landing summaries, and deterministic figures.

The complete raw development output is retained under
`benchmarks/solver/results/2026-07-14-pacing-development-v2/` at Sybil source
revision `0b62dc1f`. Its 555/555 integrity check, generated summaries, and
figures are development evidence, not held-out evidence.
