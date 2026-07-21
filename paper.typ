#set document(title: "Prediction Markets Are Fisher Markets")
#set text(font: "New Computer Modern", size: 10pt)
#set page(margin: (x: 1.5in, y: 1.2in), numbering: "1")
#set par(justify: true, leading: 0.55em)
#set heading(numbering: "1.")
#show heading.where(level: 1): it => block(above: 1.5em, below: 0.8em)[#it]
#show heading.where(level: 2): it => block(above: 1.2em, below: 0.6em)[#it]

// Theorem-like environments with auto-numbering and @label cross-referencing
#show figure.where(kind: "theorem"): it => align(left, it.body)
#show figure.where(kind: "proposition"): it => align(left, it.body)
#show figure.where(kind: "lemma"): it => align(left, it.body)
#show figure.where(kind: "corollary"): it => align(left, it.body)

#let theorem(name: none, body) = figure(
  kind: "theorem", supplement: [Theorem], numbering: "1", outlined: false,
  block(width: 100%, inset: (left: 1em))[
    *Theorem #context counter(figure.where(kind: "theorem")).display("1")*#if name != none [ (#name)]. #body
  ]
)

#let proposition(name: none, body) = figure(
  kind: "proposition", supplement: [Proposition], numbering: "1", outlined: false,
  block(width: 100%, inset: (left: 1em))[
    *Proposition #context counter(figure.where(kind: "proposition")).display("1")*#if name != none [ (#name)]. #body
  ]
)

#let lemma(name: none, body) = figure(
  kind: "lemma", supplement: [Lemma], numbering: "1", outlined: false,
  block(width: 100%, inset: (left: 1em))[
    *Lemma #context counter(figure.where(kind: "lemma")).display("1")*#if name != none [ (#name)]. #body
  ]
)

#let corollary(name: none, body) = figure(
  kind: "corollary", supplement: [Corollary], numbering: "1", outlined: false,
  block(width: 100%, inset: (left: 1em))[
    *Corollary #context counter(figure.where(kind: "corollary")).display("1")*#if name != none [ (#name)]. #body
  ]
)

#import "figures.typ": fig-softmax, fig-obstacle, fig-psi, fig-maxent, fig-example

#show figure.caption: set text(size: 9pt)

// Intuition boxes: plain-language explanations for readers outside the area
#let intuition(body) = block(
  width: 100%,
  inset: (x: 1em, y: 0.7em),
  fill: luma(248),
  stroke: (left: 1.5pt + luma(170)),
)[#text(weight: "bold")[Intuition. ]#body]

#align(center)[
  #text(size: 15pt, weight: "bold")[
    Prediction Markets Are Fisher Markets
  ]
  #v(0.5em)
  #text(size: 11pt)[Batch Auction Clearing via Eisenberg-Gale Duality]
  #v(0.5em)
  #text(size: 10pt)[Valeriy Cherepanov]
  #v(0.3em)
  #text(size: 9pt, style: "italic")[Draft — July 2026]
]

#v(1em)

#block(inset: (x: 2em))[
  #text(weight: "bold")[Abstract.]
  A prediction-market exchange clears batched limit orders at uniform prices. Without market makers this is a linear program. Budgeted market makers break it: a market maker posts many orders against one deposited balance, and the capital those orders consume depends on clearing prices, which depend in turn on which orders fill. The resulting hard-budget constraint couples prices and fills, and the feasible set can be non-convex. We instead model the balance through a retained-cash preference $B ln(U+s)-s$. Optimizing out cash $s$ yields an exact reduced-form utility: affine while capital is slack, logarithmic once capital binds (@prop-reduced). Under this utility, batch clearing is a convex program of Eisenberg–Gale type: a quasilinear Fisher market whose supply side is minting complete sets rather than a fixed endowment (@thm-main). Budgets vanish from the constraints yet hold at every optimum, because the reduced-form utility makes them self-enforcing even for a price-taker (@lem-selfenforcing). Optima coincide with competitive equilibria of the underlying economy (@prop-eq), in which a capital-scarce market maker shades all its quotes by a single pacing factor $alpha_k = B_k \/ V_k$. For every smoothing temperature $b > 0$ clearing prices are unique, and as $b -> 0$ they converge to the maximum-entropy zero-temperature price (@prop-maxent). The convex program has a polynomial-size conic formulation and supplies a tractable surrogate for the original non-convex problem: its exact solution is feasible for the hard budgets, with additive welfare gap at most $sum_k Delta_k^2 \/ (2B_k)$ in the budget shortfalls $Delta_k$ (@cor-approx). At zero temperature it can also be solved by a certificate-bearing generalized Frank–Wolfe method whose oracle is the exchange's ordinary matching LP; in a frozen held-out synthetic evaluation the method returned verifier-valid, hard-budget-feasible allocations in all 135 declared problems.
]

#v(1em)

= Introduction

A prediction-market exchange runs _batch auctions_: orders accumulate over an interval, then clear simultaneously at uniform prices. The clearing problem chooses fills and prices to maximize welfare while delivering every promised share. Delivery comes from _minting_ complete sets, one share of every outcome for \$1. If every order locks its capital at submission, this is a linear program.

Market makers break the LP. An ordinary participant may submit "buy 100 shares of Yes at \$0.60," for which the exchange can lock \$60 upfront. A market maker posts _hundreds_ of orders across _dozens_ of markets against a single deposited balance $B_k$. Its capital use depends on the fills and their clearing prices, both chosen in the auction. The resulting price–fill product can make the feasible set non-convex for _every_ liquidity parameter $b > 0$ (§3). Standard convex optimization no longer applies directly, and the iterative heuristics used by exchanges lack a general guarantee.

The non-convexity belongs to a particular specification: a hard budget cap appended to a linear objective. For a repeat MM, we instead use the retained-cash primitive $B_k ln(U_k+s_k)-s_k$. Optimizing over unspent cash yields the exact reduced form $psi_(B_k)$ (@prop-reduced), affine while capital is slack and logarithmic once it binds. Substituting this utility for the hard cap turns clearing into a concave program of Eisenberg–Gale type, with shares supplied by minting (@thm-main).

+ A price-taking agent with utility $psi_B$ never spends more than $B$, at any prices whatsoever (@lem-selfenforcing). Every optimum therefore respects the budget although the program contains no budget constraint (@thm-main).

+ Optima are competitive equilibria of an economy with quasilinear traders and a convex-cost minting sector (@prop-eq); minting breaks even at zero temperature. A capital-scarce MM shades every limit price by one scalar $alpha_k = B_k \/ V_k <= 1$, analogous to a pacing multiplier in ad auctions.

+ For every $b > 0$, clearing prices are unique, as are each MM's deployed capital and scarcity factor (@thm-main, @prop-obs). As $b -> 0$ the prices converge to the maximum-entropy zero-temperature optimum (@prop-maxent), which gives a canonical tie-break.

+ The convex optimum is feasible for the original non-convex problem, with welfare within $sum_k Delta_k^2 \/ (2 B_k)$ of the hard-budget optimum in the budget shortfalls $Delta_k$ (@cor-approx).

+ The program admits an exponential-cone formulation and a generalized Frank–Wolfe algorithm whose iterations are ordinary matching LPs. Its certificate bounds the remaining objective gap (@prop-fw-certificate). The algorithm returned a verifier-valid, hard-budget-feasible allocation on all 135 held-out synthetic books; 110 met the configured tolerance and 25 reached the iteration cap with their residual certificates reported (§6).

There is a useful historical symmetry: Eisenberg and Gale (1959) introduced their convex program to aggregate bettors' subjective probabilities under pari-mutuel wagering; here it reappears in a modern prediction-market auction with budgeted MMs.

§2–§5 develop the model and its equilibrium consequences. §6 gives the algorithms, held-out experiment, and decomposition result; §7 collects open problems and related work.

_Closest prior work._ Convex-programming clearing of batched prediction markets goes back to the pari-mutuel call auctions of Peters, So, and Ye (2007) and the unified dynamic framework of Agrawal, Delage, Peters, Wang, and Ye (2011); cost-function market makers were axiomatized by Abernethy, Chen, and Wortman Vaughan (2013); budget constraints for cost-function market makers were studied by Devanur, Dudík, Huang, and Pennock (2015). These papers do not place a budgeted multi-order market maker inside batch clearing. We use quasilinear Eisenberg–Gale technology (Chen, Ye, and Zhang 2007; Cole et al. 2017), which also governs budget pacing in first-price ad auctions (Conitzer et al. 2022). §7 gives detailed comparisons.


= Foundations: Batch Clearing and LMSR <foundation>

The formulation places LP batch clearing and LMSR on one Fenchel-dual continuum, recasting familiar cost-function market-maker results (Abernethy et al. 2013) in batch-clearing language. Throughout, $omega$ indexes outcomes and $k$ indexes market makers.

== Minting Cost and the LP

Consider a prediction market with $K$ mutually exclusive outcomes. In a batch auction, $N$ orders arrive. Each order $i$ has a limit price $L_i$, a maximum quantity $overline(Q)_i$, a side (buy or sell), and a target outcome $omega(i)$. Some orders belong to market makers; we write $"MM"_k$ for the set of orders belonging to MM $k$.

The _net demand_ for each outcome $omega$, meaning buy volume minus sell volume, is

$
D_omega = sum_(i in "buy"(omega)) q_i - sum_(j in "sell"(omega)) q_j
$

where $q_i in [0, overline(Q)_i]$ is the fill quantity of order $i$.

To clear the market, the exchange _mints_ complete sets: one share of every outcome at cost \$1 (exactly one outcome resolves to \$1 at settlement, so the set is fairly priced). The required signed complete-set flow is $max_omega D_omega$: a positive value means minting, while a negative value means redeeming complete sets already supplied by sellers. It covers the highest-demand outcome, with surplus shares of the others left over. The net minting cost is therefore $V(bold(D)) = max_omega D_omega$, and the welfare-maximizing clearing solves

$ P: quad max_(bold(q) in [0, bold(overline(Q))]) quad sum_i w_i q_i - max_omega D_omega (bold(q)) $

where $w_i$ is the welfare coefficient of order $i$ ($+L_i$ for buyers, $-L_i$ for sellers) and $bold(overline(Q)) = (overline(Q)_1, dots, overline(Q)_N)$. Since $V$ is convex and $bold(D)$ is linear in $bold(q)$, the objective is concave. Introducing an explicit minting variable $M >= D_omega$ for each $omega$ gives the equivalent linear program

$
max_(bold(q), M) quad sum_i w_i q_i - M quad "s.t." quad D_omega (bold(q)) <= M quad forall omega, quad bold(q) in [0, bold(overline(Q))]
$

Its dual variables are the clearing prices.

== Fenchel Duality: Prices from Conjugates

The Fenchel conjugate of the minting cost imposes the probability-vector constraint $sum_omega p_omega = 1$, $p_omega >= 0$. Minting at \$1 per complete set _encodes_ the probability axiom.

#intuition[
  Economically, $V^*(bold(p))$ is the largest profit available from a technology with cost $V$ at prices $bold(p)$. A value of zero means that the prices leave no arbitrage; infinity means that the technology can be exploited without bound. The conjugate of the minting cost therefore identifies the arbitrage-free price set. The same calculation will later connect the clearing program to Fisher-market equilibrium.
]

#theorem(name: "Minting–Simplex Duality")[
  _The Fenchel conjugate of $V(bold(D)) = max_omega D_omega$ is the indicator function of the probability simplex:_
  $ V^* (bold(p)) = delta_Delta (bold(p)) = cases(0 & "if" bold(p) in Delta, +infinity & "otherwise") $
  _where $Delta = {bold(p) >= 0 : sum_omega p_omega = 1}$._
] <thm-minting>

_Proof._ For $bold(p) in Delta$, $sum_omega p_omega D_omega <= max_omega D_omega$, so the conjugate is at most zero and attains zero at $bold(D)=bold(0)$. If $sum_omega p_omega != 1$, take $bold(D)=t bold(1)$ and send $t$ to the sign that makes $t(sum_omega p_omega-1)$ diverge. If the coordinates sum to one but some $p_j<0$, take $D_j=-t$ and all other coordinates zero; then $chevron.l bold(p),bold(D)chevron.r-max_omega D_omega=-t p_j -> +infinity$. (With one outcome, the latter case cannot occur.) These cases exhaust $bold(p) in.not Delta$. #h(1fr) $square$

The probability axiom is thus a no-arbitrage condition. Any deviation from the simplex is an arbitrage (if $sum_omega p_omega > 1$, mint at \$1 and sell at $sum_omega p_omega$), and the conjugate enforces it as a hard constraint.

== Entropy Smoothing: LMSR as Soft LP

Use the explicit cost family
$
C_b(bold(D)) = cases(
  max_omega D_omega & "if" b=0,
  b ln sum_omega exp(D_omega\/b) & "if" b>0.
)
$
For $b>0$, Hanson's LMSR cost is a smooth ($C^infinity$) version of the minting cost. Its structural content is in its Fenchel conjugate: where $C_0^* = delta_Delta$ is a hard constraint (prices must be probabilities), $C_b^*$ is an entropic penalty.

#theorem(name: "LMSR–Entropy Duality")[
  _For $b>0$, the Fenchel conjugate of $C_b$ is negative Shannon entropy on the simplex:_
  $ C_b^*(bold(p)) = cases(
    b sum_omega p_omega ln p_omega quad & "if" bold(p) in Delta,
    +infinity & "otherwise"
  ) $
] <thm-lmsr>

_Proof._ First take $bold(p) in Delta$. For arbitrary finite $bold(D)$ let $r_omega = exp(D_omega\/b)\/Z$, where $Z=sum_(omega') exp(D_(omega')\/b)$. Then $bold(r)$ has full support and
$
chevron.l bold(p),bold(D)chevron.r-C_b(bold(D))
= b sum_omega p_omega ln r_omega
= b sum_omega p_omega ln p_omega-b "KL"(bold(p) parallel bold(r))
<= b sum_omega p_omega ln p_omega,
$
with $0 ln 0=0$. This argument includes boundary points of the simplex. If $bold(p)$ has full support, equality is attained by $D_omega=b ln p_omega$. If some coordinates vanish, set $bold(p)^epsilon=(1-epsilon)bold(p)+epsilon bold(u)$ for the uniform $bold(u)$ and choose $D_omega^epsilon=b ln p_omega^epsilon$; the displayed value tends to $b sum_omega p_omega ln p_omega$, so the same number is the supremum.

Outside $Delta$, if $sum_omega p_omega != 1$, the direction $bold(D)=t bold(1)$ makes the objective diverge for one sign of $t$. If the coordinates sum to one but some $p_j<0$, take $D_j=-t$ and the other coordinates zero; the linear term diverges while $C_b(bold(D))$ stays bounded as $t -> infinity$. Thus the conjugate is $+infinity$ outside the simplex. #h(1fr) $square$

The approximation quality is controlled by $b$:

#proposition(name: "LSE–Max Sandwich")[
  $max_omega D_omega <= C_b (bold(D)) <= max_omega D_omega + b ln K$. _The gap $b ln K$ is the maximum LMSR subsidy._
] <prop-sandwich>

_Proof._ $exp(max_omega D_omega\/b) <= sum_omega exp(D_omega\/b) <= K exp(max_omega D_omega\/b)$. Apply $b ln$. #h(1fr) $square$

In practice one picks $b$ so that the worst-case subsidy $b ln K$ sits below the venue's per-batch tolerance or below one price tick; the smoothed auction then stays close to LP clearing while delivering unique prices (@thm-unique). @fig-softmax shows the knob at work.

#figure(
  fig-softmax,
  kind: image,
  supplement: [Figure],
  caption: [The temperature knob in a binary market. The LP clearing price is a step at zero net demand gap ($b -> 0$); positive temperature replaces the step by the softmax $sigma(d\/b)$, at a worst-case subsidy of $b ln K$ (@prop-sandwich).],
) <fig-softmax>

The conjugate pairs are:

#align(center)[
  #table(
    columns: 3,
    align: center,
    stroke: none,
    [$V = max_omega D_omega$], [$stretch(arrow.l.r, size: #200%)^("Fenchel")$], [$V^* = delta_Delta$],
    [$arrow.t space b -> 0$], [], [$arrow.t space b -> 0$],
    [$C_b = b ln sum_omega exp(D_omega\/b)$], [$stretch(arrow.l.r, size: #200%)^("Fenchel")$], [$C_b^* = b sum_omega p_omega ln p_omega$],
  )
]

As $b -> 0$, the smooth cost $C_b$ sharpens to the LP cost $V$, and the entropy penalty hardens to the simplex indicator.

== The Smoothed Batch Auction and Its KKT Conditions

Replace the minting cost $V$ with $C_b$ in the batch clearing:

$ P_b: quad max_(bold(q) in [0, bold(overline(Q))]) quad sum_i w_i q_i - C_b (bold(D)(bold(q))) $

Since $C_b$ is convex and smooth and $bold(D)(bold(q))$ is linear, $P_b$ is a smooth concave maximization. Its first-order conditions are necessary and sufficient, and the exponentials in the clearing prices come from the minting cost, not the order book.

#theorem(name: "LMSR = Smoothed Batch Clearing")[
  _At the optimum of $P_b$, the clearing prices are the softmax of net demand:_
  $ p_omega^* = (partial C_b) / (partial D_omega) = exp(D_omega^* \/ b) / (sum_(omega') exp(D_(omega')^* \/ b)) $
  _This is the LMSR marginal price function. By construction, $sum_omega p_omega^* = 1$._
] <thm-clearing>

As $b -> 0$, the optimal value of $P_b$ converges to that of $P$ by the uniform approximation in @prop-sandwich, and cluster points of its optimizers solve $P$. As $b -> infinity$, $exp(D_omega\/b) -> 1$ for all $omega$, so prices flatten to uniform.

The KKT conditions yield the standard _Uniform Clearing Price_ (UCP) rule: an order fills fully if its limit price strictly beats the clearing price, is rejected if strictly worse, and may fill partially at equality. Entropy smoothing does not alter order-matching logic; it only makes prices depend continuously on quantities through softmax rather than discretely through the marginal order.

== Price Uniqueness Without Budgets

Without budget constraints, clearing prices are unique for every $b > 0$ and every order book. This is proved in the Fenchel dual, where the entropy term provides strict convexity. Write $W(bold(D))$ for the maximum welfare achievable at a given demand vector $bold(D)$ (the inner LP over fills $bold(q)$ with $bold(D)$ fixed). The primal problem in demand space is $max_(bold(D)) [W(bold(D)) - C_b (bold(D))]$, where $W$ is concave piecewise-linear. By Fenchel–Rockafellar duality, this is equivalent to minimizing over prices:

$
min_(bold(p) in Delta) [underbrace(Phi(bold(p)), "order surplus") + underbrace(C_b^* (bold(p)), "entropy penalty")]
$

where $Phi(bold(p)) := sup_(bold(D)) {W(bold(D)) - chevron.l bold(p), bold(D) chevron.r}$ is the order-surplus function and $C_b^* (bold(p)) = b sum_omega p_omega ln p_omega$ is the negative Shannon entropy (@thm-lmsr).

#theorem(name: "Unconstrained Price Uniqueness")[
  _The Fenchel dual of the unconstrained smoothed problem is strictly convex on the simplex: $Phi$ is convex, and $C_b^* (bold(p)) = b sum_omega p_omega ln p_omega$ is strictly convex on $Delta$ (with the convention $0 ln 0 := 0$). The clearing prices $bold(p)^*$ are therefore unique for any $b > 0$ and any order book, unconditionally._
] <thm-unique>

_Proof._ $Phi$ is a pointwise supremum of affine functions of $bold(p)$, hence convex. The scalar function $x |-> x ln x$ is strictly convex on $[0, +infinity)$, so $sum_omega p_omega ln p_omega$ is strictly convex on $Delta$. Therefore $Phi + C_b^*$ is strictly convex there. Since $Delta$ is compact and the dual objective is lower-semicontinuous, a minimizer exists; strict convexity makes it unique. #h(1fr) $square$


= The Budget Obstacle <obstacle>

Without budgets, batch clearing is a standard convex program (@thm-unique). A shared MM budget changes the geometry: the capital charged to a fill depends on its clearing price, and that price depends on the fills. The feasible set can then be non-convex.

== The Bilinear Constraint

A market maker $k$ deposits balance $B_k$ and posts orders across multiple markets. The capital consumed by each fill depends on the clearing price:

$
"cap"_k (bold(p), bold(q)) = sum_(i in "MM"_k) c_i (p_(omega(i))) dot q_i, quad c_i (p) = cases(p & "if BuyYes/SellNo", 1-p & "if SellYes/BuyNo")
$

The budget constraint $"cap"_k <= B_k$ is _bilinear_ in prices and fills, and $bold(p)$ is itself determined by $bold(q)$ through the clearing mechanism. The composite product $c(p(bold(q))) dot q$ can make the feasible set non-convex in fill space. This single constraint is what separates prediction-market clearing from a standard LP.

== Computational Consequences <computational>

The budget constraint has three consequences for computation:

*1. The feasible set can be non-convex.* Define $h_k (bold(q)) = sum_(i in "MM"_k) p_(omega(i))(bold(q)) dot q_i$ as MM $k$'s capital consumption. Take the simplest non-trivial case: an MM with buy orders on two independent binary groups, one order per group, fill quantities $q_1, q_2$. Since the groups are independent, $h = f(q_1) + f(q_2)$ where $f(q) = sigma(q\/b) dot q$ and $sigma$ is the logistic sigmoid. Differentiating:
$
f''(q) = (sigma(1-sigma)) / b [2 + q(1-2sigma) / b]
$
Since $sigma(1-sigma) > 0$, the sign is that of the bracket. At $q = 0$: $f''(0) = 1\/(2b) > 0$ (convex). For large $q$: $sigma -> 1$ and the bracket tends to $-infinity$ (concave). The inflection point is at $q^* approx 2.4 b$. So $h$ is neither convex nor concave.

This witness is not knife-edge in $b$. Writing $f_b (q) = sigma(q\/b) q$, we have the scaling identity $f_b (b t) = b f_1(t)$ and therefore $h_b (bold(q)) = b h_1(bold(q)\/b)$. So for _every_ $b > 0$, the points
$
x_b = (2 b, 9 b), quad y_b = (9 b, 2 b), quad m_b = (5.5 b, 5.5 b)
$
satisfy
$
h_b (x_b) = h_b (y_b) approx 10.7605 b, quad h_b (m_b) approx 10.9552 b
$
Hence for budget $B = 10.8 b$, both endpoints satisfy $h_b <= B$ while their midpoint violates it. All three points lie in the order-cap box $cal(C)=[0,9b]^2$, so the actual bounded feasible region ${bold(q) in cal(C):h_b(bold(q))<=B}$ is non-convex for every $b > 0$. @fig-obstacle shows the mechanism.

#figure(
  fig-obstacle,
  kind: image,
  supplement: [Figure],
  caption: [Why hard budgets break convexity ($b = 1$). Left: the capital a single order consumes, $f(q) = sigma(q\/b) thin q$, is convex in the fill for small $q$ and concave for large $q$, inflecting at $q^* approx 2.4b$. Right: capital consumed along the segment between the two fill plans $x_b$ and $y_b$ of the two-market witness. Both endpoints respect the budget, while their midpoint does not. The feasible set has a dent.],
) <fig-obstacle>

*2. No standard convex algorithm applies directly.* The unconstrained problem $P_b$ is a smooth concave maximization, solved by interior point in polynomial time. Adding the constraints ${h_k <= B_k}$ can make the feasible set non-convex, and interior point, projected gradient, and Frank–Wolfe all require convex feasible sets. No polynomial-time algorithm is known for the budget-constrained problem.

*3. The uniqueness question is open.* The proof of @thm-unique uses strict convexity of the Fenchel dual. With budgets, the argument breaks: uniqueness at one price vector requires _cross-price budget feasibility_ ($"cap"_k (bold(p)^2, bold(q)^1) <= B_k$), which the bilinear constraint does not guarantee. Whether clearing prices are nonetheless unique for all LMSR instances is open. (In the degenerate case of two identical markets with a symmetric MM, two KKT points exist by symmetry, but this requires exact parameter tuning and does not extend to generic order books.)

#proposition(name: "Computational Obstruction")[
  _For every $b > 0$, the budget-constrained risk-neutral clearing problem admits bounded instances whose feasible set ${bold(q) in cal(C) : h_k (bold(q)) <= B_k}$ is non-convex, so standard convex optimization does not apply directly. By contrast, the reduced-form program $P_b^"RA"$ (@thm-main) is convex and has a polynomial-size conic formulation; under the usual rational-data, regularity, and target-accuracy assumptions, standard conic methods compute an $epsilon$-solution in polynomial time._
] <prop-obstruction>

In practice, exchanges handle budgets by solving without them, checking violations, adjusting, and repeating. Such methods have no general guarantee. A companion note shows that the witness family above is polynomial-time solvable after a change of coordinates, while _retail liquidity walls_ preserve a non-concave frontier (see Open Problems). §5 gives a convex program whose solution is hard-budget feasible and has a quantified welfare guarantee (@cor-approx).

== The Expenditure Perspective

Changing variables to capital expenditures $e_i = c_i (p) dot q_i$ linearizes the budget constraint to $sum_(i in "MM"_k) e_i <= B_k$. In a Fisher market this substitution leads to the Eisenberg–Gale convex program. Here welfare becomes the rational function $sum_i w_i e_i \/ c_i(p)$. The Fisher objective $sum_k B_k ln U_k$ supplies curvature; linear MM welfare does not. Expenditure coordinates therefore move the non-convexity into the objective.

A hard cap may be a literal collateral or liquidity rule rather than a preference. The non-convexity here comes from combining that abrupt global boundary with constant marginal welfare. For repeat MMs, we study diminishing returns with endogenous cash retention. §4 gives the economic intuition, and §5 states the primitive and derives the clearing program.


= Budgets as Preferences <economic-case>

The convexification rests on a modeling choice: for a repeat-participation MM, the marginal value of another fill can decline once capital becomes scarce. This section gives the economic case for that choice; the formal primitive appears in §5.

== Kelly as Repeated-Game Motivation

Breiman (1961) showed that log utility is growth-optimal under classical repeated favorable-bet assumptions. Prediction-market exchanges likewise run repeated batches, so $sum_t EE[ln(1+r_t)]$ suggests why log curvature may be appropriate for survival-aware sizing. The formal model begins in §5 from an explicit retained-cash primitive.

== What a Budget Can Mean

An MM limit may be a literal collateral or institutional constraint. It may also be an internal exposure target: the next fill is worth less as more capital is already committed. The model addresses this second interpretation, preserving the dollar scale $B_k$ in a smooth marginal-value schedule.

== Order-Book Intuition

MMs often post _ladders_, with quantities falling as limit prices move down, and impose position limits. Both encode declining marginal value in the order book. Ad exchanges manage advertiser budgets by multiplicative bid shading ("pacing"), and pacing equilibria coincide with quasilinear Fisher-market equilibria (Conitzer et al. 2022). The analogy is behavioral: both systems manage a shared budget by shading many quotes with one multiplier.

= Reduced-Form Utility and Fisher-Market Clearing <risk-averse>

== Reduced-Form MM Utility

Let $U_k$ denote MM $k$'s weighted fill (fill value at limit prices, defined formally in @thm-main), and let $s_k >= 0$ be cash the MM retains rather than deploys. The MM's deployed value is $V_k = U_k + s_k$, and its objective over retained cash is $B_k ln V_k - s_k$: log utility over deployed value, quasilinear cost of cash. Optimizing out the cash yields the paper's central object (@fig-psi).

#proposition(name: "Reduced-Form MM Utility")[
  _Optimizing over retained cash yields the MM utility_
  $ psi_(B_k)(U) = max_(s >= 0) [B_k ln (U + s) - s] = cases(
    U + B_k ln B_k - B_k & "if" U <= B_k,
    B_k ln U & "if" U >= B_k
  ) $
  _This utility is concave and $C^1$, with derivative $psi_(B_k)'(U)=1$ for $U<=B_k$ and $psi_(B_k)'(U)=B_k\/U$ for $U>B_k$. Equivalently, for $U>0$ it is $min(1,B_k\/U)$; its continuous value at $U=0$ is $1$. It satisfies the affine-envelope bound $psi_(B_k)(U) <= U + B_k ln B_k - B_k$, with equality exactly on the slack-budget region $U <= B_k$. MM utility is affine when the budget is slack and logarithmic when capital binds._
] <prop-reduced>

_Proof._ In the deployed-value variable $V = U + s$, the problem is $psi_(B_k)(U) = max_(V >= U) [B_k ln V - V + U]$. The derivative and curvature of the bracket are $B_k \/ V - 1$ and $-B_k \/ V^2 < 0$, so the maximizer is $V^* = max(U, B_k)$. Substituting gives the piecewise formula; the derivative follows from the two branches and matches at $U = B_k$. #h(1fr) $square$

#figure(
  fig-psi,
  kind: image,
  supplement: [Figure],
  caption: [The reduced-form utility $psi_B$ (drawn for $B = 1$). On the slack region it coincides with the affine risk-neutral envelope; once capital binds it bends onto the log branch. The naive $B ln U$ model (dotted) would punish an MM for having spare capital; the retained-cash option pastes the two branches together $C^1$-smoothly at $U = B$.],
) <fig-psi>

The central consequence of $psi_B$ is that an agent respects the budget $B$ at any prices, without an explicit budget constraint.

#lemma(name: "Self-Enforcing Budgets")[
  _Fix any price vector $bold(p)$ and let $bold(x)^*$ maximize the quasilinear payoff_
  $ psi_B (U(bold(x))) - sum_i p_(omega(i)) x_i, quad U(bold(x)) = sum_i L_i x_i, quad L_i > 0 $
  _over the box $bold(x) in [0, bold(overline(Q))]$. Then its spending satisfies_
  $ sum_i p_(omega(i)) x_i^* <= min(U(bold(x)^*), B) <= B $
  _A price-taking agent with utility $psi_B$ never spends more than $B$, whether prices are equilibrium prices or not._
] <lem-selfenforcing>

_Proof._ Let $U^* = U(bold(x)^*)$ and $alpha = psi_B '(U^*)$, using the continuous value $alpha=1$ when $U^*=0$. The objective is concave, so first-order conditions on the box hold at $bold(x)^*$: every order with $x_i^* > 0$ has $alpha L_i >= p_(omega(i))$. Multiplying by $x_i^*$ and summing gives $sum_i p_(omega(i)) x_i^* <= alpha U^* = min(U^*, B)$. #h(1fr) $square$

The budget is now a property of demand rather than a constraint on clearing. Because @lem-selfenforcing holds at any prices, it applies in particular to the equilibrium prices of @thm-main.

#proposition(name: "Deployed-Value Lift")[
  _The reduced-form clearing problem_
  $ max_(bold(q) in cal(C)) quad sum_k psi_(B_k)(U_k (bold(q))) + sum_(j in.not "MM") w_j q_j - C_b (bold(D)(bold(q))) $
  _is equivalent to the deployed-value lift_
  $ max_(bold(q) in cal(C), bold(V) >= bold(U)(bold(q))) quad sum_k [B_k ln V_k - V_k + U_k (bold(q))] + sum_(j in.not "MM") w_j q_j - C_b (bold(D)(bold(q))) $
  _because each MM term is the pointwise maximum over $V_k >= U_k$ of the lifted objective._
] <prop-vlift>

_Proof._ Immediate from @prop-reduced, applied MM-by-MM. #h(1fr) $square$

_Remark (quasilinear Eisenberg–Gale form)._ Writing $s_k = V_k - U_k >= 0$, the lifted MM term is $B_k ln(U_k + s_k) - s_k$: this is exactly the objective of the quasilinear Eisenberg–Gale program for Fisher markets in which buyers may keep money (Chen, Ye, and Zhang 2007; Cole et al. 2017). The program below differs from the classical one only in its supply side.

#intuition[
  The logarithm absorbs a budget through unit expenditure elasticity. At fixed relative prices, doubling every price halves Cobb–Douglas demand and leaves the total bill at $B$. The cash option turns exact spending into an upper bound: the agent banks whatever cannot clear its internal return threshold.
]

== Reduced-Form Clearing Program

#theorem(name: "Reduced-Form Clearing with Budgeted Market Makers")[
  For each MM $k$, let $psi_(B_k)$ be the reduced-form utility of @prop-reduced and consider

  $ P_b^"RA": quad max_(bold(q) in cal(C)) quad underbrace(sum_k psi_(B_k)(U_k (bold(q))), "MM welfare") + underbrace(sum_(j in.not "MM") w_j q_j, "retail welfare") - underbrace(C_b (bold(D)(bold(q))), "minting cost") $

  where $"MM"_k^+$ contains MM $k$'s buy orders after each MM sell has been converted to the complementary buy described under Buy/Sell Reduction below. Converted sells remain MM-owned and enter $U_k$; only genuinely non-MM orders enter retail welfare. Here $U_k (bold(q)) = sum_(i in "MM"_k^+) L_i q_i >= 0$ is MM $k$'s weighted fill ($L_i > 0$), $cal(C) = [0, bold(overline(Q))]$ is the box of admissible fills, and $C_b$ is the cost family defined in §2. At any optimum $bold(q)^*$, define the deployed value $V_k^* = max(U_k (bold(q)^*), B_k)$, retained cash $s_k^* = V_k^* - U_k (bold(q)^*)$, and capital-scarcity factor $alpha_k = B_k \/ V_k^* = psi_(B_k)'(U_k (bold(q)^*)) <= 1$. Then:

  + The objective is concave, the feasible set is convex, and an optimum exists.
  + The program is equivalent to the deployed-value lift of @prop-vlift.
  + Limit orders are exact: if MM order $i$ fills, then $alpha_k L_i >= p_(omega(i))$, hence $L_i >= p_(omega(i))$. No negative-welfare MM fill is possible.
  + No explicit budget constraints appear. Yet at the optimum, each MM $k$ deploys at most $B_k$: capital on fills plus retained cash satisfies $sum_(i in "MM"_k^+) p_(omega(i)) q_i + s_k^* <= B_k$. (This is @lem-selfenforcing evaluated at the equilibrium prices.)
  + The program operates in two regimes per MM. If $U_k (bold(q)^*) < B_k$, then $alpha_k = 1$ and the MM's quotes are unshaded, so it obeys the ordinary risk-neutral UCP rule at the reduced-form clearing prices. A global risk-neutral allocation is recovered only under the hypothesis of @prop-welfare. If $U_k (bold(q)^*) > B_k$, then $alpha_k = B_k \/ U_k (bold(q)^*) < 1$ and lower-ROI fills are throttled.
  + For $b > 0$, clearing prices are unique and equal the softmax rule $p_omega = (partial C_b) / (partial D_omega)$. At $b = 0$, prices are dual variables of the minting epigraph and may be non-unique.
  + The program has a polynomial-size conic reformulation; standard conic complexity guarantees apply to $epsilon$-solutions under their usual input and regularity assumptions.
] <thm-main>

#block(
  inset: (x: 0.9em, y: 0.7em),
  stroke: 0.4pt,
)[
  *Proof Map.*
  #table(
    columns: 3,
    align: (left, left, left),
    stroke: none,
    [*Move*], [*Object*], [*Payoff*],
    [Identify utility], [@prop-reduced], [Affine-below-budget, log-above-budget MM objective],
    [Check price-taking], [@lem-selfenforcing], [Budgets are self-enforcing at any prices],
    [Lift to $V$], [@prop-vlift], [Exact derivation, KKT system, solver form],
    [Read KKT], [$alpha_k = B_k \/ V_k$], [Exact limit orders and budget absorption],
    [Recognize equilibrium], [@prop-eq], [Optima are competitive equilibria],
    [Project to demand], [@prop-ra-value], [Concave demand-space objective],
    [Dualize prices], [@prop-ra-dual, @prop-maxent], [Unique prices for $b > 0$; max-entropy limit],
    [Lift to cones], [@prop-conic], [Polynomial-size formulation and numerical solution],
  )
]

The next proposition is used in part (4) of the proof, where the clearing program is projected into demand space and dualized over prices.

#proposition(name: "Demand-Space Concavity")[
  _Define the feasible demand polytope_
  $ cal(D) = {bold(D) : exists bold(q) " with " bold(q) in cal(C), bold(D)(bold(q)) = bold(D)} $
  _and the inner value function_
  $ W^"RA"(bold(D)) = max_(bold(q) : bold(q) in cal(C), bold(D)(bold(q)) = bold(D)) { sum_k psi_(B_k)(U_k (bold(q))) + sum_(j in.not "MM") w_j q_j } $
  _for $bold(D) in cal(D)$, extended by $-infinity$ outside $cal(D)$. Then $W^"RA"$ is concave._
] <prop-ra-value>

_Proof._ Let $bold(D)^1, bold(D)^2 in cal(D)$ and let $bold(q)^1$ and $bold(q)^2$ attain the maxima defining $W^"RA"(bold(D)^1)$ and $W^"RA"(bold(D)^2)$. For any $theta in [0,1]$, convexity of $cal(C)$ gives $bold(q)^theta = theta bold(q)^1 + (1-theta) bold(q)^2 in cal(C)$, and linearity of $bold(D)$ and $bold(U)$ gives $bold(D)(bold(q)^theta) = theta bold(D)^1 + (1-theta) bold(D)^2$. The inner objective $G(bold(q)) = sum_k psi_(B_k)(U_k (bold(q))) + sum_(j in.not "MM") w_j q_j$ is concave in $bold(q)$, so
$
W^"RA"(theta bold(D)^1 + (1-theta) bold(D)^2) >= G(bold(q)^theta) >= theta G(bold(q)^1) + (1-theta) G(bold(q)^2) = theta W^"RA"(bold(D)^1) + (1-theta) W^"RA"(bold(D)^2)
$
#h(1fr) $square$

== Proof of the Theorem

*(1) Concavity, existence, and lift.* By @prop-reduced, each $psi_(B_k)$ is concave. Since $U_k$ and $bold(D)$ are linear in $bold(q)$, the objective of $P_b^"RA"$ is concave on the compact box $cal(C)$, so an optimum exists by Weierstrass. The deployed-value lift is @prop-vlift, and at any optimum the lifted variable is $V_k^* = max(U_k, B_k)$ with $alpha_k = B_k \/ V_k^* = psi_(B_k)'(U_k) <= 1$.

*(2) Limit order exactness and two regimes.* Work in the lift of @prop-vlift. Let $eta_k >= 0$ be the multiplier for the constraint $U_k (bold(q)) - V_k <= 0$. Stationarity in $V_k$ gives
$
B_k \/ V_k - 1 + eta_k = 0
$
so $eta_k = 1 - alpha_k$. The KKT condition for fill $q_i$ of MM $k$ is then
$
alpha_k L_i - p_(omega(i)) = lambda_i^+ - lambda_i^-
$
because the objective contributes $+L_i$ through $U_k$, while the active lift constraint subtracts $eta_k L_i$; here $lambda_i^+, lambda_i^- >= 0$ are the multipliers of $q_i <= overline(Q)_i$ and $q_i >= 0$. A fill ($q_i > 0$) forces $lambda_i^- = 0$, so $alpha_k L_i >= p_(omega(i))$ and hence $L_i >= p_(omega(i))$: the limit price must beat the clearing price. No negative-welfare fill is possible.

The two regimes follow from $V_k^* = max(U_k, B_k)$. If $U_k > B_k$: $V_k = U_k$, so $s_k = 0$ and $alpha_k = B_k \/ U_k < 1$. If $U_k < B_k$: $V_k = B_k$, so $s_k = B_k - U_k > 0$ and $alpha_k = 1$, and the fill condition $L_i >= p_(omega(i))$ is exactly the risk-neutral UCP condition.

*(3) Budget absorption.* Multiply the fill KKT condition by $q_i$ and sum over $i in "MM"_k^+$. By complementary slackness ($lambda_i^- q_i = 0$):
$
alpha_k underbrace(sum_(i in "MM"_k^+) L_i q_i, = U_k) = sum_(i in "MM"_k^+) p_(omega(i)) q_i + underbrace(sum_(i in "MM"_k^+) lambda_i^+ q_i, >= 0)
$

So $sum_i p_(omega(i)) q_i <= alpha_k U_k$. Complementary slackness for the lift constraint reads $eta_k (V_k - U_k) = 0$, i.e. $(1 - alpha_k) s_k = 0$, so $alpha_k s_k = s_k$. Therefore
$
alpha_k U_k = alpha_k V_k - alpha_k s_k = B_k - s_k
$
and hence
$
sum_(i in "MM"_k^+) p_(omega(i))^* q_i^* + s_k^* <= B_k
$

Each MM's total deployment, capital on fills plus retained cash, is at most $B_k$. The gap $sum_i lambda_i^+ q_i$ is infra-marginal rent from orders filled to their size caps: profit that requires no additional capital. In an uncapped Fisher market this accounting holds with equality; the caps $overline(Q)_i$ allow strict slack. The Eisenberg–Gale objective enforces the budget, while the retained-cash variable absorbs the surplus.

*(4) Price extraction and uniqueness for $b > 0$.* For $b > 0$, prices are the gradient of the smoothed minting cost, $p_omega = partial C_b \/ partial D_omega$. By @prop-ra-value, the demand-space value function $W^"RA"$ is concave, the primal problem is $max_(bold(D)) [W^"RA"(bold(D)) - C_b (bold(D))]$, and Fenchel–Rockafellar duality gives the price problem
$
min_(bold(p) in Delta) [Phi_"RA"(bold(p)) + C_b^*(bold(p))], quad Phi_"RA"(bold(p)) := sup_(bold(D)) {W^"RA"(bold(D)) - chevron.l bold(p), bold(D) chevron.r}
$
where $Phi_"RA"$ is convex and $C_b^*$ is strictly convex on $Delta$ by @thm-lmsr. The dual objective is strictly convex on the simplex, so the minimizing price vector is unique. At $b = 0$, prices are dual variables of the linear minting epigraph $M >= D_omega$ and may be non-unique when several outcomes tie at $max_(omega') D_(omega')$.

*(5) Conic size and solution.* At $b = 0$, @prop-conic gives an exponential-cone formulation of $P_0^"RA"$ whose size is polynomial in the explicit order-book representation. For $b > 0$, the smoothed minting cost admits a lift with $O(K)$ additional exponential cones, or can be handled directly by smooth convex optimization. Standard conic interior-point theory gives polynomial-time $epsilon$-solution guarantees when data are rational, a suitable regularity condition holds, and complexity is measured also in $log(1\/epsilon)$; the theorem does not claim exact finite-bit solution of arbitrary real instances. #h(1fr) $square$

== A Worked Example <example>

Numbers make the two regimes concrete. Consider a binary market ($K = 2$) in the zero-temperature limit $b -> 0$. An MM with budget $B = 50$ posts two buy-Yes orders: $X$ at $L_X = 0.70$ for $100$ shares and $Y$ at $L_Y = 0.55$ for $100$ shares. A retail trader posts order $Z$, buy-No at $L_Z = 0.60$ for $200$ shares.

_LP (no budgets)._ All orders fill at balanced minting ($D_"Yes" = D_"No" = 200$), and welfare is $45$. The MM's capital bill at any supporting price exceeds its budget: even at the lowest dual price $p_"Yes" = 0.40$, capital $= 0.40 times 200 = 80 > 50$. The LP solution cannot be settled.

_Risk-averse._ The MM is capital-constrained ($U^"LP" = 125 > B = 50$, so $s = 0$). Only order $X$ fills: $q_X = 100$, $q_Y = 0$, $q_Z = 100$. The retail order is partially filled, pinning $p_"No" = L_Z = 0.60$, hence $p_"Yes" = 0.40$. The scarcity factor is $alpha = B\/U = 50\/70 approx 0.71$. Order $X$ passes the shaded test because $alpha L_X = 0.50 > 0.40$; order $Y$ fails because $alpha L_Y approx 0.39 < 0.40$. Thus the pacing factor implements the greedy return-on-capital cutoff derived below (@fig-example). Welfare is $30$, and capital consumed is $0.40 times 100 = 40 <= 50$, leaving $10$ of infra-marginal rent from the capped order $X$.

_Welfare gap._ Actual gap $= 15$; the bound of @prop-gap gives $Delta - B ln(1 + Delta\/B) approx 29$ (with $Delta = U^"LP" - B = 75$). The bound is conservative because the retail side contracts proportionally.

#figure(
  fig-example,
  kind: image,
  supplement: [Figure],
  caption: [The worked example in pictures. Left: the capital-scarce MM's posted quotes (gray) are shaded by its scarcity factor $alpha = 50\/70$ (blue); the $0.70$ bid still clears the price, while the $0.55$ bid is rejected. Right: the LP fill plan consumes $80$ against a budget of $50$ and cannot settle; the reduced-form clearing consumes $40$, with slack $10$ of infra-marginal rent from the capped order $X$.],
) <fig-example>

== Optima Are Competitive Equilibria

The economy behind $P_b^"RA"$ has three kinds of participants. A _retail order_ is a quasilinear agent that values shares of its target outcome at $L_j$ apiece up to its size cap. A _market maker_ has concave fill utility $psi_(B_k)(U_k)$. A competitive _minting sector_ can create or redeem complete sets at \$1 and supplies net demand $bold(D)$ at cost $C_b(bold(D))$ to maximize $chevron.l bold(p), bold(D) chevron.r - C_b(bold(D))$.

#proposition(name: "Clearing = Competitive Equilibrium")[
  _Fix $b >= 0$. A feasible $bold(q)^*$ (with $V_k^* = max(U_k (bold(q)^*), B_k)$) is optimal for $P_b^"RA"$ if and only if there exists a price vector $bold(p)^*$ such that, writing $bold(D)^* = bold(D)(bold(q)^*)$:_

  + _(Supply optimality) $bold(D)^*$ maximizes mint-sector profit $chevron.l bold(p)^*, bold(D) chevron.r - C_b (bold(D))$; equivalently $bold(p)^* = nabla C_b (bold(D)^*)$ for $b > 0$, and for $b = 0$: $bold(p)^* in Delta$ with $chevron.l bold(p)^*, bold(D)^* chevron.r = max_omega D_omega^*$ (zero profit)._

  + _(Retail optimality) each non-MM order $j$ maximizes its surplus, $(L_j - p_(omega(j))) q_j$ for buys and $(p_(omega(j)) - L_j) q_j$ for sells, over $q_j in [0, overline(Q)_j]$._

  + _(MM optimality) each MM $k$'s fill vector maximizes the quasilinear payoff $psi_(B_k)(U_k (bold(x))) - sum_(i in "MM"_k^+) p_(omega(i))^* x_i$ over its box._

  _Markets clear by construction: the mint sector supplies exactly the traders' net demand $bold(D)^*$. Moreover, by @lem-selfenforcing, every MM's equilibrium spending respects its hard budget $B_k$._
] <prop-eq>

_Proof._ At an optimum, first-order optimality for the concave objective supplies a supporting minting price $bold(p)^* in partial C_b(bold(D)^*)$ (the gradient for $b>0$). Separability of the remaining objective then says exactly that every retail trader and MM maximizes its own utility minus payment at $bold(p)^*$; the subgradient identity is equivalent to supply optimality. This is the usual supporting-price form of the KKT conditions.

The converse is even more direct and avoids reassembling multipliers. For any alternative fills, add all agents' optimality inequalities to the mint sector's profit inequality
$chevron.l bold(p)^*,bold(D)^*chevron.r-C_b(bold(D)^*) >= chevron.l bold(p)^*,bold(D)chevron.r-C_b(bold(D))$.
Trader payments cancel against mint revenue because aggregate demand equals supply. What remains is precisely that the clearing objective at $bold(q)^*$ is at least its value at the alternative fills. #h(1fr) $square$

Two readings of @prop-eq deserve emphasis.

_First welfare theorem._ @prop-eq gives the economic interpretation promised by the title: clearing computes a competitive equilibrium among quasilinear traders and a convex-cost minting sector, which breaks even when $b=0$.

_Pacing._ Condition (3) says a capital-scarce MM behaves like an unconstrained MM whose limit prices are shaded by the single factor $alpha_k = B_k \/ V_k^*$. It fills orders with $alpha_k L_i >= p_(omega(i))$, the greedy return-on-capital rule with cutoff $1 \/ alpha_k$. The factor is analogous to a pacing multiplier in first-price ad auctions, where pacing equilibria also coincide with quasilinear Fisher-market equilibria (Conitzer et al. 2022). Here the multiplier emerges directly from the clearing program.

== Price Dual and Temperature

#proposition(name: "Risk-Averse Price Dual")[
  _Let $W^"RA"$ be the concave demand-space value function of @prop-ra-value. Then the clearing-price problem is_
  $ min_(bold(p) in Delta) [Phi_"RA"(bold(p)) + C_b^*(bold(p))], quad Phi_"RA"(bold(p)) := sup_(bold(D)) {W^"RA"(bold(D)) - chevron.l bold(p), bold(D) chevron.r} $
  _where $C_b^*(bold(p)) = b sum_omega p_omega ln p_omega$ for $b > 0$ and $C_0^* = delta_Delta$. At $b = 0$ the price set minimizes $Phi_"RA"$ over the simplex; for $b > 0$ the minimizer is unique._
] <prop-ra-dual>

_Proof._ This is the dual characterization from part (4) of @thm-main together with @thm-minting and @thm-lmsr. For $b > 0$, uniqueness follows from strict convexity of the entropy term on $Delta$. #h(1fr) $square$

The reduced-form MM utility provides curvature at every temperature, including $b=0$, where the minting cost is the LP cost:

$ P_0^"RA": quad max_(bold(q) in cal(C), bold(V) >= bold(U)(bold(q))) quad sum_k [B_k ln V_k - V_k + U_k (bold(q))] + sum_(j in.not "MM") w_j q_j - max_omega D_omega $

At zero temperature the entropy term disappears from @prop-ra-dual, so tied outcomes can support several dual-optimal prices. Any $b > 0$ makes the price dual strictly convex at subsidy cost at most $b ln K$ (@prop-sandwich). The limit as $b -> 0$ also selects a canonical price:

#proposition(name: "Maximum-Entropy Price Selection")[
  _Let $cal(P)_0 subset Delta$ be the set of zero-temperature clearing prices (the minimizers of $Phi_"RA"$ over $Delta$, @prop-ra-dual), and for $b > 0$ let $bold(p)_b^*$ be the unique clearing price. Then as $b -> 0^+$,_
  $ bold(p)_b^* -> bold(p)^"ME", quad "the unique maximizer of the entropy " H(bold(p)) = -sum_omega p_omega ln p_omega " over " cal(P)_0 $
  _Entropy smoothing selects the maximum-entropy zero-temperature price._
] <prop-maxent>

_Proof._ Write $phi = Phi_"RA"$, convex and lower-semicontinuous on the compact simplex, and fix any $bold(p)_0 in cal(P)_0$. Optimality of $bold(p)_b^*$ in the dual gives $phi(bold(p)_b^*) - b H(bold(p)_b^*) <= phi(bold(p)_0) - b H(bold(p)_0)$, and $phi(bold(p)_b^*) >= phi(bold(p)_0)$ since $bold(p)_0$ minimizes $phi$. Combining,
$
0 <= phi(bold(p)_b^*) - phi(bold(p)_0) <= b [H(bold(p)_b^*) - H(bold(p)_0)]
$
Two consequences: (i) $H(bold(p)_b^*) >= H(bold(p)_0)$ for every $bold(p)_0 in cal(P)_0$; (ii) since $0 <= H <= ln K$, $phi(bold(p)_b^*) -> min_Delta phi$. Let $overline(bold(p))$ be any accumulation point of ${bold(p)_b^*}$ as $b -> 0$. By (ii) and lower semicontinuity, $phi(overline(bold(p))) <= min_Delta phi$, so $overline(bold(p)) in cal(P)_0$. By (i) and continuity of $H$ on $Delta$, $H(overline(bold(p))) >= max_(cal(P)_0) H$. So every accumulation point is a maximum-entropy element of $cal(P)_0$; since $cal(P)_0$ is convex and $H$ strictly concave, that element is unique, and the whole family converges to it. #h(1fr) $square$

Selection by vanishing entropic penalties is classical in linear programming (Cominetti and San Martín 1994; quantitative rates in Weed 2018); @prop-maxent uses the same argument on this convex price dual. An exchange clearing at $b = 0$ can therefore maximize entropy over the zero-temperature price set and recover the limit of every smoothed auction. @fig-maxent illustrates the selection.

#figure(
  fig-maxent,
  kind: image,
  supplement: [Figure],
  caption: [Maximum-entropy price selection (schematic, $K = 3$). The thick segment depicts the zero-temperature price set $cal(P)_0$. For $b > 0$ the price is unique; as temperature falls it converges to the maximum-entropy element of $cal(P)_0$ (@prop-maxent).],
) <fig-maxent>

At positive temperature, uniqueness extends well beyond prices:

#proposition(name: "Unique Observables at Positive Temperature")[
  _Fix $b > 0$. Across all optima of $P_b^"RA"$: (i) the clearing prices are unique; (ii) each MM's deployed value $V_k^*$ and scarcity factor $alpha_k = B_k \/ V_k^*$ are unique, and every capital-constrained MM's weighted fill $U_k = V_k^*$ is unique; (iii) for one modeled outcome space, net demand $bold(D)^*$ is unique up to one global all-ones shift (complete-set churn, which leaves prices unchanged). If the cost is instead a sum over independent groups, there is one such shift per summand. Residual multiplicity is confined to order-level fill reshuffles that preserve these observables._
] <prop-obs>

_Proof._ The optimal set of a concave program is convex. Let $z^0 = (bold(q)^0, bold(V)^0)$ and $z^1 = (bold(q)^1, bold(V)^1)$ be optima of the lifted program and consider the segment $z^t$, optimal throughout. The objective is a finite sum of concave terms and is constant along the segment, so each term is affine along it: if any term lay strictly above its chord at some interior $t$, the sum would exceed the optimal value there. Applying this to $B_k ln V_k$: strict concavity of $ln$ forces $V_k^0 = V_k^1$, hence $alpha_k$ and (for capital-constrained MMs, where $U_k = V_k$) the weighted fill are unique. Applying it to $-C_b (bold(D)(bold(q)^t))$: log-sum-exp is strictly convex transverse to its global all-ones direction, so affineness forces $bold(D)(bold(q)^1)-bold(D)(bold(q)^0)$ to be a global uniform shift; softmax shift-invariance gives identical prices. The same argument applies separately to each summand when the cost decomposes by independent group. #h(1fr) $square$

== Consequences of the Affine Envelope

The reduced-form utility is exactly its affine risk-neutral envelope minus a non-negative penalty on the capital-binding region. Define the affine-envelope gap
$
g_B (U) = U + B ln B - B - psi_B (U) = cases(
  0 & "if" U <= B,
  U - B - B ln(U\/B) & "if" U >= B
)
$
Then $g_B >= 0$, with equality exactly on the slack-budget region, and for any feasible fill vector
$
sum_k psi_(B_k)(U_k (bold(q))) = sum_k [U_k (bold(q)) + B_k ln B_k - B_k] - sum_k g_(B_k)(U_k (bold(q)))
$
So, up to the constant $sum_k (B_k ln B_k - B_k)$, reduced-form clearing is risk-neutral clearing minus the envelope gap.

#proposition(name: "Risk-Neutral Recovery")[
  _Let $bold(q)^"RN"$ be any unconstrained risk-neutral optimum ($P_b$ without budgets). If $B_k >= U_k^"RN" = sum_(i in "MM"_k^+) L_i q_i^"RN"$ for every MM $k$, then $bold(q)^"RN"$ is optimal for the reduced-form program, with retained cash $s_k = B_k - U_k^"RN"$ in the lift. The two programs share an optimum whenever all MM budgets are non-binding._
] <prop-welfare>

_Proof._ If $B_k >= U_k^"RN"$ for all $k$, then $g_(B_k)(U_k^"RN") = 0$ for every MM. At $bold(q)^"RN"$ the reduced-form objective equals risk-neutral welfare plus the constant $sum_k (B_k ln B_k - B_k)$; elsewhere it subtracts the non-negative penalty $sum_k g_(B_k)(U_k (bold(q)))$. Since $bold(q)^"RN"$ maximizes risk-neutral welfare, it also maximizes the reduced-form objective. #h(1fr) $square$

The retained-cash variable acts as a _numeraire good_, eliminating the over-fill pathology of the naive $B_k ln U_k$ model, which forces all budget into fills, including unprofitable ones. The quasilinear structure is essential: without $s_k$, over-capitalized MMs would distort fills to exhaust their budgets.

#proposition(name: "Welfare Gap Bound")[
  _Let $bold(q)$ be any feasible comparator and let $bold(q)^"RA"$ be a reduced-form optimum. Write $F$ for risk-neutral welfare with the same minting cost and let $Delta_k(bold(q))=max(0,U_k(bold(q))-B_k)$. Then_

  $ F(bold(q))-F(bold(q)^"RA") <= sum_k [Delta_k(bold(q))-B_k ln(1+Delta_k(bold(q))\/B_k)] <= sum_k Delta_k(bold(q))^2\/(2B_k). $

  _In particular, $bold(q)$ may be an unconstrained risk-neutral optimum. Comparators with $U_k(bold(q))<=B_k$ contribute nothing; the bound is quadratic in the shortfall._
] <prop-gap>

_Proof._ By the envelope decomposition, the reduced-form objective is $F(bold(q)) + sum_k (B_k ln B_k - B_k) - sum_k g_(B_k)(U_k (bold(q)))$. Since $bold(q)^"RA"$ maximizes it, for every feasible comparator $bold(q)$,
$
F(bold(q)^"RA") - sum_k g_(B_k)(U_k (bold(q)^"RA")) >= F(bold(q)) - sum_k g_(B_k)(U_k(bold(q))).
$
Rearranging and using $g_B >= 0$ gives $F(bold(q))-F(bold(q)^"RA") <= sum_k g_(B_k)(U_k(bold(q)))$. Substituting $Delta_k(bold(q))=max(0,U_k(bold(q))-B_k)$ gives the exact penalty. The quadratic bound follows from $ln(1+x)>=x-x^2\/2$ for $x>=0$. #h(1fr) $square$

The exact penalty is quadratic to second order near $Delta_k=0$ and asymptotically linear for large shortfalls; the final quadratic expression is a convenient global upper bound and can be loose. If the risk-neutral program has several optima, any of them is a valid comparator, and choosing one with the smallest displayed penalty gives the sharpest corollary.

The same envelope bound connects the reduced-form solution to the hard-budget benchmark of §3 and yields an approximation algorithm.

#corollary(name: "Feasible Approximation of Hard-Budget Clearing")[
  _Fix $b > 0$ and consider the non-convex hard-budget program of §3:_
  $ "OPT"^"HB" = max {F(bold(q)) : bold(q) in cal(C), " " h_k (bold(q)) <= B_k " for all " k} $
  _where $F(bold(q)) = sum_i w_i q_i - C_b (bold(D)(bold(q)))$ is risk-neutral welfare and $h_k (bold(q)) = sum_(i in "MM"_k^+) p_(omega(i))(bold(q)) q_i$ with $bold(p)(bold(q)) = nabla C_b (bold(D)(bold(q)))$. Let $bold(q)^"RA"$ solve $P_b^"RA"$. Then $bold(q)^"RA"$ is feasible for the hard-budget program, and_
  $ "OPT"^"HB" - F(bold(q)^"RA") <= sum_k [Delta_k - B_k ln(1 + Delta_k / B_k)] <= sum_k Delta_k^2 / (2 B_k) $
  _where $Delta_k=max(0,U_k(bold(q)^"RN")-B_k)$ for any chosen unconstrained risk-neutral optimum $bold(q)^"RN"$. A single convex solve yields a feasible point of the non-convex problem with an additive welfare guarantee._
] <cor-approx>

_Proof._ Feasibility: at the optimum of $P_b^"RA"$ the clearing prices are exactly $bold(p)(bold(q)^"RA")$, so budget absorption (@thm-main, part 4) gives $h_k (bold(q)^"RA") <= B_k - s_k^* <= B_k$. Gap: dropping the budget constraints gives $"OPT"^"HB" <= F(bold(q)^"RN")$; applying @prop-gap with comparator $bold(q)^"RN"$ bounds $F(bold(q)^"RN")-F(bold(q)^"RA")$ by the displayed penalty. #h(1fr) $square$

Thus one convex optimization replaces solve–check–adjust iteration and returns a hard-budget-feasible point with a welfare guarantee. §6 gives a conic formulation and a certified method built from the exchange's matching LP.

== Fisher Interpretation

In a Fisher market (Eisenberg and Gale 1959), $n$ consumers with budgets $B_k$ purchase divisible goods with fixed supply $S_j$ at prices $p_j$. Market equilibrium is characterized by the convex program

$ "EG": quad max_(bold(x) >= 0) quad sum_k B_k ln U_k (bold(x)_k) quad "s.t." quad sum_k x_(k j) <= S_j quad forall j $

where $U_k (bold(x)_k) = sum_j u_(k j) x_(k j)$ is consumer $k$'s linear utility. The supply constraints have dual variables $p_j$, the equilibrium prices. Budget constraints do not appear explicitly; they emerge from the $B_k ln U_k$ objective by the same telescoping argument as part (3) of our proof. Adding a cash variable $s_k$ with cost $-s_k$ yields the _quasilinear_ Fisher market (Chen, Ye, and Zhang 2007; Cole et al. 2017), in which agents may retain unspent budget.

Program $P_b^"RA"$ is a quasilinear Fisher market with two extensions. Supply is endogenous: outcome shares are created by minting at convex cost $C_b (bold(D))$ rather than drawn from a fixed endowment, so prices are the gradient of the supply cost (softmax) rather than duals of supply constraints. And linear-welfare retail orders trade alongside the log-utility MMs. Both extensions preserve concavity, and @prop-eq upgrades the analogy to an exact equilibrium statement.

== Behavior at Clearing

Under $P_b^"RA"$, a capital-constrained MM ($alpha_k < 1$) applies one return-on-capital cutoff across its entire order book, so lower-ROI fills are throttled first. An over-capitalized MM ($alpha_k = 1$) has unshaded quotes and follows the same UCP rule as a risk-neutral MM at the reduced-form prices; equality of the whole allocation with a risk-neutral optimum requires the recovery hypothesis of @prop-welfare. Non-MM orders continue to follow UCP at the clearing prices; minting and limit-order exactness are unchanged. Prices are softmax for $b>0$ and dual-optimal minting prices for $b=0$.

== Buy/Sell Reduction

In a binary market, replace an MM order to sell Yes at $L$ by an order to buy No at $1-L$. If $bold(D)$ includes the sell and $bold(D)'$ the replacement, then $bold(D)' = bold(D)+q bold(1)$. Translation equivariance of minting cost gives
$
(1 - L) q - C_b(bold(D)') = (1 - L) q - C_b(bold(D) + q bold(1)) = - L q - C_b(bold(D)).
$
Thus the objective is unchanged while every newly collateralized MM position is represented as a buy in $"MM"_k^+$ and enters $U_k$. Only liquidation of shares already held, rather than a new short position, bypasses this budget accounting.

== Multiple Groups and Bundle Orders <bundles>

Nothing in @thm-main requires a single mutually exclusive group. Consider $n$ groups, group $j$ having $K_j$ mutually exclusive outcomes. The joint state space is $cal(S) = product_j {1, dots, K_j}$ (exactly one joint state is realized). Bundle orders, whose payoffs depend on the joint state, create demand $D_omega$ over $omega in cal(S)$. The minting cost generalizes to $V(bold(D)) = max_omega D_omega$, since one complete set of all joint states costs \$1, and the smoothed version is $C_b = b ln sum_omega exp(D_omega\/b)$. Both are convex in $bold(D)$, and $bold(D)$ is linear in $bold(q)$, so the proof of @thm-main goes through unchanged for any fixed state-space representation. Each MM term remains concave, $-C_b$ remains concave, and budget absorption and limit-order exactness continue to hold.

_Remark (clearing is probabilistic inference)._ With bundle orders, net demand takes the form $D_omega = sum_i theta_i (omega) thin q_i$, where the payoff tensor $theta_i$ of order $i$ depends only on the few groups the order references. The smoothed minting cost $C_b (bold(D)) = b ln sum_omega exp(D_omega\/b)$ is then $b$ times the log-partition function of the Gibbs distribution $pi(omega) prop exp(D_omega\/b)$ whose factor graph is the order book. Clearing prices are its _marginals_: the price of outcome $o$ in group $g$ is $sum_(omega: omega_g = o) pi(omega)$. Evaluating the objective and gradient is exact probabilistic inference. The junction-tree algorithm is polynomial-time for bounded-treewidth bundle-coupling graphs, while the general problem is \#P-hard (Chen et al. 2008). This inference view has precedents on the _pricing_ side: sequential updates on decomposable networks (Pennock and Xia 2011), deployed junction-tree market makers (Laskey et al. 2018), and exponential-family cost functions (Abernethy, Kutty, Lahaie, and Sami 2014). For batch clearing, the objective itself is the order book's log-partition function, making coupling-graph treewidth the relevant complexity parameter (see Open Problems).

When no orders span multiple groups, the joint problem decomposes because $C_b = sum_j C_b^(G_j)$. Cross-group orders break separability transitively: links $A$–$B$ and $B$–$C$ require the full $K_A times K_B times K_C$ space. The convex structure survives this coupling. If the graph splits into components, the joint program decomposes exactly, with each shared MM budget divided in proportion to the deployed value earned in each component (§6).


= Computation <computation>

== Conic Formulation

At $b = 0$, the minting cost $max_omega D_omega$ is modeled by LP epigraph constraints ($M >= D_omega$). In the deployed-value lift of @prop-vlift, all remaining nonlinearity is isolated in the terms $ln V_k$: after introducing epigraph variables $t_k <= ln V_k$, the objective and constraints are linear. Each constraint $t_k <= ln V_k$ is one exponential cone: $(t_k, 1, V_k) in cal(K)_"exp" = {(x,y,z) : y exp(x\/y) <= z}$. This is a polynomial-size formulation. Standard interior-point solvers (Clarabel, MOSEK) target numerical $epsilon$-solutions; their formal complexity guarantees require the usual rational encoding and regularity assumptions. The experiment below measures numerical reliability rather than asserting exact real-arithmetic polynomial time.

#proposition(name: "Conic Reformulation")[
  _At $b = 0$, $P_0^"RA"$ is a conic program: a linear objective over LP constraints plus $n_"MM"$ exponential-cone constraints (one per MM). Clearing prices are the dual variables of the minting epigraph constraints. For $b > 0$, the log-sum-exp minting cost adds $O(K)$ further exponential cones (one per outcome); the augmented-LP view below shows the overhead is modest._
] <prop-conic>

_Remark (Augmented LP)._ The EG Hessian $H = -sum_k (B_k \/ V_k^2) bold(ell)_k bold(ell)_k^T$ has rank at most $n_"MM"$, where $bold(ell)_k$ is MM $k$'s welfare weight vector. By Sherman–Morrison–Woodbury, each Newton step costs an LP interior-point step plus a rank-$n_"MM"$ correction. The LP cost dominates when $n_"MM" << n$, giving the EG problem the same asymptotic complexity as the LP.

== A Certified Matching-LP Oracle

At zero temperature, the exchange can reuse its ordinary matching LP. Each iteration reads the current scarcity factors, shades every MM's ladder by its factor, clears the shaded book, and moves toward that fill plan. The resulting method is both exchange-native and certificate-bearing.

To make this precise, drop the allocation-independent constant $B ln B - B$ from @prop-reduced and write

$
hat(psi)_B(U) = cases(
  U & "if" U <= B,
  B (1 + ln(U\/B)) & "if" U > B.
)
$

Let $R(bold(q)) = sum_(j in.not "MM") w_j q_j - max_omega D_omega(bold(q))$ collect retail welfare and the zero-temperature minting cost, so
$F(bold(q)) = R(bold(q)) + sum_k hat(psi)_(B_k)(U_k(bold(q)))$.
At iterate $bold(q)_t$, set $alpha_(k,t) = hat(psi)'_(B_k)(U_k(bold(q)_t))$, equal to one while capital is slack and $B_k\/U_k$ once it binds, and solve

$
bold(s)_t in arg max_(bold(s) in cal(C))
  [R(bold(s)) + sum_k alpha_(k,t) U_k(bold(s))].
$

This oracle is exactly an ordinary matching LP: the only change is that MM $k$'s values are multiplied by $alpha_(k,t)$. Retained cash makes the method well-defined at the empty-book start $bold(q)_0 = bold(0)$, where every scarcity factor is one. An exact one-dimensional search then chooses $gamma_t in [0,1]$ and updates $bold(q)_(t+1) = (1-gamma_t) bold(q)_t + gamma_t bold(s)_t$.

#proposition(name: "LP-Oracle Certificate")[
  _For any feasible iterate $bold(q)_t$, let $bold(s)_t$ solve the shaded matching LP above and define_
  $
  G_t = R(bold(s)_t) - R(bold(q)_t)
    + sum_k alpha_(k,t) [U_k(bold(s)_t) - U_k(bold(q)_t)].
  $
  _If $bold(q)^*$ maximizes $F$, then_
  $ 0 <= F(bold(q)^*) - F(bold(q)_t) <= G_t. $
  _Thus every oracle call produces an instance-specific upper bound on continuous objective suboptimality; $G_t = 0$ certifies optimality. Exact line search makes the objective non-decreasing._
] <prop-fw-certificate>

_Proof._ Concavity of each $hat(psi)_(B_k)$ gives
$
F(bold(q)^*) <= R(bold(q)^*) + sum_k [hat(psi)_(B_k)(U_k(bold(q)_t))
  + alpha_(k,t)(U_k(bold(q)^*)-U_k(bold(q)_t))].
$
The oracle's optimality lets us replace $bold(q)^*$ on the right by $bold(s)_t$. Subtracting $F(bold(q)_t)$ gives the upper bound $G_t$. The lower bound is optimality of $bold(q)^*$; $G_t >= 0$ also follows because the current iterate is feasible for its own oracle. Exact line search includes $gamma_t = 0$, so it cannot decrease $F$. #h(1fr) $square$

This is generalized Frank–Wolfe: the polyhedral part $R$ is kept exact in the oracle, while only the smooth retained-cash terms are linearized. The certificate is more informative than watching successive pacing factors stop moving. It reports what remains even when a product latency cap ends the iteration.

== Held-Out Solver Evaluation

The first preregistered evaluation exposed a gap between formulation and solver reliability. A generic exponential-cone implementation had a 0.034% median LP-relative welfare shortfall over its 123 valid observations, yet failed numerically in 35 of 158 declarations and succeeded on only 7/21 medium-to-large scaling books. The conic formulation was sound; its generic implementation was not yet a reliable clearing path.

That evidence motivated the retained-cash Frank–Wolfe implementation (RC-FW) described above. RC-FW uses HiGHS for the shaded matching-LP oracle, exact concave line search, and the certificate of @prop-fw-certificate. Its implementation and protocol were frozen before the held-out seeds at #link("https://github.com/MetaB0y/sybil/tree/0f0824ac892d1b9268fa45fded2004f7f9777ff7")[Sybil revision `0f0824a`]; the #link("https://github.com/MetaB0y/sybil/tree/512ecde994e7ffebac8079600ac2bd2f707b9448/benchmarks/solver/results/2026-07-13-v2")[published artifact] contains all 545 declared rows over 135 problem groups, the frozen protocol, raw JSONL, machine metadata, deterministic analysis, and figures. The analysis retains every failed and capped row.

The comparison includes a budget-blind LP, the LP-SLP successive price-linearization heuristic, the Clarabel cone backend, and RC-FW. @tab-empirical-overall reports every declared denominator beside the conditional time and quality summaries.

#figure(
  [
    #set par(justify: false)
    #table(
      columns: (1.35fr, 0.9fr, 1.2fr, 0.85fr, 1.45fr),
      inset: 4pt,
      align: (left, center, center, right, left),
      [*Method*], [*Valid / declared*], [*Termination*], [*Median time*], [*Quality or failure signal*],
      [RC-FW], [135/135], [110 tolerance; 25 cap], [37.5 ms], [P95 certificate 0.0374%],
      [LP-SLP heuristic], [125/125], [106 tolerance; 19 cap], [4.0 ms], [Median observed gap 0.0080%],
      [Clarabel quasi-Fisher], [114/135], [21 numerical failures], [5.9 ms], [Median observed gap 0.000017%],
      [LP, no MM budget], [52/125], [73 capital-invalid], [2.3 ms], [Worst capital use 7.448× budget],
    )
  ],
  caption: [Complete held-out denominators. Runtime and quality summaries use verifier-valid observations; the validity column keeps that conditioning visible. “Observed gap” compares a method with the best landed retained-cash objective returned on the same book. LP-SLP is the successive price-linearization heuristic; the last row is the unconstrained LP.],
) <tab-empirical-overall>

The budget-blind LP violates exact MM capital in 73/125 applicable books and reaches 7.448 times deposited capital in the worst case. RC-FW takes 37.5 ms at the median, about 9.4 times LP-SLP, and returns a verifier-valid, hard-budget-feasible allocation in all 135 declarations. It meets the configured certificate tolerance in 110 cases; the reported certificate distribution includes the 25 cases that reach the 100-update cap. The overall relative certificate has median zero, 95th percentile 0.0374%, and maximum 0.1159% on the heavy-tailed numerical-range stress.

The two-sided flash-liquidity ladder isolates the shared-budget interaction. One MM posts bids and asks across markets, so price and quantity meet at the bilinear boundary of §3. At the 0.5× budget point, all ten budget-blind LP allocations are invalid. LP-SLP's mean observed-best retained-objective gap is 1.9862% (paired bootstrap 95% interval [1.9164%, 2.0464%]); RC-FW's is 0.0003% [0.0001%, 0.0004%], with 10/10 valid allocations. At 0.1× almost all MM liquidity is suppressed. At 0.5× enough remains for successive price linearization to allocate the shared balance poorly, making that intermediate budget the hardest tested point.

#figure(
  image("empirical-figures/budget-retained-objective-gap.svg", width: 100%),
  kind: image,
  supplement: [Figure],
  caption: [Mean retained-cash objective gap to the best verifier-valid landed allocation observed on the same two-sided flash book, over ten paired held-out seeds per budget. RC-FW and LP-SLP are valid 10/10 at every point. Clarabel is valid respectively 9/10, 7/10, 10/10, 7/10, 10/10, and 8/10 from left to right, so its plotted means condition on success. Error bars are paired bootstrap 95% intervals; observed-best gaps are comparison statistics.],
) <fig-empirical-budget>

The guarantee in @prop-gap is an instance-scaled absolute loss. For 73 verifier-valid RC-FW books, the experiment divides observed hard-budget welfare shortfall by the theorem's sharper expression. The ratio has median 0.321 and maximum 0.402. The relevant empirical question is how much slack the proved bound has on a scale fixed before these results were inspected.

#figure(
  image("empirical-figures/certificate-gap.svg", width: 100%),
  kind: image,
  supplement: [Figure],
  caption: [The 95th-percentile RC-FW continuous-objective certificate within each held-out stratum (135/135 allocations verifier-valid). The heavy-tailed numerical-range stress remains below 0.1% at its stratum's 95th percentile; the all-suite 95th percentile is 0.0374% and the maximum is 0.1159%. These bounds concern the continuous retained-cash objective; integer landing is evaluated separately.],
) <fig-empirical-certificate>

#figure(
  image("empirical-figures/scaling-runtime.svg", width: 100%),
  kind: image,
  supplement: [Figure],
  caption: [Successful-run median wall time on held-out two-sided flash books. At 48, 400, and 2,000 declared retail orders, RC-FW and LP-SLP are valid 6/6, 6/6, and 4/4; Clarabel is valid 6/6, 4/6, and 2/4. RC-FW reaches 224.9 ms at the largest tested scale. These measurements cover the tested synthetic scales; exchange-scale production latency remains unmeasured.],
) <fig-empirical-scaling>

RC-FW optimizes continuous fills, whereas settlement requires integers. The evaluated epilogue caps every integer order by the ceiling of its continuous fill, solves a welfare LP inside those caps for uniform settlement prices, and sends the result to an independent integer verifier. Across 135/135 valid allocations, landing loss has median \$0, 95th percentile \$0.00033, and maximum \$0.4893. Rounding may add less than one share per order beyond the continuous fill. Because the landing LP is confined to those caps, it cannot reopen the full order book.

The books are synthetic, timings come from one warm host, the largest flash book has 2,000 retail orders, and 25 RC-FW rows hit the product iteration cap. Clarabel is faster on successful runs and fails numerically in 21/135 declarations. On the tested structural stresses, the retained-cash geometry yields a reliable, auditable solver; Clarabel corroborates objective values when it succeeds. Replay calibration, end-to-end latency, memory, concurrency, and bundle-coupling treewidth remain unmeasured.

== Decomposition for Exponential State Spaces

When no orders span market groups, the minting cost separates across groups, suggesting a decomposition of the EG program into independent per-group subproblems coordinated by MM budget allocation.

Equal scarcity is the coordination invariant that makes decomposition exact:

#proposition(name: "Exact Budget Decomposition")[
  _Suppose the groups partition into components $C_1, dots, C_M$ and no order spans two components, so $C_b = sum_m C_b^m$. Let $bold(q)^*$ be optimal for the monolithic $P_b^"RA"$, with deployed values $V_k^*$ and scarcity factors $alpha_k = B_k \/ V_k^*$. Split retained cash as $s_k^m>=0$ with $sum_m s_k^m=s_k^*$, and set $V_k^(m *)=U_k^m(bold(q)^*)+s_k^m$. For each active pair $(k,m)$ with $V_k^(m *)>0$, allocate_
  $ B_k^m = alpha_k thin V_k^(m *), quad "so that" quad sum_m B_k^m = B_k $
  _where the sum ranges over active pairs; an inactive pair has $U_k^m=s_k^m=0$ and MM $k$ is simply omitted (or frozen at zero fill) in that component. Then each restricted allocation is optimal for its component clearing program with the positive active budgets $bold(B)^m$. Conversely, if positive active component budgets sum to $B_k$ and component optima share one scarcity value per MM, the assembled fills are monolithically optimal. The invariant is equal scarcity, meaning one marginal return-on-capital cutoff $1 \/ alpha_k$ per MM across the whole market, not equal fills or equal budget shares._
] <prop-decomp>

_Proof._ Separability restricts the monolithic prices componentwise. In the lift, the monolithic first-order condition for a fill in component $m$ uses the supporting slope $alpha_k$; the component objective uses $B_k^m\/V_k^(m)$. On every active pair the prescribed budget makes these slopes equal. The supporting-tangent inequality for the concave $psi_B$, summed over MMs and components, therefore shows that monolithic optimality and independent component optimality are equivalent. Retained-cash complementarity is preserved because $s_k^m>0$ can occur only when $alpha_k=1$. Inactive pairs contribute neither fill utility nor cash and need no zero-budget logarithm.

Conversely, common component slopes and $sum_m B_k^m=B_k$ imply the monolithic slope arithmetically. If the common slope is one, each $U_k^m<=B_k^m$, hence $sum_m U_k^m<=B_k$. If it is below one, $B_k^m=alpha_k U_k^m$ on every active pair, hence $B_k=alpha_k sum_m U_k^m$. Thus $psi_(B_k)'(sum_m U_k^m)=alpha_k$ in either case, and the same summed supporting-tangent argument proves monolithic optimality. #h(1fr) $square$

The invariant suggests the coordination scheme: solve the components under a trial allocation, observe deployed values, and reallocate $B_k^m <- B_k dot V_k^m \/ sum_(m') V_k^(m')$. Its fixed points are the equal-scarcity allocations of @prop-decomp. At the margin, an extra dollar in component $m$ earns excess return $1 \/ alpha_k^m - 1$, so budget flows toward scarcer components until the cutoffs agree. This parallels _proportional response_ dynamics in Fisher markets (Wu and Zhang 2007; Birnbaum, Devanur, and Xiao 2011). For quasilinear Fisher markets, mirror descent on a convex reformulation has a sublinear last-iterate rate (Gao and Kroer 2020); extending that guarantee to endogenous supply and this budget-split variant is open. Ascent on the _sum of component EG objective values_ is unsound because the optimal value is convex in the budgets and rewards already saturated components. Scarcity is the appropriate coordination variable.

Under linear welfare, the hard constraint $"cap"_k <= B_k$ has no smooth component split, leaving a combinatorial allocation problem. This is a second payoff of the Fisher structure: log utility both absorbs the monolithic budget and permits componentwise decomposition.

_Empirical boundary._ The first preregistered suite tested already independent single-market groups. Decomposed LP reproduced monolithic LP welfare and allocation in all 16 declared books, but was slower and reached its coordination cap in 11; decomposed quasi-Fisher returned valid allocations in 13/16 and reached its cap in eight. That suite measures coordination overhead outside the proposition's intended combinatorial regime. The held-out RC-FW suite above focuses on the monolithic solver and does not remeasure decomposition.

Timing has to be read in regime context. On independent binary markets, monolithic clearing is already cheap, so decomposition pays coordination overhead without an asymptotic gain. It is aimed at bundle orders and coupled groups, where monolithic enumeration is exponential and coordination is the cheaper problem. If the bundle-coupling graph on $20$ binary groups splits into four components of five groups each, monolithic joint-state clearing sees $2^(20) approx 10^6$ states; componentwise clearing sees $4 dot 2^5 = 128$ plus the coordination layer. Neither preregistered suite probes that regime. Two companion notes in this repository develop the algorithmics: _Decomposed Clearing via Fisher Market Budget Allocation_ (the coordination layer of @prop-decomp, and the convex-surrogate trap it replaces) and _Bundle Clearing_ (component factorization, junction trees, and a priced-injection fallback with a welfare guarantee).


= Discussion <discussion>

== Open Problems

+ *Welfare gap calibration.* The held-out synthetic experiment now measures the instance-wise ratio suggested by @prop-gap rather than testing an arbitrary percentage threshold: over 73 applicable verifier-valid RC-FW books, the observed ratio has median 0.321 and maximum 0.402 (§6). The theorem already supplies the guarantee; the empirical question is how its slack behaves on frozen production replays, richer MM ladders, and adversarial bundle books. Structure-aware bounds could sharpen it further and would transfer directly to @cor-approx.

+ *Combinatorial clearing beyond bounded treewidth.* By the inference reduction of @bundles, bounded-treewidth coupling graphs clear in polynomial time, and the general case inherits \#P-hardness from LMSR pricing (Chen et al. 2008). Real bundle order flow is sparse and low-arity. Is clearing fixed-parameter tractable in the number of bundle orders, or can variational inference approximate it with certified duality gaps?

+ *Zero-temperature fills.* @prop-maxent selects canonical prices at $b = 0$; existence, limit-order exactness, and budget absorption hold at every temperature. What remains open is order-level fill uniqueness: under what nondegeneracy conditions are fills, or at least aggregate demands, unique when the zero-temperature price set is not a singleton?

+ *Complexity of the hard-budget model.* The companion note separates two regimes: thin books (at most one order per market) convexify in expenditure coordinates, while retail walls make the welfare–expenditure frontier genuinely non-concave. A complete hardness classification remains open, as do strong hardness, an additive FPTAS, and MM ladders.

+ *Incentives.* Fisher-market mechanisms are not strategyproof, but are approximately so in large markets, and the pacing literature offers incentive results for quasilinear EG equilibria. Do budgeted MMs have an incentive to shade limit prices or split identities, and does approximate incentive compatibility in the large transfer to batch clearing?

== Connection to Prior Work

*Eisenberg and Gale (1959)* introduced the convex program characterizing Fisher-market equilibrium to aggregate subjective probabilities in pari-mutuel betting. @thm-main extends it to endogenous minting supply and mixed agent types: log-utility MMs alongside linear-welfare retail.

*Peters, So, and Ye (2007)* and *Agrawal, Delage, Peters, Wang, and Ye (2011)* formulated pari-mutuel call auctions and a unified family of prediction-market mechanisms as convex programs, including LMSR as a limiting case. This is the closest formulation-level prior work. It does not model budgeted multi-order market makers; the quasilinear-EG layer that absorbs budgets is the contribution here. Agrawal, Megiddo, and Armbruster (2010) gave the cleanest early prediction-market–EG statement: two-sided markets reduce to parimutuel form with unique, polynomial-time equilibrium prices. That model also omits budgets.

*Taubman and Gleyzer (2026)* reduce a self-financing parimutuel batch mechanism without liquidity providers to scalar root-finding. *Liu, Shen, and Wang (2026)* extend Eisenberg–Gale clearing to value maximizers with budget and return-on-spend constraints in ad markets. Our setting adds shared-balance multi-order MMs and endogenous minting supply.

*Abernethy, Chen, and Wortman Vaughan (2013)* axiomatized cost-function market makers via conjugate duality. §2 recasts their framework as batch-auction clearing: $V = max_omega D_omega$ is the minimal cost function and LMSR its entropy smoothing.

*Devanur, Dudík, Huang, and Pennock (2015)* characterized optimal trades under budget constraints against a cost-function market maker, identifying budget-additivity conditions for sequential LMSR trade. Their setting is a single trader against the market maker; ours is the exchange's clearing problem across many budgeted MMs. Their budget additivity hints at hidden convexity in the sequential risk-neutral setting. For risk-neutral _batches_, the companion note of Open Problem 4 identifies the boundary: thin books convexify, while retail walls may prevent it.

*Chen, Ye, and Zhang (2007)* and *Cole et al. (2017)* developed the quasilinear Fisher-market convex programs that our lifted objective instantiates. The extension here is endogenous supply via a convex minting cost and the coexistence of linear-utility retail orders.

*Finster, Goldberg, and Lock (2025)* study budget-constrained quasilinear buyers with linear valuations, which they call the _quasi-Fisher market_, and ask which uniform prices a price-only seller with fixed supply should post. They prove that competitive equilibria coincide with constrained-utilitarian-efficient outcomes and, for linear valuations, that the unique equilibrium prices are also revenue-optimal. The results are complementary to @thm-main: they characterize what equilibrium achieves for a seller; we show that a batch auction with endogenous minting supply computes one. In our program, @prop-reduced absorbs budgets into the objective instead of carrying them in the demand correspondence. Whether their revenue-optimality survives endogenous supply is open.

*Cominetti and San Martín (1994)* established selection by entropic penalties in linear programming, with quantitative rates by Weed (2018); @prop-maxent instantiates the phenomenon for clearing prices, with the LMSR temperature as the penalty.

*Pennock and Xia (2011)*, *Laskey et al. (2018)*, and *Abernethy, Kutty, Lahaie, and Sami (2014)* built the inference view of combinatorial market _pricing_: decomposable-network tractability, deployed junction-tree market makers, exponential-family log-partition prices. The remark of @bundles transports that view to batch clearing, where the objective itself is the log-partition function.

*Conitzer et al. (2022)* showed that first-price pacing equilibria in ad auctions coincide with quasilinear EG solutions. Our scarcity factor $alpha_k$ is precisely a pacing multiplier; the parallel suggests that budget management and market clearing are one problem, in ad markets and prediction markets alike.

*Breiman (1961)* supplies the growth-optimal Kelly intuition used in §4; *Beygelzimer, Langford, and Pennock (2012)* studied Kelly bettors interacting with prediction markets, complementing our equilibrium view of log-utility participants.

*Fortnow, Kilian, Pennock, and Wellman (2005)* posed LP clearing for combinatorial call markets; our group minting encodes mutual exclusivity in $O(K)$ constraints rather than $O(2^K)$ enumeration. *Chen et al. (2008)* proved \#P-hardness of LMSR pricing over combinatorial spaces, which bounds what any clearing algorithm can do on general bundle order flow (@bundles).

*Chen and Pennock (2007)* introduced utility-based bounded-loss market makers. The temperature $b$ here plays the role of their liquidity parameter, with worst-case subsidy $b ln K$ (@prop-sandwich); batch clearing permits $b = 0$ and hence zero subsidy.

*Budish, Cramton, and Shim (2015)* made the case for frequent batch auctions in equity markets; this paper supplies the clearing theory for their prediction-market counterpart.

#heading(numbering: none)[References]

#block[
  #set text(size: 9pt)
  #set par(hanging-indent: 1.4em, first-line-indent: 0em)

  Abernethy, J., Chen, Y., and Wortman Vaughan, J. (2013). Efficient market making via convex optimization, and a connection to online learning. _ACM Transactions on Economics and Computation_ 1(2), Article 12.

  Abernethy, J., Kutty, S., Lahaie, S., and Sami, R. (2014). Information aggregation in exponential family markets. In _Proc. 15th ACM Conference on Economics and Computation (EC)_.

  Agrawal, S., Delage, E., Peters, M., Wang, Z., and Ye, Y. (2011). A unified framework for dynamic prediction market design. _Operations Research_ 59(3):550–568.

  Agrawal, S., Megiddo, N., and Armbruster, B. (2010). Equilibrium in prediction markets with buyers and sellers. _Economics Letters_ 109(1):46–49.

  Beygelzimer, A., Langford, J., and Pennock, D. M. (2012). Learning performance of prediction markets with Kelly bettors. In _Proc. 11th International Conference on Autonomous Agents and Multiagent Systems (AAMAS)_.

  Birnbaum, B., Devanur, N. R., and Xiao, L. (2011). Distributed algorithms via gradient descent for Fisher markets. In _Proc. 12th ACM Conference on Electronic Commerce (EC)_.

  Breiman, L. (1961). Optimal gambling systems for favorable games. In _Proc. Fourth Berkeley Symposium on Mathematical Statistics and Probability_, Vol. 1, 65–78.

  Budish, E., Cramton, P., and Shim, J. (2015). The high-frequency trading arms race: Frequent batch auctions as a market design response. _Quarterly Journal of Economics_ 130(4):1547–1621.

  Chen, L., Ye, Y., and Zhang, J. (2007). A note on equilibrium pricing as convex optimization. In _Proc. 3rd Workshop on Internet and Network Economics (WINE)_.

  Chen, Y., Fortnow, L., Lambert, N., Pennock, D. M., and Wortman, J. (2008). Complexity of combinatorial market makers. In _Proc. 9th ACM Conference on Electronic Commerce (EC)_.

  Chen, Y. and Pennock, D. M. (2007). A utility framework for bounded-loss market makers. In _Proc. 23rd Conference on Uncertainty in Artificial Intelligence (UAI)_.

  Cole, R., Devanur, N. R., Gkatzelis, V., Jain, K., Mai, T., Vazirani, V. V., and Yazdanbod, S. (2017). Convex program duality, Fisher markets, and Nash social welfare. In _Proc. 18th ACM Conference on Economics and Computation (EC)_.

  Cominetti, R. and San Martín, J. (1994). Asymptotic analysis of the exponential penalty trajectory in linear programming. _Mathematical Programming_ 67:169–187.

  Conitzer, V., Kroer, C., Panigrahi, D., Schrijvers, O., Stier-Moses, N. E., Sodomka, E., and Wilkens, C. A. (2022). Pacing equilibrium in first price auction markets. _Management Science_ 68(12):8515–8535.

  Devanur, N. R., Dudík, M., Huang, Z., and Pennock, D. M. (2015). Budget constraints in prediction markets. In _Proc. 31st Conference on Uncertainty in Artificial Intelligence (UAI)_.

  Eisenberg, E. and Gale, D. (1959). Consensus of subjective probabilities: The pari-mutuel method. _Annals of Mathematical Statistics_ 30(1):165–168.

  Finster, S., Goldberg, P. W., and Lock, E. (2025). Competitive and revenue-optimal pricing with budgets. _Theoretical Economics_ 20.

  Fortnow, L., Kilian, J., Pennock, D. M., and Wellman, M. P. (2005). Betting Boolean-style: A framework for trading in securities based on logical formulas. _Decision Support Systems_ 39(1):87–104.

  Gao, Y. and Kroer, C. (2020). First-order methods for large-scale market equilibrium computation. In _Advances in Neural Information Processing Systems 33 (NeurIPS)_.

  Hanson, R. (2003). Combinatorial information market design. _Information Systems Frontiers_ 5(1):107–119.

  Laskey, K. B., Sun, W., Hanson, R., Twardy, C., Matsumoto, S., and Goldfedder, B. (2018). Graphical model market maker for combinatorial prediction markets. _Journal of Artificial Intelligence Research_ 63.

  Liu, X., Shen, W., and Wang, Z. (2026). Mechanism design via market clearing-prices for value maximizers under budget and RoS constraints. arXiv:2602.19085.

  Pennock, D. M. and Xia, L. (2011). Price updating in combinatorial prediction markets with Bayesian networks. In _Proc. 27th Conference on Uncertainty in Artificial Intelligence (UAI)_.

  Peters, M., So, A. M.-C., and Ye, Y. (2007). Pari-mutuel markets: Mechanisms and performance. In _Proc. 3rd Workshop on Internet and Network Economics (WINE)_.

  Taubman, D. and Gleyzer, B. (2026). Batch prediction auctions with a scalar dual reduction. SSRN preprint 6869021.

  Weed, J. (2018). An explicit analysis of the entropic penalty in linear programming. In _Proc. 31st Conference on Learning Theory (COLT)_.

  Wu, F. and Zhang, L. (2007). Proportional response dynamics leads to market equilibrium. In _Proc. 39th ACM Symposium on Theory of Computing (STOC)_.
]
