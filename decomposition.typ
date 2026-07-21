#set document(title: "Decomposed Clearing via Fisher Market Budget Allocation")
#set text(font: "New Computer Modern", size: 10pt)
#set page(margin: (x: 1.5in, y: 1.2in), numbering: "1")
#set par(justify: true, leading: 0.55em)
#set heading(numbering: "1.")
#show heading.where(level: 1): it => block(above: 1.5em, below: 0.8em)[#it]
#show heading.where(level: 2): it => block(above: 1.2em, below: 0.6em)[#it]

#show figure.where(kind: "theorem"): it => align(left, it.body)
#show figure.where(kind: "proposition"): it => align(left, it.body)

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

#align(center)[
  #text(size: 15pt, weight: "bold")[
    Decomposed Clearing \ via Fisher Market Budget Allocation
  ]
  #v(0.5em)
  #text(size: 11pt)[Companion note to _Prediction Markets Are Fisher Markets_]
  #v(0.3em)
  #text(size: 9pt, style: "italic")[Draft — July 2026 (supersedes the February 2026 draft; see Errata)]
]

#v(1em)

#block(inset: (x: 2em))[
  #text(weight: "bold")[Summary.]
  Batch clearing over many market groups decomposes into independent per-group solves when no order spans groups — except that each market maker's single budget must be divided across the components. This note establishes how to divide it. The coordination invariant is _equal scarcity_: allocate each MM's budget across components in proportion to the deployed value each component receives, so that the MM's return-on-capital cutoff $1\/alpha_k$ is one number market-wide. Under that allocation the decomposition is exact (@thm-decomp). We also document a trap that an earlier draft of this note (and a prototype solver) fell into: coordinating budgets by ascending the sum of per-component Eisenberg–Gale objective values is unsound, because EG optimal values are _convex_ in budgets — the surrogate rewards piling budget onto saturated components, and its interior stationary point (equal _utility_) is a minimizer, not a maximizer (@prop-trap). The correct iterative scheme is proportional response on deployed values, whose fixed points are exactly the equal-scarcity allocations.
]

#v(1em)

= Introduction

The main paper proves that batch auction clearing with budget-constrained market makers is a quasilinear Eisenberg–Gale convex program, $P_b^"RA"$. This note addresses a computational consequence. Real venues run hundreds of market groups; when no order spans two groups, the minting cost separates ($C_b = sum_j C_b^(G_j)$) and the clearing program would split into independent, embarrassingly parallel per-group solves — if it were not for the market makers. An MM posts orders in many groups against _one_ budget $B_k$. The groups are coupled only through that scalar.

So the decomposition question is a budget-allocation question: give component $m$ a share $B_k^m$ with $sum_m B_k^m = B_k$, solve the components independently, and choose the shares so that the assembled solution is the monolithic optimum. With linear MM welfare and hard budget caps this allocation is combinatorial. With the reduced-form utility of the main paper it has a closed-form answer.

Throughout, "components" $C_1, dots, C_M$ are the connected components of the bundle-coupling graph — in this note, simply the market groups themselves (or groups of them), with no order spanning two components. The companion note on bundle clearing treats the case where orders do span groups.

= The Exact Decomposition <exact>

== Setup

For each component $m$, the _component program_ $P^m (bold(B)^m)$ is the clearing program of the main paper restricted to component $m$'s orders, with MM budgets $bold(B)^m = (B_k^m)_k$:

$
P^m (bold(B)^m): quad max_(bold(q)_m in cal(C)_m) quad sum_k psi_(B_k^m)(U_k^m (bold(q)_m)) + sum_(j in.not "MM") w_j q_j - C_b^m (bold(D)^m (bold(q)_m))
$

where $psi_B$ is the reduced-form MM utility (affine below budget, logarithmic above), $U_k^m$ is MM $k$'s weighted fill within the component, and retained cash is implicit in $psi$. Write $V_k^m = U_k^m + s_k^m$ for deployed value within the component and $alpha_k^m = B_k^m \/ V_k^m$ for the component scarcity factor.

== The Theorem

#theorem(name: "Exact Budget Decomposition")[
  _Suppose no order spans two components, so $C_b = sum_m C_b^m$. Let $bold(q)^*$ be optimal for the monolithic program, with deployed values $V_k^*$, scarcity factors $alpha_k = B_k \/ V_k^*$, and component deployed values $V_k^(m *)$ (retained cash split arbitrarily across active components). Allocate_
  $ B_k^m = alpha_k thin V_k^(m *), quad "so that" quad sum_m B_k^m = alpha_k V_k^* = B_k $
  _Then the restriction of $bold(q)^*$ to each component $m$ is optimal for $P^m (bold(B)^m)$. Conversely, if an allocation with $sum_m B_k^m = B_k$ admits component optima whose scarcity factors share a common value per MM ($alpha_k^m = alpha_k$ for all components where MM $k$ is active), then the assembled fills are optimal for the monolithic program._

  _The coordination invariant is *equal scarcity* — one marginal return-on-capital cutoff $1\/alpha_k$ per MM across the whole market. It is not equal fills, not equal utility, and not equal budget shares._
] <thm-decomp>

_Proof._ Separability restricts the monolithic clearing prices componentwise: the gradient of $C_b = sum_m C_b^m$ at $bold(D)(bold(q)^*)$ is the concatenation of the per-component softmax prices. In the deployed-value lift, the monolithic KKT condition for a fill $q_i$ in component $m$ reads
$
alpha_k L_i - p_(omega(i)) = lambda_i^+ - lambda_i^-
$
and the component program's KKT condition reads the same with the component scarcity $B_k^m \/ V_k^m$ in place of $alpha_k$. Under the stated allocation, $B_k^m \/ V_k^(m *) = alpha_k$, so the two systems coincide term by term. The cash conditions also match: $s_k^m > 0$ requires $alpha_k^m = 1$, exactly as $s_k > 0$ requires $alpha_k = 1$ monolithically (and when $alpha_k < 1$ there is no cash to split). The restricted point therefore satisfies the component KKT system, and by concavity of the component program it is component-optimal.

Conversely, suppose component optima share scarcity $alpha_k$ per MM. Summing $B_k^m = alpha_k V_k^m$ over $m$ gives $alpha_k = B_k \/ V_k^"tot"$ with $V_k^"tot" = sum_m V_k^m$, which is the monolithic stationarity condition in $V_k$; the union of the component fill conditions is then exactly the monolithic KKT system, and concavity again upgrades KKT to global optimality. #h(1fr) $square$

_Remark (economic reading)._ At the margin, an extra dollar of budget in component $m$ buys fills at the component's cutoff and earns the excess return $1\/alpha_k^m - 1$. If two components offered MM $k$ different marginal returns, moving a dollar from the lower to the higher would raise welfare. Equal scarcity is just "no internal arbitrage across the MM's own allocations."

_Remark (chicken and egg)._ The exact allocation is written in terms of the monolithic optimum, which is what we are trying to avoid computing. The theorem's value is the converse direction: it certifies a fixed point. Any coordination scheme whose fixed points are equal-scarcity allocations solves the monolithic problem by independent component solves. §4 gives such a scheme.

= The Surrogate Trap <trap>

It is tempting to coordinate by treating the sum of component optimal values as the objective: let $W_m^* (bold(B)^m)$ be the optimal value of $P^m (bold(B)^m)$ and ascend $sum_m W_m^* (bold(B)^m)$ over the allocation simplex, using the envelope gradient $partial W_m^* \/ partial B_k^m = ln V_k^(m *)$. An earlier draft of this note did exactly that, concluded that the optimum equalizes component _values_ ($V_k^m$ equal across $m$), and proposed multiplicative-weights ascent. All three steps are wrong, for one reason:

#proposition(name: "EG Values Are Convex in Budgets")[
  _For each component, the optimal value $W_m^*$ is a convex function of the budget vector $bold(B)^m$. Consequently the coordination surrogate $sum_m W_m^*$ is a convex function being maximized over a simplex: its maximizers are extreme points (all-in-one-component allocations), and its interior stationary point — the equal-value allocation — is a minimizer along allocation lines, not a maximizer._
] <prop-trap>

_Proof._ For fixed fills $bold(q)_m$, the objective of $P^m$ is affine in $bold(B)^m$ (through the $B_k^m ln V_k^m$ terms with $V$ held at the maximizing lift value; more directly, in the lifted form $B_k^m ln V_k - V_k + U_k$ the budget enters linearly). The optimal value is a pointwise supremum of affine functions of $bold(B)^m$, hence convex. #h(1fr) $square$

*A two-line counterexample.* Two identical components. In each, the MM can buy up to $overline(Q) = 10$ shares at price $p = 0.5$ with limit value $L = 1$; its total budget is $B = 10$. The monolithic optimum fills both caps: $20$ shares, spend $10 = B$, true welfare $20 dot (L - p) = 10$. The equal split $(5, 5)$ reproduces it, as @thm-decomp predicts ($alpha_k = 1\/2$ in both components). But the surrogate prefers the corner: $W^"srg" (10, 0) = 10 ln 10 - 5 approx 18.0$ versus $W^"srg" (5,5) = 2(5 ln 10 - 5) approx 13.0$. The corner allocation fills only one component — true welfare $5$, half of optimal — yet the surrogate scores it strictly higher, because the term $B_k^m ln (L overline(Q))$ keeps growing in $B_k^m$ after the component is saturated and the excess budget has nothing left to buy. The surrogate pays MMs for parking budget next to exhausted opportunities; true welfare does not.

The lesson for implementers: coordinate on _scarcity_, never on the per-component EG objective values. The two agree about nothing except symmetric instances.

= Proportional Response Coordination <algorithm>

The equal-scarcity invariant dictates the algorithm:

+ *Initialize.* $B_k^m = B_k \/ M_k$ (equal split over MM $k$'s active components).
+ *Solve.* All components in parallel: $P^m (bold(B)^m)$, yielding deployed values $V_k^(m)$.
+ *Reallocate proportionally.* $ B_k^m <- B_k dot V_k^(m) / (sum_(m') V_k^(m')) $
+ *Repeat* until the component scarcity factors $B_k^m \/ V_k^m$ agree per MM.

Fixed points are precisely the allocations with $B_k^m prop V_k^m$, i.e. equal scarcity, i.e. by @thm-decomp the exact decompositions of the monolithic optimum. The update is the natural analogue, for our quasilinear program with production, of _proportional response_ dynamics in Fisher markets, where each buyer splits its budget across goods in proportion to the utility each good delivered (Wu and Zhang 2007). For classical Fisher markets, proportional response is known to be a form of mirror descent on a correct convex potential and converges at explicit rates (Birnbaum, Devanur, and Xiao 2011; Zhang 2011). For _quasilinear_ Fisher markets, Gao and Kroer (2020) show that mirror descent on a convex reformulation yields a proportional-response-type dynamic with sublinear last-iterate convergence — the closest known guarantee to what this section needs.

*What is proved and what is not.* Fixed-point correctness is @thm-decomp. A convergence proof for this setting — endogenous supply through $C_b^m$, retail orders alongside MMs, and coordination over budget splits rather than per-good spending — is open; we conjecture the Gao–Kroer analysis transfers.

*Empirical status (July 2026 prototype).* The corrected rule was benchmarked against the surrogate on asymmetric multi-component books: both sit at $98$–$99%$ of monolithic welfare, within a point or two of each other, and sweeping an MM's budget in a hand-built book left measured welfare flat. The reading: in a venue where minting is a universal counterparty, retail surplus barely depends on how a spanning MM's budget is split, so _no_ coordination rule can move end-to-end welfare much, and the residual gap to monolithic comes from per-component solve quality and dropped cross-group orders. Adopt equal scarcity for correctness (the surrogate's fixed point is provably wrong, §3); expect and claim no welfare gain from the coordination layer alone. Books where MM budgets genuinely gate retail fills would separate the rules; the prototype's synthetic books do not.

*Cost.* Each round is $M$ independent convex programs, fully parallel, warm-startable. Without cross-component MMs no coordination is needed at all; with them, the coordination state per MM is one scalar per active component.

= When Orders Span Components <approx>

If bundle orders couple groups, the components of the coupling graph must be solved jointly, and the componentwise story above applies at the level of those larger components. Two crude options exist for orders that would otherwise merge components, both with explicit (if loose) costs:

- *Dropping.* Excluding a set $cal(O)_times$ of cross-component orders costs at most $sum_(i in cal(O)_times) w_i overline(Q)_i$ welfare, by feasibility containment.

- *Leg decomposition misprices.* Splitting a bundle into per-component marginal legs prices it linearly ($0.5 p_A + 0.5 p_B$ for "both YES") where the true product price is $p_A p_B$ — at $p_A = 0.6, p_B = 0.4$, that is $0.50$ versus $0.24$. The overpricing systematically rejects profitable bundles. Leg decomposition is a UX convenience, not a clearing algorithm.

The honest treatment of cross-group orders — exact clearing within components via sparse factorization and junction trees, and a price-taking injection fallback with a provable welfare bound for dense coupling — is the subject of the companion bundle-clearing note.

= Discussion

*A market for clearing services (sketch).* The decomposition suggests an architecture in which the exchange solves the separable part and coordinates budgets, while external solvers compete to clear coupled components — an analogue of proposer–builder separation. The proportional-response layer makes the interface natural: a component solver's input is a budget vector, its output is deployed values. Incentive properties of such a market are unexplored.

*Open problems.* (1) Convergence rate of proportional response in this setting. (2) Instance-dependent bounds for dropping or leg-decomposing cross-component orders. (3) Whether the coordination layer can run _across batches_ — warm-starting each batch's allocation from the last — with a regret guarantee against the per-batch exact split.

#v(1.5em)
#line(length: 100%)
#v(0.5em)

*Errata (vs. the February 2026 draft).* The earlier draft's Theorem 1 claimed the optimal coordination equalizes component _utilities_ and that the coordination problem is smooth and concave; its Theorem 2 claimed $O(1\/t)$ convergence of multiplicative-weights ascent on $sum_m W_m^*$. Both are incorrect: $W_m^*$ is convex in budgets (@prop-trap), the equal-utility point is not the coordination optimum, and ascent on the surrogate misallocates (the counterexample of §3 loses half the welfare). The correct invariant is equal scarcity (@thm-decomp) and the correct iteration is proportional response on deployed values (§4). Prototype solvers implementing the old update should be revised accordingly.

#v(1em)
#text(size: 9pt, style: "italic")[
  Companion to _Prediction Markets Are Fisher Markets_ (2026). References: Wu, F. and Zhang, L. (2007), Proportional response dynamics leads to market equilibrium, STOC; Birnbaum, B., Devanur, N. R., and Xiao, L. (2011), Distributed algorithms via gradient descent for Fisher markets, EC; Zhang, L. (2011), Proportional response dynamics in the Fisher market, Theoretical Computer Science 412(24); Gao, Y. and Kroer, C. (2020), First-order methods for large-scale market equilibrium computation, NeurIPS.
]
