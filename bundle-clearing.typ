#set document(title: "Bundle Clearing: Exact Within Components, Priced Injection Beyond")
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
    Bundle Clearing: Exact Within Components, \ Priced Injection Beyond
  ]
  #v(0.5em)
  #text(size: 11pt)[Companion note to _Prediction Markets Are Fisher Markets_]
  #v(0.3em)
  #text(size: 9pt, style: "italic")[Draft — July 2026 (supersedes the February 2026 draft; see Errata)]
]

#v(1em)

#block(inset: (x: 2em))[
  #text(weight: "bold")[Summary.]
  Bundle orders — payoffs over the joint state of several market groups — couple clearing across a state space of size $product_j K_j$. This note gives the computational treatment. The joint minting cost factorizes exactly across the connected components of the bundle-coupling graph, and within a component it is computable by restricted enumeration or, better, by junction tree in time exponential only in the component's treewidth — linear chains of conditionals, the common case, cost $O(K^2)$ per link rather than $K^("chain length")$ (@prop-factor, §3). For components too dense for exact inference, we give a _price-taking injection_ fallback — clear without bundles, then fill bundles at the product-form prices — with a proven welfare guarantee: the loss is at most the bundles' surplus at pre-injection prices plus a curvature term $delta_max^2 \/ (8b)$ (@prop-injection). An earlier draft claimed exact clearing in time polynomial in the number of bundles regardless of coupling; that claim was wrong (see Errata), and the corrected boundary is exactly the one predicted by the main paper's clearing-as-inference reduction.
]

#v(1em)

= Introduction

A bundle order pays as a function of the joint state of several groups: "buy YES on both $A$ and $B$," or the conditional "$A$ if $B$." The main paper shows the clearing theorem survives bundles untouched — the program stays concave over the joint state space $cal(S) = product_j {1, dots, K_j}$ — but _writing the objective down_ by enumeration costs $|cal(S)|$, which is exponential. It also shows what the objective _is_: $C_b (bold(D)) = b ln sum_omega exp(D_omega \/ b)$ is $b$ times the log-partition function of the Gibbs distribution $pi(omega) prop exp(D_omega\/b)$ whose factor graph is the order book, and clearing prices are its marginals. Clearing is inference. This note is the algorithmic half of that observation: where inference is exact and cheap, clear exactly; where it is not, fall back to a priced approximation with a bound.

One non-option first. _Leg decomposition_ — splitting a bundle into per-group marginal legs — prices "both YES" linearly at $0.5 p_A + 0.5 p_B$ where the true product-form price is $p_A p_B$: at $p_A = 0.6$, $p_B = 0.4$, that is $0.50$ against $0.24$. The systematic overpricing rejects profitable bundles. Legs are a display convenience, not a clearing algorithm.

*Notation.* Groups $j = 1, dots, N$ with $K_j$ outcomes and separable net demand $D^j_(omega_j)$ from single-group orders. Bundle $i$ has scope $G_i$ (the groups it references, $|G_i| <= 5$ in the reference implementation), payoff $phi_i (omega_(G_i)) in [0,1]$, and fill $q_i$; aggregate bundle demand is $delta_omega = sum_i phi_i (omega_(G_i)) thin q_i >= 0$ (net buys after the buy/sell reduction). Total demand: $D_omega = sum_j D^j_(omega_j) + delta_omega$.

= Component Factorization <factor>

The _coupling graph_ has the bundle-touched groups as vertices, with a clique on each scope $G_i$. Let its connected components have group sets $T_1, dots, T_C$, and let $cal(U)$ be the untouched groups. Write $Z_j = sum_(omega_j) exp(D^j_(omega_j) \/ b)$ for the per-group normalizers and $cal(S)_c = product_(j in T_c) {1, dots, K_j}$ for component $c$'s restricted state space.

#proposition(name: "Component Factorization")[
  _The partition function factorizes exactly across components:_
  $ Z = sum_omega exp(D_omega \/ b) = (product_(j in cal(U)) Z_j) dot product_c Z_c, quad Z_c = sum_(omega_c in cal(S)_c) (product_(j in T_c) exp(D^j_(omega_j) \/ b)) dot exp(delta_c (omega_c) \/ b) $
  _where $delta_c$ aggregates the demands of component $c$'s bundles. Consequently $pi$ is a product of independent distributions — the per-group softmax on untouched groups (exactly, with no rescaling) and $pi_c prop$ the summand above on each component — and every price is a marginal of the relevant factor. The cost of $Z$, all group prices, and all bundle prices $sum_(omega_c) phi_i (omega_(G_i)) pi_c (omega_c)$ is_
  $ O(sum_j K_j + sum_c |cal(S)_c|) $
] <prop-factor>

_Proof._ Each bundle lies in exactly one component, so $delta_omega = sum_c delta_c (omega_(T_c))$ and $exp(D_omega\/b)$ is a product of factors each depending on one component's coordinates (or one untouched group's). A sum of products over a product space factorizes. Marginals follow because $pi$ is then a product measure. #h(1fr) $square$

*The single-bundle special case.* If a component consists of one bundle with scope $G$ and fill $q$, expanding $e^(phi q \/ b) = 1 + (e^(phi q \/ b) - 1)$ gives
$
Z_c = product_(j in G) Z_j + sum_(omega_G) (product_(j in G) exp(D^j_(omega_j) \/ b)) (exp(phi(omega_G) q \/ b) - 1)
$
a separable base plus a correction over the bundle's own $product_(j in G) K_j <= 2^5 = 32$ states.

*Warning: per-bundle corrections do not add.* It is tempting to extend the display above to many bundles by summing one correction term per bundle. This is wrong whenever any joint state carries two active bundles — which is the typical case, since $e^((delta^1 + delta^2)\/b) - 1 != (e^(delta^1\/b) - 1) + (e^(delta^2\/b) - 1)$ unless $delta^1 delta^2 = 0$ statewise. Bundles interact through the exponential even when their scopes are disjoint within a component (a chain $A$–$B$, $B$–$C$, $C$–$D$ makes the $\{A,B\}$ and $\{C,D\}$ bundles interact through the middle link). The exact object is the component sum $Z_c$; there is no additive shortcut. An earlier draft of this note claimed one; see the Errata.

= Junction Trees: Chains Are Cheap <jtree>

Restricted enumeration costs $|cal(S)_c| = product_(j in T_c) K_j$ — fine for components of a dozen binary groups, hopeless beyond. But enumeration ignores structure _within_ the component. $Z_c$ is the partition function of a graphical model whose factors are the component's bundles (arity $<= 5$); the junction-tree algorithm computes it, and all marginals, in time exponential only in the _treewidth_ $tau_c$ of the component's coupling graph:
$
O(|T_c| dot K^(tau_c + 1)), quad K = max_j K_j
$
The distinction matters because the common shapes of real bundle flow are tree-like. A chain of conditionals $A$–$B$–$C$–$dots$ has treewidth $1$: a $20$-group chain costs $O(20 K^2)$ by junction tree versus $K^20$ by enumeration. A star of parlays through one popular market also has treewidth bounded by the largest scope. Dense, loopy coupling — many overlapping parlays across the same groups — is where treewidth grows and exact inference genuinely dies, consistent with the \#P-hardness of the general case (Chen et al. 2008, via the main paper's reduction). Junction-tree inference is not new to combinatorial markets: deployed graphical-model market makers already use it for sequential price updates (Laskey et al. 2018), and decomposable structure is the known tractability boundary for updating (Pennock and Xia 2011). The point here is that the same machinery computes the _batch-clearing_ objective and its exact marginal prices.

The practical rule: compute the components, compute (or bound) their treewidths, and clear exactly every component with $K^(tau_c + 1)$ within budget. Only the residue needs §5.

= Solving: Frank–Wolfe with an Inference Oracle <solve>

The clearing program maximizes a smooth concave objective (the quasilinear-EG objective of the main paper, with $C_b$ evaluated through @prop-factor or junction tree) over a box of fills. Frank–Wolfe applies directly:

+ *Gradient.* $nabla_i f = alpha_k L_i - "price"_i$ for MM orders, $w_i - "price"_i$ for retail, with every price a marginal from the current inference pass.
+ *Oracle.* Maximize the linearized objective over the box — coordinatewise, each order goes to $0$ or $overline(Q)_i$ by the sign of its gradient.
+ *Line search.* Bisection on the exact objective along the segment; each evaluation is one inference pass.

Standard Frank–Wolfe analysis gives $O(1\/t)$ convergence for smooth concave maximization over a compact polytope; the gradient of $C_b$ is $(1\/b)$-Lipschitz, so the constant degrades as $b -> 0$ (at $b = 0$, use the conic formulation of the main paper on the enumerated or junction-tree-lifted state space instead). Per iteration, the cost is one inference pass plus $O(n)$ — the state space never appears except inside the inference oracle.

= Price-Taking Injection (Fallback) <injection>

For components too dense to clear exactly, solve _without_ their bundles and inject the bundles at the resulting prices:

+ *Base solve.* Clear all single-group orders (and all exactly-clearable components). Output fills $bold(q)^0$, demand $bold(D)^0$, prices $bold(p)^0$.
+ *Bundle pricing.* Price each residual bundle at the product form, $"price"_i^0 = sum_(omega_(G_i)) phi_i (omega_(G_i)) product_(j in G_i) p^0_(omega_j)$ — cost $O(2^(|G_i|))$, no joint enumeration.
+ *Inject.* Fill bundle $i$ (up to $overline(Q)_i$) only if $w_i >= "price"_i^0$.

The injected fills are not re-optimized against each other; the guarantee is correspondingly additive.

#proposition(name: "Injection Guarantee")[
  _Assume bundle orders are non-MM (their welfare enters linearly; the MM case is analogous since $psi' <= 1$) and $delta >= 0$ statewise. Let $W^*$ be the optimal clearing objective with all orders, $W_"drop"$ the optimum with the residual bundles removed, $W_"inj"$ the objective of the injection solution, $tilde(bold(D))$ the demand of the all-orders optimum with its bundle fills zeroed, and $delta_max = max_omega delta_omega^"inj"$. Then:_

  + $W^* - W_"drop" <= sum_(i in "bundles") (w_i - "price"_i (tilde(bold(D))))^+ thin overline(Q)_i <= sum_(i in "bundles") w_i overline(Q)_i$

  + $W_"inj" >= W_"drop" + sum_i (w_i - "price"_i^0) thin q_i^"inj" - delta_max^2 / (8b) >= W_"drop" - delta_max^2 / (8b)$

  _Hence $W^* - W_"inj" <= sum_i (w_i - "price"_i (tilde(bold(D))))^+ overline(Q)_i + delta_max^2 \/ (8b)$: the loss is the bundles' genuine surplus at pre-injection prices, plus a curvature term that is second-order in bundle demand._
] <prop-injection>

_Proof._ We use two properties of $C_b$: convexity, and the curvature bound $C_b (bold(D) + bold(delta)) <= C_b (bold(D)) + chevron.l nabla C_b (bold(D)), bold(delta) chevron.r + ("range" thin bold(delta))^2 \/ (8b)$, which follows from $dif^2 \/ dif t^2 thin C_b (bold(D) + t bold(delta)) = "Var"_(pi_t)(bold(delta)) \/ b <= ("range" thin bold(delta))^2 \/ (4b)$ and Taylor's theorem; with $delta >= 0$, range $<= delta_max$.

(1) Let $bold(q)^*$ attain $W^*$ and let $tilde(bold(q))$ zero its bundle fills. By convexity of $C_b$, $C_b (tilde(bold(D)) + bold(delta)^*) - C_b (tilde(bold(D))) >= chevron.l nabla C_b (tilde(bold(D))), bold(delta)^* chevron.r = sum_i "price"_i (tilde(bold(D))) thin q_i^*$. So
$
W^* - f(tilde(bold(q))) = sum_i w_i q_i^* - [C_b (tilde(bold(D)) + bold(delta)^*) - C_b (tilde(bold(D)))] <= sum_i (w_i - "price"_i (tilde(bold(D)))) q_i^* <= sum_i (w_i - "price"_i (tilde(bold(D))))^+ overline(Q)_i
$
and $f(tilde(bold(q))) <= W_"drop"$ since $tilde(bold(q))$ is feasible for the drop program.

(2) The injection point is $bold(q)^0$ plus bundle fills, so by the curvature bound,
$
W_"inj" - W_"drop" = sum_i w_i q_i^"inj" - [C_b (bold(D)^0 + bold(delta)^"inj") - C_b (bold(D)^0)] >= sum_i (w_i - "price"_i^0) q_i^"inj" - delta_max^2 / (8b)
$
and the sum is non-negative because injection only fills bundles with $w_i >= "price"_i^0$. #h(1fr) $square$

_Remark (iterating)._ Injection can be repeated: re-solve the base with the injected demand held fixed, re-price, adjust. Each round is one decomposed solve. We know of no convergence proof; when bundle volume is a small fraction of single-group volume the first round's curvature term is already small, which is the regime where the fallback is intended to operate.

= Which Method Where <decision>

#align(center)[
  #table(
    columns: 3,
    align: (left, left, left),
    stroke: 0.5pt,
    inset: 6pt,
    [*Coupling structure*], [*Method*], [*Welfare loss*],
    [No bundles], [Per-group solves + budget coordination], [$0$],
    [Components with small $|cal(S)_c|$], [Restricted enumeration (@prop-factor)], [$0$],
    [Large components, small treewidth], [Junction tree (§3)], [$0$],
    [Dense residue], [Priced injection (@prop-injection)], [surplus at $tilde(bold(D))$ $+ delta_max^2 \/ 8b$],
  )
]

The decision procedure: build the coupling graph, take components, clear exactly wherever $min(|cal(S)_c|, |T_c| K^(tau_c + 1))$ fits the compute budget, inject the rest. When a large component has a small welfare-weighted cut, splitting it by dropping minimum-welfare bundles (then re-injecting them) trades bounded welfare for tractability; whether real coupling graphs have such cuts is an empirical question.

= Discussion

*What is new here.* The component factorization with exact marginal prices (@prop-factor), the identification of treewidth — not component size, not bundle count — as the exact-clearing frontier (imported from the main paper's inference reduction), and a fallback with a proven additive guarantee (@prop-injection). Together they cover chains and stars of conditionals exactly, which is the bundle flow a venue actually expects to see first.

*Open problems.* (1) _Certified approximate inference._ For dense components, variational bounds on the log-partition function (tree-reweighted upper bounds, Bethe-type lower bounds) translate directly into certified intervals on $C_b$ and hence on prices and welfare — can a clearing engine act on intervals safely? (2) _Empirical treewidth._ No venue at scale has run bundles; whether real coupling graphs stay tree-like or densify is unknown and determines everything above. (3) _Combining candidate solutions._ Fill vectors from different methods can be convex-combined and the objective only improves (concavity), but the combined softmax prices need not support the combined fills as a UCP outcome; re-solving fills at consensus prices is a workaround whose welfare properties are unclear.

#v(1.5em)
#line(length: 100%)
#v(0.5em)

*Errata (vs. the February 2026 draft).* The earlier draft's Theorem 1 claimed the joint minting cost is computable in time $O(sum_j K_j + sum_i |G_i| dot 2^(|G_i|))$ — polynomial in the number of bundles, independent of coupling. That is incorrect: the per-bundle correction formula is valid only for a single bundle per component, because corrections do not add across bundles that are simultaneously active in a state (§2). The corrected scope is component-by-component, with cost exponential in component size or, via junction tree, in component treewidth — matching the \#P-hardness boundary for the general case. The Frank–Wolfe section's claim that an oracle over a relaxed feasible set still converges was also imprecise and has been replaced by the standard statement (§4). The injection welfare bound, previously asserted, is now proved (@prop-injection).

#v(1em)
#text(size: 9pt, style: "italic")[
  Companion to _Prediction Markets Are Fisher Markets_ (2026) and to the decomposition note in this repository. References: Chen, Y., Fortnow, L., Lambert, N., Pennock, D. M., and Wortman, J. (2008), Complexity of combinatorial market makers, EC; Pennock, D. M. and Xia, L. (2011), Price updating in combinatorial prediction markets with Bayesian networks, UAI; Laskey, K. B., Sun, W., Hanson, R., Twardy, C., Matsumoto, S., and Goldfedder, B. (2018), Graphical model market maker for combinatorial prediction markets, JAIR 63.
]
