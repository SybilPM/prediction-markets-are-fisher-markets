#set document(title: "The Complexity of Clearing with Hard Budgets")
#set text(font: "New Computer Modern", size: 10pt)
#set page(margin: (x: 1.5in, y: 1.2in), numbering: "1")
#set par(justify: true, leading: 0.55em)
#set heading(numbering: "1.")
#show heading.where(level: 1): it => block(above: 1.5em, below: 0.8em)[#it]
#show heading.where(level: 2): it => block(above: 1.2em, below: 0.6em)[#it]

#show figure.where(kind: "theorem"): it => align(left, it.body)
#show figure.where(kind: "proposition"): it => align(left, it.body)
#show figure.where(kind: "lemma"): it => align(left, it.body)

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
#let conditional(name: none, body) = block(width: 100%, inset: (left: 1em))[
  *Theorem#super[$star$]*#if name != none [ (#name)]. #body
]

#align(center)[
  #text(size: 15pt, weight: "bold")[
    The Complexity of Clearing with Hard Budgets
  ]
  #v(0.5em)
  #text(size: 11pt)[Companion to _Prediction Markets Are Fisher Markets_]
  #v(0.3em)
  #text(size: 9pt, style: "italic")[Draft — July 2026. One step of the hardness proof (Theorem#super[$star$]) awaits interval-arithmetic formalization and is marked as such throughout.]
]

#v(1em)

#block(inset: (x: 2em))[
  #text(weight: "bold")[Abstract.]
  The main paper shows that batch clearing of prediction-market limit orders under hard market-maker budget caps has a non-convex feasible set, and leaves its complexity as an open problem. This note settles most of it, in both directions. _Hidden convexity:_ on books where each binary market carries at most one order, the substitution to expenditure coordinates makes the problem concave — polynomial-time solvable despite the non-convex feasible set; in particular the main paper's non-convexity witness family is a coordinate artifact (@thm-thin). _The genuine obstruction_ is resting retail liquidity: a sell wall makes the welfare–expenditure frontier non-concave, with the marginal welfare per dollar of MM capital jumping upward by the explicit factor $1 + (q^*\/b)(1 - L_R)$ the moment MM demand reaches the wall — the inframarginal repricing tax vanishes exactly when the counterparty appears (@prop-wall). _Hardness:_ an assembly of wall gadgets encodes SUBSET-SUM with exactly rational instance parameters; two welfare lemmas with explicit constants and a budget-window threshold scheme yield weak NP-hardness of the decision problem, modulo one interval-arithmetic formalization step (Theorem#super[$star$]). _Approximation stays easy:_ the separation analysis forces the reduction's yes/no gap to be exponentially small in value, so exact optimization is what is hard — the main paper's convex relaxation, which lands inside the feasible set with a quantified additive gap, is the approximation algorithm one should run. The moral: budgets are benign until retail liquidity arrives in lumps — and even then, only exactness is hard.
]

#v(1em)

= Introduction

The main paper replaces the hard-budget clearing model by a convex one and argues the replacement is better economics. But the original question does not go away: how hard is the model everyone writes down first? Its feasible set is non-convex for every temperature $b > 0$ (main paper, §3), and no polynomial-time algorithm is known. Non-convexity, however, is not hardness — a warning made concrete by Devanur, Dudík, Huang, and Pennock (2015), who found hidden convexity in the sequential single-trader version of exactly this problem. Settling the question requires either a convexification or a reduction, and this note supplies most of both:

+ *Thin books are easy* (@thm-thin). If each binary market carries at most one order, the substitution from fills to capital _expenditures_ turns the problem into a separable concave maximization over a simplex — polynomial time, for any number of market makers and any budgets. The main paper's two-lobe witness family lives in this class: its celebrated non-convexity is a coordinate artifact, and building an NP-hardness gadget out of those lobes — the obvious plan — provably cannot work.

+ *Retail walls are the true obstruction* (@prop-wall). One resting sell order makes the per-market welfare–expenditure frontier genuinely non-concave, in every coordinate system: marginal welfare per dollar _jumps up_ when MM demand reaches the wall, because the MM stops paying the inframarginal repricing tax exactly when a counterparty appears. Non-convexity in this problem is not the market maker's sigmoid; it is liquidity arriving in lumps.

+ *Hardness, one step from a theorem* (Theorem#super[$star$], §5). Wall gadgets scaled by SUBSET-SUM weights, one shared budget, and a two-point Lagrangian argmax make "which walls to absorb" a subset-sum decision. The instance parameters are exactly rational; the welfare analysis is two short lemmas with explicit constants; a budget-window lemma handles the threshold. The single remaining step is interval-arithmetic bookkeeping for the derived constants, marked explicitly.

+ *Only exactness is hard* (§6). The same deviation analysis that proves separation also shows a no-instance recovers the welfare bound up to an exponentially small deficit. Any reduction of this type therefore has $2^(-"poly")$ yes/no gaps: hardness lives entirely in the last bits of precision. Additive approximation remains easy — and the main paper's risk-averse relaxation, which is feasible for the hard budgets with additive gap $sum_k Delta_k^2 \/ 2 B_k$, is precisely the approximation algorithm the hardness result recommends.

_Related work._ The adjacent hardness results in market design are driven by indivisibilities: winner determination and core pricing in combinatorial exchanges with financially constrained buyers is $Sigma_2^p$-hard (Bichler and Waldherr 2018), and assignment markets with budgets are NP-hard even under complete information (Batziou, Bichler, and Fichtl 2022). Here everything is divisible; the hardness mechanism is the bilinear price-times-fill budget coupling, which is disjoint from packing. The #box[#smallcaps[\#P]]-hardness of combinatorial LMSR pricing (Chen et al. 2008) is orthogonal in the same sense: state-space explosion rather than budget coupling. In expenditure coordinates our problem is the maximization of a sum of non-concave scalar functions over a knapsack — the genre of sigmoidal programming, known NP-hard in general (Udell and Boyd 2014); the contribution here is that clearing _reaches_ that genre only through retail walls (@thm-thin says the MM-only fragment does not), and that within it, an exact reduction with rational instances can be assembled.

= The Decision Problem <problem>

We use the main paper's setting, specialized to $n$ independent binary market groups. Orders have limit prices, sides, caps; fills are $bold(q) in [0, bold(overline(Q))]$; group net demands $bold(D)(bold(q))$ are linear in fills; the smoothed minting cost is $C_b (bold(D)) = sum_g b ln (e^(D_("Y"g)\/b) + e^(D_("N"g)\/b))$ and clearing prices are its gradient. Risk-neutral welfare is $F(bold(q)) = sum_i w_i q_i - C_b (bold(D)(bold(q)))$. Market maker $k$'s capital consumption at the clearing prices is $h_k (bold(q)) = sum_(i in "MM"_k) p_(omega(i))(bold(q)) thin q_i$.

#block(inset: (left: 1em))[
*Problem* (D-HBC). _Given rational order data, temperatures, budgets $B_k$, and a rational threshold $W$: does there exist a UCP-valid $bold(q) in [0, bold(overline(Q))]$ with $h_k (bold(q)) <= B_k$ for all $k$ and $F(bold(q)) >= W$?_
]

Two modeling commitments. _UCP validity_ requires fills to respect limit prices at the clearing prices (a sell fills only at $p >= L$); without it, the optimizer may overfill a resting sell below its limit to depress prices and relax the MM's budget — a welfare-losing but budget-saving move the honest model forbids. The wall mechanism of §4 survives either choice (the kink sharpens without UCP), but the reduction commits to the UCP-valid variant. _Weak hardness_ is the natural target: the non-convexity is metric rather than combinatorial, the adjacent strong-hardness results all lean on indivisibilities, and §6 shows the yes/no gaps of our reduction are necessarily tiny in value — all three point the same way.

= Hidden Convexity on Thin Books <thin>

Call a book _thin_ if each binary market carries at most one order — necessarily an MM buy order (retail orders with locked capital are unaffected by budgets; relabel sells as buys of the complement). The main paper's non-convexity witness is a thin book: one MM, one order per market, capital consumption $h(bold(q)) = sum_j f_b (q_j)$ with $f_b (q) = sigma(q\/b) thin q$, whose sublevel sets have two-lobe geometry.

#theorem(name: "Thin Books Convexify")[
  _On a thin book, substitute per-market expenditure $e_j = f_(b_j)(q_j)$ (monotone, hence bijective). The clearing problem becomes_
  $ max quad sum_j gamma_j (e_j) quad "s.t." quad sum_(j in "MM"_k) e_j <= B_k thick forall k, quad e_j in [0, f_(b_j)(overline(Q)_j)] $
  _where $gamma_j = phi_j compose f_(b_j)^(-1)$ and $phi_j (q) = L_j q - C_(b_j)(q) + C_(b_j)(0)$ is market $j$'s welfare ($L_j in (1\/2, 1]$; below $1\/2$ the order never fills). Each $gamma_j$ is *strictly concave*, so the substituted problem is a separable concave maximization over box-and-simplex constraints: D-HBC on thin books is polynomial-time solvable, for any number of MMs._
] <thm-thin>

_Proof._ Markets partition across MMs and each budget constraint is separable, so it suffices to prove concavity of one $gamma$. Take $b = 1$ by the scaling identity $f_b (b t) = b f_1 (t)$ and parametrize by $q$ on the active domain ${sigma(q) < L}$: the frontier slope is $gamma' = (L - sigma) \/ (sigma(1 + q(1 - sigma)))$. Using $sigma' = sigma(1 - sigma)$, a direct computation (verified symbolically; `scripts/hardness_debts.py`) gives
$
dif / (dif q) ln gamma' = -(1 - sigma) [ underbrace(sigma / (L - sigma) + (2 + q(1 - 2 sigma)) / (1 + q(1 - sigma)), =: cal(B)(q, L)) ]
$
For $L = 1$, multiplying $cal(B)$ by the positive quantity $(1 - sigma)(1 + q(1 - sigma))$ yields exactly $(2 - sigma) + q (1 - sigma)^2 > 0$. For $L < 1$, $cal(B)$ only increases, since $sigma\/(L - sigma) > sigma\/(1 - sigma)$ on the active domain. So $gamma'$ is strictly decreasing in $q$; since $e$ is strictly increasing in $q$, $gamma$ is strictly concave in $e$. #h(1fr) $square$

Note what the proof is _not_: an inheritance. The expenditure derivative $f'$ is non-monotone (it rises to $approx 1.1$ at the inflection $q approx 2.4 b$ before falling back to $1$); the concavity of $gamma$ is a cancellation between the falling marginal welfare and the non-monotone marginal cost — which is presumably why the witness family was mistaken for a source of hardness. Two consequences. First, the main paper's §3 witness shows the feasible set is non-convex _as written_, and nothing more: the associated optimization problem is easy. Second, any hardness construction must leave the thin class — it needs either retail counterparties or several MM orders per market. The next section shows the first option suffices.

= The Wall Mechanism <wall>

Add one resting retail sell-YES order (limit $L_R$, size $Q_R$) to a binary market where the MM buys YES (limit $1$, cap on the wall as in §5). Under UCP-valid clearing, as the MM's fill $q$ grows with $q^* = b ln(L_R \/ (1 - L_R))$: _pre-wall_ ($sigma(q\/b) < L_R$), retail cannot fill and $e(q) = sigma(q\/b) q$; _on the wall_, the price pins at $L_R$, retail absorbs $r = q - q^*$, and expenditure is linear, $e = L_R q$, while welfare gains $1 - L_R$ per unit.

#proposition(name: "The Frontier Kinks Upward at the Wall")[
  _The welfare–expenditure frontier $gamma(e)$ of this market is non-concave: its slope jumps up at the wall,_
  $ gamma'(e^* -) = (1 - L_R) / (L_R thin [1 + (q^*\/b)(1 - L_R)]) quad --> quad gamma'(e^* +) = (1 - L_R) / L_R $
  _a jump by the factor $1 + (q^*\/b)(1 - L_R) > 1$. (At $b = 1$, $L_R = 0.7$: slopes $0.342 -> 0.429$.)_
] <prop-wall>

_Proof._ Pre-wall, $dif e \/ dif q = sigma + (q\/b) sigma(1 - sigma)$ and $dif phi \/ dif q = 1 - sigma$; evaluate at $sigma = L_R$. On the wall, $dif e \/ dif q = L_R$ and $dif phi \/ dif q = 1 - L_R$ exactly. Expenditure is strictly increasing in $q$ throughout, so the slope discontinuity in $q$ is a slope discontinuity in $e$. #h(1fr) $square$

The economics deserves the emphasis. Pre-wall, a marginal share costs $p + q thin dif p$: the MM re-prices its entire inframarginal position against itself. On the wall, retail supply pins the price, $dif p = 0$, and the repricing tax vanishes — _exactly when the counterparty appears_, marginal welfare per dollar improves discontinuously. The non-convexity of hard-budget clearing is not the market maker's own price impact; it is the lumpiness of resting liquidity. (Without the UCP constraint the kink survives and sharpens: overfilling the wall buys expenditure reductions at second-order welfare cost, flattening the frontier to the left of the wall, so the slope jump is from $approx 0$ to $(1 - L_R)\/L_R$.)

= The Reduction <reduction>

*Construction.* Given SUBSET-SUM data — positive integers $a_1, dots, a_n$, target $T$, $A := sum_j a_j$ — build $n$ independent binary markets sharing one MM. Market $j$ is the wall gadget _dilated by $a_j$_: temperature $b_j = a_j$, retail wall at $L_R = 7\/10$ of size $6 a_j$, MM buy order at limit $1$ capped at $overline(q)_j = 6 a_j$. By the scaling identity $f_b (b t) = b f_1 (t)$, market $j$'s frontier is an exact dilation, $gamma_j (e) = a_j thin gamma(e \/ a_j)$, of one reference frontier $gamma$. Two design points matter. The cap sits at a rational point _on_ the wall ($hat(q) = 6 < q^* + Q_R$, so the wall never exhausts): the frontier ends at $hat(x)^+ = L_R hat(q) = 21\/5$ — rational — and the shape is a strictly concave arc (@thm-thin's proof applies verbatim pre-wall) followed by a linear segment of strictly higher slope. Consequently _every instance parameter is rational._ The transcendental quantities live only in derived constants, which enter through the budget and threshold — our free choices.

*The supporting line.* Let $x^-$ be the tangency point where the chord to the endpoint $hat(x)^+$ touches the arc, $mu^*$ the chord slope, $s = hat(x)^+ - x^-$, and
$
macron(G)(x) = gamma(x^-) + mu^* (x - x^-) - gamma(x)
$
the gap to the supporting line. Strict concavity off the wall and linearity (with slope $!= mu^*$) on it give $macron(G) >= 0$ with zeros _exactly_ ${x^-, hat(x)^+}$. Write lobe coordinates $y_j = (e_j \/ a_j - x^-) \/ s$; the two lobes are $y in {0, 1}$. Reference constants (rational gadget): $x^- = 0.42766$, $mu^* = 0.42651$, $s = 3.77234$; $kappa_2 := ("wall slope" - mu^*) s = 7.783 times 10^(-3)$; and $kappa_1 := inf_(y != 0) macron(G)(x^- + y s)\/y^2 >= (s^2\/2) min_"arc" (-gamma'') >= 3.04$ by second-order Taylor, since $macron(G)(x^-) = macron(G)'(x^-) = 0$ and $macron(G)'' = -gamma''$ has the explicit form $R(1 - sigma) cal(B) \/ f'$ from @thm-thin's proof, with arc minimum $0.4271$ at the wall start.

#lemma(name: "Welfare Decomposition")[
  _For any feasible UCP-valid clearing with per-market MM expenditures $e_j in [0, a_j hat(x)^+]$ and $sum_j e_j <= B$,_
  $ F <= "Bound"(B) - mu^* (B - sum_j e_j) - sum_j a_j macron(G)(e_j \/ a_j), quad "Bound"(B) := A thin gamma(x^-) + mu^* (B - A x^-) $
  _with equality on frontier configurations; in particular $F = "Bound"$ exactly on full-budget lobe configurations._
] <lem-decompose>

_Proof._ Market $j$'s welfare is at most $a_j gamma(e_j \/ a_j)$ (frontier definition plus dilation), and $gamma(x) = [gamma(x^-) + mu^* (x - x^-)] - macron(G)(x)$ pointwise. Sum over $j$; bound $sum e_j$ by $B$. #h(1fr) $square$

#lemma(name: "Separation")[
  _Set $c_0 = 1/8 min(kappa_2, kappa_1 \/ A)$ and the ideal budget $B_0 = A x^- + T s$. For any budget $B in [B_0, B_0 + c_0\/(2 mu^*))$:_
  - _(YES) if some subset sums to $T$, its lobe configuration is feasible and achieves $F = X := A gamma(x^-) + mu^* T s$;_
  - _(NO) if no subset sums to $T$, every feasible point has $F <= X + mu^* (B - B_0) - c_0$._
] <lem-separation>

_Proof._ YES: the configuration spends $B_0 <= B$ and every $macron(G)$ term vanishes. NO: let $u = B - sum e_j >= 0$. If $u >= s\/2$, @lem-decompose already yields a deficit $mu^* s\/2 >> c_0$. Otherwise round each $y_j$ to the nearest of ${0, 1}$: the rounded configuration is a subset sum $s' != T$, so $sum_j a_j d_j >= |T - s'| - (u + B - B_0)\/s >= 1\/2$, where $d_j$ is the rounding distance. Each market's penalty obeys $macron(G) >= kappa_2 d_j$ for wall-side deviations and $macron(G) >= kappa_1 d_j^2$ off-wall. Splitting the mass $sum a_j d_j >= 1\/2$ between regimes: the linear regime pays at least $kappa_2\/4$, or the quadratic regime carries mass $>= 1\/4$ and — optimally spread across markets — pays at least $kappa_1\/(16 A)$. Either way the penalty exceeds $c_0$, with slack absorbing the budget enlargement. #h(1fr) $square$

#lemma(name: "Budget Window")[
  _Pick any rational $B in [B_0, B_0 + c_0\/(2 mu^*))$ and rational $W^* in (X - c_0\/4, thin X)$. Then YES instances of SUBSET-SUM map to YES instances of D-HBC and NO to NO. Both $B$ and $W^*$ require $O(log(A\/c_0))$ bits, i.e. polynomially many._
] <lem-window>

_Proof._ YES: $F >= X > W^*$ by @lem-separation. NO: $F <= X + mu^*(B - B_0) - c_0 <= X - c_0\/2 < W^*$. #h(1fr) $square$

#conditional[
  D-HBC — UCP-valid batch clearing with hard budgets and binary-encoded rational inputs — is (weakly) NP-hard.
]

_What the star covers._ The reduction is the construction above with @lem-window's budget and threshold. The instance parameters are exactly rational; the constants $x^-, mu^*, gamma(x^-), kappa_1, kappa_2$ entering $B$ and $W^*$ are roots and values of explicit logistic-log equations with concrete transversality margins ($mu^*$ clears the wall slope by $2.1 times 10^(-3)$; the tangency is interior by $0.42$ in $q$), so interval Newton computes them to any polynomial number of bits in polynomial time; and the Taylor certificate for $kappa_1$ needs a grid-plus-Lipschitz (or interval) evaluation of the explicit $-gamma''$. Writing these three routine verifications down carefully is all that separates the star from a theorem. Nothing conceptual is open.

*Numerical validation.* The pipeline was validated end-to-end on live instances ($a = (3,5,7)$): the YES instance $T = 8$ accepts with margin $+4.9 times 10^(-4)$, landing exactly on the predicted lobes; the NO instance $T = 9$ rejects with margin $-7.3 times 10^(-3)$, and a $400$-start global search escapes through precisely the integer-$1$ wall-back route that @lem-separation prices, with measured deficit matching $kappa_2$ to $0.15%$ (`scripts/hardness_rational.py`, `scripts/hardness_e2e.py`).

= Discussion <discussion>

*Only exactness is hard.* The separation analysis cuts both ways. A NO instance recovers the welfare bound up to $Theta(kappa_1 \/ A)$ — exponentially small in the input length whenever the subset-sum weights are — by spreading tiny off-lobe deviations across markets. So the yes/no gap of this reduction (and, we expect, of any reduction from a number problem) is necessarily $2^(-"poly")$: the hardness of hard-budget clearing lives entirely in the last bits of precision. Additive approximation is unobstructed, and the main paper already supplies the algorithm: its risk-averse convex relaxation is feasible for the hard budgets with additive welfare gap at most $sum_k Delta_k^2 \/ 2 B_k$. We conjecture an additive FPTAS exists for D-HBC; the moral stands regardless — _the convex relaxation is the right thing to run,_ now with a hardness result explaining why nothing exact should be attempted.

*Open questions.* (1) _Strong hardness._ Our reduction inherits weakness from SUBSET-SUM; whether D-HBC is strongly NP-hard (or pseudo-polynomial) is open, and the tiny-gap phenomenon suggests genuine obstacles to strong hardness for the welfare-threshold version. (2) _The approximation frontier._ Additive FPTAS, or even a PTAS in relative terms near the LP scale? (3) _Ladders._ Between thin books (@thm-thin, easy) and retail walls (@prop-wall, hard) sits the retail-free regime with several MM orders per market. The expenditure substitution no longer separates; whether ladders alone can simulate a wall — an MM's own resting orders creating the lumpy-liquidity kink for _another_ MM — is the sharpest open boundary question, and would determine whether hardness requires retail at all. (4) _The UCP-free variant._ The kink survives without UCP validity (§4), but the frontier geometry differs; the reduction should transfer with modified constants.

*Relation to the main paper.* Its §3 exhibits the two-lobe witness; this note shows the witness's non-convexity is a coordinate artifact (@thm-thin) while retail walls provide the load-bearing obstruction (@prop-wall) — a strictly sharper story that the main paper's Open Problem 4 now summarizes in one line. Nothing in the main paper changes: its response to the obstacle was never "solve the non-convex problem" but "replace the model and approximate the original with a guarantee," and the results here say that response was the right one — exactly, not just heuristically.

#v(1.5em)
#line(length: 100%)
#v(0.5em)
#text(size: 9pt, style: "italic")[
  Companion to _Prediction Markets Are Fisher Markets_ (2026); notation and the clearing model are defined there. Numerics and symbolic verifications: `scripts/hardness_gamma.py`, `hardness_debts.py`, `hardness_e2e.py`, `hardness_rational.py`. References: Batziou, E., Bichler, M., and Fichtl, M. (2022), Assignment markets with budget constraints, arXiv:2205.06132; Bichler, M. and Waldherr, S. (2018), Competitive equilibria in combinatorial exchanges with financially constrained buyers: computational hardness and algorithmic solutions, arXiv:1807.08253; Chen, Y., Fortnow, L., Lambert, N., Pennock, D. M., and Wortman, J. (2008), Complexity of combinatorial market makers, EC; Devanur, N. R., Dudík, M., Huang, Z., and Pennock, D. M. (2015), Budget constraints in prediction markets, UAI; Udell, M. and Boyd, S. (2014), Maximizing a sum of sigmoids, manuscript, Stanford University.
]
