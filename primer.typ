#set document(title: "Prediction Markets Are Fisher Markets: A Primer")
#set text(font: "New Computer Modern", size: 10pt)
#set page(margin: (x: 1.5in, y: 1.2in), numbering: "1")
#set par(justify: true, leading: 0.55em)
#set heading(numbering: "1.")
#show heading.where(level: 1): it => block(above: 1.5em, below: 0.8em)[#it]
#show heading.where(level: 2): it => block(above: 1.2em, below: 0.6em)[#it]
#show figure.caption: set text(size: 9pt)

#import "figures.typ": fig-softmax, fig-obstacle, fig-psi, fig-maxent, fig-example

#let takeaway(body) = block(
  width: 100%,
  inset: (x: 1em, y: 0.7em),
  fill: luma(248),
  stroke: (left: 1.5pt + luma(170)),
)[#body]

#align(center)[
  #text(size: 15pt, weight: "bold")[Prediction Markets Are Fisher Markets]
  #v(0.3em)
  #text(size: 11pt)[A Primer]
  #v(0.3em)
  #text(size: 9pt, style: "italic")[The ideas, without the proofs]
]

#v(1em)

#block(inset: (x: 2em, y: 0.7em), fill: luma(245), radius: 4pt)[
  *Who this is for.* Anyone technical who wants the ideas behind the paper without working through KKT systems and Fenchel conjugates. If you know what a convex optimization problem is and roughly what a prediction market does, this document is self-contained. Every claim made here is proved in the paper; this is the tour.

  #v(0.4em)
  *The one-sentence version.* A market maker's budget, taken seriously, is not a constraint — it is a preference. Model it that way and the hardest problem in prediction-market clearing turns into a convex program from 1959 that was invented, fittingly, to study betting.
]

= An Exchange That Manufactures Its Own Inventory

A prediction market sells shares that pay \$1 if an event happens and \$0 if it doesn't. The exchange running it has a superpower an ordinary stock exchange lacks: it can manufacture inventory at a known, riskless cost. Take a market with $K$ mutually exclusive outcomes — say the winner of an election. A _complete set_ (one share of every candidate) always pays exactly \$1 at settlement, no matter who wins. So the exchange can _mint_ complete sets for \$1 each, sell the pieces to whoever wants them, and take no risk at all.

This one design choice quietly settles a question people usually treat as an axiom: why do the prices of mutually exclusive outcomes sum to \$1? Because if they summed to more, anyone could mint a set for \$1 and sell it for more — free money; if less, buy a set for less and redeem it for \$1 — free money again. "Prices are probabilities" is not an assumption about rational beliefs. It is the no-arbitrage shadow of a \$1 mint. (In the paper this sentence _is_ Theorem 1, via convex duality.)

The exchange we study clears by _batch auction_: orders accumulate for an interval — a second, a minute — and then everything clears at once, at one uniform price per outcome. Batch auctions are the market designer's answer to speed races, and for prediction markets they have a second virtue: clearing a batch is an optimization problem we can reason about exactly.

= Clearing Without Market Makers Is a Solved Problem

Suppose the batch contains only simple orders: "buy up to 100 shares of Yes, at \$0.60 or better." Each order deposits its worst-case cost upfront, so nobody can overdraw. The exchange's problem is to choose fill quantities that maximize total surplus, paying the minting bill for whatever net inventory it must create:

$ max_("fills" thin bold(q)) quad underbrace(sum_i w_i q_i, "surplus from fills") - underbrace(max_omega D_omega (bold(q)), "minting bill") $

where $D_omega$ is the net demand for outcome $omega$ and the bill is driven by the most-demanded outcome (mint enough sets to cover it, and the other outcomes ride along for free). This is a linear program. Solving it fills every order whose limit price beats the clearing price, rejects every order that misses it, and lets marginal orders fill partially — the standard uniform-price call auction, derived rather than decreed.

Where do the prices come from? They are the LP's dual variables, and they behave like prices should: they sum to one, and they move against the order flow. There is one wrinkle: at exact ties the LP's prices can be ambiguous (several price vectors support the same fills). The fix is a knob called _temperature_. Replace the sharp $max$ in the minting bill by its smooth cousin $b ln sum_omega e^(D_omega\/b)$ — readers from machine learning will recognize log-sum-exp — and prices become the _softmax_ of net demand. This smoothed auction is exactly Hanson's LMSR market maker: LMSR is not a rival mechanism to batch clearing, it is batch clearing with the corners rounded off (@fig-lmsr).

#figure(
  fig-softmax,
  kind: image,
  supplement: [Figure],
  caption: [One binary market, price as a function of order-flow imbalance. At $b -> 0$ the price is the LP's step function; at $b > 0$ it is a softmax. Temperature trades a bounded subsidy ($b ln K$ at worst) for smoothness and unique prices.],
) <fig-lmsr>

The knob has a price tag, and it is explicit: smoothing costs the exchange at most $b ln K$ per batch in extra minting subsidy. Pick $b$ so that $b ln K$ is smaller than a price tick and you get uniqueness essentially for free. Everything in this story — sharp or smooth — is convex, fast, and boring. In the best way.

= The Wrench: Market Makers With Budgets

Now add the participant every real venue depends on. A market maker deposits a balance — say \$50,000 — and posts _hundreds_ of orders across _dozens_ of markets: bids and offers, laddered at several price levels, everywhere at once. It has no intention of filling all of them; it is quoting, not predicting. The exchange must guarantee the MM cannot spend more than its deposit.

Here is the trap. How much capital the MM's orders consume depends on which of them fill and at what prices. But the fills and the prices are precisely what the auction is choosing. The budget constraint is a product of two unknowns — price times quantity, where price is itself a function of all the quantities. Write it into the optimization and the feasible set stops being convex.

The paper makes this concrete with a two-market example so small you can differentiate it by hand. The capital one buy order consumes is $f(q) = sigma(q\/b) dot q$ — fill size times the price your own fill pushed up. That function is convex for small fills and concave for large ones (@fig-dent, left). Give one MM an order in each of two independent markets, and there are two fill plans that each respect a \$10.8 budget while the plan halfway between them costs \$10.96 — over budget (@fig-dent, right). A feasible set that excludes the midpoint of two feasible points is not convex, and the construction survives at _every_ temperature. Smoothing does not save you.

#figure(
  fig-obstacle,
  kind: image,
  supplement: [Figure],
  caption: [Why hard budgets break convexity. Left: the capital one order consumes is convex, then concave, in its own fill. Right: along the line between two budget-respecting fill plans, capital consumption bulges above the budget. Convex solvers cannot search a set shaped like this.],
) <fig-dent>

Non-convex feasible sets are where reliable algorithms go to die: interior-point methods, projected gradients — all of them assume away exactly this. What do production systems do? They iterate: clear ignoring budgets, check who overdrew, haircut those orders, re-clear, repeat. No convergence guarantee. The loop can cycle.

(How real is the wall? A companion note settles it: for books as simple as this example the dent can be flattened by a change of coordinates, but with big resting retail orders it cannot — clearing the hard-budget model _exactly_ is NP-hard, up to one final routine verification. Approximate clearing stays easy, and the rest of this primer is about the approximation that comes with a guarantee.)

It is tempting to file this under "markets are hard." The paper's diagnosis is more pointed: the model is arguing with itself. _Linear_ welfare says the MM values the 1,001st share exactly as much as the 1st — it would happily bet everything on a sliver of edge. The _hard budget_ says it absolutely will not. One half of the model claims risk-neutrality; the other half encodes risk-aversion. The non-convexity is the computational symptom of an economic contradiction, and that reframing tells you exactly where to look for the cure: not in the algorithm, in the utility function.

= A Budget Is a Preference in Disguise

Ask why the budget exists. A genuinely risk-neutral trader with an edge would never cap its own exposure — capping is something you do because losing your last dollar hurts more than winning another one helps. The deposit of \$50,000 rather than everything is _revealed_ risk-aversion. So instead of bolting a cap onto a linear objective, derive the utility the cap was approximating.

The derivation takes one idea: let the MM keep cash. Suppose the MM's underlying preference is logarithmic in its deployed capital (the Kelly criterion's utility — the one that maximizes long-run growth for a repeat player, which is what a market maker is), and that it can always deploy part of its budget as _retained cash_ rather than fills. Cash inside the log at face value, cash paid out at face value. Optimize the cash choice away and out drops a clean, closed-form utility for fill value $U$ against budget $B$:

$ psi_B (U) = cases(
  U + B ln B - B & "if" U <= B quad & "(budget slack: affine, slope 1)",
  B ln U & "if" U >= B quad & "(capital binds: logarithmic, slope" B\/U")"
) $

#figure(
  fig-psi,
  kind: image,
  supplement: [Figure],
  caption: [The reduced-form utility. While the budget is slack the MM is the same linear agent the LP assumed; once capital binds, the log branch takes over. The two branches meet smoothly — no kink, no threshold behavior to tune.],
) <fig-psi-primer>

Read the two branches as a personality (@fig-psi-primer). While fills are worth less than the budget, the MM is _exactly_ the linear agent the LP always assumed — the model changes nothing for well-capitalized participants. Once fills exceed the budget, marginal utility decays like $B\/U$: the scarcer capital gets, the pickier the MM becomes. One number summarizes the state,

$ alpha = psi'_B (U) = min(1, B\/U) $

the _scarcity factor_: the fraction of face value the MM still assigns to its next dollar of fills.

#takeaway[
  *Tiny example.* Budget $B = 10$. If the auction offers the MM fills worth $U = 6$, then $alpha = 1$: it behaves like the LP and keeps $4$ in cash. If the auction would let it fill $U = 16$ worth, then $alpha = 10\/16 = 0.625$: it values additional fills at $62.5$ cents on the dollar, and any order whose edge is thinner than that simply doesn't fill.
]

Now the punchline, and it is the paper's favorite lemma. Take an agent with utility $psi_B$, put it in front of _any_ prices whatsoever, and let it buy whatever it likes — no budget constraint imposed by anyone. It never spends more than $B$. The optimal spend is provably at most $min(U, B)$. The budget has become _self-enforcing_: a property of preferences rather than a rule the exchange must police. The constraint didn't get relaxed; it got internalized.

= What the Auction Becomes

Substitute $psi_B$ for each market maker's linear welfare in the clearing objective, and delete every budget constraint — you now know they'll hold on their own. What remains is a concave maximization over a convex set. The pathology of the previous section is gone, not because we found a cleverer algorithm, but because the corrected model was never non-convex to begin with.

And this program is not just "some convex program." In 1959, Eisenberg and Gale wrote down a convex program whose solutions are the competitive equilibria of a _Fisher market_ — the textbook economy where consumers with budgets buy divisible goods at market prices. Their motivating application was aggregating bettors' subjective probabilities in pari-mutuel horse-race wagering. The clearing program above is exactly a modern Fisher market of the quasilinear kind (agents may keep unspent money), with one twist: the goods are not in fixed supply — they are minted on demand at cost. Two-thirds of a century later, the machinery comes home to betting.

#align(center)[
  #table(
    columns: 3,
    align: (left, center, center),
    stroke: 0.5pt,
    inset: 6pt,
    [*Component*], [*Fisher market (1959)*], [*Batch auction (here)*],
    [Buyers with budgets], [Consumers], [Market makers],
    [Goods], [Divisible commodities], [Outcome shares],
    [Supply], [Fixed endowment], [Minted at cost (\$1 per complete set)],
    [Unspent money], [Kept as cash], [Retained cash $s_k$],
    [Prices], [Equilibrium dual variables], [Softmax of net demand],
  )
]

The identification is exact, not analogical: solutions of the clearing program coincide with competitive equilibria of this economy. Retail orders maximize surplus at the clearing prices; each MM maximizes $psi_B$-utility at the clearing prices; a zero-profit minting sector supplies exactly the net demand. The title of the paper is a theorem.

Equilibrium also tells you _what capital scarcity does_, in one sentence: a capital-constrained MM behaves exactly as if every one of its limit prices were multiplied by its scarcity factor $alpha$. Post at $0.70$ with $alpha = 0.71$ and you are effectively bidding $0.50$. All quotes shaded by one number — highest-return fills survive, thin-edge fills die, a greedy knapsack with a cutoff. If this sounds familiar, it should: it is precisely the _pacing multiplier_ that ad exchanges use to manage advertiser budgets in first-price auctions, where budget pacing is likewise known to solve a quasilinear Fisher market. Two industries, one mathematical object. In ad tech, pacing is a subsystem bolted beside the auction; here it falls out of the clearing program itself.

#takeaway[
  *The three-order example.* One binary market, $b -> 0$. An MM with budget $50$ bids Yes at $0.70$ for 100 shares and at $0.55$ for 100 more; a retail trader bids No at $0.60$ for 200. Ignore budgets and everything fills — but the MM's bill is at least $80$. It cannot settle. The Fisher-market clearing instead computes scarcity $alpha = 50\/70 approx 0.71$: the $0.70$ bid survives the shading ($0.71 times 0.70 = 0.50$, above the clearing price $0.40$), the $0.55$ bid dies ($0.39$, below), the retail order fills halfway, and the MM spends $40 <= 50$. Prices land on $0.40\/0.60$, everyone's limit price is honored, and no constraint was ever imposed. @fig-worked draws the mechanics.
]

#figure(
  fig-example,
  kind: image,
  supplement: [Figure],
  caption: [The three-order example in pictures. Left: the MM's posted quotes (gray) are shaded by $alpha = 50\/70 approx 0.71$ (blue); the $0.70$ bid clears the $0.40$ price, the $0.55$ bid does not. Right: the LP's fills cost $80$ — unsettleable against the $50$ budget — while the Fisher fills cost $40$, inside it.],
) <fig-worked>

One more bookkeeping fact deserves a sentence, because it is the mechanism that makes all of this legal. Where did the budget constraint _go_? Into the logarithm. A log-utility buyer's spending is scale-invariant — double all prices and its bill doesn't change; it always spends exactly its budget. That is the classical reason Eisenberg–Gale works, and the retained-cash option softens "exactly" to "at most." The exchange deletes the constraint; the utility enforces it.

= What You Get for Free

Once clearing is a Fisher market, decades of convex-duality machinery start paying out. Each of these is a theorem in the paper:

- *Prices are unique — and so is everything that matters.* For any temperature $b > 0$, the clearing prices are unique, and so are each MM's deployed capital and scarcity factor. Whatever multiplicity remains is economically invisible (reshuffling fills among tied orders).

- *The LP degeneracy resolves itself.* At $b = 0$ several price vectors can support the same fills. As $b -> 0$, the smoothed prices converge to a _canonical_ choice: the maximum-entropy price among the LP's dual optima (@fig-me). An exchange clearing at zero temperature can adopt "pick the max-entropy dual" as its tie-break and be exactly consistent with every smoothed auction's limit.

// TODO(validation): 0.7% figure is from the internal prototype; update with the open-source repo's numbers.
- *You approximately solved the problem you abandoned.* The Fisher solution is _feasible_ for the original hard-budget problem — budgets hold at its own prices — and its welfare is within $sum_k Delta_k^2\/(2 B_k)$ of the hard-budget optimum, where $Delta_k$ is how far the LP would have overshot MM $k$'s budget. Quadratic in the shortfall, zero for well-capitalized MMs, and under $0.7%$ in preliminary synthetic experiments even at $10 times$ oversubscription. One convex solve, with a guarantee, replacing a heuristic loop with none.

- *It runs at LP speed.* In conic form the whole program is the clearing LP plus _one_ exponential-cone constraint per market maker. Off-the-shelf solvers (Clarabel, MOSEK) handle it; with few MMs each solver iteration costs essentially what the LP's does.

- *Combinatorial markets become an inference problem.* With bundle orders over many market groups, the smoothed minting cost is the log-partition function of a Gibbs distribution whose factor graph is the order book — and clearing prices are its marginals. Sparse coupling (low treewidth) means exact polynomial-time clearing by junction tree; dense coupling is provably hard. The complexity of combinatorial clearing is the complexity of probabilistic inference, imported wholesale.

#figure(
  fig-maxent,
  kind: image,
  supplement: [Figure],
  caption: [When the LP's prices are ambiguous (thick segment), the smoothed auction's unique price approaches the maximum-entropy point of the ambiguous set as the temperature falls — a canonical tie-break, selected by the smoothing itself.],
) <fig-me>

= Mental Model

Six lines to remember:

+ *Baseline:* batch clearing is surplus minus a minting bill; prices are probabilities because complete sets cost \$1.
+ *Knob:* LMSR is the same auction with temperature $b$; smoothness costs at most $b ln K$.
+ *Obstacle:* linear MM welfare plus hard budget caps is a self-contradictory model, and its feasible set is non-convex.
+ *Move:* a budgeted MM with retained cash has utility $psi_B$ — affine while slack, logarithmic once capital binds — and never overspends at any prices.
+ *Payoff:* clearing becomes a quasilinear Fisher market with minted supply; optima are competitive equilibria; scarcity is one pacing factor per MM.
+ *Dividends:* unique prices, a max-entropy tie-break at $b = 0$, a quadratic-gap approximation to the hard-budget problem, LP-speed conic solvers, and clearing-as-inference for combinatorial markets.

For the proofs, read the paper: Sections 2–3 formalize the baseline and the obstacle, Section 5 is the main theorem and its consequences, and Section 6 is the computational story. Three companion notes in the repository go further: _Decomposed Clearing_ (how one MM budget splits exactly across independent market components), _Bundle Clearing_ (combinatorial markets, junction trees, and why treewidth is the frontier), and _The Complexity of Clearing with Hard Budgets_ (why the hard-budget model is NP-hard to solve exactly — and why only exactly, so the convex program above remains the algorithm to run).
