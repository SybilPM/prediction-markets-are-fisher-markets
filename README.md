# Prediction Markets Are Fisher Markets

Batch auction clearing via Eisenberg-Gale duality.

A market maker's balance can enter clearing as a retained-cash preference: under the primitive B log(U+s)−s, optimizing out cash gives an exact reduced form — affine when capital is slack, logarithmic when capital binds — that never overspends at any prices. Batch clearing then becomes a quasilinear Fisher market with minted supply: optima are competitive equilibria, capital scarcity acts as one pacing factor per MM, positive-temperature prices are unique and select a maximum-entropy zero-temperature price as b → 0, and one convex solve approximates the non-convex hard-budget problem with a quadratic welfare guarantee.

## Documents

- **[Primer](build/primer.pdf)** — the ideas without the proofs; start here
- **[Paper](build/paper.pdf)** — full treatment: theorems, proofs, a certified matching-LP oracle, held-out solver evidence, figures, and open problems
- **[Decomposition note](build/decomposition.pdf)** — budget coordination across market groups: the equal-scarcity theorem, proportional response, and the convex-surrogate trap
- **[Bundle-clearing note](build/bundle-clearing.pdf)** — combinatorial markets: component factorization, junction trees, priced injection with a welfare bound
- **[Complexity companion](build/complexity.pdf)** — *The Complexity of Clearing with Hard Budgets*: thin books convexify despite the non-convex feasible set, retail walls preserve a genuinely non-concave frontier, and the remaining complexity classification
- **[Empirical v2 integration material](empirical-retained-cash-v2.typ)** — held-out retained-cash solver evaluation, certificates, adversarial flash liquidity, negative findings, and reproducibility map
- **[Post-evaluation solver engineering](solver-engineering-followup.typ)** — development-only LP-oracle reuse, Clarabel formulation audit, and a certified pacing-dual research path
- **[Pacing-bundle development material](pacing-bundle-development.typ)** — fully corrective pacing derivation, model corrections, complete development matrix, landing limitation, and future paper protocol
- **[Empirical v1 integration material](empirical-material.typ)** — retained first preregistration, including the generic conic solver's negative reliability result
- **[Lean formalization](lean/README.md)** — sorry-free machine-checked formalization of every numbered analytical result in the main paper, with an exact [paper-to-Lean theorem map](lean/THEOREM_COVERAGE.md)

## Building

Requires [Typst](https://typst.app/).

```sh
typst compile paper.typ build/paper.pdf
typst compile primer.typ build/primer.pdf
typst compile decomposition.typ build/decomposition.pdf
typst compile bundle-clearing.typ build/bundle-clearing.pdf
typst compile complexity.typ build/complexity.pdf
typst compile empirical-material.typ build/empirical-material.pdf
typst compile empirical-retained-cash-v2.typ build/empirical-retained-cash-v2.pdf
typst compile solver-engineering-followup.typ build/solver-engineering-followup.pdf
typst compile pacing-bundle-development.typ build/pacing-bundle-development.pdf
```

The companion formalization is pinned to Lean 4.32.0 and mathlib 4.32.0:

```sh
cd lean
lake exe cache get
lake build
```

## License

This work is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
