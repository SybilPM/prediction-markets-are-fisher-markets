# FisherClearing

Lean 4 formalization of the mathematical results in *Prediction Markets Are
Fisher Markets*. The project is pinned to Lean 4.32.0 and mathlib 4.32.0 and
uses no external formalization library beyond mathlib.

The formalization covers every numbered analytical theorem, proposition,
lemma, and corollary in the main paper. It also checks the three-order worked
example and the unnumbered structural claims used by the proofs: UCP
fill/reject behavior, optimizer convergence as temperature vanishes, uniform
prices at infinite temperature, buy/sell complement reduction, and
independent-group factorization and marginals.

See [THEOREM_COVERAGE.md](THEOREM_COVERAGE.md) for the exact paper-to-Lean
map. The paper's held-out benchmark measurements, citations to external
complexity results, and the implementation complexity of third-party conic
solvers are evidence or imported background rather than propositions proved
inside Lean. The exact finite conic and LP-oracle reductions on which the
paper's algorithmic claims rest are machine checked.

## Model conventions

Each order fill is normalized to `[0,1]`; its size cap is absorbed into its
welfare coefficient and payoff tensor. Arbitrary finite payoff tensors cover
Arrow–Debreu orders and bundles. MM sells are represented by complementary
buys, justified by machine-checked translation-equivariance identities.
The hard-budget nonconvexity witness includes the order-cap box, and the
welfare theorem applies to every feasible comparator rather than requiring an
unnecessarily optimal comparator.

## Build

From this directory:

```sh
lake exe cache get
lake build
```

The build has no code or theorem-linter warnings. Mathlib's header linter
nevertheless prints one license-format notice per source file because it
hard-codes the Apache 2.0 header text while this project is released under
CC BY 4.0; those notices are intentional and the license is not suppressed.

To check for admitted declarations:

```sh
rg -n '\b(sorry|admit)\b|^[[:space:]]*axiom\b' \
  --glob '*.lean' FisherClearing FisherClearing.lean
```

No output is expected.

For the explicit dependency audit of representative top-level results:

```sh
lake env lean AxiomAudit.lean
```

It reports only `propext`, `Classical.choice`, and `Quot.sound`, the standard
classical/foundational axioms used by mathlib, and no `sorryAx`.
