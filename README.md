# Prediction Markets Are Fisher Markets

Batch auction clearing via Eisenberg-Gale duality.

A budgeted market maker with retained cash has a simple reduced-form utility: affine when capital is slack, logarithmic when capital binds. This converts prediction market batch auctions into a Fisher-market clearing program with exact limit-order KKT conditions, endogenous budget absorption, unique smoothed prices, and polynomial-time conic formulations.

## Documents

- **[Paper](build/paper.pdf)** — full treatment with proofs
- **[Primer](build/primer.pdf)** — compressed walkthrough of the core math

## Building

Requires [Typst](https://typst.app/).

```sh
typst compile paper.typ build/paper.pdf
typst compile primer.typ build/primer.pdf
```

## License

This work is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
