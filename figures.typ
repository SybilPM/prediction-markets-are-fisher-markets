// figures.typ — shared figures for paper.typ and primer.typ
// Semantic colors: ACCENT (blue) = the smooth/reduced-form object of interest;
// LIMIT (red) = hard/zero-temperature objects (LP step, budget cap, b->0 limit);
// REF (gray) = reference geometry (envelopes, asymptotes, naive models).

#let ACCENT = rgb("#1d4ed8")
#let LIMIT = rgb("#b91c1c")
#let AXIS = luma(140)
#let GRID = luma(215)
#let REF = luma(150)
#let INK = luma(60)

#let pline(pts, s) = place(top + left, curve(
  stroke: s,
  curve.move(pts.first()),
  ..pts.slice(1).map(p => curve.line(p)),
))

#let pfill(pts, f) = place(top + left, curve(
  fill: f, stroke: none,
  curve.move(pts.first()),
  ..pts.slice(1).map(p => curve.line(p)),
  curve.close(),
))

#let dot(pos, r: 2pt, fill: black, stroke: none) = place(
  top + left,
  dx: pos.at(0) - r, dy: pos.at(1) - r,
  circle(radius: r, fill: fill, stroke: stroke),
)

#let lbl(pos, body, dx: 0pt, dy: 0pt, size: 8pt) = place(
  top + left,
  dx: pos.at(0) + dx, dy: pos.at(1) + dy,
  text(size: size, fill: INK, body),
)

#let mkmap(x0, x1, y0, y1, w, h) = (x, y) => (
  (x - x0) / (x1 - x0) * w,
  (1.0 - (y - y0) / (y1 - y0)) * h,
)

#let sig(x) = 1.0 / (1.0 + calc.exp(-x))

#let samples(x0, x1, n, f) = range(0, n + 1).map(i => {
  let x = x0 + (x1 - x0) * i / n
  (x, f(x))
})

// ---------------------------------------------------------------------------
// Figure: softmax prices vs LP step (the temperature knob)
// ---------------------------------------------------------------------------

#let fig-softmax = {
  let w = 250pt
  let h = 110pt
  let P = mkmap(-8.0, 8.0, -0.06, 1.06, w, h)
  pad(left: 20pt, bottom: 2pt, box(width: w, height: h + 16pt, {
    // gridlines
    pline((P(-8, 0.0), P(8, 0.0)), (paint: GRID, thickness: 0.5pt, dash: "dotted"))
    pline((P(-8, 0.5), P(8, 0.5)), (paint: GRID, thickness: 0.5pt, dash: "dotted"))
    pline((P(-8, 1.0), P(8, 1.0)), (paint: GRID, thickness: 0.5pt, dash: "dotted"))
    // axes
    pline((P(-8, -0.06), P(8, -0.06)), 0.6pt + AXIS)
    pline((P(-8, -0.06), P(-8, 1.06)), 0.6pt + AXIS)
    // LP step (b -> 0)
    pline((P(-8, 0.0), P(0, 0.0), P(0, 1.0), P(8, 1.0)),
      (paint: LIMIT, thickness: 1pt, dash: "dashed"))
    // smoothed prices
    pline(samples(-8.0, 8.0, 64, d => sig(d / 3.0)).map(q => P(q.at(0), q.at(1))), 1pt + REF)
    pline(samples(-8.0, 8.0, 64, d => sig(d / 1.0)).map(q => P(q.at(0), q.at(1))), 1.2pt + ACCENT)
    // tick labels
    lbl(P(-8, 1.0), [1], dx: -10pt, dy: -5pt)
    lbl(P(-8, 0.5), [$1\/2$], dx: -16pt, dy: -5pt)
    lbl(P(-8, 0.0), [0], dx: -10pt, dy: -5pt)
    lbl(P(0, -0.06), [0], dx: -2pt, dy: 4pt)
    // curve labels
    lbl(P(1.5, 0.73), text(fill: ACCENT)[$b = 1$], dx: 2pt)
    lbl(P(5.0, 0.78), text(fill: REF.darken(25%))[$b = 3$], dy: 4pt)
    lbl(P(0, 0.75), text(fill: LIMIT)[$b -> 0$ (LP step)], dx: -62pt)
    // axis labels
    lbl(P(8, -0.06), [net demand gap $D_"Yes" - D_"No"$], dx: -105pt, dy: 5pt)
    lbl(P(-8, 1.06), [$p_"Yes"$], dx: 5pt, dy: -3pt)
  }))
}

// ---------------------------------------------------------------------------
// Figure: the budget obstacle (two panels)
// ---------------------------------------------------------------------------

#let panel-inflect = {
  let w = 165pt
  let h = 125pt
  let P = mkmap(0.0, 8.0, 0.0, 8.4, w, h)
  let f(q) = q * sig(q)
  box(width: w, height: h + 16pt, {
    // axes
    pline((P(0, 0), P(8, 0)), 0.6pt + AXIS)
    pline((P(0, 0), P(0, 8.4)), 0.6pt + AXIS)
    // asymptote y = q
    pline((P(0, 0), P(8, 8)), (paint: REF, thickness: 0.7pt, dash: "dashed"))
    // capital curve
    pline(samples(0.0, 8.0, 64, f).map(q => P(q.at(0), q.at(1))), 1.2pt + ACCENT)
    // inflection
    dot(P(2.399, f(2.399)), r: 2pt, fill: black)
    lbl(P(2.399, f(2.399)), [inflection $q^* approx 2.4b$], dx: 4pt, dy: 2pt)
    lbl(P(2.0, 0.62), text(fill: ACCENT)[convex], dy: 0pt)
    lbl(P(4.7, 3.5), text(fill: ACCENT)[concave], dy: 0pt)
    lbl(P(6.1, 7.0), text(fill: REF.darken(25%))[$y = q$], dy: -2pt)
    // axis labels
    lbl(P(8, 0), [fill $q$], dx: -24pt, dy: 5pt)
    lbl(P(0, 8.4), [capital $f(q) = sigma(q\/b) thin q$], dx: 4pt, dy: -3pt)
  })
}

#let panel-chord = {
  let w = 165pt
  let h = 125pt
  let P = mkmap(0.0, 1.0, 10.70, 11.0, w, h)
  let f(q) = q * sig(q)
  let g(t) = f(2.0 + 7.0 * t) + f(9.0 - 7.0 * t)
  box(width: w, height: h + 16pt, {
    // axes
    pline((P(0, 10.70), P(1, 10.70)), 0.6pt + AXIS)
    pline((P(0, 10.70), P(0, 11.0)), 0.6pt + AXIS)
    // budget line
    pline((P(0, 10.8), P(1, 10.8)), (paint: LIMIT, thickness: 1pt, dash: "dashed"))
    lbl(P(0.58, 10.8), text(fill: LIMIT)[budget $B = 10.8b$], dx: 0pt, dy: 3pt)
    // capital along the chord
    pline(samples(0.0, 1.0, 48, g).map(q => P(q.at(0), q.at(1))), 1.2pt + ACCENT)
    // endpoints and midpoint
    dot(P(0.0, g(0.0)), r: 2.2pt, fill: ACCENT)
    dot(P(1.0, g(1.0)), r: 2.2pt, fill: ACCENT)
    dot(P(0.5, g(0.5)), r: 2.2pt, fill: white, stroke: 1pt + LIMIT)
    lbl(P(0.0, g(0.0)), [$x_b$], dx: 3pt, dy: 4pt)
    lbl(P(1.0, g(1.0)), [$y_b$], dx: -10pt, dy: 4pt)
    lbl(P(0.5, g(0.5)), [midpoint over budget], dx: -38pt, dy: -12pt)
    // axis labels
    lbl(P(1, 10.70), [fill plans from $x_b$ to $y_b$], dx: -96pt, dy: 5pt)
    lbl(P(0, 11.0), [capital consumed], dx: 4pt, dy: -3pt)
  })
}

#let fig-obstacle = grid(
  columns: (auto, auto),
  column-gutter: 20pt,
  panel-inflect, panel-chord,
)

// ---------------------------------------------------------------------------
// Figure: the reduced-form utility psi_B (B = 1)
// ---------------------------------------------------------------------------

#let fig-psi = {
  let w = 250pt
  let h = 130pt
  let P = mkmap(-0.15, 4.2, -1.8, 3.3, w, h)
  pad(left: 6pt, bottom: 2pt, box(width: w, height: h + 14pt, {
    // shaded capital-binding region
    pfill((P(1, -1.8), P(4.2, -1.8), P(4.2, 3.3), P(1, 3.3)), luma(247))
    lbl(P(0.02, 3.05), [budget slack], dx: 4pt)
    lbl(P(1.08, 3.05), [capital binds], dx: 4pt)
    // axes through origin
    pline((P(-0.15, 0), P(4.2, 0)), 0.6pt + AXIS)
    pline((P(0, -1.8), P(0, 3.3)), 0.6pt + AXIS)
    // affine envelope U - 1 beyond the kink
    pline((P(1, 0), P(4.2, 3.2)), (paint: REF, thickness: 0.8pt, dash: "dashed"))
    lbl(P(3.0, 2.05), text(fill: REF.darken(25%))[affine envelope], dy: -4pt)
    // naive B ln U on the slack region
    pline(samples(0.19, 1.0, 32, u => calc.ln(u)).map(q => P(q.at(0), q.at(1))),
      (paint: REF, thickness: 0.8pt, dash: "dotted"))
    lbl(P(0.28, -1.35), text(fill: REF.darken(25%))[$B ln U$ (naive)])
    // psi: affine branch then log branch
    pline((P(0, -1), P(1, 0)), 1.3pt + ACCENT)
    pline(samples(1.0, 4.2, 48, u => calc.ln(u)).map(q => P(q.at(0), q.at(1))), 1.3pt + ACCENT)
    lbl(P(0.12, -0.30), text(fill: ACCENT)[slope $1$])
    lbl(P(1.9, 0.42), text(fill: ACCENT)[$psi_B$: slope $B\/U$])
    // kink
    dot(P(1, 0), r: 2.2pt, fill: black)
    lbl(P(1, 0), [$U = B$], dx: 3pt, dy: 4pt)
    // axis labels
    lbl(P(4.2, 0), [fill value $U$], dx: -50pt, dy: 4pt)
  }))
}

// ---------------------------------------------------------------------------
// Figure: the worked example (pacing test + capital bill)
// ---------------------------------------------------------------------------

#let panel-pacing = {
  let w = 165pt
  let h = 112pt
  let P = mkmap(0.0, 10.0, 0.30, 0.80, w, h)
  // downward arrowhead at canvas point p
  let arrowhead(p) = pfill(
    ((p.at(0) - 2.4pt, p.at(1) - 4.5pt), (p.at(0) + 2.4pt, p.at(1) - 4.5pt), p),
    INK,
  )
  box(width: w, height: h + 16pt, {
    // axes
    pline((P(0, 0.30), P(10, 0.30)), 0.6pt + AXIS)
    pline((P(0, 0.30), P(0, 0.80)), 0.6pt + AXIS)
    // price ticks
    lbl(P(0, 0.70), [$0.70$], dx: -22pt, dy: -5pt)
    lbl(P(0, 0.55), [$0.55$], dx: -22pt, dy: -5pt)
    lbl(P(0, 0.40), [$0.40$], dx: -22pt, dy: -5pt)
    // clearing price
    pline((P(0, 0.40), P(10, 0.40)), (paint: LIMIT, thickness: 1pt, dash: "dashed"))
    lbl(P(0.3, 0.40), text(fill: LIMIT)[clearing price $p_"Yes"$], dy: -11pt)
    // order X: posted 0.70, shaded to 0.50
    dot(P(2.6, 0.70), r: 2.2pt, fill: white, stroke: 1pt + REF)
    pline((P(2.6, 0.685), P(2.6, 0.515)), (paint: INK, thickness: 0.7pt, dash: "dotted"))
    arrowhead(P(2.6, 0.517))
    dot(P(2.6, 0.50), r: 2.2pt, fill: ACCENT)
    lbl(P(2.6, 0.70), [$L_X = 0.70$], dx: 6pt, dy: -4pt)
    lbl(P(2.6, 0.50), text(fill: ACCENT)[$alpha L_X = 0.50$ — fills], dx: 6pt, dy: -4pt)
    // order Y: posted 0.55, shaded to 0.39
    dot(P(7.4, 0.55), r: 2.2pt, fill: white, stroke: 1pt + REF)
    pline((P(7.4, 0.535), P(7.4, 0.410)), (paint: INK, thickness: 0.7pt, dash: "dotted"))
    arrowhead(P(7.4, 0.412))
    dot(P(7.4, 0.393), r: 2.2pt, fill: ACCENT)
    lbl(P(7.4, 0.55), [$L_Y = 0.55$], dx: 6pt, dy: -4pt)
    lbl(P(7.4, 0.393), text(fill: ACCENT)[$alpha L_Y approx 0.39$ — rejected], dx: -42pt, dy: 5pt)
    // shading factor
    lbl(P(0.3, 0.79), [quotes shaded by $alpha = 50\/70 approx 0.71$], dy: -2pt)
    // axis label
    lbl(P(10, 0.30), [MM orders], dx: -36pt, dy: 5pt)
  })
}

#let panel-bill = {
  let w = 165pt
  let h = 112pt
  let P = mkmap(0.0, 92.0, 0.0, 10.0, w, h)
  box(width: w, height: h + 16pt, {
    // axes
    pline((P(0, 0), P(92, 0)), 0.6pt + AXIS)
    pline((P(0, 0), P(0, 10)), 0.6pt + AXIS)
    // capital ticks
    lbl(P(0, 0), [0], dx: -2pt, dy: 4pt)
    lbl(P(40, 0), [40], dx: -5pt, dy: 4pt)
    lbl(P(80, 0), [80], dx: -5pt, dy: 4pt)
    // LP bar: 80, overrunning the budget
    pfill((P(0, 6.6), P(50, 6.6), P(50, 8.6), P(0, 8.6)), luma(230))
    pfill((P(50, 6.6), P(80, 6.6), P(80, 8.6), P(50, 8.6)), LIMIT.lighten(72%))
    pline((P(0, 6.6), P(80, 6.6), P(80, 8.6), P(0, 8.6), P(0, 6.6)), 0.6pt + REF)
    lbl(P(1.5, 8.53), [LP fills: $80$ — cannot settle], dy: 1pt)
    // Fisher bar: 40, inside the budget
    pfill((P(0, 2.0), P(40, 2.0), P(40, 4.0), P(0, 4.0)), ACCENT.lighten(72%))
    pline((P(0, 2.0), P(40, 2.0), P(40, 4.0), P(0, 4.0), P(0, 2.0)), 0.6pt + ACCENT)
    lbl(P(1.5, 3.93), text(fill: ACCENT)[Fisher fills: $40$], dy: 1pt)
    // slack bracket between 40 and 50 at Fisher bar height
    pline((P(40, 1.5), P(40, 1.1), P(50, 1.1), P(50, 1.5)), 0.5pt + INK)
    lbl(P(40, 1.1), [slack $10$ (rent)], dx: -54pt, dy: 0pt)
    // budget line
    pline((P(50, 0), P(50, 10)), (paint: LIMIT, thickness: 1pt, dash: "dashed"))
    lbl(P(50, 10), text(fill: LIMIT)[budget $B = 50$], dx: 4pt, dy: -1pt)
    // axis label
    lbl(P(92, 0), [capital consumed at $p_"Yes" = 0.40$], dx: -122pt, dy: 12pt)
  })
}

#let fig-example = grid(
  columns: (auto, auto),
  column-gutter: 20pt,
  panel-pacing, panel-bill,
)

// ---------------------------------------------------------------------------
// Figure: maximum-entropy price selection (schematic, K = 3)
// ---------------------------------------------------------------------------

#let fig-maxent = {
  let w = 230pt
  let h = 168pt
  // triangle vertices in canvas floats (pt)
  let T = (115.0, 12.0)
  let L = (25.0, 152.0)
  let R = (205.0, 152.0)
  let bary(a, b, c) = (
    (a * T.at(0) + b * L.at(0) + c * R.at(0)) * 1pt,
    (a * T.at(1) + b * L.at(1) + c * R.at(1)) * 1pt,
  )
  let A = bary(0.70, 0.22, 0.08)
  let B2 = bary(0.34, 0.10, 0.56)
  let cen = bary(0.334, 0.333, 0.333)
  let me = bary(0.492, 0.150, 0.358) // max-entropy point of the face (t ~ 0.58)
  box(width: w, height: h + 14pt, {
    // simplex
    pline((bary(1, 0, 0), bary(0, 1, 0), bary(0, 0, 1), bary(1, 0, 0)), 0.7pt + AXIS)
    lbl(bary(1, 0, 0), [$omega_1$], dx: -4pt, dy: -12pt)
    lbl(bary(0, 1, 0), [$omega_2$], dx: -14pt, dy: 2pt)
    lbl(bary(0, 0, 1), [$omega_3$], dx: 4pt, dy: 2pt)
    // LP dual face P_0
    pline((A, B2), 4pt + ACCENT.lighten(65%))
    pline((A, B2), 0.8pt + ACCENT)
    lbl(B2, text(fill: ACCENT)[$cal(P)_0$], dx: 6pt, dy: 1pt)
    // trajectory of p_b^* from uniform to the max-entropy point
    place(top + left, curve(
      stroke: (paint: ACCENT, thickness: 1pt, dash: "dotted"),
      curve.move(cen),
      curve.quad((94pt, 88pt), me),
    ))
    lbl((70pt, 80pt), text(fill: ACCENT)[$b -> 0$])
    // uniform point
    dot(cen, r: 2.2pt, fill: black)
    lbl(cen, [uniform ($b = infinity$)], dx: -28pt, dy: 7pt)
    // selected price, labeled outside the simplex with a leader line
    pline((me, (150pt, 52pt)), 0.5pt + luma(180))
    dot(me, r: 2.6pt, fill: LIMIT)
    lbl((152pt, 44pt), text(fill: LIMIT)[$p^"ME" = lim p_b^*$])
  })
}
