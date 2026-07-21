import numpy as np
from scipy.optimize import brentq
import sympy as sp

# ---- Debt 1: verify the analytic proof symbolically ----
# gamma'(t) = (L - sig)/(sig*(1 + t*(1-sig))),  sig = sigma(t), b=1
# Claim: d/dt ln gamma' = -(1-sig) * [ sig/(L-sig) + (2 + t*(1-2*sig))/(1 + t*(1-sig)) ]
# and for L=1 the bracket positivity reduces to (2-sig) + t*(1-sig)^2 > 0.
t, L = sp.symbols('t L', positive=True)
sig = 1/(1+sp.exp(-t))
R = (L - sig)/(sig*(1 + t*(1-sig)))
dlnR = sp.simplify(sp.diff(sp.log(R), t))
bracket = sig/(L-sig) + (2 + t*(1-2*sig))/(1 + t*(1-sig))
check = sp.simplify(dlnR + (1-sig)*bracket)
print("Debt1 identity check (should be 0):", check)
# L=1 reduction: bracket*(1-sig)*(1+t*(1-sig)) with sig/(1-sig) term ->
red = sp.simplify(( sig/(1-sig) + (2 + t*(1-2*sig))/(1 + t*(1-sig)) ) * (1-sig)*(1+t*(1-sig)) - ((2-sig) + t*(1-sig)**2))
print("Debt1 L=1 reduction check (should be 0):", sp.simplify(red))

# ---- Debt 2: envelope certificate for the capped wall gadget ----
# b=1, L_R=0.7, Q_R=6, MM cap at q+ = q* + Q_R  (frontier: strictly concave arc, then linear wall)
LR, QR = 0.7, 6.0
qs = np.log(LR/(1-LR))
def sigf(x): return 1/(1+np.exp(-x))
def Cb(d): return np.logaddexp(d,0.0)
def pre(q):   # pre-wall
    return sigf(q)*q, q - Cb(q) + Cb(0)
def wall(q):  # on wall
    return LR*q, q - LR*(q-qs) - Cb(qs) + Cb(0)
qplus = qs + QR
xp, Wp = wall(qplus)
def slope_pre(q):  # dW/de on pre-wall arc
    s = sigf(q)
    return (1-s)/(s*(1+q*(1-s)))
def tangency(q):
    e, W = pre(q)
    return slope_pre(q) - (Wp - W)/(xp - e)
qm = brentq(tangency, 1e-9, qs - 1e-9)
xm, Wm = pre(qm)
mu = (Wp - Wm)/(xp - xm)
wall_slope = (1-LR)/LR
print(f"\nDebt2: q- = {qm:.6f} (q* = {qs:.6f}, q+ = {qplus:.6f})")
print(f"x- = {xm:.6f}, x+ = {xp:.6f}, mu* = {mu:.6f}, wall slope = {wall_slope:.6f}")
print(f"structural doubleton: mu* < wall slope: {mu < wall_slope}, x- interior: {0 < qm < qs}")
# gap function g(x) = chord(x) - gamma(x) on [x-, x+]; quadratic constant at x-, min in the middle
qgrid = np.linspace(qm, qplus, 200001)
ev = np.where(qgrid <= qs, sigf(qgrid)*qgrid, LR*qgrid)
Wv = np.where(qgrid <= qs, qgrid - Cb(qgrid) + Cb(0), qgrid - LR*(qgrid-qs) - Cb(qs) + Cb(0))
chord = Wm + mu*(ev - xm)
gap = chord - Wv
print(f"gap >= 0 on [x-,x+]: {gap.min() >= -1e-12};  max gap = {gap.max():.6f} at e = {ev[gap.argmax()]:.4f}")
print(f"gap at wall start e* = {LR*qs:.4f}: {np.interp(LR*qs, ev, gap):.6f}")
# quadratic constant near x-: gap ~ c (e - x-)^2
mask = (ev > xm + 1e-4) & (ev < xm + 0.05)
c_est = (gap[mask]/(ev[mask]-xm)**2).min()
print(f"quadratic constant near x-: c >= {c_est:.4f}")
