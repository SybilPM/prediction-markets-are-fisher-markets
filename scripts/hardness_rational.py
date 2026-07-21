import numpy as np
from scipy.optimize import brentq, minimize
rng = np.random.default_rng(1)

# RATIONAL gadget: b=1, L_R=7/10, Q_R=6, MM cap qhat=6 (< q*+Q_R, so wall never exhausts).
# All instance parameters rational; only derived constants (x-, mu*, kappas) are transcendental.
LR, qhat = 0.7, 6.0
qs = np.log(LR/(1-LR))
def sigf(z): return 1/(1+np.exp(-z))
def Cb(d): return np.logaddexp(d,0.0)
estar = LR*qs; xplus = LR*qhat   # xplus = 4.2 exactly (rational!)
def gamma(x):
    if x <= 0: return 0.0
    if x <= estar:
        q = brentq(lambda q: sigf(q)*q - x, 0, qs)
        return q - Cb(q) + Cb(0)
    q = x/LR
    return q - LR*(q-qs) - Cb(qs) + Cb(0)
def slope_pre(q):
    s0 = sigf(q)
    return (1-s0)/(s0*(1+q*(1-s0)))
qm = brentq(lambda q: slope_pre(q) - (gamma(xplus)-gamma(sigf(q)*q))/(xplus - sigf(q)*q), 1e-9, qs-1e-9)
xm = sigf(qm)*qm; mu = (gamma(xplus)-gamma(xm))/(xplus-xm); span = xplus - xm
kappa2 = ((1-LR)/LR - mu)*span
def Gbar(x): return gamma(xm) + mu*(x-xm) - gamma(x)
# kappa1: direct inf, and certified via second-order Taylor: Gbar(x) >= (x-xm)^2/2 * min_arc Gbar''
ys = np.concatenate([np.linspace(-xm/span+1e-6, -1e-6, 4000), np.linspace(1e-6, (estar-xm)/span, 4000)])
k1_direct = min(Gbar(xm + y*span)/((y*span)**2) for y in ys) * span**2
# Gbar'' = -gamma'' on the arc; gamma'' = R'(q)/f'(q) with R = slope_pre
qq = np.linspace(1e-6, qs-1e-6, 20000)
sg = sigf(qq)
bracket = sg/(1-sg) + (2 + qq*(1-2*sg))/(1 + qq*(1-sg))
R = (1-sg)/(sg*(1+qq*(1-sg)))
fp = sg*(1+qq*(1-sg))
neg_gpp = R*(1-sg)*bracket/fp        # -gamma'' in e-coords
k1_cert = 0.5*neg_gpp.min()*span**2   # Gbar >= min(-gamma'')/2 * (x-xm)^2  => kappa1 >= this (y-units)
print(f"RATIONAL GADGET: x+ = {xplus} (exact), x- = {xm:.6f}, mu* = {mu:.6f}, span = {span:.6f}")
print(f"kappa2 = {kappa2:.6f}, kappa1 direct = {k1_direct:.4f}, kappa1 certified (Taylor) = {k1_cert:.4f}")
print(f"min(-gamma'') over arc = {neg_gpp.min():.4f} at q = {qq[neg_gpp.argmin()]:.4f}")

# ---- End-to-end with RATIONAL budget in the window [B0, B0 + c0/(2 mu*)) ----
a = np.array([3.,5.,7.]); A = a.sum()
c0 = min(kappa2, k1_cert/A)/8
def solve(T, B, nstart=400):
    def neg(e): return -sum(ai*gamma(ei/ai) for ai,ei in zip(a,e))
    cons = ({'type':'ineq','fun': lambda e: B - e.sum()},)
    bnds = [(0, ai*xplus) for ai in a]
    best = None
    starts = [np.array([ai*(xm if bit==0 else xplus) for ai,bit in zip(a,cfg)])
              for cfg in [(i>>2&1,i>>1&1,i&1) for i in range(8)]]
    starts += [np.array([rng.uniform(0,ai*xplus) for ai in a]) for _ in range(nstart)]
    for x0 in starts:
        x0 = np.minimum(x0, np.array(bnds)[:,1])
        if x0.sum() > B: x0 = x0*B/x0.sum()
        r = minimize(neg, x0, bounds=bnds, constraints=cons, method='SLSQP',
                     options={'maxiter':500,'ftol':1e-14})
        if r.success and (best is None or r.fun < best.fun): best = r
    return -best.fun
for T, tag in [(8,"YES"), (9,"NO")]:
    B0 = A*xm + T*span
    delta = c0/(4*mu)                       # rational-B window emulation
    B = B0 + delta
    X = A*gamma(xm) + mu*T*span             # lobe-configuration value (threshold anchor)
    Wstar = X - c0/4
    W = solve(T, B)
    verdict = "ACCEPT" if W >= Wstar else "REJECT"
    print(f"\nT={T} ({tag}): B = B0 + {delta:.2e};  achieved = {W:.6f}, threshold W* = {Wstar:.6f} -> {verdict}")
    print(f"  margin: {W - Wstar:+.6f}  (predicted YES ≥ +{c0/4:.4f}·..., NO ≤ -{c0/4:.6f})")
print(f"\nc0 = {c0:.6f}")
