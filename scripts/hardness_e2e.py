import numpy as np
from scipy.optimize import brentq, minimize
rng = np.random.default_rng(0)

# Per-unit frontier gamma(x), b=1, L_R=0.7, Q_R=6, MM order capped at wall end.
LR, QR = 0.7, 6.0
qs = np.log(LR/(1-LR)); qplus = qs + QR
def sigf(z): return 1/(1+np.exp(-z))
def Cb(d): return np.logaddexp(d,0.0)
estar = LR*qs; xplus = LR*qplus
def gamma(x):
    if x <= 0: return 0.0
    if x <= estar:
        q = brentq(lambda q: sigf(q)*q - x, 0, qs)
        return q - Cb(q) + Cb(0)
    q = x/LR
    return q - LR*(q-qs) - Cb(qs) + Cb(0)
def slope_pre(q):
    s = sigf(q)
    return (1-s)/(s*(1+q*(1-s)))
qm = brentq(lambda q: slope_pre(q) - (gamma(xplus)-gamma(sigf(q)*q))/(xplus - sigf(q)*q), 1e-9, qs-1e-9)
xm = sigf(qm)*qm; mu = (gamma(xplus)-gamma(xm))/(xplus-xm); span = xplus - xm
kappa2 = ((1-LR)/LR - mu)*span
# Gbar = supporting line - gamma, zeros exactly at {xm, xplus}; kappa1 = inf Gbar/d^2 near y=0
def Gbar(x): return gamma(xm) + mu*(x-xm) - gamma(x)
ys = np.concatenate([np.linspace(-xm/span+1e-6, -1e-6, 4000), np.linspace(1e-6, (estar-xm)/span, 4000)])
k1 = min(Gbar(xm + y*span)/( (y*span)**2 ) for y in ys) * span**2
print(f"x-={xm:.6f} x+={xplus:.6f} mu*={mu:.6f} span={span:.6f}")
print(f"kappa2 (wall-back constant) = {kappa2:.6f}")
print(f"kappa1 (quadratic constant, y-units) = {k1:.4f}")

# ---- End-to-end SUBSET-SUM test: a={3,5,7}; T=8 (YES: 3+5), T=9 (NO: min miss 1) ----
a = np.array([3.,5.,7.]); A = a.sum()
def solve(T, nstart=400):
    B = A*xm + T*span
    Bound = A*gamma(xm) + mu*(B - A*xm)
    def neg(e):
        return -sum(ai*gamma(ei/ai) for ai,ei in zip(a,e))
    cons = ({'type':'ineq','fun': lambda e: B - e.sum()},)
    bnds = [(0, ai*xplus) for ai in a]
    best = None
    # lobe configs + refinement
    starts = [np.array([ai*(xm if bit==0 else xplus) for ai,bit in zip(a,cfg)])
              for cfg in [(i>>2&1,i>>1&1,i&1) for i in range(8)]]
    starts += [np.array([rng.uniform(0,ai*xplus) for ai in a]) for _ in range(nstart)]
    for x0 in starts:
        x0 = np.minimum(x0, np.array(bnds)[:,1])
        if x0.sum() > B: x0 = x0*B/x0.sum()
        r = minimize(neg, x0, bounds=bnds, constraints=cons, method='SLSQP',
                     options={'maxiter':500,'ftol':1e-14})
        if r.success and (best is None or r.fun < best.fun): best = r
    W = -best.fun
    yy = (best.x/a - xm)/span
    return Bound, W, yy
for T, tag in [(8,"YES"), (9,"NO")]:
    Bound, W, yy = solve(T)
    print(f"\nT={T} ({tag}): Bound={Bound:.6f}  achieved={W:.6f}  gap={Bound-W:.6f}")
    print(f"  lobe coords y = {np.round(yy,4)}")
print(f"\npredicted NO-gap (wall-back, integer 1): {kappa2:.6f}")
print(f"separation lower bound min(kappa2, kappa1/A) = {min(kappa2, k1/A):.6f}")
