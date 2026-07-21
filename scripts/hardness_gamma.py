import numpy as np

# Welfare-vs-MM-expenditure frontier gamma(e) in a single binary market, b=1.
# Case 1: MM alone (buy YES, limit L=1). q in [0, qmax].
#   welfare phi(q) = q - Cb(q) + Cb(0);  Cb(q)=ln(e^q+1);  e(q) = sigma(q)*q
# Case 2: MM + retail sell-YES wall at L_R=0.7, size QR.
#   clearing picks retail fill r: r=0 while sigma(q)<0.7; then r=q-q* (price pinned);
#   then r=QR, price sigma(q-QR).
#   welfare = q - 0.7 r - Cb(q-r) + Cb(0);  e = p*q.

def sig(x): return 1/(1+np.exp(-x))
def Cb(d): return np.logaddexp(d, 0.0)

def case1(q):
    p = sig(q)
    return p*q, q - Cb(q) + Cb(0)

LR, QR = 0.7, 6.0
qstar = np.log(LR/(1-LR))
def case2(q):
    if sig(q) < LR:
        r = 0.0
    elif q - QR < qstar:
        r = q - qstar
    else:
        r = QR
    d = q - r
    p = sig(d)
    return p*q, q - LR*r - Cb(d) + Cb(0)

for name, fn, qmax in [("MM-alone", case1, 12.0), ("retail-wall", fn2 := case2, qstar+QR+6)]:
    qs = np.linspace(1e-4, qmax, 40001)
    ev, wv = np.array([fn(q) for q in qs]).T
    # gamma'(e) via chain rule on the grid
    gp = np.gradient(wv, ev)
    # detect any increase in gamma' (non-concavity), ignoring tiny numeric noise
    inc = np.where(np.diff(gp) > 1e-6)[0]
    print(f"{name}: gamma' starts {gp[1]:.4f}, min {gp.min():.4f}")
    if len(inc):
        j = inc[0]
        print(f"  NON-CONCAVE: gamma' rises at e={ev[j]:.4f} (q={qs[j]:.4f}): {gp[j]:.4f} -> {gp[inc].max():.4f} max later")
        # size of the jump across the wall
        k = np.searchsorted(qs, qstar)
        print(f"  at wall q*={qstar:.4f}: gamma'_before={gp[k-5]:.4f}, gamma'_after={gp[k+5]:.4f}")
    else:
        print("  concave along the whole frontier (gamma' monotone decreasing)")
