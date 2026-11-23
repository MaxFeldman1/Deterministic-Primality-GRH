"""Upper bound  C(1) <= C*(1) <= sup_t |ghat(t)| < TARGET  for the explicit dual function psi = s(v) e^{v/2},
s piecewise constant on [0,V] (values in inside_dual_s.json, |s| <= 1), s = 0 beyond V:
     ghat(t) = 1/z - sum_j s_j (e^{z b_j} - e^{z a_j})/z,      z = 1/2 + it.
Verification = branch-and-bound over t with a global Lipschitz constant:
     |ghat'(t)| <= int |v| |g(v)| dv <= 4 + int_0^V v e^{v/2} dv = L,
     tail: |ghat(t)| <= B/|z|, B = 1 + |s_1| + sum_j |s_{j+1}-s_j| e^{v_j/2} + |s_m| e^{V/2}   (Abel summation).
STATUS: float64 evaluation with an explicit rounding allowance EPS = 1e-8 (a priori rounding error of the
m-term sum is < 1e-10); this is NOT interval arithmetic, but every inequality has margin >> rounding error."""
import json, sys, numpy as np
d = json.load(open("inside_dual_s.json"))
V = float(d["V"]); s = np.array([float(x) for x in d["s"]]); m = len(s)
assert np.all(np.abs(s) <= 1)
TARGET = float(sys.argv[1]) if len(sys.argv) > 1 else 1.14654
EPS = 1e-8
edges = np.linspace(0, V, m+1)
jump = np.concatenate([[s[0]], np.diff(s), [-s[-1]]])        # ghat = (1 + sum_j jump_j e^{z v_j}) / z  with v_0 = 0 .. v_m = V
def absg(t):
    z = 0.5 + 1j*t[:, None]
    return np.abs((1 + (jump[None, :]*np.exp(z*edges[None, :])).sum(axis=1))/z[:, 0])
L = 4 + (2*np.exp(V/2)*(V-2) + 4)
B = 1 + np.sum(np.abs(jump)*np.exp(edges/2))
T0 = B/1.0                                                   # for t >= T0: |ghat| <= B/t <= 1.0 < TARGET
print("m = %d cells, V = %g, Lipschitz L = %.2f, tail constant B = %.2f -> scan t in [0, %.1f]" % (m, V, L, B, T0))
a = np.linspace(0, T0, 20001)[:-1]; b = np.linspace(0, T0, 20001)[1:]
sup_seen, nev, depth = 0.0, 0, 0
while len(a):
    mid = (a+b)/2
    val = np.concatenate([absg(mid[i:i+4000]) for i in range(0, len(mid), 4000)])
    nev += len(mid); sup_seen = max(sup_seen, val.max())
    assert sup_seen < TARGET - EPS, "target violated: %.9f" % sup_seen
    bad = val + L*(b-a)/2 + EPS > TARGET
    a2, b2, m2 = a[bad], b[bad], mid[bad]
    a = np.concatenate([a2, m2]); b = np.concatenate([m2, b2]); depth += 1
    assert depth < 60
print("verified: |ghat(t)| < %.6f for all real t   (%d evaluations, depth %d, largest value seen %.8f)" % (TARGET, nev, depth, sup_seen))
print("=> C(1) <= C*(1) < %.6f,  so no test function in (EP1) gives c below  %.6f" % (TARGET, TARGET**-2))
