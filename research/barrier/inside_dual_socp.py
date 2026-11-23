"""Discretised dual problem (EP2, A = 1):  minimise  sup_t | 1/(1/2+it) - int_0^V s(v) e^{(1/2+it)v} dv |
over s: [0,V] -> [-1,1] piecewise constant on m cells (s = 0 beyond V).  Every feasible s gives a valid
psi = s e^{v/2} in B_1, so the value (re-evaluated on a fine t-grid) is an upper bound for C(1).
Floating point exploration (Clarabel)."""
import sys, numpy as np, cvxpy as cp
V = float(sys.argv[1]) if len(sys.argv) > 1 else 3.0
m = int(sys.argv[2]) if len(sys.argv) > 2 else 600
Tmax = float(sys.argv[3]) if len(sys.argv) > 3 else 60.0
nt = int(sys.argv[4]) if len(sys.argv) > 4 else 1500
edges = np.linspace(0, V, m+1)
def mat(ts):
    z = 0.5 + 1j*ts[:, None]
    return (np.exp(z*edges[None, 1:]) - np.exp(z*edges[None, :-1]))/z, 1/z[:, 0]
ts = np.concatenate([np.linspace(0, 12, nt), np.linspace(12, Tmax, nt//3)[1:]])
M, g0 = mat(ts)
s = cp.Variable(m); r = cp.Variable()
res = g0 - M @ s
cons = [cp.abs(res) <= r, s >= -1, s <= 1]
prob = cp.Problem(cp.Minimize(r), cons)
prob.solve(solver=cp.CLARABEL)
sv = s.value
tf = np.linspace(0, 4*Tmax, 400001)
vals = np.zeros(len(tf))
for i in range(0, len(tf), 20000):
    Mf, gf = mat(tf[i:i+20000]); vals[i:i+20000] = np.abs(gf - Mf @ sv)
print("V=%g m=%d: SOCP value %.7f ; fine-grid sup %.7f at t=%.3f ; c>= %.6f" % (V, m, prob.value, vals.max(), tf[vals.argmax()], vals.max()**-2))
# structure of s
sw = [(edges[i+1], round(sv[i],3), round(sv[i+1],3)) for i in range(m-1) if abs(sv[i]-sv[i+1]) > 0.05]
print(" transitions (v, s_before, s_after):", sw[:60])
np.save("/private/tmp/claude-501/-Users-maxfeldman-Desktop/adeaa94f-ea9f-4c13-80e6-10ff2e96c919/scratchpad/dual_s_%g_%d.npy" % (V, m), sv)
