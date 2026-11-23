"""Float exploration that produced dual_sol.json (input of dual_gen.py).  Needs cvxpy + clarabel.
Dual problem (EP2), A = 1:  minimise  sup_t | 1/(1/2+it) - int_0^V s(v) e^{(1/2+it)v} dv |  over step
functions s with values in [-1,1] on a SPARSE grid: nodes 0 < p1 < p2 < p3 < p4 (the bang-bang switches,
optimised by Nelder-Mead) followed by a fixed coarse tail grid on [2.1, 6]; for fixed nodes the problem is an
SOCP in the values of s.  The nodes are then rounded to 5 decimals, s is re-optimised and rounded to 7 decimals.
Result: 27 nodes, sup = 1.1465166 (float).  Nothing here is trusted by the Lean proof.
usage: python3 dual_socp.py out.json"""
import sys, json, warnings, numpy as np, cvxpy as cp
from scipy.optimize import minimize
warnings.filterwarnings("ignore")

def solve(edges, Tmax=80.0, nt=1800):
    edges = np.array(edges)
    def mat(ts):
        z = 0.5 + 1j*ts[:, None]
        return (np.exp(z*edges[None, 1:]) - np.exp(z*edges[None, :-1]))/z, 1/z[:, 0]
    ts = np.concatenate([np.linspace(0, 12, nt), np.linspace(12, Tmax, nt)[1:]])
    M, g0 = mat(ts)
    s = cp.Variable(len(edges)-1); r = cp.Variable()
    cp.Problem(cp.Minimize(r), [cp.abs(g0 - M @ s) <= r, s >= -1, s <= 1]).solve(solver=cp.CLARABEL)
    sv = np.clip(s.value, -1, 1)
    tf = np.linspace(0, 3*Tmax, 300001)
    vals = np.concatenate([np.abs(mat(tf[i:i+20000])[1] - mat(tf[i:i+20000])[0] @ sv) for i in range(0, len(tf), 20000)])
    return sv, vals.max(), tf[vals.argmax()]

if __name__ == "__main__":
    tail = np.array(list(np.arange(2.1, 3.0, 0.1)) + list(np.arange(3.0, 6.01, 0.25)))
    def val(p):
        e = np.concatenate([[0], p, tail])
        return 9 if np.any(np.diff(e) <= 1e-4) else solve(e)[1]
    p = np.array([0.9634, 1.391, 1.724, 1.946])
    r = minimize(val, p, method='Nelder-Mead', options=dict(xatol=2e-5, fatol=2e-8, maxfev=120,
                 initial_simplex=[p] + [p + 0.002*np.eye(4)[i] for i in range(4)]))
    e = np.round(np.concatenate([[0], r.x, tail]), 5)
    sv, mx, at = solve(e, nt=4000)
    sv = np.round(sv, 7)
    json.dump(dict(e=[float(x) for x in e], s=[float(x) for x in sv]), open(sys.argv[1], "w"))
    print("%d nodes, sup %.7f at t = %.3f" % (len(e), mx, at))
