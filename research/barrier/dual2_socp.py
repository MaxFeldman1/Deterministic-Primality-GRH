"""Float exploration that produced dual2_sol.json (input of dual2_gen.py).  Needs cvxpy + clarabel + scipy.
Refinement of dual_socp.py.  Dual problem (EP2), A = 1:  minimise
     sup_t | 1/(1/2+it) - int_0^V s(v) e^{(1/2+it)v} dv |
over step functions s with values in [-1,1] on a SPARSE grid: nodes 0 < p1 < p2 < p3 < p4 (the bang-bang
switches) followed by the tail grid 2.1 (0.1) 3.0 (0.25) 8.0.  Differences with dual_socp.py:
  * the tail reaches V = 8 instead of 6 (this is what gains 3e-6; a finer mesh gains < 2e-7 more);
  * the weighted variation B = sum_k |jump_k| e^{v_k/2} is constrained (B <= 45), so that the trivial bound
    |N(y)| <= B takes over beyond y = B/c < Tmax and the sampled t-range [0, Tmax] is enough;
  * the switches are optimised by Nelder-Mead in two rounds (470 SOCP solves) from those of dual_sol.json;
  * the values of s are rounded to 7 decimals four at a time from the right, re-optimising the remaining
    ones after each step (plain rounding of all values costs ~1e-7).
Result: 35 nodes, sup = 1.1465127 (float).  Nothing here is trusted by the Lean proof.
usage: python3 dual2_socp.py out.json [--nm]     (--nm: redo the Nelder-Mead search, ~10 minutes)"""
import sys, json, warnings, numpy as np, cvxpy as cp
warnings.filterwarnings("ignore")

TAIL = np.array(list(np.arange(2.1, 3.0 - 1e-9, 0.1)) + list(np.arange(3.0, 8.0 + 1e-9, 0.25)))
P0 = np.array([0.9636, 1.39247, 1.72377, 1.94466])                 # dual_sol.json
P1 = np.array([0.96369143, 1.39308944, 1.72434579, 1.94510554])    # result of nm(P0)

def mat(edges, ts):
    z = 0.5 + 1j*ts[:, None]
    return (np.exp(z*edges[None, 1:]) - np.exp(z*edges[None, :-1]))/z, 1/z[:, 0]

def sup(edges, sv, T=200.0, n=400001):
    tf = np.linspace(0, T, n); mx = 0
    for i in range(0, n, 20000):
        Mf, gf = mat(edges, tf[i:i+20000]); mx = max(mx, np.abs(gf - Mf @ sv).max())
    return mx

def solve(edges, fixed={}, Tmax=60.0, nt=1800, Bmax=45.0):
    """SOCP in the values of s; `fixed`: index -> prescribed value"""
    edges = np.array(edges)
    ts = np.concatenate([np.linspace(0, 12, nt), np.linspace(12, Tmax, nt)[1:]])
    M, g0 = mat(edges, ts)
    s = cp.Variable(len(edges)-1); r = cp.Variable(); w = np.exp(edges/2)
    cons = [cp.abs(g0 - M @ s) <= r, s >= -1, s <= 1,
            w[0]*(1+s[0]) + cp.sum(cp.multiply(w[1:-1], cp.abs(cp.diff(s)))) + w[-1]*cp.abs(s[-1]) <= Bmax]
    cons += [s[i] == v for i, v in fixed.items()]
    cp.Problem(cp.Minimize(r), cons).solve(solver=cp.CLARABEL)
    return np.clip(s.value, -1, 1)

def nm(p):
    from scipy.optimize import minimize
    def val(q):
        e = np.concatenate([[0], q, TAIL])
        return 9 if np.any(np.diff(e) <= 1e-4) else sup(e, solve(e))
    for step, xatol, maxfev in ((1e-3, 1e-5, 250), (2e-4, 3e-6, 220)):
        r = minimize(val, p, method='Nelder-Mead', options=dict(xatol=xatol, fatol=1e-9, maxfev=maxfev,
                     initial_simplex=[p] + [p + step*np.eye(4)[i] for i in range(4)]))
        p = r.x; print("Nelder-Mead:", repr(p), "%.8f" % r.fun)
    return p

def rounded(e, group=4):
    n = len(e)-1; fixed = {}; i = n
    sv = solve(e)
    print("before rounding s: sup %.8f" % sup(e, sv))
    while i > 0:
        lo = max(0, i-group)
        for k in range(lo, i): fixed[k] = round(float(sv[k]), 7)
        i = lo
        if i > 0: sv = solve(e, fixed)
    return np.array([fixed[k] for k in range(n)])

if __name__ == "__main__":
    p = nm(P0) if "--nm" in sys.argv else P1
    e = np.round(np.concatenate([[0], p, TAIL]), 5)
    sv = rounded(e)
    d = np.concatenate([[1+sv[0]], np.diff(sv), [-sv[-1]]])
    json.dump(dict(e=[float(x) for x in e], s=[float(x) for x in sv]), open(sys.argv[1], "w"))
    print("%d nodes, sup %.8f, B = %.3f" % (len(e), sup(e, sv), np.sum(np.abs(d)*np.exp(e/2))))
