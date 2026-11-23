"""Outer optimisation over (beta, c) of the SOCP in inside_primal_socp.py (floating point exploration)."""
import sys, numpy as np
from multiprocessing import Pool
from inside_primal_socp import solve, evaluate
D = int(sys.argv[1]) if len(sys.argv) > 1 else 30
def f(bc):
    try:
        val, qv = solve(bc[0], bc[1], D, M=3000, panels=50)
        return val
    except Exception as e:
        return float('nan')
if __name__ == "__main__":
    betas = [float(x) for x in sys.argv[2].split(',')]
    cs = [float(x) for x in sys.argv[3].split(',')]
    pts = [(b, c) for b in betas for c in cs]
    with Pool(14) as P: vals = P.map(f, pts)
    A = np.array(vals).reshape(len(betas), len(cs))
    print("D=%d rows beta, cols c =" % D, cs)
    for b, row in zip(betas, A): print("beta=%-6g" % b, " ".join("%.6f" % x for x in row))
    i = np.nanargmax(A); print("best", pts[i], "J=%.7f c_inf=%.6f" % (vals[i], vals[i]**-2))
