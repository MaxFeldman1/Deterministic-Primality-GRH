"""Generator for the refined Lean dual certificate  C(1) <= 1.14652
(lean/DetPrimality/Barrier/dual2_Data.lean, dual2_Run*.lean, dual2_RunAll.lean).

Same architecture as dual_gen.py (whose rounding, exact checker mirror `Checker` and greedy planner are
imported and reused; the Lean checker is dual_Cert.lean, unchanged): only the dual function (dual2_sol.json,
from dual2_socp.py), the constant c' = CN/10^7 and the splitting into files differ.
Nothing here is trusted: every number is re-checked in the Lean kernel.
usage: python3 dual2_gen.py dual2_sol.json [CN [lean/DetPrimality/Barrier [cells_per_piece pieces_per_file]]]"""
import sys
import numpy as np
import dual_gen as G

if __name__ == "__main__":
    G.CN = int(sys.argv[2]) if len(sys.argv) > 2 else 11465199    # c' ; final constant c' + 2 eta
    chunk = int(sys.argv[4]) if len(sys.argv) > 4 else 150
    perfile = int(sys.argv[5]) if len(sys.argv) > 5 else 5
    V, D = G.load(sys.argv[1])
    A = G.alphas(V, D)
    assert V[-1] <= 8*G.DV                            # needed by dualCoeffOK
    ys = np.linspace(0, 80, 1600001)                  # float sanity value of sup |N|/sqrt(1/4+y^2)
    Nv = sum(a/G.SA*np.exp(1j*ys*v/G.DV) for a, v in zip(A, V))
    print("float sup = %.8f, c' = %.7f" % (np.max(np.abs(Nv)/np.sqrt(0.25+ys*ys)), G.CN/G.CD), file=sys.stderr)
    ck, R, chunks = G.plan(V, A, chunk)
    if len(sys.argv) > 3:
        import dual2_emit
        dual2_emit.emit(sys.argv[3], V, D, A, ck, R, chunks, dict(CN=G.CN, ETA=G.ETA, NFILES=-(-len(chunks)//perfile)))
