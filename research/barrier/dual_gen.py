"""Generator for the Lean dual certificate  C(1) <= 1.14654  (lean/DetPrimality/Barrier/dual_Data.lean, dual_Run*.lean).

Dual function (CMQR (EP2), A = 1), v = 2 pi t:   psi(t) = s(v) e^{pi t},  s a step function with values in [-1,1]:
     g(t) = e^{pi t} * sum_k d_k 1_{v < v_k},   d_0 = 1 + s_0, d_k = s_k - s_{k-1}, d_K = -s_{K-1}
     2 pi |ghat(x)| = |N(-x)| / sqrt(1/4 + x^2),     N(y) = sum_k d_k e^{v_k/2} e^{i y v_k}.
This script (i) rounds a float solution (dual_sol.json: nodes v_k, values s_k) to rationals, (ii) plans the
cells for the Lean checker `dualRun` (second order Taylor bound on each cell, fixed point ball arithmetic)
by simulating that checker EXACTLY (Python ints), (iii) writes the Lean data files.
Nothing here is trusted: every number is re-checked in the Lean kernel.
usage: python3 dual_gen.py dual_sol.json [lean/DetPrimality/Barrier]"""
import sys, json
import mpmath as mp
mp.mp.dps = 60

DV = 10**5; DD = 10**7; SA = 10**15; S = 10**22       # dDv, dDd, dSa, dS
Q = 65536; SD = 10**13; CD = 10**7                    # dQ, dSd, dCd
CN = 11465399                                         # c' = CN/CD ; final constant c' + 2 eta <= 1.14654
ETA = (1, 10**8)
LEVELS = list(range(3, 17))                           # radius r = 2^-j = RN/Q, RN = 2^(16-j)

def load(path):
    d = json.load(open(path))
    V = [int(round(x*DV)) for x in d["e"]]
    s = [int(round(max(-1, min(1, x))*DD)) for x in d["s"]]
    assert V[0] == 0 and all(a < b for a, b in zip(V, V[1:])) and len(s) == len(V)-1
    D = [DD + s[0]] + [s[k]-s[k-1] for k in range(1, len(s))] + [-s[-1]]
    keep = [k for k in range(len(V)) if D[k] != 0]
    return [V[k] for k in keep], [D[k] for k in keep]

def alphas(V, D):
    return [int(mp.nint(mp.mpf(SA)*d*mp.exp(mp.mpf(v)/DV/2)/DD)) for v, d in zip(V, D)]

def rots(j, V):
    out = []
    for v in V:
        z = mp.mpf(v)/DV/2**j
        out.append((int(mp.nint(S*mp.cos(z))), int(mp.nint(S*mp.sin(z)))))
    return out

def sigz(Y):
    """mirror of dualSigZ"""
    n0 = (Q*Q + 4*Y*Y)*(SD*SD)//(4*Q*Q) + 1
    x = SD//2 + Y*SD//Q + 1
    for _ in range(5): x = (x + n0//x)//2
    return x + 1

class Checker:
    """mirror of the Lean functions dualAdv / dualChkZ / dualCell"""
    def __init__(self, V, A):
        self.V, self.A = V, A
        self.AV = [a*v for a, v in zip(A, V)]
        self.Bn = sum(abs(a) for a in A)
        self.B1n = sum(abs(a)*v for a, v in zip(A, V))
        self.M2n = sum(abs(a)*v*v for a, v in zip(A, V))
    def adv(self, st, rt):
        return [((a*c - b*d)//S, (a*d + b*c)//S) for (a, b), (c, d) in zip(st, rt)]
    def chk(self, Y, Rn, err, st):
        p0r = sum(a*e[0] for a, e in zip(self.A, st)); p0i = sum(a*e[1] for a, e in zip(self.A, st))
        p1r = sum(a*e[0] for a, e in zip(self.AV, st)); p1i = sum(a*e[1] for a, e in zip(self.AV, st))
        Sg = sigz(Y)
        if not (Sg > 0 and (Q*Q + 4*Y*Y)*(SD*SD) <= 4*Q*Q*(Sg*Sg)): return False
        epsN = 2*Q*DV*err*(Q*DV*self.Bn + Rn*self.B1n) + Rn*Rn*self.M2n*S
        for sg in (1, -1):
            RN = CN*(Q*Q + 4*Y*(Y + sg*Rn))*SD*SA*(DV*DV)*S - 2*CD*Sg*epsN
            if not (0 <= RN and ((Q*DV*p0r - sg*Rn*p1i)**2 + (Q*DV*p0i + sg*Rn*p1r)**2)*(4*Q*CD*Sg*DV)**2 <= RN**2):
                return False
        return True
    def cell(self, st, err, Y, Rn, rt):
        st1 = self.adv(st, rt)
        if not (Rn > 0 and err + 16 <= S and self.chk(Y + Rn, Rn, err + 8, st1)): return None
        return self.adv(st1, rt), err + 16, Y + Rn + Rn

def plan(V, A, chunk):
    """greedy plan; returns the list of chunks [(prog, (st, err, Y))] with at most `chunk` cells each"""
    ck = Checker(V, A)
    R = {j: rots(j, V) for j in LEVELS}
    st = [(S, 0)]*len(V); err = 0; Y = 0; j = LEVELS[-1]; ncell = 0
    chunks = []; prog = []; nin = 0; cnt = {}
    while not ck.Bn*CD*Q <= CN*Y*SA:                 # dualTailOK
        j = max(LEVELS[0], j-1)
        while True:
            res = ck.cell(st, err, Y, 2**(16-j), R[j])
            if res is not None: break
            j += 1
            assert j <= LEVELS[-1], "no level passes at y = %s" % (Y/Q)
        st, err, Y = res; ncell += 1; nin += 1; cnt[j] = cnt.get(j, 0) + 1
        if prog and prog[-1][0] == j: prog[-1][1] += 1
        else: prog.append([j, 1])
        if nin == chunk:
            chunks.append((prog, (st, err, Y))); prog = []; nin = 0
    if prog: chunks.append((prog, (st, err, Y)))
    print("K = %d nodes, B = %.4f, end point %.3f, cells = %d, chunks = %d, final err = %d" %
          (len(V), ck.Bn/SA, Y/Q, ncell, len(chunks), err), file=sys.stderr)
    print("cells per level:", sorted(cnt.items()), file=sys.stderr)
    return ck, R, chunks

if __name__ == "__main__":
    V, D = load(sys.argv[1])
    A = alphas(V, D)
    import numpy as np                                # float sanity value of sup |N|/sqrt(1/4+y^2)
    ys = np.linspace(0, 60, 600001)
    Nv = sum(a/SA*np.exp(1j*ys*v/DV) for a, v in zip(A, V))
    print("float sup = %.8f" % np.max(np.abs(Nv)/np.sqrt(0.25+ys*ys)), file=sys.stderr)
    ck, R, chunks = plan(V, A, 150)
    if len(sys.argv) > 2:
        import dual_emit
        dual_emit.emit(sys.argv[2], V, D, A, ck, R, chunks, dict(CN=CN, ETA=ETA, NFILES=8))
