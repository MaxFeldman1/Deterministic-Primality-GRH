#!/usr/bin/env python3
"""
skeptic_rational.py -- referee's feasibility probe (floating point; grid-checked; NOT a proof).

Question: can sum_gamma |Gamma(1/2 + i gamma)| be bounded explicitly using ONLY partial-fraction identities
at real points sigma = 1/2 + a > 1 (the Lean-friendly inputs of BRIEF.md), i.e. with a majorant

      M(t) = sum_{j,k} c_{j,k} Re (a_j + i t)^{-k}  >=  |Gamma(1/2+it)| = sqrt(pi / cosh(pi t)),   a_j > 1/2 ?

For primitive chi mod q (GRH), with xi'/xi(s) = (1/2) log(q/pi) + (1/2) psi((s+a)/2) + L'/L(s):
   sum_gamma Re (a + i gamma)^{-k} = Re [(-1)^{k-1}/(k-1)!] (xi'/xi)^{(k-1)}(1/2 + a)
so  sum_gamma M(gamma) <= (1/2) (sum_j c_{j,1}) log q  +  sum |c_{j,k}| D(a_j,k) + (Gamma-factor terms, O(1)),
    D(a,k) = sum_n Lambda(n) (log n)^{k-1} n^{-1/2-a} / (k-1)!   (bounds the L'/L part, any chi).
We minimise  I_M * L + P  (I_M = (1/2) sum c_{j,1},  P = sum |c| D,  L = log q) by LP and report the
resulting effective constant c(L) for h = 2 (kernel Gamma(s+1/2), free lambda), with allowance E for other O(1) terms.
The Gamma-factor terms are ignored here (they are O(1), of either sign, |.| <~ 2).
"""
import numpy as np
import mpmath as mp
from scipy.optimize import linprog

mp.mp.dps = 25
g = lambda t: np.sqrt(np.pi / np.cosh(np.pi * np.minimum(np.abs(t), 200)))
IK = float(2 * mp.quad(lambda t: mp.sqrt(mp.pi / mp.cosh(mp.pi * t)), [0, 1, 5, 20, 60]) / (2 * mp.pi))

def D(a, k):
    s = mp.mpf(1) / 2 + a
    f = lambda z: -mp.zeta(z, derivative=1) / mp.zeta(z)
    return float(abs(mp.diff(f, s, k - 1)) / mp.factorial(k - 1))

def probe(amin, KMAX, Ls, E=3.0):
    a_list = [amin * r for r in (1.0, 1.25, 1.6, 2.0, 2.6, 3.4, 4.5, 6.0, 8.0, 11.0)]
    basis = [(a, k) for a in a_list for k in range(1, KMAX + 1)]
    tg = np.concatenate([np.arange(0, 12, 0.004), np.geomspace(12, 1e5, 4000)])
    cols = np.array([np.real((a + 1j * tg) ** (-k)) for (a, k) in basis]).T
    Dv = np.array([D(a, k) for (a, k) in basis])
    dens = np.array([0.5 if k == 1 else 0.0 for (a, k) in basis])       # coefficient of log q
    out = []
    for L in Ls:
        # variables c+ , c-  (c = c+ - c-); objective dens.c * L + Dv.(c+ + c-)
        obj = np.concatenate([dens * L + Dv, -dens * L + Dv])
        A = np.hstack([-cols, cols])
        res = linprog(obj, A_ub=A, b_ub=-g(tg) * (1 + 1e-9), bounds=[(0, None)] * (2 * len(basis)), method="highs")
        if not res.success:
            out.append((L, None)); continue
        c = res.x[:len(basis)] - res.x[len(basis):]
        IM = float(dens @ c); P = float(Dv @ np.abs(c))
        best = min((lam * ((IM * L + P + E) / L) ** 2 / (1 - 2 * np.exp(-lam)) ** 2, lam)
                   for lam in np.linspace(1.6, 3.6, 81))
        out.append((L, IM / IK - 1, P, best[0], best[1]))
    return out

print("(1/2pi) int |Gamma(1/2+it)| dt = %.6f ; c_inf = 0.79342 (h=2)" % IK)
Ls = (100, 300, 1000, 3000, 10000, 30000, 100000, 1000000)
for amin, KMAX in ((0.75, 4), (0.6, 4), (0.6, 8), (0.55, 8), (0.51, 10)):
    print("\npoles at a >= %.2f (sigma = 1/2 + a >= %.2f), orders k <= %d, E = 3" % (amin, 0.5 + amin, KMAX))
    print("     log q      eps=I_M/I_K-1     P(prime const)   effective c(q)   lambda")
    for row in probe(amin, KMAX, Ls):
        if row[1] is None:
            print("  %9d   LP failed" % row[0]); continue
        print("  %9d     %10.5f      %10.3f        %8.5f      %.2f" % row)
