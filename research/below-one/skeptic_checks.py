#!/usr/bin/env python3
"""
skeptic_checks.py -- referee's numerical sanity checks (NOT a proof; floating point, no intervals).

 (1) Re-derive the LLS constant 0.7935 for K(s) = Gamma(s+1/2), h = 2, lambda = 2.452.
 (2) "Naive" route: sum_gamma |K(i gamma)| via zero counting N(T,chi) with |S| <= A log q / log log q.
     Relative error = 2 pi A (TV(|K|) / ||K||_1) / log log q   ->  N0 is doubly exponential.
 (3) "Majorant" route: M >= |K(it)| on R with supp(M^) in [-log y, log y] (angular frequency).
     Then  sum_gamma |K(i gamma)| <= sum_gamma M(gamma)
              = (1/2pi) int M (log(q/pi) + Re psi(1/4 + a/2 + it/2)) dt - (1/pi) Re sum_n Lambda(n) chi(n) n^{-1/2} M^(log n)
     is an EXACT identity (Guinand-Weil), so the error is an absolute constant C(M) -- no S(t) at all.
     We find M by linear programming and report excess eps = int M / int |K| - 1 and the constant C(M).
 (4) Crude N0 for c in {0.95, 0.9, 0.85, 0.8} from
        (1 - 2 e^{-lam}) sqrt(X/lam) <= (log q) I_M + C(M) + E,   X = c log^2 q,
     with E = crude allowance for all other O(1) terms (see skeptic.md, section 3).
"""
import numpy as np
import mpmath as mp
from scipy.optimize import linprog

mp.mp.dps = 30

# ---------------------------------------------------------------- (1)
g = lambda t: mp.sqrt(mp.pi / mp.cosh(mp.pi * t))          # |Gamma(1/2+it)|
L1 = 2 * mp.quad(g, [0, 1, 5, 20, 60])
I_K = L1 / (2 * mp.pi)
cfun = lambda lam: lam * I_K**2 / (1 - 2 * mp.e**(-lam))**2
lam_opt = mp.findroot(lambda l: mp.diff(cfun, l), 2.45)
print("(1) int|Gamma(1/2+it)|dt = %s ; (1/2pi) int = %s" % (mp.nstr(L1, 12), mp.nstr(I_K, 12)))
print("    c(2.452) = %s ; optimal lambda = %s , c_inf = %s" % (
    mp.nstr(cfun(2.452), 10), mp.nstr(lam_opt, 8), mp.nstr(cfun(lam_opt), 10)))
for h in (2, 3, 4, 10, 100):
    ch = lambda lam: lam * ((h - 1) * I_K)**2 / (h * (1 - mp.e**(-lam)) - 1)**2
    lo = mp.findroot(lambda l: mp.diff(ch, l), 2.0)
    print("    h=%3d: best lambda %s, c_inf(h) = %s" % (h, mp.nstr(lo, 6), mp.nstr(ch(lo), 8)))
CINF = float(cfun(lam_opt)); LAM = float(lam_opt); IK = float(I_K)

# ---------------------------------------------------------------- (2)
TV = 2 * g(0)
print("\n(2) TV(|K|) = %s, TV/L1 = %s" % (mp.nstr(TV, 8), mp.nstr(TV / L1, 8)))
for A, name in ((0.25, "A=1/4 (CCM leading const, pretending no lower-order terms)"),
                (1.0, "A=1 (typical size of a genuinely explicit Selberg-type constant)")):
    print("    " + name)
    for c in (0.95, 0.9, 0.85, 0.8):
        budget = mp.sqrt(c / CINF) - 1
        LL = 2 * mp.pi * A * (TV / L1) / budget
        print("      c=%.2f: budget %.4f -> need log log q >= %.1f, i.e. log10(log q) >= %.1f" % (
            c, budget, LL, LL / mp.log(10)))

# ---------------------------------------------------------------- (3)
def bspline3(x):
    x = np.abs(x)
    return np.where(x < 2, ((2 - x)**3 - 4 * np.clip(1 - x, 0, None)**3) / 6.0, 0.0)

def psi_hat(u, tau):
    # psi(t) = sinc(tau t/4)^4, sinc(x)=sin x/x ;  psi^(u) = int psi(t) e^{-itu} dt, supported |u|<=tau
    a = tau / 4.0
    return (1 / (2 * np.pi))**3 * (np.pi / a)**4 * (2 * a)**3 * bspline3(u / (2 * a))

def psi(t, tau):
    x = tau * t / 4.0
    return np.sinc(x / np.pi)**4

def mangoldt_upto(y):
    y = int(y)
    lam = np.zeros(y + 1)
    sieve = np.ones(y + 1, dtype=bool); sieve[:2] = False
    for p in range(2, y + 1):
        if sieve[p]:
            sieve[2 * p::p] = False
            pk = p
            while pk <= y:
                lam[pk] = np.log(p); pk *= p
    return lam

gnp = lambda t: np.sqrt(np.pi / np.cosh(np.pi * np.minimum(np.abs(t), 200)))

def majorant(y, T=45.0, dt=0.01):
    tau = np.log(y)
    hstep = np.pi / tau / 1.5          # oversampled shifts
    K = int(T / hstep)
    shifts = np.arange(0, K + 1) * hstep
    tg = np.arange(0, T + 30, dt)       # constraint grid (even function -> t >= 0)
    cols = []
    for s in shifts:
        col = psi(tg - s, tau) + (psi(tg + s, tau) if s > 0 else 0)
        cols.append(col)
    Amat = np.array(cols).T
    mass = psi_hat(0.0, tau) * np.where(shifts > 0, 2.0, 1.0)
    res = linprog(mass, A_ub=-Amat, b_ub=-gnp(tg) * (1 + 1e-9), bounds=[(None, None)] * len(shifts),
                  method="highs")
    if not res.success:
        return None
    a = res.x
    intM = float(mass @ a)
    eps = intM / float(L1) - 1
    # prime-sum constant  P = (1/pi) sum_{n<y} Lambda(n) n^{-1/2} |M^(log n)|
    lam = mangoldt_upto(y)
    n = np.nonzero(lam)[0]
    u = np.log(n)
    Mhat = psi_hat(u, tau) * (a[0] + 2 * (np.cos(np.outer(u, shifts[1:])) @ a[1:]))
    P = float(np.sum(lam[n] / np.sqrt(n) * np.abs(Mhat)) / np.pi)
    # Gamma-term constant  G_a = (1/2pi) int M(t) (Re psi(1/4 + a/2 + it/2) - log pi) dt  (a = 0, 1)
    tt = np.arange(-T - 30, T + 30, 0.01)
    Mv = sum(a[i] * (psi(tt - s, tau) + (psi(tt + s, tau) if s > 0 else 0)) for i, s in enumerate(shifts))
    G = []
    for par in (0, 1):
        dg = np.array([float(mp.re(mp.digamma(mp.mpf(1) / 4 + mp.mpf(par) / 2 + 0.5j * float(t)))) for t in tt[::10]])
        G.append(float(np.sum(Mv[::10] * (dg - np.log(np.pi))) * 0.1 / (2 * np.pi)))
    minM = float(Mv.min())
    return dict(y=y, eps=eps, intM=intM, P=P, G0=G[0], G1=G[1], minM=minM, nvar=len(shifts))

print("\n(3) band-limited majorants M >= |Gamma(1/2+it)|, supp M^ in [-log y, log y] (LP upper bounds, grid-checked only)")
print("     y      eps=intM/int|K|-1    P(primes)   G(a=0)    G(a=1)    C=P+max(G,0)   min M")
rows = []
for y in (2, 4, 10, 30, 100, 300, 1000, 3000, 10000):
    r = majorant(y)
    if r is None:
        print("   %6d  LP failed" % y); continue
    r["C"] = r["P"] + max(r["G0"], r["G1"], 0.0)
    rows.append(r)
    print("   %6d   %12.6f      %9.4f  %8.3f  %8.3f   %9.4f   %9.2e" % (
        y, r["eps"], r["P"], r["G0"], r["G1"], r["C"], r["minM"]))

# ---------------------------------------------------------------- (4)
print("\n(4) crude N0 (as log q) via majorant route; E = allowance for remaining O(1) terms")
def logq_needed(c, IM, C, E):
    # need: (1-2e^{-lam}) sqrt(c/lam) L > IM L + C + E(L)  for all larger L  (then X=c log^2 q contradicts)
    best = None
    for lam in np.linspace(1.6, 3.4, 37):
        lhs = (1 - 2 * np.exp(-lam)) * np.sqrt(c / lam)
        if lhs <= IM:
            continue
        L = 10.0
        for _ in range(200):
            X = c * L * L
            Eq = E + 2 * np.exp(-lam) * np.sqrt(lam) * np.log(X)**2 / (8 * np.pi)   # sharp cut-off at X, Schoenfeld-type
            Lnew = (C + Eq) / (lhs - IM)
            if abs(Lnew - L) < 1e-9: break
            L = Lnew
        if best is None or L < best[0]:
            best = (L, lam)
    return best
for E in (3.0, 10.0):
    print("   E = %.0f" % E)
    for c in (0.95, 0.9, 0.85, 0.8):
        cand = []
        for r in rows:
            b = logq_needed(c, r["intM"] / (2 * np.pi), r["C"], E)
            if b: cand.append((b[0], b[1], r["y"]))
        if cand:
            L, lam, y = min(cand)
            print("     c=%.2f: log q >= %9.1f  (N0 ~ 10^%d), using y=%d, lambda=%.2f" % (c, L, int(L / np.log(10)) + 1, y, lam))
        else:
            print("     c=%.2f: no majorant in table is good enough" % c)
