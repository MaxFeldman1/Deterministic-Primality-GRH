"""Referee B, script 3: zero-free end-to-end tests on real data (floating point, evidence only).
 T1  Lemma 6 and Lemma 7 lower bounds against directly computed prime sums, X from 45 to 1e6.
 T2  Lemma 5: true T(X) against c0(3 log X+7)/sqrt X.
 T3  Lemma 3 + Lemma 4 together, with the hypothesis gain: for real primitive characters (Legendre symbols mod
     primes q) with large least non-residue X = n_chi, check for many y that
        Phi_chi(y) <= (3/2) y (log q - kappa_a + 4 T(X)) + (log q+G0) log^3 y + 3 G1 log^2 y + 3 G2 log y + G3.
     If the sign of the 'hypothesis gain' in (4.2) were wrong this would fail by a wide margin.
 T4  exact S4 from (4.1) (Hurwitz zeta) for a few q, compared with the bound (4.2) and with the 'no hypothesis' bound.
"""
import numpy as np, math
from mpmath import mp, mpf, zeta, digamma, polygamma, log as mlog, pi as mpi
import refereeB_table as RT
NMAX = 3_100_000
def mangoldt(N):
    lam = np.zeros(N + 1); sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if sieve[p]: sieve[p * p::p] = False
    primes = np.nonzero(sieve)[0]
    for p in primes:
        pk = int(p); lp = math.log(p)
        while pk <= N:
            lam[pk] = lp; pk *= int(p)
    return lam, primes
LAM, PRIMES = mangoldt(NMAX)
IDX = np.nonzero(LAM)[0]; LV = LAM[IDX]; SQ = np.sqrt(IDX); LG = np.log(IDX)
def A(j, y):                      # sum_{n<y} Lambda(n) sqrt(n) log^j(y/n)
    k = np.searchsorted(IDX, y, side="left")
    return float(np.sum(LV[:k] * SQ[:k] * (math.log(y) - LG[:k]) ** j))
f = float
Z2, Z3, Z4 = f(RT.Z2u), f(RT.Z3u), f(RT.Z4u); gam = [f(v) for v in RT.gam]; G = [f(v) for v in RT.G]
D, e1, e2 = f(RT.D), f(RT.e1), f(RT.e2); l0 = math.log(3); F0, F1 = f(RT.F[0]), f(RT.F[1])

print("T1: Lemma 6 / Lemma 7 against direct sums")
worst6 = worst7 = 1e99; arg6 = arg7 = None
Xs = [float(p) for p in PRIMES[(PRIMES >= 45) & (PRIMES < 1_000_000)][::37]] + [45.0, 46.5, 100.0, 1e3, 1e4, 1e5, 1e6]
for X in Xs:
    x = 3 * X
    lhs6 = A(0, X); rhs6 = 2 / 3 * X ** 1.5 - 2 * math.sqrt(Z2) * X ** 1.25 - gam[0] - 1
    T_lt = l0 ** 3 * A(0, X) + 3 * l0 ** 2 * A(1, X) + 3 * l0 * A(2, X) + A(3, X)
    lhs7 = 2 * T_lt - A(3, x); rhs7 = D * x ** 1.5 - e1 * x ** 1.25 - e2 * x - f(RT.rhostar(mpf(x)))
    s6 = (lhs6 - rhs6) / X ** 1.25; s7 = (lhs7 - rhs7) / x ** 1.25
    if s6 < worst6: worst6, arg6 = s6, X
    if s7 < worst7: worst7, arg7 = s7, X
print("   %d values of X in [45, 1e6] (X = primes, so the prime X itself is excluded from n<X: worst case)" % len(Xs))
print("   Lemma 6: min (A0(X) - bound)/X^1.25 = %.4f at X = %g   (must be >= 0)" % (worst6, arg6))
print("   Lemma 7: min (2T_< - A3(x) - bound)/x^1.25 = %.4f at X = %g   (must be >= 0; e1 = %.4f)" % (worst7, arg7, e1))
for X in (45.0, 310.0, 509.0, 7500.0, 1e6):
    x = 3 * X
    T_lt = l0 ** 3 * A(0, X) + 3 * l0 ** 2 * A(1, X) + 3 * l0 * A(2, X) + A(3, X)
    print("   X=%-8g (2T_< - A3(x))/x^1.5 = %.5f   D = %.5f   lemma-7 bound/x^1.5 = %.5f"
          % (X, (2 * T_lt - A(3, x)) / x ** 1.5, D, (D * x ** 1.5 - e1 * x ** 1.25 - e2 * x - f(RT.rhostar(mpf(x)))) / x ** 1.5))

print("T2: Lemma 5")
def Ttrue(X):
    k = np.searchsorted(IDX, X, side="left")
    part = float(np.sum(LV[:k] * (1 + LG[:k]) / IDX[:k] ** 1.5))
    return F0 + F1 - part
for X in (2, 10, 45, 100, 310, 509, 1e4, 1e5):
    print("   X=%-7g T(X) = %.5f   Lemma 5 bound (c0=1.04) = %.5f   ratio %.3f"
          % (X, Ttrue(X), 1.04 * (3 * math.log(X) + 7) / math.sqrt(X), Ttrue(X) / (1.04 * (3 * math.log(X) + 7) / math.sqrt(X))))

print("T3: Phi_chi(y) against (3.2)+(4.2) for Legendre symbols with large least non-residue")
def kappa_a(a):
    return f(RT.kappa_of(a, RT.F[0] + RT.F[1]))
from sympy import jacobi_symbol, isprime
cands = []
# primes with large least prime non-residue: scan q < 3e6, plus known pseudosquares
small = [int(p) for p in PRIMES[:40]]
for q in PRIMES[(PRIMES > 1000)]:
    q = int(q)
    n = next(p for p in small if pow(p, (q - 1) // 2, q) != 1)
    if n >= 31: cands.append((q, n))
for q in (9257329, 22000801, 48473881, 175244281, 427733329, 898716289, 2805544681, 10310263441, 23616331489,
          85157610409, 196265095009):
    if isprime(q):
        n = next(p for p in small if pow(p, (q - 1) // 2, q) != 1); cands.append((q, n))
ys = np.unique(np.concatenate([np.arange(3.5, 400, 1.0), np.geomspace(400, 3e6, 600)]))
kY = np.searchsorted(IDX, ys, side="left")
worst = -1e99
for q, X in sorted(set(cands), key=lambda t: -t[1])[:14]:
    a = 0 if q % 4 == 1 else 1
    chi = np.array([int(jacobi_symbol(int(n) % q, q)) for n in IDX], dtype=float)
    S4bd = 0.25 * (math.log(q) - kappa_a(a) + 4 * Ttrue(X))
    S4nohyp = 0.25 * (math.log(q) - kappa_a(a) + 4 * (F0 + F1))
    best = (-1e99, None); bestratio = -1e99
    for y, k in zip(ys, kY):
        ly = math.log(y)
        phi = float(np.sum(LV[:k] * chi[:k] * SQ[:k] * (ly - LG[:k]) ** 3))
        low = (math.log(q) + G[0]) * ly ** 3 + 3 * G[1] * ly ** 2 + 3 * G[2] * ly + G[3]
        impl = (phi - low) / (6 * y)          # lower bound for the true S4 implied by Lemma 3
        if impl > best[0]: best = (impl, y)
        bestratio = max(bestratio, phi / (6 * y * S4bd + low))
    worst = max(worst, best[0] / S4bd)
    print("   q=%-13d parity %d  n_chi=%-3d  S4 <= %.4f by (4.2) [no-hypothesis bound %.4f];  "
          "Lemma 3 forces S4 >= %.4f (y=%.0f);  max Phi/RHS = %.3f"
          % (q, a, X, S4bd, S4nohyp, best[0], best[1], bestratio))
print("   worst (implied lower bound)/(4.2 upper bound) = %.3f  (must be <= 1)" % worst)

print("T4: exact S4 via (4.1) and Hurwitz zeta, small conductors with largest n_chi")
mp.dps = 18
def S4_exact(q, a):
    s = mpf(3) / 2
    L = [sum(int(jacobi_symbol(r, q)) * sum(mp.binomial(d, i) * (-mlog(q)) ** (d - i) * zeta(s, mpf(r) / q, i)
             for i in range(d + 1)) for r in range(1, q)) for d in range(3)]
    series = -(L[1] / L[0]) + (L[2] / L[0] - (L[1] / L[0]) ** 2)
    return mlog(mpf(q) / mpi) / 4 + digamma((s + a) / 2) / 4 - polygamma(1, (s + a) / 2) / 8 - series / 2
rows = []
for q in PRIMES[(PRIMES > 2) & (PRIMES < 2500)]:
    q = int(q); n = next(p for p in small if pow(p, (q - 1) // 2, q) != 1); rows.append((n, q))
for n, q in sorted(rows, reverse=True)[:5] + [(2, 3), (2, 5)]:
    a = 0 if q % 4 == 1 else 1
    ex = float(S4_exact(q, a))
    print("   q=%-5d n_chi=%-3d parity %d: S4 exact = %.5f ; (4.2) with true T(n_chi): %.5f ; "
          "with Lemma 5 bound: %.5f ; trivial |L'/L|<=F bound: %.5f ; (1/4)log q = %.4f"
          % (q, n, a, ex, 0.25 * (math.log(q) - kappa_a(a) + 4 * Ttrue(n)),
             0.25 * (math.log(q) - kappa_a(a) + 4 * 1.04 * (3 * math.log(n) + 7) / math.sqrt(n)),
             0.25 * (math.log(q) - kappa_a(a) + 4 * (F0 + F1)), 0.25 * math.log(q)))
