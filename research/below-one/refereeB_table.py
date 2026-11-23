"""Referee B, script 2: independent recomputation of all constants of designB and of the (c, N0) table.
Own implementation; every constant is rounded in the unfavourable direction by RELPAD.
Options explored: c0 (Chebyshev constant), a deficit in the lower bound of F0+F1, and the 'no hypothesis
in Lemma 4' fallback."""
from mpmath import mp, mpf, zeta, digamma, polygamma, pi, log, sqrt, diff, quad, inf, exp, floor, nstr
mp.dps = 40
PAD = mpf(10) ** -9
up = lambda v: v + abs(v) * PAD + PAD
dn = lambda v: v - abs(v) * PAD - PAD

s = mpf(3) / 2
zz = lambda z: zeta(z, derivative=1) / zeta(z)
F = [(-1) ** (k + 1) * diff(zz, s, k) for k in range(4)]          # F_k = sum Lambda log^k n n^{-3/2}
# independent check of F0,F1 by zeta derivatives in closed form
z0, z1, z2 = zeta(s), zeta(s, derivative=1), zeta(s, derivative=2)
assert abs(F[0] + z1 / z0) < 1e-30 and abs(F[1] - (z2 / z0 - (z1 / z0) ** 2)) < 1e-25
Z2 = -F[0] + 2 - log(pi) / 2 + digamma(mpf(7) / 4) / 2
Z4 = (Z2 + 4 - F[1] - polygamma(1, mpf(7) / 4) / 4) / 2
Z2u, Z4u = up(Z2), up(Z4); Z3u = up(sqrt(Z2u * Z4u))
gz = [abs(diff(lambda z: -zz(z), mpf(-1) / 2, k)) for k in range(4)]
gam = [up(v) for v in gz]

def kappa_of(a, Fsum):
    return log(pi) - digamma((s + a) / 2) + polygamma(1, (s + a) / 2) / 2 + 2 * Fsum
def G0_of(a):
    return -log(pi) + digamma((mpf(-1) / 2 + a) / 2) / 2 + digamma((s + a) / 2) / 2 + F[0]
def Gk_of(a, k):
    return (abs(polygamma(k, (mpf(-1) / 2 + a) / 2)) + abs(polygamma(k, (s + a) / 2))) / 2 ** (k + 1) + F[k]
G = [up(max(G0_of(0), G0_of(1)))] + [up(max(Gk_of(0, k), Gk_of(1, k))) for k in (1, 2, 3)]

lam = mpf(1) / 3; l0 = log(3)
P = l0 ** 3 + 2 * l0 ** 2 + mpf(8) / 3 * l0 + mpf(16) / 9
D = dn(mpf(4) / 3 * lam ** 1.5 * P - mpf(32) / 27)
# cross-check D by quadrature of the kernel K~(u) = u log^3(1/u):  D = 2 int_0^lam u^{1/2} log^3(1/u) du - K(1/2)
Dq = 2 * quad(lambda u: sqrt(u) * log(1 / u) ** 3, [0, lam]) - mpf(6) / (mpf(3) / 2) ** 4
I = quad(lambda t: 6 / (1 + t * t) ** 2, [-inf, inf]) / (2 * pi)
assert abs(Dq - D) < 1e-6 and abs(I - 1.5) < 1e-20
cinf = lam * I ** 2 / D ** 2
e1 = up(4 * l0 ** 3 * sqrt(Z2u) * lam ** 1.25)
e2 = up(2 * lam * (3 * l0 ** 2 * Z2u + 6 * l0 * Z3u + 6 * Z4u) + 6 * Z4u)

def r(j, y):
    from mpmath import binomial, factorial
    return sum(binomial(j, i) * gam[j - i] * log(y) ** i for i in range(j + 1)) + mpf("0.64") * factorial(j)
def rhostar(x):
    return 2 * l0 ** 3 * (gam[0] + 1) + 6 * l0 ** 2 * r(1, x) + 6 * l0 * r(2, x) + 3 * r(3, x)
def Tbound(X, c0):
    return c0 * (3 * log(X) + 7) / sqrt(X)
def Err(L, c, c0):
    X = c * L * L; x = 3 * X; lx = log(x)
    return 6 * Tbound(X, c0) + L * lx ** 3 / x + (G[0] * lx ** 3 + 3 * G[1] * lx ** 2 + 3 * G[2] * lx + G[3] + rhostar(x)) / x
def margin(L0, c, c0, kappa):
    """(6.2): inf_{L>=L0}(alpha L - beta sqrt L) + 1.5 kappa - e2 - Err(L0); valid only if 3 c L0^2 >= 404"""
    al = D * sqrt(3 * c) - mpf(3) / 2; be = e1 * (3 * c) ** mpf("0.25")
    if al <= 0 or 3 * c * L0 * L0 < 404: return mpf(-999)
    w = max(sqrt(L0), be / (2 * al))
    return al * w * w - be * w + mpf(3) / 2 * kappa - e2 - Err(L0, c, c0)
def threshold(c, c0, kappa, hi=mpf(10) ** 6):
    lo = mpf(1)
    if margin(hi, c, c0, kappa) <= 0: return None
    # margin(L0) is increasing in L0 (Err decreasing, inf increasing); bisect
    for _ in range(80):
        mid = (lo + hi) / 2
        if margin(mid, c, c0, kappa) > 0: hi = mid
        else: lo = mid
    return hi

if __name__ == "__main__":
    print("F_k =", [nstr(v, 12) for v in F])
    print("Z2 = %s  Z4 = %s  sqrt(Z2 Z4) = %s" % (nstr(Z2, 10), nstr(Z4, 10), nstr(sqrt(Z2 * Z4), 10)))
    print("|g_zeta^(k)(-1/2)| =", [nstr(v, 10) for v in gz])
    print("kappa_a (a=0,1) = %s, %s" % (nstr(kappa_of(0, F[0] + F[1]), 10), nstr(kappa_of(1, F[0] + F[1]), 10)))
    print("G0(a=0,1) = %s, %s ; G = %s" % (nstr(G0_of(0), 9), nstr(G0_of(1), 9), [nstr(v, 9) for v in G]))
    print("D = %s (quadrature %s)  I = %s  c_inf = %s  e1 = %s  e2 = %s  2sqrt(Z2) = %s"
          % (nstr(D, 9), nstr(Dq, 9), nstr(I, 6), nstr(cinf, 9), nstr(e1, 8), nstr(e2, 8), nstr(2 * sqrt(Z2u), 8)))
    # optimal lambda for this kernel (reduced functional)
    best = min(((lam_ * mpf(9) / 4 / (mpf(4) / 3 * lam_ ** 1.5 * (log(1 / lam_) ** 3 + 2 * log(1 / lam_) ** 2
               + mpf(8) / 3 * log(1 / lam_) + mpf(16) / 9) - mpf(32) / 27) ** 2, lam_)
                for lam_ in [mpf(i) / 10000 for i in range(2500, 4500)]), key=lambda t: t[0])
    print("optimal lambda = %s, c_inf(opt) = %s" % (nstr(best[1], 5), nstr(best[0], 8)))
    kap = dn(min(kappa_of(0, F[0] + F[1]), kappa_of(1, F[0] + F[1])))
    cs = [mpf(v) for v in ("0.95", "0.90", "0.85", "0.80", "0.79", "0.78", "0.779")]
    variants = [("designB as stated: c0=1.04, exact F0+F1", mpf("1.04"), kap),
                ("c0 = 1.03883 (Rosser-Schoenfeld Thm 12)", mpf("1.03883"), kap),
                ("c0 = log 4 + small = 1.39 (elementary Chebyshev)", mpf("1.39"), kap),
                ("c0 = 2", mpf(2), kap),
                ("c0=1.04, F0+F1 lower bound short by 0.14 (partial sums to 1e4)", mpf("1.04"), kap - mpf("0.28")),
                ("NO hypothesis in Lemma 4 (kappa - 4(F0+F1)), c0 irrelevant->T=0", mpf(0), kap - 4 * (F[0] + F[1]))]
    import math
    for name, c0, kp in variants:
        print("\n-- %s  (kappa = %s) --" % (name, nstr(kp, 8)))
        for c in cs:
            L0 = threshold(c, c0, kp)
            if L0 is None: print("   c = %s: no threshold below L = 1e6" % nstr(c, 4)); continue
            L0c = mp.ceil(L0 * 100) / 100
            k10 = int(mp.ceil(L0c / log(10)))
            print("   c = %-5s  L0 = %-9s  N0 = 10^%d  margin at L0: %s ; at log 10^%d: %s ; x0 = %s"
                  % (nstr(c, 4), nstr(L0c, 7), k10, nstr(margin(L0c, c, c0, kp), 3), k10,
                     nstr(margin(k10 * log(10), c, c0, kp), 4), nstr(3 * c * L0c ** 2, 6)))
    # Corollary 10: largest admissible k as a function of L1
    print("\n-- Corollary 10: a < c_inf (L + b sqrt L - k)^2, largest admissible k at L1; equivalent c at L1 --")
    b = mpf("0.238"); c0 = mpf("1.04")
    print("   (2/3) e1 (3 c_inf)^(1/4) = %s <= b" % nstr(mpf(2) / 3 * e1 * (3 * cinf) ** 0.25, 6))
    def cor_margin(L1, k):
        th = k / L1; x1 = 3 * cinf * (L1 - k) ** 2; lx = log(x1)
        if x1 < 404: return mpf(-999)
        Es = 6 * c0 * (3 * log(x1 / 3) + 7) / sqrt(x1 / 3) + lx ** 3 / (sqrt(3 * cinf) * (1 - th) * sqrt(x1)) \
             + (G[0] * lx ** 3 + 3 * G[1] * lx ** 2 + 3 * G[2] * lx + G[3] + rhostar(x1)) / x1
        return mpf(3) / 2 * (kap - k) - e2 - e1 * (3 * cinf) ** 0.25 * b / 2 - Es
    for L1 in (25.23, 30, 50, 100, 200, 1000, 10000):
        L1 = mpf(L1); lo, hi = mpf(-50), L1 / 2
        for _ in range(60):
            mid = (lo + hi) / 2
            if cor_margin(L1, mid) > 0: lo = mid
            else: hi = mid
        ceff = cinf * (L1 + b * sqrt(L1) - lo) ** 2 / L1 ** 2
        print("   L1 = %-7s k_max = %-8s  => bound c(n) <= %s at L = L1   (k = 0 gives %s; designB's k margin: %s)"
              % (nstr(L1, 6), nstr(lo, 5), nstr(ceff, 5), nstr(cinf * (1 + b / sqrt(L1)) ** 2, 5),
                 {30: nstr(cor_margin(L1, 0), 4), 50: nstr(cor_margin(L1, 4), 4), 100: nstr(cor_margin(L1, 7), 4),
                  200: nstr(cor_margin(L1, 9), 4), 1000: nstr(cor_margin(L1, 11), 4),
                  10000: nstr(cor_margin(L1, 12), 4)}.get(int(L1), "-")))
