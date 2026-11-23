"""Referee B, script 1: independent numerical verification of designB Lemmas 1-4.
Written from scratch (no import of designB_*). mpmath only.
  - primitive characters mod 3,4,5,7,8: zeros located on the critical line, then
    (4.1) [exact S4 identity], Lemma 3 [explicit formula for Phi_chi(y)], and the
    functional-equation expression for g^(k)(-1/2).
  - zeta: Z2, Z4 (Lemma 1) and A_j(y) (Lemma 2) against zetazero().
"""
import sys
from mpmath import mp, mpf, mpc, zeta, gamma, loggamma, digamma, polygamma, pi, log, exp, sqrt, \
    findroot, diff, re, im, conj, binomial, factorial, zetazero, e as E, nstr
mp.dps = 25

# ---------- characters ----------
def char_table(q):
    """all primitive characters mod q for q in {3,4,5,7,8} as lists of length q"""
    out = []
    if q in (3, 5, 7):
        g = {3: 2, 5: 2, 7: 3}[q]
        for k in range(1, q - 1):
            chi = [mpc(0)] * q
            x = 1
            for j in range(q - 1):
                chi[x] = mp.expjpi(mpf(2) * j * k / (q - 1))
                x = x * g % q
            out.append(("mod%d k=%d" % (q, k), chi))
    elif q == 4:
        out.append(("mod4", [mpc(0), mpc(1), mpc(0), mpc(-1)]))
    elif q == 8:
        out.append(("mod8 even", [mpc(v) for v in (0, 1, 0, -1, 0, -1, 0, 1)]))
        out.append(("mod8 odd", [mpc(v) for v in (0, 1, 0, 1, 0, -1, 0, -1)]))
    return out

def Lfun(s, chi, d=0):
    """d-th s-derivative of L(s,chi) through Hurwitz zeta"""
    q = len(chi)
    lq = log(q)
    tot = mpc(0)
    for a in range(1, q):
        if chi[a] == 0: continue
        # d^d/ds^d [ q^{-s} zeta(s,a/q) ] by Leibniz
        v = mpc(0)
        for i in range(d + 1):
            v += binomial(d, i) * (-lq) ** (d - i) * zeta(s, mpf(a) / q, i)
        tot += chi[a] * v
    return tot * mpf(q) ** (-s)

def g_chi(z, chi):            # -L'/L
    return -Lfun(z, chi, 1) / Lfun(z, chi, 0)

def parity(chi):
    return 0 if abs(chi[len(chi) - 1] - 1) < 1e-10 else 1

def zeros_on_line(chi, T, step=mpf("0.04")):
    q = len(chi); a = parity(chi)
    def w(t):
        s = mpf(1) / 2 + 1j * t
        ph = mp.expj(t / 2 * log(mpf(q) / pi) + im(loggamma((s + a) / 2)))
        return ph * Lfun(s, chi)
    w0 = w(mpf("0.37"))
    rootW = sqrt(w0 / conj(w0))
    Z = lambda t: re(w(t) * conj(rootW))
    zs = []
    t = -T; prev = Z(t)
    while t < T:
        t2 = t + step; cur = Z(t2)
        if prev == 0 or prev * cur < 0:
            r = findroot(Z, (t, t2), solver="anderson", tol=1e-18, maxsteps=60)
            zs.append(r)
        t, prev = t2, cur
    return zs

def Lam(n):
    """von Mangoldt by trial division (small n)"""
    if n < 2: return mpf(0)
    m = n; p = 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0: m //= p
            return log(p) if m == 1 else mpf(0)
        p += 1
    return log(n)

def check_character(name, chi, T=80):
    q = len(chi); a = parity(chi)
    print("== %s (q=%d, parity %d) ==" % (name, q, a)); sys.stdout.flush()
    zs = zeros_on_line(chi, T)
    # expected count: N(T) both signs ~ (T/pi) log(qT/(2 pi e))
    print("   zeros found in |gamma|<%d: %d   (Riemann-von Mangoldt main term %.1f)" %
          (T, len(zs), float(T / pi * log(q * T / (2 * pi * E)))))
    S4 = sum(1 / (1 + g * g) ** 2 for g in zs)
    tail = (log(q * T / (2 * pi)) / (3 * mpf(T) ** 3) + 1 / (9 * mpf(T) ** 3)) / pi
    # (4.1) right side, Dirichlet series through L'/L and (L'/L)' at 3/2
    s = mpf(3) / 2
    L0, L1, L2 = Lfun(s, chi, 0), Lfun(s, chi, 1), Lfun(s, chi, 2)
    LL = L1 / L0                       # L'/L = -sum Lambda chi n^-s
    LLp = L2 / L0 - (L1 / L0) ** 2     # (L'/L)' = sum Lambda chi log n n^-s
    series = re(-LL + LLp)             # Re sum Lambda chi (1+log n) n^{-3/2}
    rhs = log(mpf(q) / pi) / 4 + digamma((s + a) / 2) / 4 - polygamma(1, (s + a) / 2) / 8 - series / 2
    print("   (4.1)  S4 from zeros (+tail est %s) = %s   identity RHS = %s   diff = %s"
          % (nstr(tail, 3), nstr(S4 + tail, 12), nstr(rhs, 12), nstr(S4 + tail - rhs, 3)))
    # cross-check the Dirichlet series by brute force partial sum (slow convergence -> few digits)
    N = 20000
    ps = sum(Lam(n) * re(chi[n % q]) * (1 + log(n)) / mpf(n) ** 1.5 for n in range(2, N))
    print("   Dirichlet series: via Hurwitz %s, partial sum n<%d: %s (tail O(%.3f))"
          % (nstr(series, 10), N, nstr(ps, 8), float((2 * log(N) + 6) / sqrt(N))))
    # g^(k)(-1/2): direct vs functional equation
    gk = []
    chib = [conj(c) for c in chi]
    worst = 0
    for k in range(4):
        direct = diff(lambda z: g_chi(z, chi), mpf(-1) / 2, k)
        if k == 0:
            fe = log(mpf(q) / pi) + digamma((mpf(-1) / 2 + a) / 2) / 2 + digamma((mpf(3) / 2 + a) / 2) / 2 \
                 + Lfun(s, chib, 1) / Lfun(s, chib, 0)
        else:
            fe = polygamma(k, (mpf(-1) / 2 + a) / 2) / 2 ** (k + 1) \
                 + (-1) ** k * polygamma(k, (mpf(3) / 2 + a) / 2) / 2 ** (k + 1) \
                 + (-1) ** k * diff(lambda z: Lfun(z, chib, 1) / Lfun(z, chib, 0), s, k)
        worst = max(worst, abs(direct - fe))
        gk.append(direct)
    print("   g^(k)(-1/2), k=0..3 direct vs functional equation: max |diff| = %s ; values %s"
          % (nstr(worst, 3), [nstr(v, 8) for v in gk]))
    # Lemma 3
    for y in (mpf("7.5"), mpf("60.5"), mpf("400.5")):
        direct = sum(Lam(n) * chi[n % q] * sqrt(n) * log(y / n) ** 3 for n in range(2, int(y) + 1))
        zsum = sum(y ** (1 + 1j * g) / (1 + 1j * g) ** 4 for g in zs)
        res0 = sum(binomial(3, i) * log(y) ** i * gk[3 - i] for i in range(4))
        triv = sum(y ** (mpf(1) / 2 - a - 2 * m) / (mpf(1) / 2 - a - 2 * m) ** 4 for m in range(0, 60))
        formula = -6 * zsum + res0 - 6 * triv
        print("   Lemma 3 y=%s: direct %s   formula %s   |diff| = %s (zero-tail allowance %s)"
              % (nstr(y, 5), nstr(direct, 12), nstr(formula, 12), nstr(abs(direct - formula), 3),
                 nstr(6 * y * tail, 3)))
    sys.stdout.flush()

def check_zeta(NZ=400):
    print("== zeta, %d zeros ==" % NZ); sys.stdout.flush()
    gam = [im(zetazero(n)) for n in range(1, NZ + 1)]
    T = gam[-1]
    s = mpf(3) / 2
    zz = lambda z: zeta(z, derivative=1) / zeta(z)
    F0 = -zz(s); F1 = diff(zz, s)
    Z2f = -F0 + 2 - log(pi) / 2 + digamma(mpf(7) / 4) / 2
    Z4f = (Z2f + (4 - F1 - polygamma(1, mpf(7) / 4) / 4)) / 2
    Z2z = 2 * sum(1 / (1 + g * g) for g in gam); t2 = (log(T / (2 * pi)) + 1) / (pi * T)
    Z4z = 2 * sum(1 / (1 + g * g) ** 2 for g in gam); t4 = (log(T / (2 * pi)) / 3 + mpf(1) / 9) / (pi * T ** 3)
    print("   F0 = %s  F1 = %s" % (nstr(F0, 12), nstr(F1, 12)))
    print("   Z2: formula %s   zeros+tail %s" % (nstr(Z2f, 10), nstr(Z2z + t2, 10)))
    print("   Z4: formula %s   zeros+tail %s" % (nstr(Z4f, 10), nstr(Z4z + t4, 10)))
    gz = lambda z: -zz(z)
    gk = [diff(gz, mpf(-1) / 2, k) for k in range(4)]
    print("   g_zeta^(k)(-1/2) = %s" % [nstr(v, 10) for v in gk])
    for y in (mpf("20.5"), mpf("300.5"), mpf("3000.5")):
        for j in (1, 2, 3):
            direct = sum(Lam(n) * sqrt(n) * log(y / n) ** j for n in range(2, int(y) + 1))
            zsum = 2 * re(sum(y ** (1 + 1j * g) / (1 + 1j * g) ** (j + 1) for g in gam))
            res0 = sum(binomial(j, i) * log(y) ** i * gk[j - i] for i in range(j + 1))
            triv = sum(y ** (mpf(1) / 2 - 2 * m) / (mpf(1) / 2 - 2 * m) ** (j + 1) for m in range(1, 60))
            f = factorial(j)
            formula = f * (mpf(2) / 3) ** (j + 1) * y ** 1.5 - f * zsum + res0 - f * triv
            allow = f * y * 2 * (log(T / (2 * pi)) + 1) / (2 * pi * j * T ** j)
            print("   Lemma 2 j=%d y=%s: direct %s  formula %s  |diff| %s (tail allowance %s)"
                  % (j, nstr(y, 6), nstr(direct, 13), nstr(formula, 13), nstr(abs(direct - formula), 3),
                     nstr(allow, 3)))
    sys.stdout.flush()

if __name__ == "__main__":
    check_zeta(400)
    for q in (3, 4, 5, 7, 8):
        for name, chi in char_table(q):
            check_character(name, chi)
