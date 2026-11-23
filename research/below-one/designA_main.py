#!/usr/bin/env python3
"""
designA_main.py -- explicit constants for design A (polynomial / Riesz-type one-sided kernels).

Weight:  w(u) = sum_{k=2..K} c_k (1-u)^k on [0,1], 0 for u>1  (c_k rational, w >= 0).
Mellin:  W(s) = sum_k c_k k!/(s(s+1)...(s+k))   (rational; this is LLS's K(s-1/2)).
Majorant g(t) = sum_j a_j w_j/(w_j^2+t^2) >= |W(1/2+it)|  (certified exactly, Sturm).

For every target c the script finds a majorant g (LP), certifies it in exact rational
arithmetic, and computes the least L0 (to 3 digits, rounded up) with F(L) > 0 for L >= L0,
where F is the final inequality of Theorem 1 of designA.md (index h = 2, the worst case).
N0 = exp(L0).

All "analytic" numerics are: -zeta'/zeta(sigma) at finitely many real sigma>1, digamma at
finitely many real points, log(pi).  They are computed with mpmath at 40 digits and
rounded in the unfavourable direction by MARGIN.
"""
import sys, json, math
from fractions import Fraction as Fr
import numpy as np
import sympy as sp
import mpmath as mp
from scipy import optimize

mp.mp.dps = 40
MARGIN = mp.mpf(10) ** (-12)
u, s, t, tau = sp.symbols('u s t tau', real=True)


# --------------------------------------------------------------------------- numerics
def Zup(sig):
    """upper bound for -zeta'/zeta(sig) = sum Lambda(n) n^-sig, sig>1"""
    sig = mp.mpf(sig.numerator) / sig.denominator if isinstance(sig, Fr) else mp.mpf(sig)
    return -mp.zeta(sig, derivative=1) / mp.zeta(sig) + MARGIN


def half_psi_max(wj):
    """max over parity a in {0,1} of (1/2) psi((1/2+w_j+a)/2), as (val_a0, val_a1)"""
    wj = mp.mpf(wj.numerator) / wj.denominator
    return [mp.digamma((mp.mpf(1) / 2 + wj + a) / 2) / 2 for a in (0, 1)]


def T_up_const(wj):
    """T(w) := sum_gamma w/(w^2+gamma^2) = Re xi'/xi(1/2+w) <= (1/2) log q + T_up_const(w).
    (clipped at 0 from below so that monotonicity arguments are trivial)"""
    c = -mp.log(mp.pi) / 2 + max(half_psi_max(wj)) + Zup(Fr(1, 2) + wj) + MARGIN
    return max(c, mp.mpf(0))


# --------------------------------------------------------------------------- weight
class Weight:
    def __init__(self, name, coefs, lam):
        self.name, self.coefs, self.lam = name, dict(coefs), Fr(lam)
        assert min(coefs) >= 2
        self.K = max(coefs)
        self.w = sum(sp.Rational(c.numerator, c.denominator) * (1 - u) ** k for k, c in coefs.items())
        self.wp = sp.Poly(sp.expand(self.w), u)
        # (i) w >= 0 on [0,1]:  w = (1-u)^2 v(u), v>0 on [0,1]
        v = sp.Poly(sp.expand(self.w), u)
        one_minus = sp.Poly(1 - u, u)
        while v.eval(1) == 0:
            v = sp.div(v, one_minus)[0]
        assert v.eval(0) > 0 and v.count_roots(0, 1) == 0, "w not positive on [0,1)"
        lamS = sp.Rational(self.lam.numerator, self.lam.denominator)
        self.w0 = self.wp.eval(0)
        self.wlam = self.wp.eval(lamS)
        # (ii) D = 2 int_0^lam w - int_0^1 w   (exact)
        self.Ilam = sp.integrate(self.w, (u, 0, lamS))
        self.Itot = sp.integrate(self.w, (u, 0, 1))
        self.D = 2 * self.Ilam - self.Itot
        assert self.D > 0
        # (iii) total variations V[0,lam], V[lam,1]  (critical points isolated to 40 digits)
        dw = sp.Poly(sp.diff(sp.expand(self.w), u), u)
        crit = sorted(set(mp.mpf(sp.N(r, 40)) for r in sp.real_roots(dw)))
        lamf = mp.mpf(self.lam.numerator) / self.lam.denominator
        wf = lambda x: mp.polyval([mp.mpf(c.p) / c.q for c in self.wp.all_coeffs()], x)

        def var(a, b):
            pts = [a] + [r for r in crit if a < r < b] + [b]
            return sum(abs(wf(pts[i + 1]) - wf(pts[i])) for i in range(len(pts) - 1)) + MARGIN

        self.V0lam, self.Vlam1 = var(mp.mpf(0), lamf), var(lamf, mp.mpf(1))
        self.monotone = all(not (0 < r < 1) for r in crit)
        # (iv) crude sup bounds for |w'|, |w''| on [0,1]
        self.V1 = sum(abs(mp.mpf(c.numerator) / c.denominator) * k for k, c in coefs.items())
        self.V2 = sum(abs(mp.mpf(c.numerator) / c.denominator) * k * (k - 1) for k, c in coefs.items())
        # (iv') Taylor data for the zeta-side lemma:  f(u) = sum_{m>=1} d_m (beta-u)^m on [0,beta]
        #   f = w on [0,1] (d_k = c_k), and f_lam = w - w(lam) on [0,lam].
        def kappa(m):
            return mp.factorial(m) / mp.fprod([j + mp.mpf(1) / 2 for j in range(2, m + 1)])
        self.kap_w = sum(abs(mp.mpf(c.numerator) / c.denominator) * kappa(k) for k, c in coefs.items())
        self.kap_lam = mp.sqrt(lamf) * sum(
            abs(mp.mpf(sp.Rational(sp.diff(self.w, u, m).subs(u, lamS) / sp.factorial(m)).p)
                / sp.Rational(sp.diff(self.w, u, m).subs(u, lamS) / sp.factorial(m)).q) * lamf ** m * kappa(m)
            for m in range(1, self.K + 1))
        self.sup_w = wf(mp.mpf(0)) if self.monotone else self.V0lam + self.Vlam1
        # (v) |W(1/2+it)|^2 = NN(tau)/prod_{j=0..K}((j+1/2)^2+tau),  tau=t^2
        Nn = sum(sp.Rational(c.numerator, c.denominator) * sp.factorial(k)
                 * sp.prod([s + j for j in range(k + 1, self.K + 1)]) for k, c in coefs.items())
        e = sp.expand(Nn.subs(s, sp.Rational(1, 2) + sp.I * t) * Nn.subs(s, sp.Rational(1, 2) - sp.I * t))
        pt = sp.Poly(e, t)
        assert all(m[0] % 2 == 0 for m in pt.monoms())
        self.NN = sp.Poly(sum(cf * tau ** (m[0] // 2) for m, cf in zip(pt.monoms(), pt.coeffs())), tau)
        self.DD = sp.Poly(sp.prod([(sp.Rational(2 * j + 1, 2)) ** 2 + tau for j in range(self.K + 1)]), tau)

    def absW(self, tt):
        """float |W(1/2+it)| on a numpy grid"""
        r = np.zeros_like(tt, dtype=complex)
        for k, c in self.coefs.items():
            term = float(c) * math.factorial(k) * np.ones_like(tt, dtype=complex)
            for j in range(k + 1):
                term = term / (0.5 + j + 1j * tt)
            r += term
        return np.abs(r)

    def I(self):
        """(1/2pi) int |W(1/2+it)| dt  (only for reporting eps; not used in the proof)"""
        f = lambda x: abs(sum(mp.mpf(c.numerator) / c.denominator * mp.factorial(k)
                              / mp.fprod([mp.mpc(0.5 + j, x) for j in range(k + 1)])
                              for k, c in self.coefs.items()))
        return mp.quad(f, [0, 1, 2, 4, 8, 16, 64, 256, 4096, mp.inf]) / mp.pi


# --------------------------------------------------------------------------- majorant
WIDTHS = [Fr(9, 16), Fr(5, 8), Fr(3, 4), Fr(1), Fr(3, 2), Fr(2), Fr(5, 2), Fr(3), Fr(4), Fr(5), Fr(6)]
TGRID = np.concatenate([np.linspace(0, 16, 6401), np.geomspace(16, 5000, 3000)[1:]])


def lp_majorant(W, L, widths=WIDTHS):
    """float LP: minimise (1/2 sum a_j) L + A subject to g >= |W| on a grid."""
    m = len(widths)
    wf = [float(x) for x in widths]
    G = np.array([x / (x * x + TGRID ** 2) for x in wf]).T
    Zs = np.array([float(Zup(Fr(1, 2) + x)) for x in widths])
    base = L / 2 - math.log(math.pi) / 2
    cost = np.concatenate([base + Zs, -base + Zs, [1.0]])
    A_ub = [np.hstack([-G, G, np.zeros((len(TGRID), 1))])]
    b_ub = [-W.absW(TGRID)]
    for a in (0, 1):
        ps = np.array([float(half_psi_max(x)[a]) for x in widths])
        A_ub.append(np.concatenate([ps, -ps, [-1.0]])[None, :]); b_ub.append([0.0])
    # tail control: sum a_j w_j >= small positive number
    A_ub.append(np.concatenate([-np.array(wf), np.array(wf), [0.0]])[None, :]); b_ub.append([-1e-3 * float(W.w0)])
    res = optimize.linprog(cost, A_ub=np.vstack(A_ub), b_ub=np.concatenate(b_ub),
                           bounds=[(0, None)] * (2 * m) + [(None, None)], method='highs')
    assert res.status == 0
    return res.x[:m] - res.x[m:2 * m]


def certify(W, widths, a_float, eta):
    """rationalise (1+eta)*a and certify g >= |W(1/2+it)| for all real t exactly.
    Returns (a_rational list) or None."""
    a = [Fr(int(round(x * (1 + eta) * 10 ** 9)), 10 ** 9) for x in a_float]
    keep = [(aj, wj) for aj, wj in zip(a, widths) if aj != 0]
    R = lambda q: sp.Rational(q.numerator, q.denominator)
    Gden = sp.Poly(sp.prod([R(wj) ** 2 + tau for _, wj in keep]), tau)
    Gnum = sp.Poly(sum(R(aj) * R(wj) * sp.prod([R(wi) ** 2 + tau for (_, wi) in keep if wi != wj])
                       for aj, wj in keep), tau)
    # g > 0 on tau >= 0
    if not (Gnum.eval(0) > 0 and Gnum.count_roots(0, None) == 0):
        return None
    Q = Gnum * Gnum * W.DD - W.NN * Gden * Gden
    if not (Q.eval(0) > 0 and Q.LC() > 0 and Q.count_roots(0, None) == 0):
        return None
    return keep


def majorant_constants(keep):
    """S(q) := sum_gamma |W(1/2+i gamma)| <= half_sum * log q + A   (Lemma 5)"""
    half_sum = sum(aj for aj, _ in keep) / 2          # exact rational = (1/2pi) int g
    hs = mp.mpf(half_sum.numerator) / half_sum.denominator
    par = [sum(mp.mpf(aj.numerator) / aj.denominator * half_psi_max(wj)[a] for aj, wj in keep) for a in (0, 1)]
    A = -mp.log(mp.pi) * hs + max(par) + sum(abs(mp.mpf(aj.numerator) / aj.denominator) * Zup(Fr(1, 2) + wj)
                                             for aj, wj in keep) + MARGIN
    return hs, max(A, mp.mpf(0))


# --------------------------------------------------------------------------- final inequality
SUM_RHO2 = 2 + mp.euler - mp.log(4 * mp.pi) + MARGIN      # sum_rho 1/|rho|^2 for zeta under RH = 0.0461914...
EMODE = 'S'


def E0(y):
    """psi(y^-) >= y - E0(y).
    'S': Schoenfeld 1976 Thm 10 under RH (y>=73.2), plus trivial range.
    'H': self-contained (Lemma 3 with a trapezoid):  2 sqrt(SUM_RHO2) y^(3/4) + 2.1  (y >= 10)."""
    if EMODE == 'S':
        return max(mp.mpf(74), mp.sqrt(y) * mp.log(y) ** 2 / (8 * mp.pi))
    return 2 * mp.sqrt(SUM_RHO2) * y ** mp.mpf('0.75') + mp.mpf('2.1')


def err_zeta(kap, supf, V1, V2, beta, x):
    """Lemma 3:  |Psi_f(x) - x int_0^beta f| <= err_zeta   (zeta, RH)"""
    return (mp.sqrt(x) * SUM_RHO2 * kap + mp.mpf('2.03') * supf + supf / ((beta * x) ** 2 - 1)
            + (V1 * (mp.log(x) + mp.mpf('0.05')) + mp.mpf('0.02') * V2 / x) / x)


SIG0 = Fr(3, 2)
W1_CHOICES = [Fr(5, 8), Fr(3, 4), Fr(1)]


def lower_order(W, x, L):
    """R(x,L): upper bound for  Re Psi_w(x,chi) - sqrt(x) sum_gamma |W(1/2+i gamma)|  (Lemma 4),
    with log q <= L."""
    weps = W.w0 + W.V1 / x
    best = None
    for w1 in W1_CHOICES:
        Tw1 = L / 2 + T_up_const(w1)
        Ts0 = L / 2 + T_up_const(SIG0 - Fr(1, 2))
        s0 = mp.mpf(SIG0.numerator) / SIG0.denominator
        w1f = mp.mpf(w1.numerator) / w1.denominator
        val = (weps * (Zup(SIG0) + 1 / s0 + 1 / (x - 1) + 2 * w1f * Tw1 + Ts0)
               + W.V1 * mp.log(x) / x + (W.V1 + mp.mpf('0.4') * W.V2 / x) / x * 4 * w1f * Tw1)
        best = val if best is None else min(best, val)
    return best


def F_parts(W, hs, A, c, L):
    lam = mp.mpf(W.lam.numerator) / W.lam.denominator
    x = c * L * L / lam
    D = mp.mpf(W.D.p) / W.D.q
    wl = mp.mpf(W.wlam.p) / W.wlam.q
    parts = dict(
        main=x * D,
        jump=2 * wl * E0(lam * x),
        zeta_smooth=2 * err_zeta(W.kap_lam, W.V0lam, W.V1, W.V2, lam, x) + err_zeta(W.kap_w, W.sup_w, W.V1, W.V2, 1, x),
        zeros_main=mp.sqrt(x) * hs * L,
        zeros_A=mp.sqrt(x) * A,
        lower=lower_order(W, x, L),
        imprim=W.Vlam1 * L)
    return parts


def F(W, hs, A, c, L):
    """F(L) > 0  ==> contradiction for log N = L (h=2).  x = c L^2 / lam."""
    p = F_parts(W, hs, A, c, L)
    return p['main'] - p['jump'] - p['zeta_smooth'] - p['zeros_main'] - p['zeros_A'] - p['lower'] - p['imprim']


def find_L0(W, hs, A, c):
    c = mp.mpf(c)
    lam = mp.mpf(W.lam.numerator) / W.lam.denominator
    D = mp.mpf(W.D.p) / W.D.q
    if mp.sqrt(c / lam) * D <= hs:
        return None
    lo, hi = mp.mpf(30), mp.mpf(10) ** 9
    if F(W, hs, A, c, hi) <= 0:
        return None
    while hi / lo > 1.0005:
        mid = mp.sqrt(lo * hi)
        if F(W, hs, A, c, mid) > 0:
            hi = mid
        else:
            lo = mid
    # round up to 3 significant digits and re-check
    e = mp.floor(mp.log10(hi)) - 2
    L0 = mp.ceil(hi / 10 ** e) * 10 ** e
    assert F(W, hs, A, c, L0) > 0
    assert c * L0 * L0 > mp.e ** 4 and c * L0 * L0 > 100   # monotonicity range (lam*x = X > e^4)
    return L0


def best_for(W, c, verbose=False):
    """iterate LP <-> L0; returns (L0, keep, hs, A)"""
    best = None
    L = 3000.0
    for it in range(6):
        a = lp_majorant(W, L)
        keep = None
        for eta in (2e-5, 1e-4, 5e-4, 2e-3):
            keep = certify(W, WIDTHS, a, eta)
            if keep is not None:
                break
        if keep is None:
            L *= 2; continue
        hs, A = majorant_constants(keep)
        L0 = find_L0(W, hs, A, c)
        if verbose:
            print("    it", it, "L_lp=%.0f" % L, "eta=%g" % eta, "half_sum=%.6f A=%.4f" % (hs, A), "L0=", L0)
        if L0 is None:
            L *= 4; continue
        if best is None or L0 < best[0]:
            best = (L0, keep, hs, A)
        if abs(float(L0) - L) / L < 0.02:
            break
        L = float(L0)
    return best


# --------------------------------------------------------------------------- weights
def riesz(b):
    return {b: Fr(1)}


WEIGHTS = {}


def load_weights():
    from designA_weights import WEIGHT_DATA
    for name, (coefs, lam) in WEIGHT_DATA.items():
        WEIGHTS[name] = Weight(name, coefs, lam)


def main():
    load_weights()
    targets = ['0.95', '0.9', '0.85', '0.8', '0.79', '0.78']
    out = {}
    print("=" * 100)
    print("Weights")
    for name, W in WEIGHTS.items():
        I = W.I()
        lam = mp.mpf(W.lam.numerator) / W.lam.denominator
        D = mp.mpf(W.D.p) / W.D.q
        W.cinf = lam * I * I / D ** 2
        print(f"  {name}: K={W.K} lam={W.lam} D={mp.nstr(D, 10)} w(0)={mp.nstr(mp.mpf(W.w0.p) / W.w0.q, 8)} "
              f"w(lam)={mp.nstr(mp.mpf(W.wlam.p) / W.wlam.q, 8)} monotone={W.monotone} "
              f"V[0,lam]={mp.nstr(W.V0lam, 8)} V[lam,1]={mp.nstr(W.Vlam1, 8)} "
              f"I=(1/2pi)int|W|={mp.nstr(I, 10)}  c_inf(w)=lam I^2/D^2={mp.nstr(W.cinf, 8)}")
        print("     coefficients c_k:", {k: str(c) for k, c in W.coefs.items()})
    print("=" * 100)
    global EMODE
    for mode in ('S', 'H'):
        EMODE = mode
        print("=" * 100)
        print("psi lower bound mode:", mode, "(S = Schoenfeld, H = self-contained Hadamard/trapezoid)")
        print("(c, N0) table: for each c the best weight; L0 = log N0")
        for c in targets:
            rows = []
            for name, W in WEIGHTS.items():
                if float(W.cinf) >= float(c):
                    continue
                r = best_for(W, c)
                if r is not None:
                    rows.append((r[0], name, r))
            if not rows:
                print(f"  c={c}: no weight works"); continue
            rows.sort(key=lambda z: z[0])
            for L0, name, (_, keep, hs, A) in rows:
                W = WEIGHTS[name]
                lam = mp.mpf(W.lam.numerator) / W.lam.denominator
                D = mp.mpf(W.D.p) / W.D.q
                cg = lam * hs ** 2 / D ** 2
                eps = hs / W.I() - 1
                print(f"  c={c}  weight={name:10s} log N0={mp.nstr(L0, 6):>10s}  log10 N0={mp.nstr(L0 / mp.log(10), 6):>9s}"
                      f"   c_g={mp.nstr(cg, 7)} eps={mp.nstr(eps, 4)} A={mp.nstr(A, 6)} (1/2)sum a={mp.nstr(hs, 9)}")
            L0, name, (_, keep, hs, A) = rows[0]
            out[mode + ":" + c] = dict(weight=name, L0=str(L0), half_sum=str(hs), A=str(A),
                          g=[(str(aj), str(wj)) for aj, wj in keep])
            pp = F_parts(W := WEIGHTS[name], hs, A, mp.mpf(c), L0)
            print("     terms of F at L0 (relative to main):", {k: mp.nstr(v / pp['main'], 4) for k, v in pp.items()})
            print("     best majorant g(t)=sum a_j w_j/(w_j^2+t^2), (a_j, w_j):",
                  [(str(aj), str(wj)) for aj, wj in keep])
    json.dump(out, open("designA_certificates.json", "w"), indent=1)


if __name__ == "__main__":
    main()
