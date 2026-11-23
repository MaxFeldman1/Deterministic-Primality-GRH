#!/usr/bin/env python3
"""designA_rate.py -- re-verify the stored certificates independently of the LP, and derive an explicit
rate  c(N) = (lam/D^2) * ( hs + (A+B1)/L + B2*log(L)^2/L )^2 ,  L = log N   (Corollary 2 of designA.md).
For each stored certificate: (i) re-certify g >= |W(1/2+it)| exactly (Sturm); (ii) recompute hs, A;
(iii) check F(L0) > 0; (iv) compute B1, B2 and check on a grid that c >= c_rate(L) => F(c, L) > 0."""
import json
from fractions import Fraction as Fr
import mpmath as mp
import designA_main as M
from designA_main import sp, tau

M.load_weights()
cert = json.load(open("designA_certificates.json"))
for key, d in cert.items():
    mode, c = key.split(":")
    M.EMODE = mode
    W = M.WEIGHTS[d["weight"]]
    keep = [(Fr(a), Fr(w)) for a, w in d["g"]]
    R = lambda q: sp.Rational(q.numerator, q.denominator)
    Gden = sp.Poly(sp.prod([R(wj) ** 2 + tau for _, wj in keep]), tau)
    Gnum = sp.Poly(sum(R(aj) * R(wj) * sp.prod([R(wi) ** 2 + tau for (_, wi) in keep if wi != wj]) for aj, wj in keep), tau)
    ok1 = Gnum.eval(0) > 0 and Gnum.count_roots(0, None) == 0
    Q = Gnum * Gnum * W.DD - W.NN * Gden * Gden
    ok2 = Q.eval(0) > 0 and Q.LC() > 0 and Q.count_roots(0, None) == 0
    hs, A = M.majorant_constants(keep)
    L0 = mp.mpf(d["L0"])
    ok3 = M.F(W, hs, A, mp.mpf(c), L0) > 0
    lam = mp.mpf(W.lam.numerator) / W.lam.denominator
    D = mp.mpf(W.D.p) / W.D.q
    cg = lam * hs ** 2 / D ** 2
    print(f"{key:8s} weight={d['weight']:8s} deg Q={Q.degree()}  g>0:{ok1}  g>=|W|:{ok2}  F(L0)>0:{ok3}  log N0={mp.nstr(L0,6)}  c_g={mp.nstr(cg,8)}")
    assert ok1 and ok2 and ok3
    if mode == 'S':
        # explicit rate, valid for L >= Lmin and c in [c_g, 1]
        Lmin = mp.mpf(100)
        wl = mp.mpf(W.wlam.p) / W.wlam.q
        B2 = wl * mp.sqrt(lam) / mp.pi
        xmin = cg * Lmin ** 2 / lam
        p = M.F_parts(W, hs, A, cg, Lmin)
        B1 = (p['zeta_smooth'] + p['lower'] + p['imprim']) / mp.sqrt(xmin)
        B1 = mp.ceil(B1 * 1000) / 1000
        crate = lambda L: lam / D ** 2 * (hs + (A + B1) / L + B2 * mp.log(L) ** 2 / L) ** 2
        bad = 0
        for L in [Lmin * mp.mpf('1.05') ** k for k in range(0, 260)]:
            cc = crate(L)
            if cc <= 1:
                for c2 in (cc, (cc + 1) / 2, mp.mpf(1)):
                    if not M.F(W, hs, A, c2, L) > 0:
                        bad += 1
        print(f"         rate: c(N) = {mp.nstr(lam / D**2, 8)} * ( {mp.nstr(hs, 9)} + {mp.nstr(A + B1, 6)}/L + {mp.nstr(B2, 5)}*log(L)^2/L )^2,"
              f"  L=log N >= {Lmin};  grid violations: {bad}")
        print("         c_rate at L = 200,300,500,1000,3000,1e4,1e5,1e6:",
              [mp.nstr(crate(mp.mpf(L)), 5) for L in (200, 300, 500, 1000, 3000, 1e4, 1e5, 1e6)])
