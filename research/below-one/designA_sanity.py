#!/usr/bin/env python3
"""designA_sanity.py -- numerical sanity checks of the identities used in designA.md.
(1) Hadamard-form explicit formula for zeta (Lemma 2, identity (2.3)) with f=(1-u)^3, using zeta zeros.
(2) Mellin transform W(s) of w, and |W(1/2+it)|^2 = NN(t^2)/DD(t^2).
(3) Lorentzian zero-sum identity for zeta:  sum_gamma w/(w^2+gamma^2) = Re xi'/xi(1/2+w).
(4) constants: sum_rho 1/|rho|^2, Re xi'/xi(2) for zeta."""
import mpmath as mp
mp.mp.dps = 20
NZ = 800
zeros = [mp.zetazero(n) for n in range(1, NZ + 1)]
Z = lambda s: -mp.zeta(s, derivative=1) / mp.zeta(s)

# (1)
b = 3
f = lambda u: (1 - u) ** b if u < 1 else mp.mpf(0)
for x in (mp.mpf('30.5'), mp.mpf('200.3')):
    eps = 1 / x
    lhs = mp.fsum(mp.mangoldt(n) * f(n / x) for n in range(1, int(x) + 1))
    main = x * mp.quad(f, [eps, 1])
    const = f(eps) * (Z(2) - 1)
    J = lambda c: mp.quad(lambda t: t ** (-c - 1) * f(t / x), [1, x])
    psi_sum = mp.nsum(lambda k: f(eps) / (2 * k + 2) - J(2 * k), [1, 60]) + f(eps) * (mp.nsum(lambda k: 1 / (2 * k + 2) - 1 / (2 * k), [61, mp.inf]))
    zsum = mp.mpf(0)
    for rho in zeros:
        # closed form of x^rho int_eps^1 u^(rho-1)(1-u)^3 du via binomial expansion
        term = sum(mp.binomial(b, m) * (-1) ** m * (x ** rho - x ** (-m)) / (rho + m) for m in range(b + 1))
        zsum += 2 * mp.re(term - f(eps) / (2 - rho))
    rhs = main + const + psi_sum - zsum
    print(f"(1) x={x}: sum Lambda(n) f(n/x) = {mp.nstr(lhs, 12)}   Hadamard-form RHS ({NZ} zero pairs) = {mp.nstr(rhs, 12)}   diff = {mp.nstr(lhs - rhs, 4)}"
          f"   (expected truncation error ~ {mp.nstr(2 * f(eps) * 2 / zeros[-1].imag * mp.log(zeros[-1].imag) / (2 * mp.pi), 3)})")

# (2)
from designA_main import Weight, WEIGHTS, load_weights, sp, tau
load_weights()
for name in ("riesz4", "opt8"):
    W = WEIGHTS[name]
    wnum = lambda uu: sum(mp.mpf(c.numerator) / c.denominator * (1 - uu) ** k for k, c in W.coefs.items())
    for tt in (0, 0.7, 3.3, 11):
        s = mp.mpc(0.5, tt)
        direct = mp.quad(lambda uu: wnum(uu) * uu ** (s - 1), [0, 0.01, 0.1, 0.5, 1])
        formula = sum(mp.mpf(c.numerator) / c.denominator * mp.factorial(k) / mp.fprod([s + j for j in range(k + 1)]) for k, c in W.coefs.items())
        rat = mp.mpf(sp.N(W.NN.eval(sp.Rational(str(tt)) ** 2) / W.DD.eval(sp.Rational(str(tt)) ** 2), 25))
        print(f"(2) {name} t={tt}: |W| direct={mp.nstr(abs(direct), 10)} formula={mp.nstr(abs(formula), 10)} sqrt(NN/DD)={mp.nstr(mp.sqrt(rat), 10)}")

# (3),(4)
for w in (mp.mpf(5) / 8, mp.mpf(1)):
    s = mp.mpf(1) / 2 + w
    lhs = 2 * mp.fsum(w / (w * w + r.imag ** 2) for r in zeros)
    rhs = 1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2 - Z(s)
    print(f"(3) w={w}: sum over {NZ} zero pairs = {mp.nstr(lhs, 8)}  Re xi'/xi(1/2+w) = {mp.nstr(rhs, 8)}  (tail ~ {mp.nstr(2*w/zeros[-1].imag*mp.log(zeros[-1].imag)/(2*mp.pi), 3)})")
print("(4) sum_rho 1/|rho|^2 = 2+gamma-log(4pi) =", mp.nstr(2 + mp.euler - mp.log(4 * mp.pi), 12),
      " partial sum:", mp.nstr(2 * mp.fsum(1 / abs(r) ** 2 for r in zeros), 8))
print("    Re xi'/xi(2) (zeta) =", mp.nstr(mp.mpf(3) / 2 - mp.log(mp.pi) / 2 + mp.digamma(1) / 2 - Z(2), 12),
      "  sum_rho 1/rho = ", mp.nstr(1 + mp.euler / 2 - mp.log(4 * mp.pi) / 2, 12), "  Z(2)-1 =", mp.nstr(Z(2) - 1, 10))
