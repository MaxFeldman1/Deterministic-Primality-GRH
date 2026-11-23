"""miller4_main.py -- constants and (c, N0) tables for miller4.md.

Index-h version of designB (kernel 6/(s+1)^4, weight sqrt(n) log^3(x/n) on n < x = X/lambda) for a subgroup
H of (Z/n)^* of index h >= 4 that contains every integer 1 <= a < X.

Inputs: the Round-11 Lean Props (lean/DetPrimality/Bach/R11Defs.lean), i.e. the LOOSENED constants
  Z2 <= 0.047, Z4 <= 0.00012 (Z3 <= sqrt(Z2 Z4) <= 0.002375), kappa >= 12.4,
  G = (1.30, 9.31, 32.91, 198.31), gamma = (1.771, 0.148, 1.281, 0.0515), Chebyshev c0 in {2, 1.39}.
For comparison the same tables with the sharp designB constants (c0 = 1.04) are printed too.
Everything is 40-digit mpmath; D is rounded down, E1, E2 up, at 1e-6."""
import mpmath as mp
mp.mp.dps = 40
R = mp.mpf
up = lambda v, d=6: mp.ceil(v*10**d)/10**d
dn = lambda v, d=6: mp.floor(v*10**d)/10**d

R11 = dict(Z2=R('0.047'), Z4=R('0.00012'), Z3=R('0.002375'), kappa=R('12.4'),
           G=[R('1.30'), R('9.31'), R('32.91'), R('198.31')],
           gam=[R('1.771'), R('0.148'), R('1.281'), R('0.0515')])
SHARP = dict(Z2=R('0.046136'), Z4=R('0.000074'), Z3=R('0.001848'), kappa=R('12.691241'),
             G=[R('1.274646'), R('9.125903'), R('32.262139'), R('194.419965')],
             gam=[R('1.735827'), R('0.145038'), R('1.255863'), R('0.050451')])
assert mp.sqrt(R11['Z2']*R11['Z4']) <= R11['Z3'] and mp.sqrt(SHARP['Z2']*SHARP['Z4']) <= SHARP['Z3']

def P(l):
    return l**3 + 2*l**2 + R(8)/3*l + R(16)/9

def a_of(lam):
    """a(lambda) = int_0^lambda sqrt(u) log^3(1/u) du = (2/3) lambda^{3/2} P(log 1/lambda);  a(1) = 32/27."""
    return R(2)/3*lam**R('1.5')*P(mp.log(1/lam))

def consts(h, lam, C):
    l = mp.log(1/lam)
    D = dn((h*a_of(lam) - R(32)/27)/(h - 1))
    E1 = up(R(h)/(h - 1)*2*l**3*mp.sqrt(C['Z2'])*lam**R('1.25'))
    E2 = up((h*lam*(3*l**2*C['Z2'] + 6*l*C['Z3'] + 6*C['Z4']) + 6*C['Z4'])/(h - 1))
    return l, D, E1, E2

def cinf(h, lam):
    return R(9)/4*lam/((h*a_of(lam) - R(32)/27)/(h - 1))**2

def r(j, y, C):
    ly = mp.log(y)
    return sum(mp.binomial(j, i)*C['gam'][j - i]*ly**i for i in range(j + 1)) + R('0.64')*mp.factorial(j)

def rho(h, l, x, C):
    """rho_h(x)/(h-1): everything that is O(log^3 x) on the prime side, already divided by h-1."""
    return (h*(l**3*(C['gam'][0] + 1) + 3*l**2*r(1, x, C) + 3*l*r(2, x, C) + r(3, x, C)) + r(3, x, C))/(h - 1)

def Err(L, c, h, lam, C, c0):
    l = mp.log(1/lam)
    X = c*L*L; x = X/lam; lx = mp.log(x); G = C['G']
    return (6*c0*(3*mp.log(X) + 7)/mp.sqrt(X) + L*lx**3/x
            + (G[0]*lx**3 + 3*G[1]*lx**2 + 3*G[2]*lx + G[3] + rho(h, l, x, C))/x)

def margin(L0, c, h, lam, C, c0):
    """Lemma M9: sufficient for a contradiction at EVERY L >= L0 (needs x0 >= 404, X0 >= 45, alpha > 0)."""
    l, D, E1, E2 = consts(h, lam, C)
    X0 = c*L0*L0; x0 = X0/lam
    al = D*mp.sqrt(c/lam) - R(3)/2; be = E1*(c/lam)**R('0.25')
    if al <= 0 or x0 < 404 or X0 < 45: return R(-999)
    w = max(mp.sqrt(L0), be/(2*al))
    return al*w*w - be*w + R(3)/2*C['kappa'] - E2 - Err(L0, c, h, lam, C, c0)

def threshold(c, h, lam, C, c0, hi=R(10)**7):
    if margin(hi, c, h, lam, C, c0) <= 0: return None
    lo = R(1)
    for _ in range(90):
        mid = (lo + hi)/2
        if margin(mid, c, h, lam, C, c0) > 0: hi = mid
        else: lo = mid
    return mp.ceil(hi*100)/100

def N0exp(L0):
    return int(mp.ceil(L0/mp.log(10)))

if __name__ == "__main__":
    print("== reduced functional: c_inf(h, lambda) = 9 lambda / (4 D_h^2),  D_h = (h a(lambda) - 32/27)/(h-1) ==")
    for h in (2, 3, 4, 5, 6, 8, 16, 10**6):
        best = min(((cinf(h, R(i)/10000), R(i)/10000) for i in range(1000, 4500)), key=lambda t: t[0])
        print("  h = %-8d optimal lambda = %s  c_inf = %s ;  lambda=1/3: %s  1/4: %s  6/25: %s  1/5: %s" % (
            h, mp.nstr(best[1], 4), mp.nstr(best[0], 6), mp.nstr(cinf(h, R(1)/3), 6), mp.nstr(cinf(h, R(1)/4), 6),
            mp.nstr(cinf(h, R(6)/25), 6), mp.nstr(cinf(h, R(1)/5), 6)))
    print("  monotonicity in h (h = 4 is the worst case among h >= 4): a(lambda) < 32/27 for lambda < 1:",
          all(a_of(R(i)/100) < R(32)/27 for i in range(1, 100)))

    lams = [("1/3", R(1)/3), ("1/4", R(1)/4), ("6/25", R(6)/25), ("1/5", R(1)/5)]
    print("\n== constants for h = 4 ==")
    for nameC, C in (("Round-11 Props", R11), ("sharp designB", SHARP)):
        for nm, lam in lams:
            l, D, E1, E2 = consts(4, lam, C)
            print("  [%s] lambda = %-5s l = %s  D = %s  c_inf = 9 lam/(4 D^2) = %s  E1 = %s  E2 = %s" % (
                nameC, nm, mp.nstr(l, 8), D, mp.nstr(up(R(9)/4*lam/D**2), 7), E1, E2))

    cs = ["0.75", "0.72", "0.70", "0.69", "0.68", "0.67", "0.66", "0.65", "0.645", "0.642"]
    for nameC, C, c0s in (("Round-11 Props (Z2<=0.047, Z4<=0.00012, kappa>=12.4, G, gamma loosened)", R11, ("2", "1.39")),
                          ("sharp designB constants (reference only)", SHARP, ("1.04",))):
        for c0 in c0s:
            print("\n== h = 4, %s, c0 = %s:  log10 N0 (L0) ==" % (nameC, c0))
            print("   c      " + "".join("lambda=%-14s" % nm for nm, _ in lams) + "best")
            for c in cs:
                row = []; best = None
                for nm, lam in lams:
                    L0 = threshold(R(c), 4, lam, C, R(c0))
                    if L0 is None: row.append("--"); continue
                    row.append("10^%d (%s)" % (N0exp(L0), mp.nstr(L0, 6)))
                    if best is None or L0 < best[0]: best = (L0, nm)
                print("   %-6s " % c + "".join("%-21s" % s for s in row)
                      + ("10^%d at lambda=%s" % (N0exp(best[0]), best[1]) if best else "not reached"))

    print("\n== margins at the tabulated N0 (Round-11 Props, h = 4) ==")
    final = [("0.75", "1/3"), ("0.72", "1/3"), ("0.70", "1/3"), ("0.70", "1/4"), ("0.68", "1/4"), ("0.66", "1/4"),
             ("0.65", "1/4")]
    lamd = dict(lams)
    for c0 in ("2", "1.39"):
        for c, nm in final:
            L0 = threshold(R(c), 4, lamd[nm], R11, R(c0))
            k = N0exp(L0); Lk = k*mp.log(10)
            l, D, E1, E2 = consts(4, lamd[nm], R11)
            print("  c0 = %-4s c = %-5s lambda = %-4s L0 = %-8s N0 = 10^%-4d margin(log N0) = %s  (X0 = %s, x0 = %s; "
                  "lhs scale 1.5 L0 = %s)" % (c0, c, nm, mp.nstr(L0, 6), k, mp.nstr(margin(Lk, R(c), 4, lamd[nm], R11, R(c0)), 4),
                                            mp.nstr(R(c)*Lk**2, 5), mp.nstr(R(c)*Lk**2/lamd[nm], 5), mp.nstr(1.5*Lk, 4)))

    print("\n== larger h with the h = 4 constants is never worse; sample (Round-11, c0 = 2, lambda = 1/4, c = 0.68) ==")
    for h in (4, 5, 6, 8, 16, 100):
        L0 = threshold(R('0.68'), h, R(1)/4, R11, R(2))
        l, D, E1, E2 = consts(h, R(1)/4, R11)
        print("  h = %-4d D = %s E1 = %s E2 = %s  L0 = %s" % (h, D, E1, E2, mp.nstr(L0, 6)))

    print("\n== h = 2, lambda = 1/3 regression against R11_BRIEF (c0 = 2: 10^12, 10^14, 10^16, 10^19, 10^21) ==")
    for c0 in ("2", "1.39"):
        print("  c0 = %s: " % c0 + ", ".join("%s: 10^%d" % (c, N0exp(threshold(R(c), 2, R(1)/3, R11, R(c0))))
                                            for c in ("0.95", "0.90", "0.85", "0.80", "0.79")))
    print("  c_inf(h=2, 1/3) with rounded D: %s" % mp.nstr(R(3)/4/consts(2, R(1)/3, R11)[1]**2, 8))
