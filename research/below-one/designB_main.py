"""designB_main.py -- every numeric constant of designB.md and the (c, N0) table.

Kernel: K(s) = 6/(s+1)^4, i.e. weight sqrt(n) log^3(x/n) on n < x, x = X/lambda, lambda = 1/3.
All constants are computed with mpmath at 40 digits and then rounded OUTWARD (in the direction that
weakens the final inequality) to 6 decimals; the table is computed from the rounded constants only.
Notation follows designB.md (section numbers in comments)."""
import mpmath as mp
mp.mp.dps = 40
R = mp.mpf

def up(v, d=6):   # round up
    return mp.ceil(v*10**d)/10**d
def dn(v, d=6):   # round down
    return mp.floor(v*10**d)/10**d

half = R(1)/2
s0 = R(3)/2
zl = lambda s: mp.zeta(s, derivative=1)/mp.zeta(s)          # zeta'/zeta
# ---- Dirichlet-series constants F_k = sum Lambda(n) log^k n n^{-3/2} = (-1)^(k+1) (zeta'/zeta)^{(k)}(3/2)
F = [(-1)**(k+1)*(mp.diff(zl, s0, k) if k else zl(s0)) for k in range(4)]
# cross-check F_0, F_1 by a direct prime sum with an integral tail estimate (sanity only)
def direct(k, N=200000):
    sieve = bytearray([1])*(N+1); tot = R(0)
    for p in range(2, N+1):
        if sieve[p]:
            for m in range(p*p, N+1, p): sieve[m] = 0
            lp = mp.log(p); q = p
            while q <= N:
                tot += lp*mp.log(q)**k/R(q)**1.5; q *= p
    return tot + mp.quad(lambda t: mp.log(t)**k/t**1.5, [N, mp.inf])
print("== Dirichlet series at 3/2 ==")
for k in range(4):
    print("  F_%d = %s" % (k, mp.nstr(F[k], 12)) + ("   (direct prime sum + PNT tail: %s)" % mp.nstr(direct(k), 8) if k < 2 else ""))
F_lo = [dn(f) for f in F]; F_hi = [up(f) for f in F]

# ---- zeta zero sums (Lemma 1): Z2 = sum 1/(1+g^2), Z4 = sum 1/(1+g^2)^2, Z3 <= sqrt(Z2 Z4)
Z2 = zl(s0) + 2 - mp.log(mp.pi)/2 + mp.digamma(R(7)/4)/2
Q2 = -mp.diff(zl, s0) + 4 - mp.polygamma(1, R(7)/4)/4      # sum Re 1/(3/2-rho)^2
Z4 = (Z2 + Q2)/2
Z3 = mp.sqrt(Z2*Z4)
Z2, Z3, Z4 = up(Z2), up(Z3), up(Z4)
print("== zeta zero sums ==\n  Z2 <= %s   Z3 <= %s   Z4 <= %s" % (Z2, Z3, Z4))

# ---- g_zeta^{(k)}(-1/2), g_zeta = -zeta'/zeta   (Lemma 2), computed directly and via the functional equation
gz = lambda z: -zl(z)
gam = []
print("== |g_zeta^(k)(-1/2)| ==")
for k in range(4):
    direct_v = mp.diff(gz, -half, k) if k else gz(-half)
    # zeta'/zeta(z) = log(pi) - psi(z/2)/2 - psi((1-z)/2)/2 - zeta'/zeta(1-z)
    fe = (mp.polygamma(k, -half/2) + (-1)**k*mp.polygamma(k, R(3)/4))/2**(k+1) + (-1)**k*(mp.diff(zl, s0, k) if k else zl(s0)) - (mp.log(mp.pi) if k == 0 else 0)
    assert abs(direct_v - fe) < R(10)**(-15), (k, direct_v, fe)
    gam.append(up(abs(fe)))
    print("  k=%d: value %s   gamma_%d = %s" % (k, mp.nstr(fe, 12), k, gam[k]))

# ---- L-side constants (Lemmas 3, 4)
print("== L-function side ==")
kap = []; G = [R(0)]*4
for a in (0, 1):
    u1 = (R(-1)/2 + a)/2; u2 = (R(3)/2 + a)/2
    kappa = mp.log(mp.pi) - mp.digamma(u2) + mp.polygamma(1, u2)/2 + 2*(F_lo[0] + F_lo[1])
    kap.append(kappa)
    g0 = -mp.log(mp.pi) + (mp.digamma(u1) + mp.digamma(u2))/2 + F_hi[0]
    G[0] = max(G[0], g0)
    for k in (1, 2, 3):
        G[k] = max(G[k], (abs(mp.polygamma(k, u1)) + abs(mp.polygamma(k, u2)))/2**(k+1) + F_hi[k])
    print("  parity a=%d: kappa_a = %s ; Re g_chi(-1/2) - log q <= %s" % (a, mp.nstr(kappa, 10), mp.nstr(g0, 8)))
kappa = dn(min(kap)); G = [up(max(g, 0)) for g in G]
print("  kappa = %s ;  G0..G3 = %s" % (kappa, [str(g) for g in G]))

# ---- kernel constants (section 5)
lam = R(1)/3; l0 = mp.log(3)
P = l0**3 + 2*l0**2 + R(8)/3*l0 + R(16)/9
D = dn(R(4)/3*lam**1.5*P - R(32)/27)
cinf = R(9)/4*lam/D**2
delta0 = 2*mp.sqrt(Z2)
e1 = up(4*l0**3*mp.sqrt(Z2)*lam**1.25)
e2 = up(2*lam*(3*l0**2*Z2 + 6*l0*Z3 + 6*Z4) + 6*Z4)
c0 = R('1.04')     # psi(t) <= c0 t  (Rosser-Schoenfeld 1962, Thm 12: psi(t) < 1.03883 t)
print("== kernel K(s)=6/(s+1)^4, lambda=1/3 ==")
print("  D = %s   c_inf = 9*lambda/(4 D^2) = %s   delta0 = %s   e1 = %s   e2 = %s" % (D, mp.nstr(cinf, 8), mp.nstr(delta0, 6), e1, e2))

def r(j, y):
    ly = mp.log(y)
    return sum(mp.binomial(j, i)*gam[j-i]*ly**i for i in range(j+1)) + R('0.64')*mp.factorial(j)
def rho_star(x):
    return 2*l0**3*(gam[0] + 1) + 6*l0**2*r(1, x) + 6*l0*r(2, x) + 3*r(3, x)
def Tail(X):       # sum_{n>=X} Lambda(n)(1+log n) n^{-3/2} <= c0 (3 log X + 7)/sqrt X
    return c0*(3*mp.log(X) + 7)/mp.sqrt(X)
def Err(L, c):
    X = c*L*L; x = X/lam; lx = mp.log(x)
    return 6*Tail(X) + L*lx**3/x + (G[0]*lx**3 + 3*G[1]*lx**2 + 3*G[2]*lx + G[3] + rho_star(x))/x
def H(L, c):       # contradiction iff H > 0   (inequality (5.7))
    x = c*L*L/lam
    return D*mp.sqrt(x) - R(3)/2*L - e1*x**R('0.25') - e2 + R(3)/2*kappa - Err(L, c)
def ok_from(L0, c):
    """rigorous sufficient condition for: H(L,c) > 0 for ALL L >= L0   (Lemma 8)"""
    X0 = c*L0*L0; x0 = X0/lam
    if x0 < 404 or X0 < 45: return False
    alpha = D*mp.sqrt(c/lam) - R(3)/2; beta = e1*(c/lam)**R('0.25'); const = R(3)/2*kappa - e2
    if alpha <= 0: return False
    w0 = mp.sqrt(L0); wv = max(w0, beta/(2*alpha))
    return alpha*wv*wv - beta*wv + const - Err(L0, c) > 0
def ok_range(L0, L1, c):
    """sufficient condition for H(L,c) > 0 on [L0, L1] when alpha <= 0 (q decreasing in w)"""
    X0 = c*L0*L0
    if X0/lam < 404 or X0 < 45: return False
    alpha = D*mp.sqrt(c/lam) - R(3)/2; beta = e1*(c/lam)**R('0.25'); const = R(3)/2*kappa - e2
    assert alpha <= 0
    w1 = mp.sqrt(L1)
    return alpha*w1*w1 - beta*w1 + const - Err(L0, c) > 0

print("== Table: least-witness bound a < c (log n)^2 for all n >= N0 = exp(L0) ==")
print("   (L0 = smallest value, on a grid of step 0.01, passing the rigorous test of Lemma 8)")
for c in ('0.95', '0.90', '0.85', '0.80', '0.79', '0.78', '0.779', '0.778', '0.7775'):
    cc = R(c); found = None
    L0 = R(1)
    while L0 < 4000:
        if ok_from(L0, cc): found = L0; break
        L0 += R('0.01') if L0 < 60 else R(1)
    if found is None:
        print("  c = %s : test fails for all L0 < 4000 (alpha = %s)" % (c, mp.nstr(D*mp.sqrt(cc/lam) - R(3)/2, 5)))
    else:
        X0 = cc*found**2
        print("  c = %-6s L0 = log N0 = %-7s N0 = %-10s (X0 = c L0^2 = %s, x0 = %s, margin H-bound = %s)" %
              (c, mp.nstr(found, 6), mp.nstr(mp.exp(found), 4), mp.nstr(X0, 5), mp.nstr(3*X0, 5),
               mp.nstr(H(found, cc), 4)))
print("== c at or below c_inf: valid on a bounded range exp(30) <= n <= exp(L1) ==")
for c in ('0.777', '0.775', '0.77', '0.76', '0.75'):
    cc = R(c)
    assert D*mp.sqrt(cc/lam) - R(3)/2 <= 0
    L0 = R(30); best = None; L1 = L0
    while L1 < 1e7 and ok_range(L0, L1, cc): best = L1; L1 *= R('1.01')
    print("  c = %-7s valid for 30 <= log n <= %s" % (c, mp.nstr(best, 6) if best else None))

print("== explicit shape (Corollary 10): a < c_inf (L + b sqrt(L) - k)^2 for L >= L1 ==")
b = up(R(2)/3*e1*(cinf/lam)**R('0.25'), 3)
print("  c_inf = 3/(4 D^2) = %s ; b = %s  (>= (2/3) e1 (c_inf/lambda)^(1/4) = %s)" % (mp.nstr(cinf, 8), b, mp.nstr(R(2)/3*e1*(cinf/lam)**R('0.25'), 6)))
def cor_margin(L1, k):
    theta = R(k)/L1
    X = cinf*(L1 - k)**2; x = X/lam; lx = mp.log(x)
    assert x >= 404 and X >= 45
    Estar = 6*Tail(X) + mp.sqrt(lam/cinf)/(1-theta)*lx**3/mp.sqrt(x) + (G[0]*lx**3 + 3*G[1]*lx**2 + 3*G[2]*lx + G[3] + rho_star(x))/x
    return R(3)/2*(kappa - k) - e2 - e1*(cinf/lam)**R('0.25')*b/2 - Estar
for (L1, k) in ((30, 0), (50, 4), (100, 7), (200, 9), (1000, 11), (10000, 12)):
    print("  L1 = %-6s k = %-3s margin = %s" % (L1, k, mp.nstr(cor_margin(R(L1), k), 5)))

print("== sample values of H(L, c) (no rigor needed: illustrates sizes) ==")
for L in (15, 20, 30, 50, 100, 230, 1000, 10000):
    print("  L = %-6s" % L + "  ".join("H(c=%s) = %-9s" % (c, mp.nstr(H(R(L), R(c)), 5)) for c in ('0.8', '0.85', '0.9', '0.95')))
