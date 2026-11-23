"""designB_check.py -- independent numerical sanity checks (NOT part of the proof) of the three
analytic identities used in designB.md:
  (C1) zero-sum identity  S4(chi) = sum_gamma 1/(1+gamma^2)^2 = (1/2)(P1+P2)        [Lemma 4]
  (C2) explicit formula for Phi_chi(y) = sum_{n<y} Lambda(n) chi(n) sqrt(n) log^3(y/n) [Lemma 3]
  (C3) explicit formula for A_j(y) (zeta), and Z2, Z4                                 [Lemma 2]
Zeros are located numerically (sign changes of the completed L-function on the critical line)."""
import mpmath as mp
mp.mp.dps = 20

def mangoldt_table(N):
    lam = [mp.mpf(0)]*(N+1)
    sieve = list(range(N+1))
    for p in range(2, N+1):
        if sieve[p] == p:
            for m in range(p, N+1, p):
                if sieve[m] == m: sieve[m] = p
    for n in range(2, N+1):
        p = sieve[n]; m = n
        while m % p == 0: m //= p
        if m == 1: lam[n] = mp.log(p)
    return lam

def Lzeros(chi, q, a, T, step=0.1):
    """ordinates gamma in (0,T) of zeros of L(1/2+it, chi), chi real primitive."""
    def Z(t):
        s = mp.mpf(1)/2 + 1j*t
        v = (mp.mpf(q)/mp.pi)**((s+a)/2)*mp.gamma((s+a)/2)*mp.dirichlet(s, chi)
        return v
    # completed function has constant phase on the line for real chi: rotate by the phase at t=1
    ph = Z(mp.mpf(1)); ph = ph/abs(ph)
    f = lambda t: mp.re(Z(t)/ph)*mp.exp(mp.pi*t/4)   # undo Gamma decay
    zs = []; t = mp.mpf(step)/2; prev = f(t)
    while t < T:
        t2 = t + step; cur = f(t2)
        if prev*cur < 0:
            zs.append(mp.findroot(f, (t, t2), solver='anderson'))
        t, prev = t2, cur
    return zs

def check_char(chi, q, a, T=60):
    zs = Lzeros(chi, q, a, T)
    # real chi: zeros symmetric => sum over all gamma = 2 * sum over gamma>0
    S4 = 2*sum(1/(1+g*g)**2 for g in zs)
    tail = mp.quad(lambda t: mp.log(q*t/(2*mp.pi))/(mp.pi)/(1+t*t)**2, [T, mp.inf])
    L = lambda s: mp.dirichlet(s, chi)
    ld = lambda s: mp.diff(L, s)/L(s)
    P1 = mp.log(mp.mpf(q)/mp.pi)/2 + mp.digamma((mp.mpf(3)/2+a)/2)/2 + ld(mp.mpf(3)/2)
    P2 = -mp.polygamma(1, (mp.mpf(3)/2+a)/2)/4 - mp.diff(ld, mp.mpf(3)/2)
    print("  (C1) q=%d a=%d: #zeros(0<g<%d)=%d  S4(zeros)+tail=%s   (P1+P2)/2=%s" %
          (q, a, T, len(zs), mp.nstr(S4+tail, 10), mp.nstr((P1+P2)/2, 10)))
    # (C2) explicit formula
    y = mp.mpf(60.5); N = 60
    lam = mangoldt_table(N)
    lhs = sum(lam[n]*chi[n % q]*mp.sqrt(n)*mp.log(y/n)**3 for n in range(2, N+1))
    zsum = sum(2*mp.re(y**(1+1j*g)/(1+1j*g)**4) for g in zs)
    g0 = lambda z: -ld(z)
    gk = [g0(mp.mpf(-1)/2)] + [mp.diff(g0, mp.mpf(-1)/2, k) for k in (1, 2, 3)]
    res = sum(mp.binomial(3, i)*mp.log(y)**i*gk[3-i] for i in range(4))
    triv = sum(y**(mp.mpf(1)/2-a-2*m)/(mp.mpf(1)/2-a-2*m)**4 for m in range(0, 60))
    rhs = -6*zsum + res - 6*triv
    print("  (C2) Phi_chi(60.5): direct=%s  explicit formula=%s  (zero tail error <~ %s)" %
          (mp.nstr(lhs, 10), mp.nstr(rhs, 10), mp.nstr(6*y*2*mp.quad(lambda t: mp.log(q*t)/(2*mp.pi)/t**4, [T, mp.inf]), 3)))
    # functional-equation formula for g_chi^{(k)}(-1/2)
    for k in range(4):
        fe = (mp.polygamma(k, (mp.mpf(-1)/2+a)/2) + (-1)**k*mp.polygamma(k, (mp.mpf(3)/2+a)/2))/2**(k+1) \
             + (-1)**k*(mp.diff(ld, mp.mpf(3)/2, k) if k else ld(mp.mpf(3)/2)) + (mp.log(mp.mpf(q)/mp.pi) if k == 0 else 0)
        print("       g^(%d)(-1/2): direct=%s  via functional equation=%s" % (k, mp.nstr(gk[k], 10), mp.nstr(fe, 10)))

print("Checks for the odd character mod 3 and the even character mod 5:")
check_char([0, 1, -1], 3, 1)
check_char([0, 1, -1, -1, 1], 5, 0)

print("Zeta checks:")
M = 400
gam = [mp.im(mp.zetazero(k)) for k in range(1, M+1)]
Tm = gam[-1]
Z2z = 2*sum(1/(1+g*g) for g in gam) + mp.quad(lambda t: mp.log(t/(2*mp.pi))/mp.pi/(1+t*t), [Tm, mp.inf])
Z4z = 2*sum(1/(1+g*g)**2 for g in gam)
zl = lambda s: mp.zeta(s, derivative=1)/mp.zeta(s)
s0 = mp.mpf(3)/2
Z2 = zl(s0) + 2 - mp.log(mp.pi)/2 + mp.digamma(mp.mpf(7)/4)/2
P2 = -mp.diff(zl, s0) + 4 - mp.polygamma(1, mp.mpf(7)/4)/4
print("  (C3) Z2: zeros(+tail)=%s  Hadamard=%s ;  Z4: zeros=%s  Hadamard=%s" %
      (mp.nstr(Z2z, 8), mp.nstr(Z2, 8), mp.nstr(Z4z, 8), mp.nstr((Z2+P2)/2, 8)))
N = 300; y = mp.mpf(300.5); lam = mangoldt_table(N)
gz = lambda z: -zl(z)
gk = [gz(mp.mpf(-1)/2)] + [mp.diff(gz, mp.mpf(-1)/2, k) for k in (1, 2, 3)]
for j in (1, 2, 3):
    lhs = sum(lam[n]*mp.sqrt(n)*mp.log(y/n)**j for n in range(2, N+1))
    zsum = sum(2*mp.re(y**(1+1j*g)/(1+1j*g)**(j+1)) for g in gam)
    res = sum(mp.binomial(j, i)*mp.log(y)**i*gk[j-i] for i in range(j+1))
    triv = sum(y**(mp.mpf(1)/2-2*m)/(mp.mpf(1)/2-2*m)**(j+1) for m in range(1, 60))
    fj = mp.factorial(j)
    rhs = fj*(mp.mpf(2)/3)**(j+1)*y**1.5 - fj*zsum + res - fj*triv
    print("  (C3) A_%d(300.5): direct=%s  explicit formula=%s" % (j, mp.nstr(lhs, 12), mp.nstr(rhs, 12)))
