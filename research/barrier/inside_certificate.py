"""RIGOROUS certificate for  J(phi) >= J_lo  (hence, by CMQR Theorem 3 with ell = 2,
limsup n_chi / log^2 q <= C(1)^-2 <= J(phi)^-2 <= J_lo^-2) for the explicit test function of inside_testfn.json.

Dependencies: Python stdlib (fractions) + mpmath interval arithmetic (mpmath.iv).  No floating-point value is
trusted: every number is an exact rational or an mpmath interval; the only floats are root *guesses*, which are
then verified exactly.

Test function (beta, c, q_0..q_D rational):
   phi(v) = Phi(beta (v - c)) for v < c, 0 for v >= c,     Phi(y) = (-y) e^{y} R(y),
   R(y)   = sum_n q_n (-1)^n/(n+1) * L_n^{(1)}(-2y) = sum_n q_n (-1)^n/(n+1) sum_{k<=n} C(n+1, n-k) (2y)^k / k!
Facts used (inside.md, Lemma 1):
   (i)   K(t) := int phi(v) e^{itv} dv = (e^{itc}/beta) u^2 q(z),  u = 1/(1+it/beta), z = 2u-1, q(z) = sum q_n z^n;
         I(phi) := (1/2pi) int |K| dt = (1/2pi) int_0^pi |q(e^{i theta})| d theta.
   (ii)  int phi(v) e^{v/2} dv = (e^{c/2}/beta) u0^2 q(z0),  u0 = 2beta/(2beta+1), z0 = (2beta-1)/(2beta+1).
   (iii) N(phi) := int_{v<0} phi e^{v/2} - int_{v>0} |phi| e^{v/2} = int phi e^{v/2} - 2 int_0^c phi_+ e^{v/2} dv
         and int_0^c phi_+ e^{v/2} dv = (e^{c/2}/beta) int_{-beta c}^0 [(-y) R(y)]_+ e^{kappa y} dy, kappa = 1 + 1/(2 beta).
Steps:
   A. exact R; all roots of R in (-beta c, 0) isolated: Sturm count (exact) = number of verified sign changes.
   B. upper bound for T2 = int [(-y)R]_+ e^{kappa y}: exact antiderivative on the intervals where R > 0.
   C. upper bound for I by Cauchy-Schwarz on M cells: int_cell |q| <= sqrt(h * int_cell |q|^2), the latter
      integral being an explicit trigonometric antiderivative.
"""
import json, sys, time
from fractions import Fraction as Fr
from math import comb, factorial
from mpmath import iv, mp, mpf
import mpmath
iv.prec = 260; mp.prec = 400
M_CELLS = int(sys.argv[1]) if len(sys.argv) > 1 else 40000

d = json.load(open("inside_testfn.json"))
beta, c, D = Fr(d["beta"]), Fr(d["c"]), d["D"]
q = [Fr(s) for s in d["q"]]
assert len(q) == D+1

# ---------- polynomial helpers (exact, coefficient lists low -> high) ----------
def pev(P, x):
    r = Fr(0)
    for a in reversed(P): r = r*x + a
    return r
def pder(P): return [k*P[k] for k in range(1, len(P))] or [Fr(0)]
def pstrip(P):
    P = list(P)
    while len(P) > 1 and P[-1] == 0: P.pop()
    return P
def prem(A, B):                       # remainder of A mod B over Q
    A = pstrip(A); B = pstrip(B); db = len(B)-1
    assert B != [0]
    while len(A)-1 >= db and A != [0]:
        f = A[-1]/B[-1]; s = len(A)-1-db
        for i in range(db+1): A[s+i] -= f*B[i]
        assert A[-1] == 0
        A = pstrip(A[:-1] or [Fr(0)])
    return A
def sturm_chain(P):
    ch = [pstrip(P), pstrip(pder(P))]
    while len(ch[-1]) > 1:
        r = prem(ch[-2], ch[-1])
        if r == [0]: break
        ch.append([-a for a in r])
    return ch
def sign_changes(ch, x):
    s = [pev(P, x) for P in ch]; s = [v for v in s if v != 0]
    return sum(1 for i in range(len(s)-1) if (s[i] > 0) != (s[i+1] > 0))
def to_iv(x):                         # exact rational -> interval enclosure
    return iv.mpf(x.numerator)/iv.mpf(x.denominator)

# ---------- A. exact R and its roots in (-beta c, 0) ----------
R = [Fr(0)]*(D+1)
for n in range(D+1):
    cn = q[n]*(-1)**n/Fr(n+1)
    for k in range(n+1):
        R[k] += cn*comb(n+1, n-k)*Fr(2**k, factorial(k))
a_end, b_end = -beta*c, Fr(0)
assert pev(R, a_end) != 0 and pev(R, b_end) != 0
t0 = time.time()
ch = sturm_chain(R)
gcd_const = (len(ch[-1]) == 1)        # R squarefree  <=> last element is a non-zero constant
nroots = sign_changes(ch, a_end) - sign_changes(ch, b_end)
print("A. deg R = %d, R squarefree: %s, Sturm: number of distinct roots of R in (-beta c, 0) = %d   [%.1fs]" % (len(pstrip(R))-1, gcd_const, nroots, time.time()-t0))
guess = mpmath.polyroots([mpf(a.numerator)/mpf(a.denominator) for a in reversed(R)], maxsteps=2000, extraprec=2000)
guess = sorted(mpmath.re(z) for z in guess if abs(mpmath.im(z)) < mpf(10)**-30 and float(a_end) < mpmath.re(z) < 0)
eps = Fr(1, 10**45)
iso = []
for g in guess:
    gr = Fr(int(mpmath.floor(g*mpf(10)**50)), 10**50)
    lo, hi = gr-eps, gr+eps
    assert a_end < lo and hi < 0
    assert pev(R, lo)*pev(R, hi) < 0, "no sign change at root guess"
    iso.append((lo, hi))
assert all(iso[i][1] < iso[i+1][0] for i in range(len(iso)-1))
assert len(iso) == nroots, "root isolation incomplete"
print("   isolated %d roots (each in an interval of width 2e-45, exact sign change verified):" % len(iso))
print("   y_i =", [float(lo) for lo, hi in iso], " i.e. v_i = c + y_i/beta =", [round(float(c+lo/beta), 6) for lo, hi in iso])
# sign of R on each gap (constant there since all roots are inside the isolating intervals)
pts = [a_end] + [x for lohi in iso for x in lohi] + [b_end]
gaps = [(pts[2*i], pts[2*i+1]) for i in range(len(iso)+1)]            # [a, lo_1], [hi_1, lo_2], ..., [hi_m, 0]
gsign = [1 if pev(R, (g[0]+g[1])/2) > 0 else -1 for g in gaps]
assert all(gsign[i] != gsign[i+1] for i in range(len(gsign)-1))
print("   sign of phi on (0,c) between consecutive roots (from v = 0 upwards):", gsign)

# ---------- B. T2 = int_{-beta c}^0 [(-y) R(y)]_+ e^{kappa y} dy ----------
kappa = 1 + 1/(2*beta)
G = [Fr(0)] + [-a for a in R]                                        # G(y) = -y R(y)
Wp = [Fr(0)]*len(G); Dj = list(G); j = 0                             # W(y) = e^{kappa y} * Wp(y),  W' = G e^{kappa y}
while any(Dj):
    for i, a in enumerate(Dj): Wp[i] += (-1)**j*a/kappa**(j+1)
    Dj = pder(Dj); j += 1
# exact check that (Wp' + kappa Wp) = G
chk = [ (pder(Wp)[i] if i < len(Wp)-1 else 0) + kappa*Wp[i] for i in range(len(Wp))]
assert chk == G
def W_iv(x):                          # enclosure of W at an exact rational point
    return to_iv(pev(Wp, x))*iv.exp(to_iv(kappa*x))
T2 = iv.mpf(0)
for (ga, gb), s in zip(gaps, gsign):
    if s > 0: T2 += W_iv(gb) - W_iv(ga)                              # exact integral over a sub-interval where G >= 0 ... 
# ... plus the isolating intervals themselves (width 2e-45): |G e^{kappa y}| <= sum |G_k| (beta c)^k there
Gabs = sum(abs(a)*(beta*c)**k for k, a in enumerate(G))
T2 += iv.mpf([0, 1])*to_iv(Gabs*2*eps*len(iso))
T2_hi = T2.b
print("B. T2 = int [(-y)R]_+ e^{kappa y} dy  in  [%s, %s]" % (mpmath.nstr(mpf(T2.a), 15), mpmath.nstr(mpf(T2.b), 15)))
u0 = 2*beta/(2*beta+1); z0 = (2*beta-1)/(2*beta+1)
T1 = u0**2*pev(q, z0)                                                # exact rational
pref = iv.exp(to_iv(c/2))/to_iv(beta)
N = pref*(to_iv(T1) - 2*T2)
print("   T1 = u0^2 q(z0) = %.15f (exact rational);   N(phi) in [%s, %s]" % (float(T1), mpmath.nstr(mpf(N.a), 15), mpmath.nstr(mpf(N.b), 15)))

# ---------- C. I = (1/2pi) int_0^pi |q(e^{i theta})| d theta ----------
r = [sum(q[n]*q[n+k] for n in range(D+1-k))*(1 if k == 0 else 2) for k in range(D+1)]   # |q|^2 = r0 + sum r_k cos k theta
r_iv = [to_iv(x) for x in r]
t0 = time.time()
iv.prec = 120
pi_iv = iv.pi
def Aprim(i):                         # enclosure of int_0^{theta_i} |q|^2, theta_i = i pi / M
    th = pi_iv*i/M_CELLS
    # sin(k th) via Chebyshev recurrence s_{k+1} = 2 cos(th) s_k - s_{k-1}  (interval arithmetic => still an enclosure)
    cth, s_prev, s_cur = iv.cos(th), iv.mpf(0), iv.sin(th)
    tot = r_iv[0]*th
    for k in range(1, D+1):
        tot += r_iv[k]*s_cur/k
        s_prev, s_cur = s_cur, 2*cth*s_cur - s_prev
    return tot
h_iv = pi_iv/M_CELLS
S = iv.mpf(0); prev = Aprim(0); worst = 0
for i in range(1, M_CELLS+1):
    cur = Aprim(i)
    Gi = cur - prev
    Gi_hi = Gi.b if Gi.b > 0 else mpf(0)
    S += iv.sqrt(h_iv*iv.mpf(Gi_hi))                                # >= int_cell |q|   (Cauchy-Schwarz)
    worst = max(worst, float(mpf(Gi.b) - mpf(Gi.a)))
    prev = cur
I_iv = S/(2*pi_iv)
I_hi = I_iv.b
print("C. I(phi) <= %s   (M = %d cells, widest enclosure of a cell integral %.1e)   [%.1fs]" % (mpmath.nstr(mpf(I_hi), 15), M_CELLS, worst, time.time()-t0))

# ---------- conclusion ----------
iv.prec = 260
J_lo = (iv.mpf(N.a)/iv.mpf(I_hi)).a
c_hi = (1/(iv.mpf(J_lo)**2)).b
print("RESULT:  J(phi) >= %s   =>   C(1) >= %s   and   limsup n_chi/log^2 q <= %s" % (mpmath.nstr(mpf(J_lo), 12), mpmath.nstr(mpf(J_lo), 9), mpmath.nstr(mpf(c_hi), 9)))
assert J_lo > mpf("1.1465") and c_hi < mpf("0.76077")
print("CERTIFIED:  C(1) > 1.1465,   c_inf <= C(1)^-2 < 0.76077 < 0.7615")
