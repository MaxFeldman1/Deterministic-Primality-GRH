"""designB_explore.py -- the reduced LLS functional for rational kernel families (floating point; evidence
for the design choice, not part of the proof).

Reduced functional (BRIEF.md), h characters, phi(v) = Ktilde(e^v), x = X/lambda, ell = log(lambda):
    c = lambda (h-1)^2 I^2 / ( h int_{v<ell} phi e^{v/2} dv - int phi e^{v/2} dv )^2,   I = (1/2pi) int |K(it)| dt.
"""
import math, warnings
import numpy as np
from math import factorial
from scipy.integrate import quad
from scipy.optimize import minimize, minimize_scalar
warnings.filterwarnings("ignore")

def c_general(phi, I, ell, h=2, lo=-80.0, hi=0.0):
    tot = quad(lambda v: phi(v)*math.exp(v/2), lo, hi, limit=400)[0]
    ins = quad(lambda v: phi(v)*math.exp(v/2), lo, min(ell, hi), limit=400)[0]
    D = h*ins - tot
    return math.exp(ell)*(h-1)**2*I*I/D**2 if D > 0 else 1e9

print("1. Reference: Gamma kernel K(s)=Gamma(s+1/2) (LLS), h=2")
Ig = quad(lambda t: math.sqrt(math.pi/math.cosh(math.pi*t)), 0, 60)[0]/math.pi
r = minimize_scalar(lambda lam: lam*Ig**2/(1-2*math.exp(-lam))**2, bounds=(1, 5), method="bounded")
print("   I = %.6f, optimal lambda = %.4f, c_inf = %.5f" % (Ig, r.x, r.fun))

print("2. One-sided kernel with ALL its support counted (support u<1, lambda=1): c = (I/K(1/2))^2 >= 1")
print("   (Nehari/Hankel duality, see designB.md section 1; equality for K=1/(s+1/2)^2: I=1, K(1/2)=1, c=1)")

print("3. Pure powers K(s) = (k-1)!/(s+a)^k, Ktilde(u) = u^a log^{k-1}(1/u) on (0,1), support beyond X (lambda<1)")
def c_pow(k, a, ell, h=2):
    I = quad(lambda t: factorial(k-1)*(a*a+t*t)**(-k/2.0), 0, np.inf)[0]/math.pi
    return c_general(lambda v: (-v)**(k-1)*math.exp(a*v), I, ell, h)
print("   k : c_inf at a=3/4 (sigma=5/4), a=1 (sigma=3/2), a=3/2 (sigma=2) [lambda optimised] | free optimum")
for k in range(2, 9):
    row = []
    for a in (0.75, 1.0, 1.5):
        rr = minimize_scalar(lambda l: c_pow(k, a, l), bounds=(-6, 0), method="bounded")
        row.append("%.4f (lam=%.3f)" % (rr.fun, math.exp(rr.x)))
    rr = minimize(lambda p: c_pow(k, p[0], p[1]) if p[0] > 0.5 else 1e9, [0.6+0.2*k, -0.5-0.2*k], method="Nelder-Mead", options={"xatol": 1e-7, "fatol": 1e-10})
    print("   k=%d: %s | a=%.3f lam=%.3f c=%.5f %s" % (k, "  ".join(row), rr.x[0], math.exp(rr.x[1]), rr.fun,
          "<- |K(it)| rational" if k % 2 == 0 else ""))
print("   chosen: k=4, a=1, lambda=1/3: c_inf = %.6f  (optimal lambda for a=1: see row k=4)" % c_pow(4, 1.0, -math.log(3)))

print("4. The chosen kernel for index h (h characters chi^j; D_h = (2h/3) lam^{3/2} P(log 1/lam) - 32/27)")
for h in (2, 3, 4, 5, 10, 100):
    rr = minimize_scalar(lambda l: c_pow(4, 1.0, l, h), bounds=(-6, 0), method="bounded")
    print("   h=%-3d c_inf = %.4f at lambda = %.3f ;  at lambda=1/3: %.4f" % (h, rr.fun, math.exp(rr.x), c_pow(4, 1.0, -math.log(3), h)))

print("5. Beta kernels Ktilde(u) = u^beta (1-u)^k on (0,1): K(s) = k!/prod_{j=0..k}(s+beta+j)")
def c_beta(beta, k, ell):
    I = quad(lambda t: factorial(k)/math.prod(math.hypot(beta+j, t) for j in range(k+1)), 0, np.inf)[0]/math.pi
    return c_general(lambda v: math.exp(beta*v)*(1-math.exp(v))**k, I, ell)
for (beta, k) in ((0.75, 1), (1, 1), (0.75, 2), (1, 2), (1.5, 2), (1, 3), (1.5, 3), (2, 3), (1.5, 4), (2, 4), (2, 6), (3, 6)):
    rr = minimize_scalar(lambda l: c_beta(beta, k, l), bounds=(-6, 0), method="bounded")
    print("   beta=%.2f k=%d: c_inf = %.4f (lambda=%.3f)" % (beta, k, rr.fun, math.exp(rr.x)))

print("6. Polynomial numerators: phi(v) = e^{v} * sum_{j<J} theta_j v^j (v<0), K(s) = N(s)/(s+1)^J (convex programme)")
try:
    import cvxpy as cp
    T = 3000.0; nt = 40001
    t = np.sinh(np.linspace(0, np.arcsinh(T), nt)); wt = np.gradient(t); wt[0] /= 2; wt[-1] /= 2
    def solve(J, ell, a=1.0, vmax=50.0, nv=10001):
        v = -np.linspace(0, vmax, nv)[::-1]; dv = vmax/(nv-1)
        wv = np.full(nv, dv); wv[0] = wv[-1] = dv/2
        A = np.array([(-1)**j*factorial(j)/(a+1j*t)**(j+1) for j in range(1, J)]).T      # j=0 excluded (continuity at 0)
        Pm = np.array([v**j*np.exp(a*v) for j in range(1, J)]).T
        th = cp.Variable(J-1); phi = Pm@th; g = wv*np.exp(v/2); ins = v < ell
        obj = g[ins]@phi[ins] - g[~ins]@cp.abs(phi[~ins])
        pr = cp.Problem(cp.Maximize(obj), [cp.sum(cp.multiply(wt, cp.abs(A@th)))/np.pi <= 1])
        pr.solve(solver=cp.CLARABEL)
        return th.value
    def evaluate(th, ell, a=1.0):
        J = len(th)+1
        K = lambda tt: sum(th[j-1]*(-1)**j*factorial(j)/(a+1j*tt)**(j+1) for j in range(1, J))
        I = (quad(lambda tt: abs(K(tt)), 0, 30, limit=2000)[0] + quad(lambda u: abs(K(1/u))/u**2, 0, 1/30.0, limit=2000)[0])/math.pi
        phi = lambda vv: sum(th[j-1]*vv**j for j in range(1, J))*math.exp(a*vv)
        ins = quad(lambda vv: phi(vv)*math.exp(vv/2), -80, ell, limit=800)[0]
        out = quad(lambda vv: abs(phi(vv))*math.exp(vv/2), ell, 0, limit=800)[0]
        vs = np.linspace(ell, 0, 2001); mn = min(phi(x) for x in vs)
        return math.exp(ell)*I*I/(ins-out)**2, I, K, mn
    for J in (4, 5, 6, 8):
        best = None
        for ell in np.linspace(-1.6, -0.5, 12):
            th = solve(J, ell)
            if th is None: continue
            cacc, I, K, mn = evaluate(th, ell)
            if best is None or cacc < best[0]: best = (cacc, ell, th, I, K, mn)
        cacc, ell, th, I, K, mn = best
        print("   J=%d: accurate re-evaluation c_inf = %.5f at lambda=%.3f (min phi on (ell,0) = %.2e)" % (J, cacc, math.exp(ell), mn))
        # majorant LP: G(t) = sum_{k=1..M} e_k/(1+t^2)^k >= |K(it)|, minimise int G
        tg = np.concatenate([np.linspace(0, 40, 8001), np.geomspace(40, 1e5, 2000)])
        absK = np.array([abs(K(x)) for x in tg])
        for M in (J//2+1, J, J+4):
            e = cp.Variable(M)
            B = np.array([(1+tg**2)**(-k) for k in range(1, M+1)]).T
            ints = np.array([math.pi*math.comb(2*k-2, k-1)/4**(k-1) for k in range(1, M+1)])
            pr = cp.Problem(cp.Minimize(ints@e), [B@e >= absK])
            pr.solve(solver=cp.CLARABEL)
            ratio = pr.value/(2*math.pi*I)
            print("        majorant G = sum_{k<=%d} e_k/(1+t^2)^k: int G/int|K| = %.5f  -> c_inf(with G) = %.5f" % (M, ratio, cacc*ratio**2))
except ImportError:
    print("   (cvxpy not installed: skipped)")
