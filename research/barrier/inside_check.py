"""Independent floating-point sanity check (mpmath quadrature, no use of the closed forms of the certificate)
of the identities of Lemma 1 for the test function in inside_testfn.json, and of J(phi)."""
import json
from mpmath import mp, mpf, mpc, quad, exp, laguerre, pi, inf, fabs, nstr
mp.dps = 30
d = json.load(open("inside_testfn.json")); beta, c, D = mpf(d["beta"]), mpf(d["c"]), d["D"]; q = [mpf(s) for s in d["q"]]
def Phi(y): return sum(q[n]*(-1)**n/(n+1)*(-y)*exp(y)*laguerre(n, 1, -2*y) for n in range(D+1)) if y < 0 else mpf(0)
def phi(v): return Phi(beta*(v-c))
pts = [-inf, -30, -15, -8, -4, -2, -1, 0, 0.5, 0.964972, 1.396047, 1.737286, 2]
for t in [mpf(0), mpf('0.7'), mpf(3), mpf(11)]:
    Kd = quad(lambda v: phi(v)*exp(1j*t*v), pts)
    u = 1/(1+1j*t/beta); z = 2*u-1
    Kc = exp(1j*t*c)/beta*u**2*sum(q[n]*z**n for n in range(D+1))
    print("t=%5s  K by quadrature %s   closed form %s   |diff| = %s" % (nstr(t,3), nstr(Kd,12), nstr(Kc,12), nstr(abs(Kd-Kc),3)))
Nd = quad(lambda v: phi(v)*exp(v/2), pts[:8]) - quad(lambda v: fabs(phi(v))*exp(v/2), pts[7:])
Id = 2*quad(lambda t: abs(sum(q[n]*((1-1j*t/beta)/(1+1j*t/beta))**n for n in range(D+1))/(1+1j*t/beta)**2)/beta, [0, 0.5, 1, 2, 4, 8, 16, 32, 64, 128, 256, 1024, inf])/(2*pi)
print("N = %s   I = (1/2pi) int |K| dt = %s   J = %s   J^-2 = %s" % (nstr(Nd,12), nstr(Id,12), nstr(Nd/Id,10), nstr((Nd/Id)**-2,9)))
print("phi(0) = %s, phi(c-) = %s, sample values phi(0.5), phi(1.2), phi(1.6), phi(1.9) = %s" % (nstr(phi(mpf(0)),8), nstr(phi(c-mpf(10)**-20),3), [nstr(phi(mpf(x)),6) for x in ('0.5','1.2','1.6','1.9')]))
