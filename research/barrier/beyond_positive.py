"""beyond_positive.py -- ideas (b),(c): can positivity of the zero measure / multi-scale quadratic forms beat the barrier?

Claim tested: the dual certificate (profile a(v), |G| <= M) is realised by a POSITIVE even 'zero measure'
   nu(t) = D * (1-|w|^2)/|1-w|^2,   w(t) = rho(t) e^{-itL},  rho = -conj(G(t))/M',  D = log q/2pi,  L = log X,
(a Poisson kernel in the fast phase tL), i.e. for EVERY test function phi
   prime side  P(phi)/log q = sqrt(c) * int a(v) e^{v/2} phi(v) dv ,            c = 1/M'^2,
   zero  side  Z(phi)/log q = -(1/2pi) int phihat(t) e^{itL} (nu(t)/D - 1) dt   (the '1' is the conductor term)
agree up to terms that vanish as L -> infinity (harmonics k>=2 live at n ~ X^k where they cost a relative
bias O(L/log q) in chi(p)).  So every linear, quadratic or SDP inequality that follows from
{nu >= 0, mean density log q/2pi, |chi(p)| <= 1, chi(p) = 1 for p < X} holds for this pair: no gain.
M' = 1.02 M is used so that |w| < 1 (smooth density; M' = M is the delta-comb limit).
"""
import numpy as np
from beyond_dual import G

M = 1.1473077
def check(L, Mp, phis):
    dt = 2e-4
    t = np.arange(-80, 80, dt)
    Gt = G(t)
    rho = -np.conj(Gt)/Mp
    w = rho*np.exp(-1j*t*L)
    dens = (1-np.abs(w)**2)/np.abs(1-w)**2          # nu/D >= 0
    v = np.linspace(-60, 12, 720001); dv = v[1]-v[0]
    from beyond_dual import V, S
    a = np.where(v < 0, 1.0, 0.0)
    for j, sg in enumerate(S):
        a = np.where((v >= V[j]) & (v < V[j+1]), sg, a)
    out = []
    for name, phi, phihat in phis:
        P = (1/Mp)*np.sum(a*np.exp(v/2)*phi(v))*dv
        Z = -(1/(2*np.pi))*np.sum(phihat(t)*np.exp(1j*t*L)*(dens-1))*dt
        Z1 = -(1/(2*np.pi))*np.sum(phihat(t)*np.exp(1j*t*L)*(2*np.real(w)))*dt   # first harmonic only
        out.append((name, P, Z.real, Z1.real))
    return dens.min(), dens.max(), out

def gauss(mu, s):
    return ("gauss(mu=%.1f,s=%.1f)" % (mu, s),
            lambda v: np.exp(-(v-mu)**2/(2*s*s)),
            lambda t: s*np.sqrt(2*np.pi)*np.exp(-s*s*t*t/2 + 1j*t*mu))

if __name__ == "__main__":
    phis = [gauss(0.0, 0.5), gauss(0.8, 0.3), gauss(-1.0, 1.0), gauss(1.5, 0.4)]
    for L in (20.0, 40.0, 80.0):
        mn, mx, out = check(L, 1.02*M, phis)
        print("L = log X = %g:  min nu/D = %.3e (>= 0), max nu/D = %.1f" % (L, mn, mx))
        for name, P, Z, Z1 in out:
            print("   %-22s prime side %+.6f   zero side (positive nu) %+.6f   [1st harmonic only %+.6f]" % (name, P, Z, Z1))
