"""beyond_smooth.py -- idea (e): Vinogradov / smooth numbers under GRH at the scale X ~ log^2 q.

(1) The sharpest GRH bound for sums over ALL integers,  |sum chi(n) w(n/y)| <= y^sigma max|L(sigma+it)| int|W|,
    with log|L(sigma+it,chi)| <= sum_{p<=z} p^{-sigma} (z = z_eff ~ log^2 q), optimised over sigma = 1 - w/log z,
    y = z^u, has exponent  min_w [-u w + E(w)],  E(w) = int_0^w (e^s-1)/s ds  -- the de Bruijn saddle point for
    Dickman's rho(u).  So GRH gives exactly "sum <= Psi(y, z_eff) * slop", never o(Psi).   Table (1) checks this.
(2) Sensitivity to the constant c in X = c log^2 q:  Psi(y, cz)/Psi(y, z) ~ exp(u xi(u) log c / log z).
    It beats a slop factor F only if u xi(u) |log c| > log F * log z.   Table (2).
(3) What the lower bound really is.  For completely multiplicative f = 1 on X-smooth n with f(p) of local mean
    a(v) at p = X e^v, the saddle exponent is that of Psi(y, X_eff) with log X_eff = log X + int a(v) dv:
    non-residues just above X lower X_eff.  The comparison "Psi(y,X_eff) <= Psi(y,z_eff)" is then
        log c + I1 <= log c_eff     (c_eff = e/4 at sigma -> 1: this is the LLS L(1,chi) bound),
    a LINEAR constraint on prime data, already inside the LP.  Table (3): the CMQR fake passes it.
"""
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq

def E(w): return quad(lambda s: np.expm1(s)/s if s else 1.0, 0, w)[0]
def xi(u): return brentq(lambda w: np.expm1(w)/w - u, 1e-12, 50) if u > 1 else 0.0

def dickman(umax, h=1e-3):
    n = int(round(umax/h)); u = np.arange(n+1)*h; r = np.ones(n+1); k = int(round(1/h))
    # u rho'(u) = -rho(u-1)  ->  rho(u) = (1/u) int_{u-1}^u rho  (trapezoid, implicit in rho(u))
    cs = np.zeros(n+1)
    for i in range(1, n+1):
        if i <= k:
            r[i] = 1.0
        else:
            r[i] = (cs[i-1] - cs[i-k] + 0.5*h*r[i-1]) / (u[i] - 0.5*h)
        cs[i] = cs[i-1] + 0.5*h*(r[i]+r[i-1])
    return u, r

if __name__ == "__main__":
    u, r = dickman(12.0)
    print("(1) u   rho(u)        exp(-u xi + E(xi))   ratio   [saddle exponent of the GRH Perron bound = Dickman]")
    for U in (2, 3, 5, 8, 12):
        x = xi(U); rho = r[int(round(U/1e-3))]; sd = np.exp(-U*x + E(x))
        print("    %-3d %.4e    %.4e           %.2f   (ratio ~ sqrt(2 pi u)/e^gamma-type polynomial factor)" % (U, rho, sd, sd/rho))
    print("\n    threshold: Psi(y, log^2 q) = y^{1/2+o(1)} for y = q^eps  (u = eps log q/(2 loglog q)); numerically")
    for lq in (1e2, 1e4, 1e8):
        z = lq**2; eps = 0.1; U = eps*lq/np.log(z); x = xi(U)
        print("      log q = %.0e: log Psi/log y ~ 1 + (-u xi + E(xi))/(u log z) = %.3f" % (lq, 1 + (-U*x + E(x))/(U*np.log(z))))
    print("\n(2) factor gained from c: exp(u xi(u) |log c| / log z), c = 0.76 vs 1, log z = 2 loglog q")
    for lq in (1e3, 1e6, 1e12):
        lz = 2*np.log(lq)
        print("    log q = %.0e (log z = %.1f): " % (lq, lz) + ", ".join("u=%d: %.3f" % (U, np.exp(U*xi(U)*abs(np.log(0.76))/lz)) for U in (2, 5, 20, 100)))
    print("    -> O(1/loglog q) effect for bounded u; needs u >> loglog q, where the bound's slop (powers of log z per unit of xi) is larger still")
    from beyond_dual import V, S, G
    I1 = sum(sg*(V[j+1]-V[j]) for j, sg in enumerate(S)); c = 1/abs(G(0.0))**2
    print("\n(3) effective smoothness of the CMQR fake: X_eff = X e^{I1} = %.4f log^2 q   (c = %.4f, I1 = %.4f)" % (c*np.exp(I1), c, I1))
    print("    GRH ceiling at sigma -> 1 (LLS L(1,chi)): z_eff = (e/4) log^2 q = %.4f log^2 q   -> no contradiction" % (np.e/4))
    print("    naive Vinogradov hope (pretend chi has mean >= 0 just above X): c <= e/4 = %.4f < 0.7596 -- NOT available" % (np.e/4))
