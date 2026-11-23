"""beyond_dual.py -- the CMQR dual certificate read as a 'fake character', and what it saturates.

Variables: v = log(n/X) (CMQR's t = v/2pi), a(v) = local mean of chi(p) at p = X e^v.
Profile B(v) = a(v) e^{v/2}; a = 1 for v < 0 (hypothesis), a = -/+1 alternating on (v_i, v_{i+1}), 0 beyond v_N.
G(t) = int B(v) e^{itv} dv  (= conj of CMQR's g_1).  LP barrier: c >= 1/sup|G|^2.
Floating point (numpy); evidence, not proof.
"""
import numpy as np

T = [0.0, 0.1509068, 0.2090402, 0.2318820, 0.2409230, 0.2629189, 0.2789340, 0.2820042]  # CMQR Table, A = 1
V = [2*np.pi*x for x in T]
S = [(-1)**(j+1) for j in range(len(V)-1)]          # -1, +1, -1, ...

def G(t):
    s = 0.5 + 1j*np.asarray(t, dtype=complex)
    g = 1/s
    for j, sg in enumerate(S):
        g = g + sg*(np.exp(s*V[j+1]) - np.exp(s*V[j]))/s
    return g

if __name__ == "__main__":
    t = np.linspace(0, 200, 2_000_001)
    m = np.abs(G(t))
    M = m.max()
    print("sup|G| = %.7f at t = %.4f   (CMQR: 1.1473077 at 0)" % (M, t[m.argmax()]))
    for lo, hi in [(0.2, 0.4), (0.9, 1.2), (1.5, 200)]:
        k = (t >= lo) & (t <= hi)
        print("   max on [%.1f,%.1f]: %.5f at t=%.4f" % (lo, hi, m[k].max(), t[k][m[k].argmax()]))
    c = 1/M**2
    print("barrier c = 1/sup^2 = %.5f" % c)
    print("fake character: chi(p)=+1 for p<X, then on windows of n/X:")
    for j, sg in enumerate(S):
        print("   (%.3f, %.3f): %+d" % (np.exp(V[j]), np.exp(V[j+1]), sg))
    print("   beyond %.3f X: mean 0" % np.exp(V[-1]))
    # --- consistency with other sharp GRH theorems (all proved by the same explicit formula) ---
    I1 = sum(sg*(V[j+1]-V[j]) for j, sg in enumerate(S))
    print("\nL(1,chi): fake gives e^gamma (log log^2 q + log c + I1), I1 = int a dv over v>0 = %.4f" % I1)
    print("   log c + I1 = %.4f  vs LLS Thm 1.5 ceiling 1 - 2 log 2 = %.4f  -> %s" %
          (np.log(c)+I1, 1-2*np.log(2), "satisfied" if np.log(c)+I1 <= 1-2*np.log(2) else "VIOLATED"))
    print("   (if chi(p) were 0-mean right above X, L(1) alone would force c <= e/4 = %.4f)" % (np.e/4))
    print("phase at t=0: G(0) = %.5f > 0  => rho(0) = -G/M = -1: zero clusters at t = +-pi/L, +-3pi/L, ... (L = log X ~ 2 loglog q)" % G(0).real)
    print("   cluster size  = log q / L          = (1/2) log q/loglog q   [= Goldston-Gonek multiplicity ceiling]")
    print("   S(t) sawtooth = +-(1/2) cluster    = (1/4) log q/loglog q   [= Carneiro-Chandee-Milinovich ceiling]")
    print("   lowest zero   = pi/L               = (pi/2)/loglog q,  gap = pi/loglog q  [= known gap ceiling]")
    print("   |L(1/2+it)| between clusters ~ 2^(log q/L) = exp((log2/2) log q/loglog q)  [= Chandee-Soundararajan ceiling]")
