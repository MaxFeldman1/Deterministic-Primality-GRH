"""Primal problem (EP1, A = 1) on the 'Hardy/Laguerre' family
     phi(v) = Phi(beta (v - c)),  Phi(y) = sum_{n=0}^{D} q_n Phi_n(y) 1_{y<0},
     Phi_n(y) = (-1)^n/(n+1) * (-y) e^{y} L_n^{(1)}(-2y)     <->   int Phi_n e^{iwy} dy = u^2 z^n,
     u = 1/(1+iw),  z = 2u - 1 = (1-iw)/(1+iw)  (|z| = 1 for real w).
   With q(z) = sum q_n z^n:
     I(phi) = (1/2pi) int |K| dt = (1/2) * mean_{|z|=1} |q(z)|          (an H^1 norm)
     int phi e^{v/2} dv = (e^{c/2}/beta) u0^2 q(z0),  u0 = 2beta/(2beta+1), z0 = (2beta-1)/(2beta+1)
     N(phi) = int phi e^{v/2} dv - 2 int_0^c phi_+ e^{v/2} dv .
   For fixed (beta, c, D): maximise N subject to I <= 1 -- an SOCP (floating point, Clarabel).
   CMQR's Table 2 function is in this family with beta = 1/(2a) = 2.0325, c = 1.252, D = 22."""
import sys, numpy as np, cvxpy as cp
from scipy.special import eval_genlaguerre
from numpy.polynomial.legendre import leggauss

def basis(y, D):
    """matrix [Phi_n(y_i)] for y<0"""
    y = np.asarray(y, float)
    return np.stack([(-1)**n/(n+1.0)*(-y)*np.exp(y)*eval_genlaguerre(n, 1, -2*y) for n in range(D+1)], axis=1)

def setup(beta, c, D, M=4000, panels=60, gl=8):
    th = (np.arange(M)+0.5)*np.pi/M                      # half circle (q real => |q| symmetric)
    Z = np.exp(-1j*np.outer(th, np.arange(D+1)))
    u0 = 2*beta/(2*beta+1); z0 = (2*beta-1)/(2*beta+1)
    lin = np.exp(c/2)/beta*u0**2*z0**np.arange(D+1)
    x, w = leggauss(gl)
    ed = np.linspace(0, c, panels+1)
    v = np.concatenate([(ed[i]+ed[i+1])/2 + (ed[i+1]-ed[i])/2*x for i in range(panels)])
    wv = np.concatenate([(ed[i+1]-ed[i])/2*w for i in range(panels)])
    B = basis(beta*(v-c), D)
    return th, Z, lin, v, wv*np.exp(v/2), B

def solve(beta, c, D, M=4000, panels=60, gl=8, verbose=False):
    th, Z, lin, v, wv, B = setup(beta, c, D, M, panels, gl)
    q = cp.Variable(D+1); p = cp.Variable(len(v), nonneg=True)
    cons = [p >= B @ q, cp.sum(cp.abs(Z @ q))/len(th)/2 <= 1]
    prob = cp.Problem(cp.Maximize(lin @ q - 2*(wv @ p)), cons)
    prob.solve(solver=cp.CLARABEL, verbose=verbose)
    return prob.value, q.value

def evaluate(beta, c, qv, M=200000, panels=4000, gl=8):
    """accurate floating re-evaluation of J for given coefficients"""
    D = len(qv)-1
    th, Z, lin, v, wv, B = setup(beta, c, D, 1, panels, gl)
    th = (np.arange(M)+0.5)*np.pi/M
    val = np.polynomial.polynomial.polyval(np.exp(-1j*th), qv)
    I = np.mean(np.abs(val))/2
    N = lin @ qv - 2*(wv @ np.maximum(B @ qv, 0))
    return N/I, N, I

if __name__ == "__main__":
    beta = float(sys.argv[1]); c = float(sys.argv[2]); D = int(sys.argv[3])
    val, qv = solve(beta, c, D)
    J, N, I = evaluate(beta, c, qv)
    print("beta=%g c=%g D=%d: SOCP %.7f ; re-evaluated J = %.7f (N=%.6f I=%.6f)  c_inf = %.6f" % (beta, c, D, val, J, N, I, J**-2))
    print(" q =", np.array2string(qv, precision=6, max_line_width=150))
