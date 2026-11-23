"""Reproduce the two CMQR numbers for A = 1 (index h = 2):
   primal  C(1) > 1.14600  (Table 2 test function)  ->  C^-2 < 0.7615
   dual    C(1) <= C*(1) < 1.14731 (Table 1 switching times) -> C^-2 > 0.7596
Normalisation used throughout research/barrier (v = log(n/X) = 2*pi*t_CMQR):
   phi real on R,  K(t) = int phi(v) e^{itv} dv,
   N(phi) = int_{v<0} phi e^{v/2} - int_{v>0} |phi| e^{v/2}        (A = 1)
   I(phi) = (1/2pi) int |K(t)| dt,     J = N/I,   C(1) = sup J,  c = J^-2.
"""
from mpmath import mp, mpf, mpc, quad, exp, factorial, pi, findroot, inf, fabs
mp.dps = 30

# ---------- primal: CMQR Table 2, A = 1 ----------
b = [mpf(s) for s in ['-0.0027383','0.0','4.1716','-0.6464','3.4098','1.0923','-1.4628','2.5377',
                      '0.94904','-2.5121','2.1423','-0.3164']]
c, a = mpf('0.626'), mpf('0.246')
# CMQR: hat F(t) = g((pi t - c)/a), g(y) = sum b_n y^(2n-1) e^y 1_{y<0}/(2n-1)!   (pi t = v/2)
def phi(v):
    y = (v/2 - c)/a
    if y >= 0: return mpf(0)
    return -sum(b[n]*y**(2*n+1)/factorial(2*n+1) for n in range(12))*exp(y)   # sign as in the ancillary lb.py (f_n = -e^x x^(2n-1)/(2n-1)!)
# K(t) = int phi e^{itv} dv = 2a e^{2ict} sum b_n * (-1)^(2n+1)... closed form: int_{y<0} y^k e^{y(1+i w)} dy = (-1)^k k!/(1+iw)^{k+1}, w = 2 a t
def K(t):
    w = 2*a*t
    return 2*a*sum(b[n]*(-1)/(1+1j*w)**(2*n+2) for n in range(12))   # modulus only matters (phase e^{2ict} dropped)
num = quad(lambda v: phi(v)*exp(v/2), [-inf, -40, -20, -10, -5, -2, 0]) \
    - quad(lambda v: fabs(phi(v))*exp(v/2), [0, 0.3, 0.6, 0.9, 1.0, 1.1, 1.15, 1.2, 2*c])
I = 2*quad(lambda t: abs(K(t)), [0, 1, 2, 4, 8, 16, 32, 64, 128, inf])/(2*pi)
J = num/I
print("primal (CMQR Table 2, A=1):  N = %s  I = %s  J = %s   c = J^-2 = %s" % (mp.nstr(num,12), mp.nstr(I,12), mp.nstr(J,10), mp.nstr(J**-2,10)))

# ---------- dual: CMQR Table 1, A = 1 ----------
T = [mpf(0)] + [mpf(s) for s in ['0.1509068','0.2090402','0.2318820','0.2409230','0.2629189','0.2789340','0.2820042']]
V = [2*pi*x for x in T]                       # switching points in v
# psi = e^{v/2} * s(v),  s = +1 (=A) on (V0,V1), -1 on (V1,V2), ... , 0 beyond V7
def ghat(t):
    z = mpc(0.5, t)
    r = 1/z
    for n in range(7):
        s = 1 if n % 2 == 0 else -1
        r -= s*(exp(z*V[n+1]) - exp(z*V[n]))/z
    return r
# sup_t |ghat(t)|: scan + refine
import mpmath
best = (0, 0)
ts = [mpf(k)/200 for k in range(0, 200*60)]
vals = [abs(ghat(t)) for t in ts]
loc = [(vals[i], ts[i]) for i in range(1, len(ts)-1) if vals[i] >= vals[i-1] and vals[i] >= vals[i+1]]
loc.append((vals[0], ts[0]))
loc.sort(reverse=True)
print("dual (CMQR Table 1, A=1): largest local maxima of |ghat| on [0,60): ", [(mp.nstr(x,9), mp.nstr(t,5)) for x, t in loc[:4]])
# for |t| large: |ghat| <= (1 + sum_j 2 e^{V_j/2} ) / |z|  -> < 1 beyond t = 60 trivially
bound = (1 + 2*sum(exp(v/2) for v in V[1:]))
print("   tail: |ghat(t)| <= %s/|t|  (< 1.1 for t > %s)" % (mp.nstr(bound,6), mp.nstr(bound/1.1,5)))
Cs = loc[0][0]
print("   C*(1) <= %s   =>  barrier  c >= C*^-2 = %s" % (mp.nstr(Cs,9), mp.nstr(Cs**-2,9)))
