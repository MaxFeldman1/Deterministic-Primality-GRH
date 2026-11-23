"""Floating-point exploration for formal076.md (needs numpy/scipy/cvxpy+clarabel; run inside research/barrier).
   Notation of inside.md (Hardy/Laguerre family, pole beta, support v < c = ell, K = e^{itc} u^2 q(z)/beta).
   Family (E) "exact modulus":  q = r(z) r#(z), r# = r with some zeros reflected in the unit circle; then
   |q| = |r|^2 on |z| = 1,  I = (1/2) sum r_n^2 (Parseval), |K(it)| is an even rational function with poles +-i beta only.
     design A: q = r^2, r = (1+z) r1          (K = H^2; phi >= 0 on (0,c));  for a fixed sign pattern N is a quadratic
               form in r, so the optimum is the top eigenvalue of a Hankel matrix (a Nehari problem).
     design B: q = (1+z)^2 r0^2 (z-alpha)(1-alpha z)    (one real zero of K in Re s > 0; one sign change of phi on (0,c)).
   usage: formal076_family.py conv | A | B ell d0 [d0 ...]"""
import sys, os, numpy as np, scipy.linalg as sl
from scipy.optimize import minimize
HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,HERE)
from inside_primal_socp import setup, evaluate, basis
cv=np.convolve; P=np.polynomial.polynomial

def solve_convex(beta,c,D,pos=True,div=2,M=3000,panels=60,gl=8):
    """convex optimum over all q of degree D with (1+z)^div | q; pos: phi >= 0 on (0,c), else -|phi|"""
    import cvxpy as cp
    th,Z,lin,v,wv,B = setup(beta,c,D,M,panels,gl)
    q = cp.Variable(D+1); n=np.arange(D+1)
    cons=[cp.sum(cp.abs(Z@q))/len(th)/2<=1]
    if div>=1: cons.append(((-1.0)**n)@q==0)
    if div>=2: cons.append((n*(-1.0)**n)@q==0)
    if pos: cons.append(B@q>=0); obj = lin@q - 2*(wv@(B@q))
    else:
        p=cp.Variable(len(v),nonneg=True); cons.append(p>=B@q); obj = lin@q-2*(wv@p)
    pr=cp.Problem(cp.Maximize(obj),cons); pr.solve(solver=cp.CLARABEL)
    return pr.value,q.value

def designA(beta,c,d):
    th,Z,lin,v,wv,B = setup(beta,c,2*d,1,400,8)
    l = lin-(2*wv)@B
    T=np.zeros((d+1,d))
    for j in range(d): T[j,j]=1; T[j+1,j]=1
    A=T.T@np.array([[l[i+j] for j in range(d+1)] for i in range(d+1)])@T; G=T.T@T/2
    w,V=sl.eigh(A,G); r=T@V[:,-1]; q=cv(r,r)
    J,N,I=evaluate(beta,c,q,M=20000,panels=2000)
    return N/(np.sum(r**2)/2), w[-1], r

def outer_sqrt(q, n=4096):
    th = 2*np.pi*np.arange(n)/n; zc = np.exp(1j*th)
    lq = np.log(np.abs(P.polyval(zc,q))+1e-300)/2
    ck = np.fft.fft(lq)/n
    co = np.zeros(n,complex); co[0]=ck[0]; co[1:n//2]=2*ck[1:n//2]
    return zc, np.exp(np.fft.ifft(co)*n)

class FamB:
    def __init__(s,beta,c,d0,panels=200):
        s.beta,s.c,s.d0=beta,c,d0
        th,Z,s.lin,s.v,s.wv,s.B = setup(beta,c,2*d0+4,1,panels,8)
    def rr(s,x):
        b=cv([1,1],x[:-1]); al=x[-1]
        return cv(b,[-al,1]), cv(b,[1,-al])
    def J(s,x):
        r,rs=s.rr(x); q=cv(r,rs)
        return (s.lin@q - 2*(s.wv@np.maximum(s.B@q,0)))/(np.sum(r**2)/2)

def polish(F,x,rounds=8):
    best=x.copy(); fb=F(best)
    for it in range(rounds):
        imp=False
        for meth,opt in [('BFGS',{'gtol':1e-11,'maxiter':5000}),('Powell',{'xtol':1e-11,'ftol':1e-14,'maxiter':20000})]:
            res=minimize(lambda y:-F(y),best,method=meth,options=opt)
            if -res.fun>fb+1e-10: best,fb,imp=res.x,-res.fun,True
        if not imp: break
    return best,fb

def designB(beta,c,d0,prev=None,Dc=50,seed=1):
    """local optimisation started from the outer square root of the convex optimum"""
    val,qo = solve_convex(beta,c,Dc,pos=False,div=2)
    rts=np.roots(qo[::-1]); ins=rts[(np.abs(rts)<0.97)]
    al = float(np.real(ins[np.argmin(np.abs(ins.imag))])) if len(ins) else -0.8
    zc,ro = outer_sqrt(qo)
    base = (1+zc)*(1-al*zc)
    Am = np.stack([base*zc**k for k in range(d0+1)],axis=1)
    r0 = np.linalg.lstsq(np.vstack([Am.real,Am.imag]),np.concatenate([ro.real,ro.imag]),rcond=None)[0]
    F=FamB(beta,c,d0); x=np.append(r0,al); rng=np.random.default_rng(seed)
    cands=[x]+[x*(1+0.02*rng.standard_normal(len(x))) for k in range(3)]
    if prev is not None: cands.append(np.concatenate([prev[:-1],np.zeros(d0+1-len(prev[:-1])),[prev[-1]]]))
    best=None; fb=-1
    for cnd in cands:
        y,fy=polish(F.J,cnd)
        if fy>fb: best,fb=y,fy
    r,rs=F.rr(best); q=cv(r,rs); J,N,I=evaluate(beta,c,q,M=20000,panels=2000)
    return N/(np.sum(r**2)/2), best

if __name__=="__main__":
    import warnings; warnings.filterwarnings("ignore")
    mode=sys.argv[1]
    if mode=="conv":
        print("convex optimum (all q, (1+z)^2 | q, beta = 1): c_inf for phi >= 0 on (0,c) ['pos'] and with -|phi| ['abs']; zeros of q in |z| < 0.97")
        for c,D in [(np.log(3),70),(1.375,70),(np.log(4),80),(np.log(6),60),(2.0,80)]:
            for pos in [True,False]:
                val,qv=solve_convex(1.0,c,D,pos); J,N,I=evaluate(1.0,c,qv)
                r=np.roots(qv[::-1]); ins=r[np.abs(r)<0.97]
                print("  c=%.4f D=%d %s: c_inf = %.6f   zeros in disc: %s"%(c,D,'pos' if pos else 'abs',J**-2,np.round(ins,3)),flush=True)
    elif mode=="A":
        print("design A (K = H^2, x = 3X, c = log 3): c* as a function of beta and d = deg r (m = d+1, pole order 2m)")
        for beta in [1,1.5,2,2.5,3]:
            print("  beta=%.1f: "%beta+"  ".join("d=%d: %.6f"%(d,designA(beta,np.log(3),d)[0]**-2) for d in [4,6,8,10,12,14,16,20]),flush=True)
        print("  beta=1, c=11/10: "+"  ".join("d=%d: %.6f"%(d,designA(1.0,1.1,d)[0]**-2) for d in [10,12,13,14,15,16,18,20]),flush=True)
    else:
        c=float(sys.argv[2]); prev=None
        print("design B (K = (Z-(s-1)^2) H0^2, beta = 1, c = ell = %g): c* as a function of d0 = deg r0 (m = d0+3)"%c)
        for d0 in [int(a) for a in sys.argv[3:]]:
            J,x=designB(1.0,c,d0,prev); prev=x
            np.save(os.path.join(HERE,"formal076_initB_%g_%d.npy"%(c,d0)),x)
            print("  d0=%2d m=%2d: c* = %.6f  alpha = %.5f (zero of K at s_in = %.3f)"%(d0,d0+3,J**-2,x[-1],(1-x[-1])/(1+x[-1])),flush=True)
