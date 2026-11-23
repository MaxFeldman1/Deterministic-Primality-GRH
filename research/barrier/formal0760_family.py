"""formal0760: family (E_p) with p reflected zeros, any single pole beta (floating point; numpy/scipy/cvxpy+clarabel).
   Notation of inside.md: q(z) = (1+z)^2 r0(z)^2 F(z) F#(z),  F monic real of degree p (zeros of K in Re s_in > 0),
   F#(z) = z^p F(1/z);  |q| = |(1+z) r0 F|^2 on |z| = 1, so I = (1/2) ||(1+z) r0 F||^2 (Parseval) and
   K = Q(s_in^2) H0(s_in)^2, H0 = u^(p+2) r0(z), pole of H0 of order m = d0 + p + 2 at s_in = -beta, Q(-t^2) >= 0.
   Objective: true N (with -|phi| on (0,c)) by Gauss quadrature, analytic gradient, L-BFGS from the outer square root
   of the convex optimum.   usage: formal0760_family.py conv | scan | scan2 | one beta c p d0   (outputs: formal0760_convex.out, formal0760_family.out, formal0760_family2.out)"""
import sys, os, numpy as np, warnings; warnings.filterwarnings("ignore")
from scipy.optimize import minimize
HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,HERE)
from inside_primal_socp import setup, evaluate
cv=np.convolve; P=np.polynomial.polynomial
_conv={}
def convex(beta,c,Dc=64):
    from formal076_family import solve_convex
    k=(beta,c,Dc)
    if k not in _conv: _conv[k]=solve_convex(beta,c,Dc,pos=False,div=2)
    return _conv[k]
def outer_sqrt(q,n=8192):
    th=2*np.pi*np.arange(n)/n; zc=np.exp(1j*th)
    lq=np.log(np.abs(P.polyval(zc,q))+1e-300)/2; ck=np.fft.fft(lq)/n
    co=np.zeros(n,complex); co[0]=ck[0]; co[1:n//2]=2*ck[1:n//2]
    return zc,np.exp(np.fft.ifft(co)*n)
class Fam:
    def __init__(s,beta,c,p,d0,panels=240):
        s.beta,s.c,s.p,s.d0=beta,c,p,d0; s.D=2*d0+2+2*p
        th,Z,s.lin,s.v,s.wv,s.B=setup(beta,c,s.D,1,panels,8)
    def split(s,x): return x[:s.d0+1], np.append(x[s.d0+1:],1.0)       # r0, F (ascending, monic)
    def q(s,x):
        r0,F=s.split(x); A=cv([1,1],r0); return cv(cv(A,A),cv(F,F[::-1])), cv(A,F)
    def J(s,x):
        q,r=s.q(x); return (s.lin@q-2*(s.wv@np.maximum(s.B@q,0)))/(r@r/2)
    def negJ_grad(s,x):
        r0,F=s.split(x); A=cv([1,1],r0); E=cv(F,F[::-1]); S=cv(A,A); q=cv(S,E); r=cv(A,F)
        ph=s.B@q; N=s.lin@q-2*(s.wv@np.maximum(ph,0)); I=r@r/2
        g=s.lin-2*((s.wv*(ph>0))@s.B)                                  # dN/dq
        dA=2*np.correlate(g,cv(A,E),'valid')                           # len D+1-(len(A)+len(E)-1)+1 = len(A)
        dE=np.correlate(g,S,'valid')                                   # len(E)
        dF=np.array([sum(dE[k]*((F[s.p-k+j] if 0<=s.p-k+j<=s.p else 0)+(F[k-s.p+j] if 0<=k-s.p+j<=s.p else 0)) for k in range(2*s.p+1)) for j in range(s.p)])
        dIA=np.correlate(r,F,'valid'); dIF=np.correlate(r,A,'valid')[:s.p]
        dN=np.concatenate([np.correlate(dA,[1,1],'valid'),dF]); dI=np.concatenate([np.correlate(dIA,[1,1],'valid'),dIF])
        return -N/I, -(dN/I-N/I**2*dI)
    def init(s,Dc=64):
        val,qo=convex(s.beta,s.c,Dc); rts=np.roots(qo[::-1]); ins=rts[np.abs(rts)<0.985]
        ins=sorted(ins,key=lambda z:abs(z)); 
        # keep p zeros closed under conjugation (smallest modulus first)
        sel=[]
        for z in ins:
            if len(sel)>=s.p: break
            if abs(z.imag)<1e-9: sel.append(z.real)
            elif z.imag>0 and len(sel)+2<=s.p: sel+= [z,np.conj(z)]
        while len(sel)<s.p: sel.append(-0.8-0.03*len(sel))
        F=np.real(P.polyfromroots(sel)); Fr=F[::-1]
        zc,ro=outer_sqrt(qo); base=(1+zc)*P.polyval(zc,Fr)
        Am=np.stack([base*zc**k for k in range(s.d0+1)],axis=1)
        r0=np.linalg.lstsq(np.vstack([Am.real,Am.imag]),np.concatenate([ro.real,ro.imag]),rcond=None)[0]
        return np.concatenate([r0,F[:-1]])
    def optimise(s,x0s,rounds=6):
        best=None; fb=-1
        for x0 in x0s:
            x=x0.copy()
            for it in range(rounds):
                res=minimize(s.negJ_grad,x,jac=True,method='L-BFGS-B',options={'maxiter':20000,'maxfun':40000,'ftol':1e-15,'gtol':1e-12,'maxcor':40})
                res2=minimize(s.negJ_grad,res.x,jac=True,method='BFGS',options={'maxiter':3000,'gtol':1e-12})
                xn=res2.x if res2.fun<res.fun else res.x
                if abs(s.J(xn)-s.J(x))<1e-11: x=xn; break
                x=xn
            f=s.J(x)
            if f>fb: best,fb=x,f
        return best,fb
    def report(s,x):
        q,r=s.q(x); J,N,I=evaluate(s.beta,s.c,q,M=20000,panels=3000); Jx=N/(r@r/2)
        r0,F=s.split(x); al=np.roots(F[::-1]); a=s.beta*(1-al)/(1+al)          # zeros of K at s_in = a
        ph=s.B@q; sg=np.sign(ph); ch=s.v[1:][sg[1:]!=sg[:-1]]
        return Jx**-2, a, ch
def run(beta,c,p,d0,prev=None,seeds=2):
    F=Fam(beta,c,p,d0); x0=F.init(); rng=np.random.default_rng(1)
    c0=[x0]+[x0*(1+0.03*rng.standard_normal(len(x0))) for k in range(seeds)]
    if prev is not None and len(prev)-p<=d0+1:
        c0.append(np.concatenate([prev[:-p],np.zeros(d0+1-(len(prev)-p)),prev[-p:]]))
    x,f=F.optimise(c0); cs,a,ch=F.report(x)
    return cs,a,ch,x
def job(a):
    beta,c,p,d0s=a; out=[]; prev=None
    for d0 in d0s:
        try:
            cs,al,ch,x=run(beta,c,p,d0,prev); prev=x
            out.append("beta=%.2f c=%.4f p=%d d0=%2d m=%2d (pole order of K: %d): c* = %.6f   sign changes of phi at v = %s   zeros of K at s_in = %s"%(beta,c,p,d0,d0+p+2,2*(d0+p+2),cs,np.array2string(ch,precision=3),np.array2string(al,precision=2)))
        except Exception as e: out.append("beta=%.2f c=%.4f p=%d d0=%d: FAILED %s"%(beta,c,p,d0,e))
    return "\n".join(out)
def convjob(a):
    from formal076_family import solve_convex
    beta,c,D=a; val,qv=solve_convex(beta,c,D,pos=False,div=2,M=3000,panels=60)
    J,N,I=evaluate(beta,c,qv,M=40000,panels=1000); r=np.roots(qv[::-1])
    return (beta,c,D,J**-2,int(np.sum(np.abs(r)<0.985)))
if __name__=="__main__":
    if sys.argv[1]=="scan":
        from multiprocessing import Pool
        jobs=[(b,c,p,[6,8,10,12,14,16,18,20,24,28]) for b in [1.0,1.5,2.0,3.0] for (c,p) in [(1.375,1),(1.6,2),(np.log(6),2),(2.0,3)]]
        with Pool(16) as pool:
            for r in pool.imap(job,jobs): print(r,flush=True)
    elif sys.argv[1]=="scan2":
        from multiprocessing import Pool
        jobs=[(b,c,2,[12,14,15,16,17,18,19,20,22]) for b in [2.0,3.0,4.0] for c in [1.7,1.8,1.9]]
        jobs+=[(b,c,3,[12,14,15,16,17,18,20]) for b in [2.0,3.0,4.0] for c in [2.0,2.15]]
        jobs+=[(1.0,1.8,2,[28,32,36,40,44,48,56]),(1.0,2.0,3,[28,32,36,40,44,48,56])]
        with Pool(17) as pool:
            for r in pool.imap(job,jobs): print(r,flush=True)
    elif sys.argv[1]=="conv":
        from multiprocessing import Pool
        jobs=[(b,c,D) for b in [1.0,1.5,2.0,3.0] for c in [1.375,1.6,np.log(6),2.0] for D in [24,32,40,48,56,64,80,100]]
        with Pool(16) as pool:
            for r in pool.imap(convjob,jobs): print("beta=%.1f c=%.4f D=%3d (pole order %3d): convex optimum c_inf = %.6f   zeros of q in |z|<0.985: %d"%(r[0],r[1],r[2],r[2]+2,r[3],r[4]),flush=True)
    else:
        beta,c,p,d0=float(sys.argv[2]),float(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5])
        print(job((beta,c,p,[d0])))
