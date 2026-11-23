"""formal0760: design of an explicit test function in family (E_p) with EXACT rational sign changes (floating point).
   q = sum_a zeta_a q_a,  q_a = (1+z)^2 r0^2 (-1)^a beta^(2a) (1-z)^(2a) (1+z)^(2p-2a) / 4^p   <->  (-s_in^2)^a H0^2,
   H0 = u^(p+2) r0(z), u = beta/sg;  zeta_p = 1 and zeta_0..zeta_{p-1} solve phi(v_i) = 0 at v_i = ell - L_i.
   Start: optimum of formal0760_family.Fam, then BFGS/Powell polish in r0; conversion to the basis u^i = (beta/sg)^i (the scaled variable s'' = sg/beta of the Lean plan); rounding to integers.
   usage: formal0760_design.py name beta ell_num ell_den p L1n L1d [L2n L2d ...] d0 digits"""
import sys, os, json, numpy as np, warnings; warnings.filterwarnings("ignore")
from fractions import Fraction as Fr
from scipy.optimize import minimize
HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,HERE)
from inside_primal_socp import setup, basis
from formal0760_family import Fam, run
cv=np.convolve
def ppow(b,k):
    out=np.array([1.0])
    for _ in range(k): out=cv(out,b)
    return out
class Des:
    def __init__(s,beta,c,Ls,d0,panels=400):
        s.beta,s.c,s.p,s.d0=beta,c,len(Ls),d0; p=s.p; s.D=2*d0+2+2*p
        th,Z,s.lin,s.v,s.wv,s.B=setup(beta,c,s.D,1,panels,8)
        s.b=basis(np.array([beta*(-L) for L in Ls]),s.D)             # rows: phi at v = c - L_i
        s.fa=[(-1)**a*beta**(2*a)*cv(ppow([1,-1],2*a),ppow([1,1],2*p-2*a+2))/4**p for a in range(p+1)]
        s.ia=[(cv(ppow([1,-1],a),ppow([1,1],p-a+1)),beta**(2*a)/4**p) for a in range(p+1)]
    def parts(s,r0):
        rr=cv(r0,r0); qa=[cv(rr,f) for f in s.fa]; p=s.p
        A=np.array([[s.b[i]@qa[a] for a in range(p)] for i in range(p)]); rhs=-np.array([s.b[i]@qa[p] for i in range(p)])
        zeta=np.append(np.linalg.solve(A,rhs),1.0)
        q=sum(z*x for z,x in zip(zeta,qa))
        I=sum(z*np.sum(cv(r0,pol)**2)*sc/2 for z,(pol,sc) in zip(zeta,s.ia))
        return q,I,zeta
    def J(s,r0):
        q,I,zeta=s.parts(r0)
        if min(zeta)<=0 or I<=0: return -1.0
        return (s.lin@q-2*(s.wv@np.maximum(s.B@q,0)))/I
def to_sigma_basis(r0,k0,beta):
    """coefficients of u^k0 r0(2u-1), u = beta/sg, in powers of 1/sg (exact rationals of the floats)"""
    out=[Fr(0)]*(len(r0)+k0); pz=[Fr(1)]
    for n,rn in enumerate(r0):
        rn=Fr(float(rn))
        for k,pk in enumerate(pz): out[k+k0]+=rn*pk
        pz=[(2*(pz[k-1] if k>0 else 0))-(pz[k] if k<len(pz) else 0) for k in range(len(pz)+1)]
    return out            # coefficients in powers of u = beta/sg  (scaled variable s'' = sg/beta = 1/u)
if __name__=="__main__":
    name=sys.argv[1]; beta=int(sys.argv[2]); ell=Fr(int(sys.argv[3]),int(sys.argv[4])); p=int(sys.argv[5])
    Ls=[Fr(int(sys.argv[6+2*i]),int(sys.argv[7+2*i])) for i in range(p)]; d0=int(sys.argv[6+2*p]); dg=int(sys.argv[7+2*p])
    c=float(ell)
    fi=os.path.join(HERE,"formal0760_init_%s.npy"%name)
    if not os.path.exists(fi):
        best=None
        for dd in sorted(set([max(6,d0-4),max(6,d0-2),d0])):         # continuation in the degree
            cs,a,ch,x=run(float(beta),c,p,dd,prev=best,seeds=4); best=x
        print("family optimum: c* = %.6f, sign changes at L = %s"%(cs,np.array2string(c-ch[::-1],precision=4))); np.save(fi,x)
    x=np.load(fi); r0=x[:d0+1]
    D=Des(float(beta),c,[float(L) for L in Ls],d0)
    if D.J(-r0)>D.J(r0): r0=-r0
    bestx=r0; fb=D.J(r0); print("start (exact zeros at L = %s): J = %.7f c* = %.6f"%([str(L) for L in Ls],fb,fb**-2 if fb>0 else 9))
    for it in range(8):
        imp=False
        for meth,opt in [('BFGS',{'gtol':1e-11,'maxiter':5000}),('Powell',{'xtol':1e-11,'ftol':1e-14,'maxiter':40000})]:
            res=minimize(lambda y:-D.J(y),bestx,method=meth,options=opt)
            if -res.fun>fb+1e-10: bestx,fb,imp=res.x,-res.fun,True
        if not imp: break
    q,I,zeta=D.parts(bestx); ph=D.B@q; sg=np.sign(ph); ch=D.v[1:][sg[1:]!=sg[:-1]]
    print("optimised: J = %.7f  c* = %.6f  zeta = %s  sign changes at L = %s"%(fb,fb**-2,np.array2string(zeta,precision=5),np.array2string(c-ch[::-1],precision=4)))
    h=to_sigma_basis(bestx,p+2,beta); mx=max(abs(t) for t in h); hi=[int(round(t*Fr(10**dg)/mx)) for t in h]
    json.dump({"name":name,"beta":beta,"ell":[ell.numerator,ell.denominator],"L":[[L.numerator,L.denominator] for L in Ls],"m":d0+p+2,"scaled":True,"h":hi[p+2:],
               "comment":"H0 = sum_{i=p+2}^{m} h[i-p-2] u^i, u = beta/sg, sg = s + beta - 1 (i.e. coefficient of sg^-i is h_i beta^i); K = Q H0^2; Q = sum zeta_a (-(sg-beta)^2)^a with W(L_i) = 0","float_cstar":fb**-2},
              open(os.path.join(HERE,"formal0760_testfn_%s.json"%name),"w"),indent=1)
    print("h =",hi[p+2:])
