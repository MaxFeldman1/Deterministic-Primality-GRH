"""Family (E) ("exact modulus"), pole beta = 1 (Perron variable s, zeros at s = 1 + i gamma, u = 1/s, z = 2u - 1):
     design B:  K(s) = (Z - (s-1)^2) H0(s)^2,  H0 = u^3 r0(z),  x = e^ell X, one sign change of the weight at L = L1
     design A:  K(s) = H(s)^2,                 H  = u^2 r1(z),  x = e^ell X, weight >= 0
   |K(1+it)| = (t^2+Z)|H0(1+it)|^2  resp. |H(1+it)|^2 : rational, so the zero sum is exact and
   I = (1/2pi) int |K| is a rational quadratic form.   Floating-point optimisation (local, BFGS/Powell), then
   conversion to the basis s^-i, scaling and rounding to INTEGER coefficients h_i.  Output: formal076_testfn_{A,B}.json.
   usage: formal076_design.py B ell_num ell_den L1_num L1_den d0 [digits]   |   formal076_design.py A ell_num ell_den d [digits]"""
import sys, json, numpy as np
from fractions import Fraction as Fr
from math import comb
from scipy.optimize import minimize
import scipy.linalg as sl
import os; HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,HERE)
from inside_primal_socp import setup, basis
cv=np.convolve
def to_u_basis(r, k0):
    """u^k0 * r(2u-1) as integer-indexed coefficient list in powers of u (index = power)"""
    out=[Fr(0)]*(len(r)+k0)
    p=[Fr(1)]                      # (2u-1)^n
    for n,rn in enumerate(r):
        rn=Fr(float(rn))
        for k,pk in enumerate(p): out[k+k0]+=rn*pk
        p=[ (2*(p[k-1] if k>0 else 0)) - (p[k] if k<len(p) else 0) for k in range(len(p)+1)]
    return out
def round_scale(h, digits):
    mx=max(abs(x) for x in h); sc=Fr(10**digits)/mx
    return [int(round(x*sc)) for x in h]
import warnings; warnings.filterwarnings("ignore")
mode=sys.argv[1]
if mode=='B':
    ell=Fr(int(sys.argv[2]),int(sys.argv[3])); L1=Fr(int(sys.argv[4]),int(sys.argv[5])); d0=int(sys.argv[6]); digits=int(sys.argv[7]) if len(sys.argv)>7 else 10
    c=float(ell); v1=float(ell-L1); D=2*d0+4
    th,Z_,lin,v,wv,B = setup(1.0,c,D,1,300,8)
    b1=basis(np.array([v1-c]),D)[0]
    def parts(r0):
        a=cv([1,1],r0); ra=cv([1,-1],a); rb=cv([1,1],a)        # (1-z)(1+z) r0 , (1+z)^2 r0
        qa=cv(ra,ra); qb=cv(rb,rb); Z=(b1@qa)/(b1@qb)
        return Z*qb-qa, (np.sum(ra**2)+Z*np.sum(rb**2))/2, Z
    def J(r0):
        q,I,Z=parts(r0)
        if Z<=0: return -1.0
        return (lin@q-2*(wv@np.maximum(B@q,0)))/I
    fi=os.path.join(HERE,"formal076_initB_%g_%d.npy"%(c,d0))
    if not os.path.exists(fi):
        from formal076_family import designB
        np.save(fi,designB(1.0,c,d0)[1])
    x=np.load(fi); r0=x[:-1]
    if J(-r0)>J(r0): r0=-r0
    best=r0; fb=J(r0); print("start J=%.7f c*=%.6f"%(fb,fb**-2))
    for it in range(10):
        imp=False
        for meth,opt in [('BFGS',{'gtol':1e-11,'maxiter':5000}),('Powell',{'xtol':1e-11,'ftol':1e-14,'maxiter':30000})]:
            res=minimize(lambda y:-J(y),best,method=meth,options=opt)
            if -res.fun>fb+1e-10: best,fb,imp=res.x,-res.fun,True
        if not imp: break
    q,I,Z=parts(best); print("optimised J=%.7f c*=%.6f  Z=%.4f (z1=%.4f)"%(fb,fb**-2,Z,Z**.5))
    h=to_u_basis(best,3)           # H0 = sum_{i=3}^{m} h_i u^i
    hi=round_scale(h,digits)
    json.dump({"design":"B","ell":[ell.numerator,ell.denominator],"L1":[L1.numerator,L1.denominator],"m":d0+3,"h":hi[3:],
               "comment":"H0(s) = sum_{i=3}^{m} h[i-3] s^-i ; K(s) = (Z - (s-1)^2) H0(s)^2 ; Z := rational making W(L1) = 0","float_cstar":fb**-2},
              open(os.path.join(HERE,"formal076_testfn_B.json"),"w"),indent=1)
    print("h =",hi[3:])
else:
    ell=Fr(int(sys.argv[2]),int(sys.argv[3])); d=int(sys.argv[4]); digits=int(sys.argv[5]) if len(sys.argv)>5 else 10
    c=float(ell); D=2*d
    th,Z_,lin,v,wv,B = setup(1.0,c,D,1,300,8)
    l=lin-(2*wv)@B
    T=np.zeros((d+1,d)); 
    for j in range(d): T[j,j]=1;T[j+1,j]=1
    A=T.T@np.array([[l[i+j] for j in range(d+1)] for i in range(d+1)])@T; G=T.T@T/2
    w,V=sl.eigh(A,G); r=T@V[:,-1]; q=cv(r,r)
    Jt=(lin@q-2*(wv@np.maximum(B@q,0)))/(np.sum(r**2)/2)
    print("design A: J_lin=%.7f J=%.7f c*=%.6f"%(w[-1],Jt,Jt**-2))
    r1=np.polynomial.polynomial.polydiv(r,[1,1])[0]
    h=to_u_basis(cv([1,1],r1)/2*2,1)    # H = u r(z) = u (1+z) r1 = 2u^2 r1(2u-1)
    hi=round_scale(h,digits)
    if sum(hi)<0: hi=[-a for a in hi]
    json.dump({"design":"A","ell":[ell.numerator,ell.denominator],"m":d+1,"h":hi[2:],"lowest_power_error":hi[1],
               "comment":"H(s) = sum_{i=2}^{m} h[i-2] s^-i ; K(s) = H(s)^2","float_cstar":Jt**-2},open(os.path.join(HERE,"formal076_testfn_A.json"),"w"),indent=1)
    print("h =",hi[1:])
