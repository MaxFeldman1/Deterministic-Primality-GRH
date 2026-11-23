"""formal07605: re-optimised exact-modulus designs (family (E_p) of formal0760.md, beta = 3) beyond b3m24:
   p = 2 (ell = 9/5) with larger m, and p = 3 (ell = 2, three exact rational sign changes).  Floating point.
   Thin driver around formal0760_design.Des (same parametrisation, same json format), writing
   formal07605_testfn_<name>.json and caching the optimiser state in formal07605_init_<name>.npy.
   The start is the optimum of formal0760_family.Fam (continuation in the degree d0-8, d0-4, d0).
   usage: formal07605_design.py name beta ell_num ell_den p L1n L1d [L2n L2d ...] d0 digits
   Needs numpy, scipy, cvxpy, clarabel (convex start).  Designs used:
     b3p3m29: formal07605_design.py b3p3m29 3 2 1 3 4 15 3 5 31 30 24 14
     b3p3m33: formal07605_design.py b3p3m33 3 2 1 3 4 15 3 5 31 30 28 16
     b3p3m37: formal07605_design.py b3p3m37 3 2 1 3 4 15 3 5 31 30 32 18
     b3p2m32: formal07605_design.py b3p2m32 3 9 5 2 2 5 5 6 28 16"""
import sys, os, json, numpy as np, warnings; warnings.filterwarnings("ignore")
from fractions import Fraction as Fr
from scipy.optimize import minimize
HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,HERE)
from formal0760_design import Des, to_sigma_basis
from formal0760_family import run
if __name__=="__main__":
    name=sys.argv[1]; beta=int(sys.argv[2]); ell=Fr(int(sys.argv[3]),int(sys.argv[4])); p=int(sys.argv[5])
    Ls=[Fr(int(sys.argv[6+2*i]),int(sys.argv[7+2*i])) for i in range(p)]; d0=int(sys.argv[6+2*p]); dg=int(sys.argv[7+2*p])
    c=float(ell)
    fi=os.path.join(HERE,"formal07605_init_%s.npy"%name)
    if not os.path.exists(fi):
        best=None
        for dd in sorted(set([max(6,d0-8),max(6,d0-4),d0])):
            cs,a,ch,x=run(float(beta),c,p,dd,prev=best,seeds=3); best=x
        print("family optimum: c* = %.7f, sign changes at L = %s"%(cs,np.array2string(c-ch[::-1],precision=4))); np.save(fi,x)
    x=np.load(fi); r0=x[:d0+1]
    D=Des(float(beta),c,[float(L) for L in Ls],d0)
    if D.J(-r0)>D.J(r0): r0=-r0
    bestx=r0; fb=D.J(r0); print("start (exact zeros at L = %s): J = %.8f c* = %.7f"%([str(L) for L in Ls],fb,fb**-2 if fb>0 else 9))
    for it in range(8):
        imp=False
        for meth,opt in [('BFGS',{'gtol':1e-11,'maxiter':5000}),('Powell',{'xtol':1e-11,'ftol':1e-14,'maxiter':40000})]:
            res=minimize(lambda y:-D.J(y),bestx,method=meth,options=opt)
            if -res.fun>fb+1e-10: bestx,fb,imp=res.x,-res.fun,True
        if not imp: break
    q,I,zeta=D.parts(bestx); ph=D.B@q; sg=np.sign(ph); ch=D.v[1:][sg[1:]!=sg[:-1]]
    print("optimised: J = %.8f  c* = %.7f  zeta = %s  sign changes at L = %s"%(fb,fb**-2,np.array2string(zeta,precision=5),np.array2string(c-ch[::-1],precision=4)))
    h=to_sigma_basis(bestx,p+2,beta); mx=max(abs(t) for t in h); hi=[int(round(t*Fr(10**dg)/mx)) for t in h]
    json.dump({"name":name,"beta":beta,"ell":[ell.numerator,ell.denominator],"L":[[L.numerator,L.denominator] for L in Ls],"m":d0+p+2,"scaled":True,"h":hi[p+2:],
               "comment":"H0 = sum_{i=p+2}^{m} h[i-p-2] u^i, u = beta/sg, sg = s + beta - 1 (i.e. coefficient of sg^-i is h_i beta^i); K = Q H0^2; Q = sum zeta_a (-(sg-beta)^2)^a with W(L_i) = 0","float_cstar":fb**-2},
              open(os.path.join(HERE,"formal07605_testfn_%s.json"%name),"w"),indent=1)
    print("h =",hi[p+2:])
