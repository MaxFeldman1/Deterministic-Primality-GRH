"""formal0760, option (a): convex reference value for kernels with TWO poles (s_in = -beta1 and -beta2), floating point.
   K(t) = e^{itc} [ u1^2 q1(z1)/beta1 + u2^2 q2(z2)/beta2 ],  deg q_i = D_i, (1+z_i)^2 | q_i;  maximise N subject to I <= 1 (SOCP).
   This is the best any kernel with these poles and orders can do (no exact-modulus restriction), to be compared with the
   single-pole convex values at the same total order D1 + D2 + 4."""
import sys, os, numpy as np, cvxpy as cp, warnings; warnings.filterwarnings("ignore")
HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,HERE)
from inside_primal_socp import setup
def solve(c,poles,M=6000,panels=60):
    th=(np.arange(M)+0.5)*np.pi/M; T=3.0; t=T*np.tan(th/2); wt=(T/2)/np.cos(th/2)**2*(np.pi/M)/np.pi   # (1/2pi) int over R = (1/pi) int_0^inf
    Zs=[]; ls=[]; Bs=[]; Cs=[]
    for beta,D in poles:
        _,_,l,v,wv,B=setup(beta,c,D,1,panels,8)
        u=1/(1+1j*t/beta); z=2*u-1; n=np.arange(D+1)
        # impose (1+z)^2 | q by parametrising q = (1+z)^2 * r
        Tm=np.zeros((D+1,D-1))
        for j in range(D-1): Tm[j,j]=1; Tm[j+1,j]=2; Tm[j+2,j]=1
        Zs.append(((u**2/beta)[:,None]*z[:,None]**n[None,:])@Tm); ls.append(l@Tm); Bs.append(B@Tm)
    Z=np.hstack(Zs); l=np.concatenate(ls); B=np.hstack(Bs)
    # orthonormalise the (nearly dependent) union of the two bases in L^2(dt): SVD, drop tiny singular values
    A=np.vstack([Z.real,Z.imag])*np.sqrt(np.concatenate([wt,wt]))[:,None]
    U,sv,Vt=np.linalg.svd(A,full_matrices=False); keep=sv>1e-10*sv[0]; V=Vt[keep].T/sv[keep][None,:]
    Z=Z@V; l=l@V; B=B@V
    y=cp.Variable(Z.shape[1]); p=cp.Variable(len(v),nonneg=True)
    pr=cp.Problem(cp.Maximize(l@y-2*(wv@p)),[p>=B@y, wt@cp.abs(Z@y)<=1]); pr.solve(solver=cp.CLARABEL)
    return pr.value**-2, int(keep.sum())
def job(a):
    c,poles=a
    try:
        val,rk=solve(c,poles); return "c=%.2f poles (beta,D)=%s total pole order %d (numerical rank %d): c_inf = %.6f"%(c,poles,sum(D+2 for b,D in poles),rk,val)
    except Exception as e: return "c=%.2f poles=%s FAILED %s"%(c,poles,e)
if __name__=="__main__":
    from multiprocessing import Pool
    jobs=[]
    for c in [1.8]:
        for tot in [24,32,40]:      # total pole order of K
            jobs+=[(c,[(b,tot-2)]) for b in [1.0,2.0,3.0]]
            h=tot//2-2
            jobs+=[(c,[(b1,h),(b2,h)]) for (b1,b2) in [(1.0,2.0),(1.0,3.0),(2.0,3.0),(2.0,4.0),(1.5,4.0)]]
    with Pool(12) as pool:
        for r in pool.imap(job,jobs): print(r,flush=True)
