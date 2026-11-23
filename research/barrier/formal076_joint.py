"""Task 1 (floating point): JOINT optimisation of the test function and a rational majorant.
   phi in the Hardy/Laguerre family (beta, c, D) of inside.md  (K(t) = e^{itc} u^2 q(z)/beta, w = t/beta),
   G(t) = sum_{j,k} e_{jk} Re (a_j + i t)^{-k},  k = 1..Kmax,  a_j > 1/2   (exact zero sum at sigma_j = a_j + 1/2).
   maximise N(phi)  s.t.  G(t) >= |K(t)| for all t (grid; second-order cone),  (1/2pi) int G = sum_j e_{j1}/2 <= 1.
   Reported: c* = J^-2 with J = N / ((1/2pi) int G), after rescaling G by max(|K|/G) on a 20x finer grid."""
import sys, numpy as np, cvxpy as cp
import os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from inside_primal_socp import setup
def Gbasis(t, a_list, Kmax):
    cols=[]; first=[]
    for a in a_list:
        for k in range(1,Kmax+1):
            cols.append(np.real((a+1j*t)**(-k))); first.append(0.5 if k==1 else 0.0)
    return np.stack(cols,axis=1), np.array(first)
def joint(beta,c,D,a_list,Kmax,M=1500,pos=False,div=0):
    th,Z,lin,v,wv,B = setup(beta,c,D,M,60,8)
    w=np.tan(th/2); t=beta*w
    GB,first = Gbasis(t,a_list,Kmax)
    scale=(1+w**2)
    q=cp.Variable(D+1); e=cp.Variable(GB.shape[1])
    cons=[cp.abs(Z@q)/beta <= cp.multiply(scale,GB@e), first@e<=1]
    nn=np.arange(D+1)
    if div>=1: cons.append(((-1.0)**nn)@q==0)
    if div>=2: cons.append((nn*(-1.0)**nn)@q==0)
    if pos: cons.append(B@q>=0); obj=lin@q-2*(wv@(B@q))
    else:
        p=cp.Variable(len(v),nonneg=True); cons.append(p>=B@q); obj=lin@q-2*(wv@p)
    pr=cp.Problem(cp.Maximize(obj),cons); pr.solve(solver=cp.CLARABEL)
    qv,ev=q.value,e.value
    # re-evaluate
    th2,Z2,lin2,v2,wv2,B2 = setup(beta,c,D,1,2000,8)
    N = lin2@qv - 2*(wv2@np.maximum(B2@qv,0))
    M2=20*M; thf=(np.arange(M2)+0.5)*np.pi/M2; wf=np.tan(thf/2)
    Kf=np.abs(np.polynomial.polynomial.polyval(np.exp(-1j*thf),qv))/beta
    Gf=(1+wf**2)*(Gbasis(beta*wf,a_list,Kmax)[0]@ev)
    viol=np.max(Kf/Gf) if np.min(Gf)>0 else np.inf
    Itrue=np.mean(Kf)*beta/2
    return N/(first@ev*viol), N/Itrue, viol
if __name__=="__main__":
    beta,c,D=2.0,2.0,32
    print("phi family beta=%g c=%g D=%d (unrestricted optimum c_inf = 0.760762 for this family; 0.76075 overall)"%(beta,c,D))
    for a_list,Kmax in [([1],4),([1],8),([1],12),([1],16),([1],24),([2],8),([2],16),([2],24),([1,2],8),([1,2],12),([0.75,1,1.5,2,3],6),([0.75,1,1.5,2,3,4,6],8),([1,2,4],12)]:
        try:
            J,Jt,viol=joint(beta,c,D,a_list,Kmax)
            print(" a_j=%-22s K<=%2d (%3d terms): c* = %.6f   [phi alone: %.6f; loss int G/int|K| - 1 = %.2e; grid violation %.1e]"%(a_list,Kmax,len(a_list)*Kmax,J**-2,Jt**-2,(Jt/J-1),viol-1),flush=True)
        except Exception as ex: print(a_list,Kmax,'failed',ex,flush=True)
