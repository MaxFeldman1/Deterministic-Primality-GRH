"""formal07605: copy of r14Cert_gen/data.py reading formal07605_{testfn,certificate}_<name>.json (same directory).
Exact data for the Lean certificates of Round 14 (formal0760), in the SCALED variables
s'' = (s+beta-1)/beta, L'' = beta*log(x/n).  stdlib only.  Everything is recomputed from formal0760_testfn_<name>.json
(the integers h_i) and checked by exact rational arithmetic; the result is compared with the certified c* of
formal0760_certificate_<name>.json.

  H0 = sum_{i=p+2}^m h_i s^-i,  Q = sum_{a<=p} zeta_a (-(s-1)^2)^a  (zeta_p = 1, the others from W(b_i) = 0),
  K = Q H0^2 = sum_j theta_j s^-(j+1),  W(L) = sum_j theta_j L^j/j!,  b = [0, beta L_1, .., beta L_p, beta ell],
  Q(s) P(s) P(2-s) = sum_k e_k/2 (s^(m-k)(2-s)^m + s^m (2-s)^(m-k)),  P = s^m H0,
  kappa = 1 + 1/(2 beta),  R(L) = sum_j theta_j sum_{i<=j} L^i/i! kappa^-(j+1-i),  F(L) = e^{-kappa L} R(L),
  N = F(b_{p+1}) - sum_{i<=p} (-1)^(p-i) (F(b_i) - F(b_{i+1})),   c* = e^{-b_{p+1}/beta} (beta e_1/(2N))^2.
"""
import json, sys, os
from fractions import Fraction as Fr
from math import comb, factorial, lcm
HERE=os.path.dirname(os.path.abspath(__file__))
def pmul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]+=x*y
    return r
def padd(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def trim(a):
    a=list(a)
    while a and a[-1]==0: a.pop()
    return a
def ppow(a,n):
    r=[1]
    for _ in range(n): r=pmul(r,a)
    return r
def peval(a,x):
    r=Fr(0)
    for c in reversed(a): r=r*x+c
    return r
def pdivmod(a,b):
    a=trim(a); b=trim(b); q=[Fr(0)]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b):
        c=Fr(a[-1])/b[-1]; k=len(a)-len(b); q[k]=c
        for i,y in enumerate(b): a[i+k]-=c*y
        a=trim(a)
    return q,a
def solve(A,b):
    n=len(A); M=[list(A[i])+[b[i]] for i in range(n)]
    for i in range(n):
        piv=next(r for r in range(i,n) if M[r][i]!=0); M[i],M[piv]=M[piv],M[i]
        M[i]=[x/M[i][i] for x in M[i]]
        for r in range(n):
            if r!=i and M[r][i]!=0: M[r]=[x-M[r][i]*y for x,y in zip(M[r],M[i])]
    return [M[i][n] for i in range(n)]
def build(name):
    t=json.load(open(os.path.join(HERE,"formal07605_testfn_%s.json"%name)))
    cj=json.load(open(os.path.join(HERE,"formal07605_certificate_%s.json"%name)))
    assert t.get("scaled")
    beta=int(t["beta"]); m=t["m"]; ell=Fr(*t["ell"]); Ls=[Fr(*x) for x in t["L"]]; p=len(Ls)
    i0=p+2; h=[Fr(0)]*i0+[Fr(x) for x in t["h"]]; assert len(h)==m+1
    b=[Fr(0)]+[beta*x for x in Ls]+[beta*ell]
    J=2*m-1
    c=[Fr(x) for x in pmul(h,h)]                                   # index = power of 1/s
    def mulq(k_):                                 # multiply by -(s-1)^2 = -s^2 + 2s - 1
        out=[Fr(0)]*len(k_)
        for k,ck in enumerate(k_):
            if ck: out[k-2]-=ck; out[k-1]+=2*ck; out[k]-=ck
        return out
    kas=[c]
    for a in range(p): kas.append(mulq(kas[-1]))
    W_of=lambda kap:[kap[n]/factorial(n-1) for n in range(1,len(kap))]
    Ws=[W_of(k_) for k_ in kas]
    zeta=solve([[peval(Ws[a],L) for a in range(p)] for L in b[1:p+1]],[-peval(Ws[p],L) for L in b[1:p+1]])+[Fr(1)]
    assert all(z>0 for z in zeta)
    kap=[sum(zeta[a]*kas[a][n] for a in range(p+1)) for n in range(len(c))]
    assert all(kap[n]==0 for n in range(4)) and len(kap)==2*m+1
    # e_k
    g=[h]
    for a in range(p):
        prev=g[-1]; nx=[Fr(0)]*(m+1)
        for i,x in enumerate(prev):
            if x: nx[i-1]+=x; nx[i]-=x
        g.append(nx)
    Qm=[[sum(zeta[a]*g[a][i]*g[a][k] for a in range(p+1)) for k in range(m+1)] for i in range(m+1)]
    e=[Fr(0)]*(m+1)
    for a in range(1,m+1):
        e[a]=2*sum(Qm[i][k]*Fr(comb(i+k-a-1,k-1),2**(i+k-a)) for i in range(a,m+1) for k in range(1,m+1) if Qm[i][k])
    # common scaling
    D=1
    for v in kap+e+zeta: D=lcm(D,Fr(v).denominator)
    theta=[int(kap[j+1]*D) for j in range(J+1)]
    ee={k:int(e[k]*D) for k in range(1,m+1)}
    z=[int(x*D) for x in zeta]
    d=m-i0+1
    hP=[int(h[m-i]) for i in range(d)]
    # identities (integer polynomials in s)
    qf=[0]; base=[-1,2,-1]; pw=[1]
    for a in range(p+1): qf=padd(qf,[z[a]*x for x in pw]); pw=pmul(pw,base)
    lhs1=[theta[J-i] for i in range(J+1)]
    assert trim(lhs1)==trim(pmul(qf,pmul(hP,hP))), "identity 1"
    P2=[0]
    for i,x in enumerate(hP): P2=padd(P2,[x*y for y in ppow([2,-1],i)])
    lhs2=pmul(qf,pmul(hP,P2))
    rhs2=[0]
    for k in range(1,m+1):
        term=padd(pmul([0]*(m-k)+[1],ppow([2,-1],m)),pmul([0]*m+[1],ppow([2,-1],m-k)))
        rhs2=padd(rhs2,[Fr(ee[k],2)*x for x in term])
    assert trim(lhs2)==trim(rhs2), "identity 2"
    assert ee[1]>0
    # W and Bernstein
    W=[Fr(theta[j],factorial(j)) for j in range(J+1)]
    den=[Fr(0),Fr(0),Fr(0),Fr(1)]
    for L in b[1:p+1]: den=pmul(den,[-L,Fr(1)])
    Wt,rem=pdivmod(W,den); assert not trim(rem); Wt=trim(Wt); n=len(Wt)-1
    top=b[p+1]; pe,qe=top.numerator,top.denominator
    q=[Wt[i]*top**i for i in range(n+1)]
    bern=[sum(Fr(comb(k,i),comb(n,i))*q[i] for i in range(k+1)) for k in range(n+1)]
    assert min(bern)>0
    cc=[bern[k]*comb(n,k)*qe**k/Fr(pe)**n for k in range(n+1)]
    lins=[(x.denominator,x.numerator) for x in b[1:p+1]]         # factor (qL*L - pL), root pL/qL
    for (qL,pL) in lins: cc=[x/qL for x in cc]
    F=1
    for x in cc: F=lcm(F,x.denominator)
    ci=[int(x*F) for x in cc]
    S=[0]
    for k in range(n+1): S=padd(S,[ci[k]*x for x in pmul([0]*k+[1],ppow([pe,-qe],n-k))])
    full=[0,0,0,1]
    for (qL,pL) in lins: full=pmul(full,[-pL,qL])
    assert trim(pmul(full,S))==trim([x*F for x in W]), "bernstein identity"
    # R values
    kappa=1+Fr(1,2*beta); ik=1/kappa
    tau=[sum(theta[j]*ik**(j+1-i) for j in range(i,J+1)) for i in range(J+2)]
    assert tau[J+1]==0 and all(tau[i]==ik*(theta[i]+tau[i+1]) for i in range(J+1))
    Rv=[sum(x**i/factorial(i)*tau[i] for i in range(J+1)) for x in b]
    coef=[Fr(0)]*(p+2); coef[p+1]+=1
    for i in range(p+1):
        s=(-1)**(p-i); coef[i]-=s; coef[i+1]+=s
    return dict(name=name,beta=beta,p=p,m=m,J=J,b=b,ell=ell,D=D,theta=theta,e=ee,z=z,d=d,hP=hP,F=F,ci=ci,n=n,pe=pe,qe=qe,
                lins=lins,kappa=kappa,tau=tau,Rv=Rv,coef=coef,cstar_ref=cj["cstar_upper"])
if __name__=="__main__":
    from math import exp
    for nm in sys.argv[1:]:
        r=build(nm)
        N=sum(float(cf*R/r["e"][1])*exp(-float(r["kappa"]*x)) for cf,R,x in zip(r["coef"],r["Rv"],r["b"]))   # N/e_1 (avoids float overflow)
        cs=exp(-float(r["b"][-1])/r["beta"])*(r["beta"]/(2*N))**2
        print(nm,"beta",r["beta"],"p",r["p"],"m",r["m"],"b",[str(x) for x in r["b"]],"coef",[str(x) for x in r["coef"]])
        print("  digits: D",len(str(r["D"])),"theta",max(len(str(abs(x))) for x in r["theta"]),"e",max(len(str(abs(x))) for x in r["e"].values()),
              "z",[len(str(x)) for x in r["z"]],"F",len(str(r["F"])),"ci",max(len(str(x)) for x in r["ci"]))
        print("  c* (scaled formula e^{-b_{p+1}/beta} (beta e_1/(2N))^2) = %.10f   certified (unscaled, formal0760_certificate) = %.10f"%(cs,r["cstar_ref"]))
