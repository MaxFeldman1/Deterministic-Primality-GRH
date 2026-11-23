"""Exact data for the Lean certificate R13CertB (design B of formal076). stdlib only."""
import json, sys, os
from fractions import Fraction as Fr
from math import comb, factorial, lcm, gcd
HERE=os.path.dirname(os.path.abspath(__file__))
def load(design):
    t=json.load(open(os.path.join(HERE,"..","formal076_testfn_%s.json"%design)))
    c=json.load(open(os.path.join(HERE,"..","formal076_certificate_%s.json"%design)))
    return t,c
def exp_lo(a,n):  # partial sum
    return sum(Fr(a)**i/factorial(i) for i in range(n))
def build(design="B"):
    t,c=load(design); m=t["m"]; ell=Fr(*t["ell"]); L1=Fr(*t["L1"]) if design=="B" else Fr(0)
    Z=Fr(c["Z"]) if design=="B" else None
    kap={int(n):Fr(v) for n,v in c["kappa"].items()}
    e={int(n):Fr(v) for n,v in c["e"].items()}
    i0=3 if design=="B" else 2
    hh={i0+i:x for i,x in enumerate(t["h"])}           # H0 = sum h_i s^-i
    J=2*m-1
    # scaling: all of theta, e integers
    D=1
    for v in kap.values(): D=lcm(D,v.denominator)
    for v in e.values(): D=lcm(D,v.denominator)
    theta=[int(kap.get(j+1,Fr(0))*D) for j in range(J+1)]
    ee={k:int(e[k]*D) for k in e}
    if design=="B": A=Z*D; B=Fr(D)
    else: A=Fr(D); B=Fr(0)
    assert A.denominator==1
    A=int(A); B=int(B)
    # P(s) = sum_i hP[i] s^i,  P = s^m H0
    d=m-i0+1
    hP=[hh[m-i] for i in range(d)]
    # checks of the two identities (in s), integer polynomials
    def pmul(a,b):
        r=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
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
    fac=padd([A],[-B*x for x in pmul([-1,1],[-1,1])])
    lhs1=[theta[J-i] for i in range(J+1)]           # sum_j theta_j s^(J-j)
    assert trim(lhs1)==trim(pmul(fac,pmul(hP,hP))), "identity 1"
    P2=[0]
    for i,x in enumerate(hP): P2=padd(P2,[x*y for y in ppow([2,-1],i)])
    lhs2=pmul(fac,pmul(hP,P2))
    rhs2=[0]
    for k in range(1,m+1):
        term=padd(pmul([0]*(m-k)+[1],ppow([2,-1],m)),pmul([0]*m+[1],ppow([2,-1],m-k)))
        rhs2=padd(rhs2,[Fr(ee[k],2)*x for x in term])
    assert trim(lhs2)==trim(rhs2), "identity 2"
    # W and Bernstein
    W=[Fr(theta[j],factorial(j)) for j in range(J+1)]
    Wt=[Fr(x)*D for x in c["Wt"]]; n=len(Wt)-1
    den=[0,0,0,1] if design=="A" else pmul([0,0,0,1],[-L1,1])
    assert trim(pmul(den,Wt))==trim(W)
    # W = L^3 (pL*L - qL) * sum_k c_k L^k (pe - qe L)^(n-k),  ell = pe/qe, L1 = qL/pL
    pe,qe=ell.numerator,ell.denominator
    # Bernstein coefficients of Wt on [0,ell]
    q=[Wt[i]*ell**i for i in range(n+1)]
    b=[sum(Fr(comb(k,i),comb(n,i))*q[i] for i in range(k+1)) for k in range(n+1)]
    assert min(b)>0
    # Wt(L) = sum_k b_k C(n,k) (L/ell)^k (1-L/ell)^(n-k) = sum_k b_k C(n,k) qe^k L^k (pe - qe L)^(n-k) / pe^n
    cc=[b[k]*comb(n,k)*qe**k/Fr(pe)**n for k in range(n+1)]
    if design=="B":
        pL,qL=L1.denominator,L1.numerator
        cc=[x/pL for x in cc]
    F=1
    for x in cc: F=lcm(F,x.denominator)
    ci=[int(x*F) for x in cc]
    # check: F*W = L^3 (pL L - qL) sum ci L^k (pe - qe L)^(n-k)
    S=[0]
    for k in range(n+1): S=padd(S,[ci[k]*x for x in pmul([0]*k+[1],ppow([pe,-qe],n-k))])
    lin=[-qL,pL] if design=="B" else [1]
    assert trim(pmul(pmul([0,0,0,1],lin),S))==trim([x*F for x in W]), "bernstein identity"
    # R values
    def R(L):
        return sum(theta[j]*sum(Fr(L)**i/factorial(i)*Fr(2,3)**(j+1-i) for i in range(j+1)) for j in range(J+1))
    Rl,R1,R0=R(ell),R(L1),R(0)
    return dict(design=design,m=m,J=J,ell=ell,L1=L1,D=D,theta=theta,e=ee,A=A,B=B,d=d,hP=hP,F=F,ci=ci,n=n,pe=pe,qe=qe,
                lin=lin,Rl=Rl,R1=R1,R0=R0)
if __name__=="__main__":
    for des in sys.argv[1:] or ["B"]:
        r=build(des)
        print(des,"D digits",len(str(r["D"])),"max theta digits",max(len(str(abs(x))) for x in r["theta"]),
              "max e digits",max(len(str(abs(x))) for x in r["e"].values()),"F digits",len(str(r["F"])),"max ci digits",max(len(str(x)) for x in r["ci"]))
        print(" R:",float(r["Rl"]),float(r["R1"]),float(r["R0"]), "R dens digits",[len(str(x.denominator)) for x in (r["Rl"],r["R1"],r["R0"])])
        from math import exp
        N=2*float(r["Rl"])*exp(-1.5*float(r["ell"]))-2*float(r["R1"])*exp(-1.5*float(r["L1"]))+float(r["R0"])
        print(" N",N," c*",exp(-float(r["ell"]))*(r["e"][1]/(2*N))**2)
