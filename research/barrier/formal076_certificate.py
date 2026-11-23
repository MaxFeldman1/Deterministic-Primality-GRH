"""Exact certificate for formal076.md (stdlib only: fractions, math, json; every inequality is between rationals).

  Data (formal076_testfn_{A,B}.json): integers h_i, rationals ell (and L1 for design B).
    design A:  H(s) = sum_{i=2}^m h_i s^-i,   K = H^2,                      weight W >= 0 on [0, ell]
    design B:  H0(s) = sum_{i=3}^m h_i s^-i,  K = (Z - (s-1)^2) H0^2,       W <= 0 on [0, L1], W >= 0 on [L1, ell],
               Z := W_a(L1)/W_b(L1) (rational), so that W(L1) = 0 exactly.
    K(s) = sum_{n=4}^{2m} kappa_n s^-n,   W(L) = sum_n kappa_n L^(n-1)/(n-1)!  (weight of n is sqrt(n) W(log(x/n)), x = e^ell X).
  Certified:
    (a) sign pattern of W: W = L^3 (L - L1) Wt (resp. L^3 Wt), Wt > 0 on [0, ell]  (Sturm count + Bernstein certificate);
        Nhat = 2 e^{-3 ell/2} R(ell) - 2 e^{-3 L1/2} R(L1) + R(0)  (design A: 2 e^{-3 ell/2} R(ell) - R(0))  >= N_lo,   R(L) = sum_n kappa_n sum_{i<n} L^i/i! (2/3)^(n-i);
    (b) |K(1+it)| = G(t) := sum_{k=1}^m e_k Re (1+it)^-k   (polynomial identity; G >= 0 because G = (t^2+Z)|H0|^2);
    (c) Ihat = (1/2pi) int G = e_1/2  (rational);
    =>  c* = e^{-ell} (Ihat/Nhat)^2 <= bound."""
import sys, json
from fractions import Fraction as Fr
from math import comb, factorial
def padd(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def pmul(a,b):
    r=[Fr(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]+=x*y
    return r
def pscale(a,c): return [c*x for x in a]
def peval(a,x):
    r=Fr(0)
    for c in reversed(a): r=r*x+c
    return r
def ptrim(a):
    a=list(a)
    while a and a[-1]==0: a.pop()
    return a
def pdivmod(a,b):
    a=ptrim(a); b=ptrim(b); q=[Fr(0)]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b):
        c=a[-1]/b[-1]; k=len(a)-len(b); q[k]=c
        for i,y in enumerate(b): a[i+k]-=c*y
        a=ptrim(a)
    return q,a
def pder(a): return [i*a[i] for i in range(1,len(a))]
def sturm_count(p,lo,hi):
    """number of distinct roots of p in (lo,hi]"""
    ch=[ptrim(p),ptrim(pder(p))]
    while len(ch[-1])>1:
        _,r=pdivmod(ch[-2],ch[-1]); r=ptrim(r)
        if not r: break
        ch.append(pscale(r,-1))
    def var(x):
        s=[peval(c,x) for c in ch]; s=[v for v in s if v!=0]
        return sum(1 for i in range(len(s)-1) if (s[i]>0)!=(s[i+1]>0))
    return var(lo)-var(hi), max(max(abs(c.numerator),c.denominator) for pp in ch for c in pp)
def bernstein(p,lo,hi):
    """Bernstein coefficients of p on [lo,hi] (degree n = deg p)"""
    n=len(p)-1
    # shift to [0,1]: q(y)=p(lo+(hi-lo)y)
    q=[Fr(0)]; 
    for c in reversed(p): q=padd(pmul(q,[lo,hi-lo]),[c])
    q=q+[Fr(0)]*(n+1-len(q))
    return [sum(Fr(comb(k,i),comb(n,i))*q[i] for i in range(k+1)) for k in range(n+1)]
def exp_bounds(a,n=60):
    """rationals lo <= e^a <= hi for rational a >= 0"""
    assert a>=0 and n+1>a
    S=Fr(0); t=Fr(1)
    for k in range(n): S+=t; t=t*a/(k+1)
    return S, S+t/(1-a/(n+1))
def digits(x): return len(str(abs(x.numerator))), len(str(x.denominator))
def main(fn):
    d=json.load(open(fn)); design=d["design"]; m=d["m"]; ell=Fr(*d["ell"])
    i0 = 3 if design=="B" else 2
    h=[Fr(0)]*i0+[Fr(x) for x in d["h"]]; assert len(h)==m+1          # h[i] = coefficient of s^-i
    c=pmul(h,h)                                                       # H0^2 (index = power of 1/s)
    print("design %s: m = %d (K has a pole of order %d at s = 0; weights sqrt(n) log^j(x/n), 3 <= j <= %d), ell = %s, x = e^ell X"%(design,m,2*m,2*m-1,ell))
    W_of=lambda kap: [kap[n]/factorial(n-1) for n in range(1,len(kap))]     # W(L) = sum kap_n L^(n-1)/(n-1)!
    if design=="B":
        L1=Fr(*d["L1"])
        # (s-1)^2 H0^2 = sum c_k ( s^-(k-2) - 2 s^-(k-1) + s^-k )
        ka=[Fr(0)]*len(c)
        for k,ck in enumerate(c):
            if ck: ka[k-2]+=ck; ka[k-1]-=2*ck; ka[k]+=ck
        Wa=W_of(ka); Wb=W_of(c)
        Z=peval(Wa,L1)/peval(Wb,L1); assert Z>0
        kap=[Z*c[k]-ka[k] for k in range(len(c))]
        print("  L1 = %s,  Z = %.12f (rational, digits num/den = %s)   [zero of K at s = 1 +- sqrt(Z)]"%(L1,float(Z),digits(Z)))
    else:
        kap=c; Z=None
    assert all(kap[n]==0 for n in range(4)), "K must be O(s^-4)"
    W=W_of(kap)
    # ---- (a) sign pattern
    den=[Fr(0),Fr(0),Fr(0),Fr(1)] if design=="A" else pmul([Fr(0),Fr(0),Fr(0),Fr(1)],[-L1,Fr(1)])
    Wt,rem=pdivmod(W,den); assert not ptrim(rem), "W not divisible"
    Wt=ptrim(Wt)
    nroots,size=sturm_count(Wt,Fr(0),ell)
    assert peval(Wt,Fr(0))>0 and peval(Wt,ell)>0 and nroots==0
    print("  (a) W(L) = L^3%s Wt(L), deg Wt = %d; Sturm: Wt has no root in [0, ell], Wt(0) = %.3e > 0  (largest integer in the Sturm chain: 10^%d)"%("" if design=="A" else " (L - L1)",len(Wt)-1,float(peval(Wt,Fr(0))),len(str(size))))
    # Bernstein certificate with bisection
    todo=[(Fr(0),ell)]; cells=[]
    while todo:
        lo,hi=todo.pop()
        b=bernstein(Wt,lo,hi)
        if min(b)>0: cells.append((lo,hi,b))
        else:
            assert hi-lo>Fr(1,10**6); mid=(lo+hi)/2; todo+= [(lo,mid),(mid,hi)]
    cells.sort()
    print("      Bernstein certificate: all %d Bernstein coefficients > 0 on each of %d cell(s): %s"%(len(Wt),len(cells),", ".join("[%s,%s]"%(a,b_) for a,b_,_ in cells)))
    print("      (min coefficient / max coefficient per cell: %s)"%", ".join("%.1e"%float(min(b)/max(b)) for _,_,b in cells))
    # ---- N hat
    def R(L):
        tot=Fr(0)
        for n in range(4,len(kap)):
            if kap[n]:
                tot+=kap[n]*sum(L**i/factorial(i)*Fr(2,3)**(n-i) for i in range(n))
        return tot
    Rl=R(ell); R0=R(Fr(0))
    elo,ehi=exp_bounds(3*ell/2)                # e^{3 ell/2}
    assert Rl>0
    if design=="B":
        R1=R(L1); e1lo,e1hi=exp_bounds(3*L1/2); assert R1>0
        N_lo=2*Rl/ehi-2*R1/e1lo+R0
        N_hi=2*Rl/elo-2*R1/e1hi+R0
    else:
        N_lo=2*Rl/ehi-R0; N_hi=2*Rl/elo-R0
    assert N_lo>0
    # ---- (b),(c): modulus on the line and its partial fractions
    M=lambda i,k: Fr(comb(i+k-2,i-1),2**(i+k-1))      # (1/2pi) int (1+it)^-i (1-it)^-k dt
    g=[Fr(0)]*(m+1)
    if design=="B":
        for i in range(3,m+1): g[i-1]+=h[i]; g[i]-=h[i]       # (s-1) H0
        Q=[[g[i]*g[k]+Z*h[i]*h[k] for k in range(m+1)] for i in range(m+1)]
    else:
        Q=[[h[i]*h[k] for k in range(m+1)] for i in range(m+1)]
    Ihat=sum(Q[i][k]*M(i,k) for i in range(1,m+1) for k in range(1,m+1) if Q[i][k])
    # G = sum_{i,k} Q_ik s^-i (2-s)^-k = sum_a (e_a/2) (s^-a + (2-s)^-a)
    e=[Fr(0)]*(m+1)
    for a in range(1,m+1):
        e[a]=2*sum(Q[i][k]*Fr(comb(i+k-a-1,k-1),2**(i+k-a)) for i in range(a,m+1) for k in range(1,m+1) if Q[i][k])
    assert e[1]==2*Ihat
    # verify the polynomial identity  Num(s) := sum_{i,k} Q_ik s^(m-i) (2-s)^(m-k) = sum_a (e_a/2) ( s^(m-a) (2-s)^m + s^m (2-s)^(m-a) )
    two_s=[Fr(2),Fr(-1)]; pw=[[Fr(1)]]
    for _ in range(m): pw.append(pmul(pw[-1],two_s))
    mono=lambda k:[Fr(0)]*k+[Fr(1)]
    lhs=[Fr(0)]
    for i in range(1,m+1):
        for k in range(1,m+1):
            if Q[i][k]: lhs=padd(lhs,pscale(pmul(mono(m-i),pw[m-k]),Q[i][k]))
    rhs=[Fr(0)]
    for a in range(1,m+1):
        rhs=padd(rhs,pscale(padd(pmul(mono(m-a),pw[m]),pmul(mono(m),pw[m-a])),e[a]/2))
    assert ptrim(padd(lhs,pscale(rhs,-1)))==[], "partial fraction identity fails"
    # and that lhs really is (Z-(s-1)^2) P0(s) P0(2-s)  (P0(s) = s^m H0(s))
    P0=[h[m-j] for j in range(m+1)]                     # P0(s)=sum h_i s^(m-i)
    P0r=[Fr(0)]
    for j,cj in enumerate(P0): P0r=padd(P0r,pscale(pw[j],cj))     # P0(2-s)
    fac=[Fr(1)] if design=="A" else padd([Z],pscale(pmul([Fr(-1),Fr(1)],[Fr(-1),Fr(1)]),-1))
    assert ptrim(padd(pmul(fac,pmul(P0,P0r)),pscale(lhs,-1)))==[]
    print("  (b) |K(1+it)| = G(t) = sum_{k<=%d} e_k Re(1+it)^-k : polynomial identity of degree %d in s verified exactly; G >= 0 structurally"%(m,2*m))
    print("  (c) Ihat = e_1/2 = %.12g (exact rational);   Nhat in [%.12g, %.12g]"%(float(Ihat),float(N_lo),float(N_hi)))
    # ---- c*
    xlo,xhi=exp_bounds(ell)                            # e^{ell}
    cs_hi=(Ihat/N_lo)**2/xlo; cs_lo=(Ihat/N_hi)**2/xhi
    print("  RESULT: c* = e^{-ell} (Ihat/Nhat)^2 in [%.9f, %.9f];   J = Nhat e^{ell/2}/Ihat >= %.8f"%(float(cs_lo),float(cs_hi),float(cs_hi)**-0.5))
    # sizes
    L=1
    from math import lcm
    for n in range(4,len(kap)): L=lcm(L,kap[n].denominator)
    ki=[int(kap[n]*L) for n in range(len(kap))]
    print("  sizes: after clearing denominators the %d coefficients kappa_n are integers with <= %d digits; e_k: <= %s digits (num/den)"%(sum(1 for x in ki if x),max(len(str(abs(x))) for x in ki),max(digits(x) for x in e[1:])))
    out={"design":design,"m":m,"ell":str(ell),"Z":str(Z) if Z is not None else None,"L1":str(d.get("L1") and Fr(*d["L1"])),
         "kappa":{str(n):str(kap[n]) for n in range(4,len(kap))},"e":{str(a):str(e[a]) for a in range(1,m+1)},
         "Ihat":str(Ihat),"N_lo":str(N_lo),"cstar_upper":float(cs_hi),
         "Wt":[str(x) for x in Wt],"bernstein_cells":[[str(a),str(b_)] for a,b_,_ in cells]}
    json.dump(out,open(fn.replace("testfn","certificate"),"w"),indent=0)
    return cs_hi
if __name__=="__main__":
    for fn in sys.argv[1:]: main(fn)
