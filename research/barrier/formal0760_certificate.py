"""Exact certificate for formal0760.md (stdlib only; every inequality is between rationals).  Generalises
formal076_certificate.py to (i) a pole at s = -a (a = beta-1 >= 0 integer; weights sqrt(n) (n/x)^a W(log(x/n))) and
(ii) p >= 1 exact sign changes.   Variable sg = s + a (pole at sg = 0, zeros on Re sg = beta).

  Data (formal0760_testfn_*.json): beta, ell, L = [L_1 < ... < L_p] (rationals), m, integers h_i (i = p+2..m).
    H0(sg) = sum h_i sg^-i,   K = Q H0^2,   Q = sum_{a<=p} zeta_a (-(sg-beta)^2)^a,  zeta_p = 1,
    zeta_0..zeta_{p-1} := the rational solution of W(L_i) = 0 (i = 1..p).
    K = sum_{n=4}^{2m} kappa_n sg^-n,  W(L) = sum kappa_n L^(n-1)/(n-1)!.
  Certified:
    (a) zeta_a > 0 for all a (so Q(-t^2) = sum zeta_a t^(2a) > 0);
    (b) W = L^3 prod (L - L_i) Wt, Wt > 0 on [0, ell] (Bernstein coefficients, no subdivision unless needed):
        sign of W on [L_i, L_{i+1}] is (-1)^(p-i)  (L_0 = 0, L_{p+1} = ell);
    (c) |K(beta+it)| = G(t) := sum_{k<=m} e_k Re (beta+it)^-k  (two polynomial identities);  Ihat = e_1/2;
    (d) Nhat = F(ell) - sum_i (-1)^(p-i) (F(L_i) - F(L_{i+1})),  F(L) = e^{-(beta+1/2) L} R(L),
        R(L) = sum_n kappa_n sum_{i<n} L^i/i! (beta+1/2)^-(n-i);
    =>  c* = e^{-ell} (Ihat/Nhat)^2 <= bound.
  usage: formal0760_certificate.py testfn.json [...]"""
import sys, json
from fractions import Fraction as Fr
from math import comb, factorial, lcm
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
def bernstein(p,lo,hi):
    n=len(p)-1; q=[Fr(0)]
    for c in reversed(p): q=padd(pmul(q,[lo,hi-lo]),[c])
    q=q+[Fr(0)]*(n+1-len(q))
    return [sum(Fr(comb(k,i),comb(n,i))*q[i] for i in range(k+1)) for k in range(n+1)]
def exp_bounds(a,n=90):
    assert a>=0 and n+1>a
    S=Fr(0); t=Fr(1)
    for k in range(n): S+=t; t=t*a/(k+1)
    return S, S+t/(1-a/(n+1))
def solve(A,b):
    n=len(A); M=[list(A[i])+[b[i]] for i in range(n)]
    for i in range(n):
        piv=next(r for r in range(i,n) if M[r][i]!=0); M[i],M[piv]=M[piv],M[i]
        M[i]=[x/M[i][i] for x in M[i]]
        for r in range(n):
            if r!=i and M[r][i]!=0: M[r]=[x-M[r][i]*y for x,y in zip(M[r],M[i])]
    return [M[i][n] for i in range(n)]
def digits(x): return len(str(abs(x.numerator))), len(str(x.denominator))
def round_dec(x,nd,up):
    """decimal rounding of a positive rational to nd significant digits, upwards or downwards"""
    from math import floor, ceil
    e=0; y=x
    while y>=10: y/=10; e+=1
    while y<1: y*=10; e-=1
    sc=Fr(10)**(nd-1); z=(ceil(y*sc) if up else floor(y*sc))
    return Fr(z)/sc*Fr(10)**e
def main(fn, expdigits=None):
    d=json.load(open(fn)); beta=Fr(d["beta"]); m=d["m"]; ell=Fr(*d["ell"]); Ls=[Fr(*x) for x in d["L"]]; p=len(Ls)
    assert all(Ls[i]<Ls[i+1] for i in range(p-1)) and 0<Ls[0] and Ls[-1]<ell
    i0=p+2; h=[Fr(0)]*i0+[Fr(x) for x in d["h"]]; assert len(h)==m+1
    if d.get("scaled"): h=[x*beta**i for i,x in enumerate(h)]            # data given in powers of u = beta/sg
    rate=beta+Fr(1,2)
    print("%s: beta = %s (pole at s = %s; weights sqrt(n) (n/x)^%s log^j(x/n), 3 <= j <= %d), p = %d, m = %d (pole order %d), ell = %s, L = %s"%(d.get("name",fn),beta,-(beta-1),beta-1,2*m-1,p,m,2*m,ell,[str(x) for x in Ls]))
    c=pmul(h,h)                                           # H0^2, index = power of 1/sg
    def mulq(k_):                                         # multiply by -(sg-beta)^2
        out=[Fr(0)]*len(k_)
        for k,ck in enumerate(k_):
            if ck: out[k-2]-=ck; out[k-1]+=2*beta*ck; out[k]-=beta*beta*ck
        return out
    kas=[c]
    for a in range(p): kas.append(mulq(kas[-1]))
    W_of=lambda kap:[kap[n]/factorial(n-1) for n in range(1,len(kap))]
    Ws=[W_of(k_) for k_ in kas]
    zeta=solve([[peval(Ws[a],L) for a in range(p)] for L in Ls],[-peval(Ws[p],L) for L in Ls])+[Fr(1)]
    assert all(z>0 for z in zeta), "Q must have positive coefficients"
    print("  (a) Q(-T) = sum zeta_a T^a, zeta = %s  (all > 0; digits num/den: %s)"%(["%.6g"%float(z) for z in zeta],[digits(z) for z in zeta]))
    kap=[sum(zeta[a]*kas[a][n] for a in range(p+1)) for n in range(len(c))]
    assert all(kap[n]==0 for n in range(4)), "K must be O(sg^-4)"
    W=W_of(kap)
    den=[Fr(0),Fr(0),Fr(0),Fr(1)]
    for L in Ls: den=pmul(den,[-L,Fr(1)])
    Wt,rem=pdivmod(W,den); assert not ptrim(rem); Wt=ptrim(Wt)
    todo=[(Fr(0),ell)]; cells=[]
    while todo:
        lo,hi=todo.pop(); b=bernstein(Wt,lo,hi)
        if min(b)>0: cells.append((lo,hi,b))
        else:
            assert hi-lo>Fr(1,10**4), "Wt not positive"; mid=(lo+hi)/2; todo+=[(lo,mid),(mid,hi)]
    cells.sort()
    print("  (b) W = L^3 prod(L - L_i) Wt, deg Wt = %d; Bernstein: all coefficients > 0 on %d cell(s) %s (min/max %s)"%(len(Wt)-1,len(cells),", ".join("[%s,%s]"%(a,b_) for a,b_,_ in cells),", ".join("%.1e"%float(min(b)/max(b)) for _,_,b in cells)))
    def R(L):
        tot=Fr(0)
        for n in range(4,len(kap)):
            if kap[n]: tot+=kap[n]*sum(L**i/factorial(i)/rate**(n-i) for i in range(n))
        return tot
    pts=[Fr(0)]+Ls+[ell]; coef=[Fr(0)]*(p+2); coef[p+1]+=1
    for i in range(p+1):
        s=(-1)**(p-i); coef[i]-=s; coef[i+1]+=s
    N_lo=Fr(0); N_hi=Fr(0); Rv=[R(x) for x in pts]; encl=[]
    for x,cf,r in zip(pts,coef,Rv):
        if cf==0: continue
        lo,hi=exp_bounds(rate*x)                         # e^{rate x}
        if expdigits and x!=0: lo,hi=round_dec(lo,expdigits,False),round_dec(hi,expdigits,True)
        encl.append((rate*x,lo,hi))
        t=cf*r
        N_lo+= t/hi if t>0 else t/lo; N_hi+= t/lo if t>0 else t/hi
    assert N_lo>0
    g=[h]
    for a in range(p):                                    # (sg-beta) * X : sg^-i -> sg^-(i-1) - beta sg^-i
        prev=g[-1]; nx=[Fr(0)]*(m+1)
        for i,x in enumerate(prev):
            if x: nx[i-1]+=x; nx[i]-=beta*x
        g.append(nx)
    Q=[[sum(zeta[a]*g[a][i]*g[a][k] for a in range(p+1)) for k in range(m+1)] for i in range(m+1)]
    tb=2*beta
    e=[Fr(0)]*(m+1)
    for a in range(1,m+1):
        e[a]=2*sum(Q[i][k]*Fr(comb(i+k-a-1,k-1))/tb**(i+k-a) for i in range(a,m+1) for k in range(1,m+1) if Q[i][k])
    Ihat=sum(Q[i][k]*Fr(comb(i+k-2,i-1))/tb**(i+k-1) for i in range(1,m+1) for k in range(1,m+1) if Q[i][k])
    assert e[1]==2*Ihat and Ihat>0
    two_s=[tb,Fr(-1)]; pw=[[Fr(1)]]
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
    P0=[h[m-j] for j in range(m+1)]; P0r=[Fr(0)]
    for j,cj in enumerate(P0): P0r=padd(P0r,pscale(pw[j],cj))
    qf=[Fr(0)]; base=pscale(pmul([-beta,Fr(1)],[-beta,Fr(1)]),-1); pwq=[Fr(1)]
    for a in range(p+1): qf=padd(qf,pscale(pwq,zeta[a])); pwq=pmul(pwq,base)
    assert ptrim(padd(pmul(qf,pmul(P0,P0r)),pscale(lhs,-1)))==[]
    # K sg^(2m) = Q P0^2
    Kp=[kap[2*m-j] if 2*m-j<len(kap) else Fr(0) for j in range(2*m+1)]
    assert ptrim(padd(pmul(qf,pmul(P0,P0)),pscale(Kp,-1)))==[]
    print("  (c) |K(beta+it)| = G(t) = sum_{k<=%d} e_k Re(beta+it)^-k: identities of degree %d verified; Ihat = e_1/2 = %.12g"%(m,2*m,float(Ihat)))
    xlo,xhi=exp_bounds(ell)
    if expdigits: xlo,xhi=round_dec(xlo,expdigits,False),round_dec(xhi,expdigits,True)
    cs_hi=(Ihat/N_lo)**2/xlo; cs_lo=(Ihat/N_hi)**2/xhi
    print("  (d) Nhat in [%.12g, %.12g]   (terms coef*R(L_i)/Ihat: %s)"%(float(N_lo),float(N_hi),", ".join("%.3f"%float(cf*r/Ihat) for cf,r in zip(coef,Rv))))
    print("  RESULT%s: c* in [%.9f, %.9f];  J >= %.8f"%((" (%d-digit exp enclosures)"%expdigits) if expdigits else "",float(cs_lo),float(cs_hi),float(cs_hi)**-0.5))
    Lc=1
    for n in range(4,len(kap)): Lc=lcm(Lc,kap[n].denominator)
    ki=[int(kap[n]*Lc) for n in range(len(kap))]
    ks=[kap[n]/beta**n for n in range(len(kap))]; Ls_=1                  # scaled variable s'' = sg/beta: kappa''_n = kappa_n/beta^n, e''_k = e_k/beta^k
    for x in ks: Ls_=lcm(Ls_,x.denominator)
    ksi=[int(x*Ls_) for x in ks]; es=[e[k]/beta**k for k in range(1,m+1)]
    print("  sizes in the scaled variable s'' = sg/beta: |h_i| <= 10^%d; kappa''_n integers <= %d digits; e''_k <= %s digits"%(len(str(max(abs(int(x)) for x in d["h"])))-1,max(len(str(abs(x))) for x in ksi),max(digits(x) for x in es)))
    # scaled variable s'' = sg/beta (zeros on Re s'' = 1): kappa''_n = kappa_n / beta^n
    if not d.get("scaled"): print("  sizes: |h_i| <= 10^%d; kappa_n (integers after clearing one denominator): <= %d digits; e_k: <= %s digits (num/den); Bernstein coefficients (integers): <= %d digits"%(len(str(max(abs(int(x)) for x in h)))-1,max(len(str(abs(x))) for x in ki),max(digits(x) for x in e[1:]),max(len(str(abs(int(b*lcm(*[y.denominator for y in cells[0][2]]))))) for b in cells[0][2])))
    if not expdigits:
        out={"name":d.get("name"),"beta":str(beta),"p":p,"m":m,"ell":str(ell),"L":[str(x) for x in Ls],"zeta":[str(z) for z in zeta],
             "kappa":{str(n):str(kap[n]) for n in range(4,len(kap))},"e":{str(a):str(e[a]) for a in range(1,m+1)},
             "Ihat":str(Ihat),"N_lo":str(N_lo),"cstar_upper":float(cs_hi),"Wt":[str(x) for x in Wt],
             "bernstein_cells":[[str(a),str(b_)] for a,b_,_ in cells],"exp_arguments":[str(x[0]) for x in encl]+[str(ell)]}
        json.dump(out,open(fn.replace("testfn","certificate"),"w"),indent=0)
    return cs_hi
if __name__=="__main__":
    for fn in sys.argv[1:]:
        main(fn); main(fn,expdigits=9)
