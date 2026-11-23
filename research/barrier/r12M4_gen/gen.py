"""r12M4 generator: constants of the (h, lambda) = (4, 1/4) core and the row search.
Core (X = W^4, x = 4X, lo = 1.38629 <= log 4 <= hi = 1.3863), divided by 3:
  Dc W^6 - e1 W^5 + K0 W^4 <= 6 L W^4 + 24 T W^4 + (L+1.30) lam^3 + 27.93 lam^2 + 98.73 lam + 198.31
      + c1 r1 W + c2 r1 + c3 r2 + (4/3) r3 + (1/3) r3x."""
from fractions import Fraction as Fr
from math import *
lo=Fr('1.38629'); hi_l=Fr('1.3863')
EXP_LO=Fr('2.7182818283')
def dn(v,d): return Fr(floor(v*10**d),10**d)
def up(v,d): return Fr(ceil(v*10**d),10**d)
Dc_exact=Fr(4,3)*(lo**3*Fr(2,3)+3*lo**2*Fr(4,9)+3*lo*Fr(16,27)+Fr(32,27))-Fr(32,27)*Fr(8,3)
Dc=dn(Dc_exact,4)
e1=up(Fr(4,3)*lo**3*Fr('0.4336'),4)
e2_exact=Fr(4,3)*(3*lo**2*Fr('0.047')+3*lo*2*Fr('0.002375')+6*Fr('0.00012'))+Fr(1,3)*6*Fr('0.00012')*4
K0=dn(Fr('74.4')-e2_exact,4)
c1=up(Fr(4,3)*lo**3*2/Fr('0.4336'),4)
c2=up(4*lo**2,4)
c3=up(4*lo,4)
# r1 = 1.771 l + 0.788 ; r2 = 1.771 l^2 + 0.296 l + 2.561 ; r3 = 1.771 l^3 + 0.444 l^2 + 3.843 l + 3.8915
g=[Fr('1.771'),Fr('0.788')]; g2=[Fr('1.771'),Fr('0.296'),Fr('2.561')]; g3=[Fr('1.771'),Fr('0.444'),Fr('3.843'),Fr('3.8915')]
# Err coefficients
E={}
E['lam3_W4']=up(Fr('1.30')+g3[0]/3,3)          # lam^3
E['lam2_W4']=up(Fr('27.93')+g3[1]/3,3)
E['lam1_W4']=up(Fr('98.73')+g3[2]/3,3)
E['const_W4']=up(Fr('198.31')+g3[3]/3+c2*g[1]+c3*g2[2]+Fr(4,3)*g3[3],3)
E['l1_W3']=up(c1*g[0],3)
E['l0_W3']=up(c1*g[1],3)
E['l1_W4']=up(c2*g[0]+c3*g2[1]+Fr(4,3)*g3[2],3)
E['l2_W4']=up(c3*g2[0]+Fr(4,3)*g3[1],3)
E['l3_W4']=up(Fr(4,3)*g3[0],3)
def Err(a,b,d,ik,W0,l1):
    L1=l1+hi_l
    return (72*a*l1/W0**2+(168*a+24*d)/W0**2+36*b*l1/W0**4+48*b/W0**4+ik*L1**3/W0**2
        +E['lam3_W4']*L1**3/W0**4+E['lam2_W4']*L1**2/W0**4+E['lam1_W4']*L1/W0**4+E['const_W4']/W0**4
        +E['l1_W3']*l1/W0**3+E['l0_W3']/W0**3+E['l1_W4']*l1/W0**4+E['l2_W4']*l1**2/W0**4+E['l3_W4']*l1**3/W0**4)
def pieces(a,b,d,c,L0,kdig=5,margin=Fr('0.03'),k=None):
    a,b,d=Fr(a),Fr(b),Fr(d)
    if k is None: k=Fr(floor(sqrt(float(c))*10**kdig),10**kdig)
    assert k*k<=Fr(c)
    ik=1/k
    al=Dc-6*ik; be=e1; C=K0
    assert al>0
    f=lambda w: al*w*w-be*w+C
    fp=lambda w: 2*al*w-be
    v=be/(2*al)
    W0=Fr(floor(sqrt(float(k)*L0)*100),100)
    assert W0*W0<=k*Fr(L0).limit_denominator(10**6)
    out=[]; lo_=W0
    while True:
        l1=Fr(ceil(4*log(float(lo_))*100),100)
        while (lo_**4)**100 > EXP_LO**int(l1*100): l1+=Fr(1,100)
        l1=max(l1,Fr(6))
        Ev=Err(a,b,d,ik,lo_,l1)
        p=max(lo_, Fr(ceil(float(v)*100),100))
        assert fp(p)>=0
        if Ev+margin < f(p)-fp(p)*(p-lo_):
            out.append((lo_,None,l1,p,float(f(p)-fp(p)*(p-lo_)-Ev)))
            break
        step=Fr(1,100)
        # largest h<=v with E+margin<f(h) (f decreasing on [lo,v])
        if not (Ev+margin<f(lo_+step)): return None,(float(Ev),float(f(lo_)),float(lo_))
        a_,b_=lo_+step,min(v,lo_+10**6)
        a_i=int(a_*100); b_i=int(floor(b_*100))
        while a_i<b_i:
            mid=(a_i+b_i+1)//2
            if Ev+margin<f(Fr(mid,100)): a_i=mid
            else: b_i=mid-1
        best=Fr(a_i,100)
        out.append((lo_,best,l1,best,float(f(best)-Ev)))
        lo_=best
        if len(out)>40: return None,"too many"
    return (k,W0,out),None
if __name__=="__main__":
    print("Dc",Dc,float(Dc_exact),"e1",e1,"K0",K0,"c1",c1,"c2",c2,"c3",c3)
    print(E)
    print("c_inf = (6/Dc)^2 =",float((6/Dc)**2))
    for a,b,d in (('1.093','1.84','1.1734'),):
        for c in ('0.75','0.72','0.7','0.69','0.68','0.67','0.66','0.65','0.645'):
            for N in range(6,80):
                try: r,err=pieces(a,b,d,c,N*2.30257)
                except AssertionError: continue
                if r:
                    k,W0,out=r
                    if float(W0)**4<250 or W0<3: continue
                    print(c,"N=",N,"k",float(k),"W0",float(W0),"pieces",len(out),[(float(x[0]),x[1] and float(x[1]),float(x[2]),float(x[3]),round(x[4],3)) for x in out][:8])
                    break
