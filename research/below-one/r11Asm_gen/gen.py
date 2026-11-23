from fractions import Fraction as Fr
from math import *
hi_l3=Fr('1.0987')
EXP_LO=Fr('2.7182818283')
def Err(a,b,d,ik,W0,l1):
    L1=l1+hi_l3
    return (54*a*l1/W0**2+(126*a+18*d)/W0**2+27*b*l1/W0**4+36*b/W0**4+ik*L1**3/W0**2
        +Fr('3.071')*L1**3/W0**4+Fr('28.374')*L1**2/W0**4+Fr('102.573')*L1/W0**4+Fr('232.58')/W0**4
        +Fr('21.664')*l1/W0**3+Fr('9.639')/W0**3+Fr('22.463')*l1/W0**4+Fr('12.562')*l1**2/W0**4+Fr('3.542')*l1**3/W0**4)
def pieces(a,b,d,c,L0,kdig=5,margin=Fr('0.03'),verbose=False):
    a,b,d=Fr(a),Fr(b),Fr(d)
    k=Fr(floor(sqrt(float(c))*10**kdig),10**kdig)
    assert k*k<=Fr(c)
    ik=1/k
    al=Fr('5.1046')-Fr('4.5')*ik; be=Fr('1.1499'); C=Fr('55.4247')
    assert al>0
    f=lambda w: al*w*w-be*w+C
    fp=lambda w: 2*al*w-be
    v=be/(2*al)
    W0=Fr(floor(sqrt(float(k)*L0)*100),100)
    assert W0*W0<=k*Fr(L0).limit_denominator(10**6)
    out=[]; lo=W0
    while True:
        l1=Fr(ceil(4*log(float(lo))*100),100)
        while (lo**4)**100 > EXP_LO**int(l1*100): l1+=Fr(1,100)
        l1=max(l1,Fr(6))
        E=Err(a,b,d,ik,lo,l1)
        p=max(lo, Fr(ceil(float(v)*100),100))
        assert fp(p)>=0
        if E+margin < f(p)-fp(p)*(p-lo):
            out.append((lo,None,l1,p,float(f(p)-fp(p)*(p-lo)-E)))
            break
        # bounded piece, hi<=v
        hi=None
        step=Fr(1,100)
        h=lo+step
        best=None
        while h<=v:
            if E+margin< f(h): best=h
            else: break
            h+=step
        if best is None:
            return None,(float(E),float(f(lo)),float(lo))
        # use big steps
        out.append((lo,best,l1,best,float(f(best)-E)))
        lo=best
        if len(out)>60: return None,"too many"
    return (k,W0,out),None
if __name__=="__main__":
    for a,b in (('2','0'),('1.3863','1.84')):
        for c in ('0.95','0.9','0.85','0.8','0.79','0.78'):
            for N in range(8,40):
                r,err=pieces(a,b,'0',c,N*2.30257)
                if r:
                    k,W0,out=r
                    print(a,b,c,"N=",N,"k",float(k),"W0",float(W0),"pieces",len(out),[(float(x[0]),x[1] and float(x[1]),float(x[2]),float(x[3]),round(x[4],3)) for x in out][:6])
                    break
