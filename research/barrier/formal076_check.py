"""Independent floating-point checks of formal076_certificate.py (mpmath quadrature; no closed forms shared):
   (1) Nhat = int_0^lam W(log 1/t) sqrt t dt - int_lam^1 |W(log 1/t)| sqrt t dt,   Ihat = (1/2pi) int |K(1+it)| dt,
       computed from the kappa_n only;  c* = lam (Ihat/Nhat)^2,  lam = e^-ell.
   (2) G(t) = sum e_k Re(1+it)^-k equals |K(1+it)| at sample points.
   (3) sanity of the whole normalisation on designB's kernel K = 6/s^4, ell = log 3 (must give 0.77684).
   (4) Lean-friendly decimal enclosures and a ROUGH (uncertified) estimate of an explicit threshold N0."""
import sys, json
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps=40
def cstar(kap, ell, breaks=()):
    W=lambda L: sum(k*L**(n-1)/mp.factorial(n-1) for n,k in kap.items())
    K=lambda s: sum(k*s**(-n) for n,k in kap.items())
    lam=mp.e**(-ell)
    f=lambda t: W(mp.log(1/t))*mp.sqrt(t)
    pts=[lam]+sorted(mp.e**(-mp.mpf(b)) for b in breaks)+[1]
    Nh=mp.quad(f,mp.linspace(0,lam,12))-sum(mp.quad(lambda t:abs(f(t)),mp.linspace(pts[i],pts[i+1],8)) for i in range(len(pts)-1))
    Ih=mp.quad(lambda t: abs(K(1+1j*t)),[0,0.5,1,2,4,8,16,32,64,128,mp.inf])/mp.pi
    return lam*(Ih/Nh)**2, Nh, Ih, W, K
print("(3) designB kernel 6/s^4, ell = log 3: c* = %s  (designB.md: 0.77684)"%mp.nstr(cstar({4:mp.mpf(6)},mp.log(3))[0],8))
for fn in sys.argv[1:]:
    c=json.load(open(fn)); ell=mp.mpf(Fr(c["ell"]).numerator)/Fr(c["ell"]).denominator
    kap={int(n):mp.mpf(Fr(v).numerator)/Fr(v).denominator for n,v in c["kappa"].items()}
    br=[] if c["design"]=="A" else [mp.mpf(Fr(c["L1"]).numerator)/Fr(c["L1"]).denominator]
    cs,Nh,Ih,W,K=cstar(kap,ell,br)
    Ie=mp.mpf(Fr(c["Ihat"]).numerator)/Fr(c["Ihat"]).denominator; Nl=mp.mpf(Fr(c["N_lo"]).numerator)/Fr(c["N_lo"]).denominator
    print("design %s: (1) quadrature: Nhat = %s, Ihat = %s, c* = %s   | certificate: N_lo = %s, Ihat = %s, c* <= %.9f"%(c["design"],mp.nstr(Nh,14),mp.nstr(Ih,14),mp.nstr(cs,10),mp.nstr(Nl,14),mp.nstr(Ie,14),c["cstar_upper"]))
    e={int(a):mp.mpf(Fr(v).numerator)/Fr(v).denominator for a,v in c["e"].items()}
    err=max(abs(sum(ek*mp.re((1+1j*t)**(-k)) for k,ek in e.items())-abs(K(1+1j*mp.mpf(t))))/abs(K(1+1j*mp.mpf(t))) for t in [0,0.3,1,2.5,7,20,100])
    print("          (2) max relative |G - |K|| at 7 sample points: %s"%mp.nstr(err,3))
    # (4)
    import math
    up=lambda x,d: math.ceil(x*10**d)/10**d
    dn=lambda x,d: math.floor(x*10**d)/10**d
    print("          (4) e^{3ell/2} <= %.9f, e^{ell} >= %.9f%s"%(up(float(mp.e**(1.5*ell)),9),dn(float(mp.e**ell),9),"" if not br else ", e^{3 L1/2} >= %.9f"%dn(float(mp.e**(1.5*br[0])),9)))
    J=mp.e**(ell/2)*Nh/Ih; Z2=mp.mpf('0.046136')
    e1=4*W(ell)*mp.sqrt(Z2)*mp.e**(-5*ell/4)/Ih            # loss  e1 x^{1/4}  (in units of Ihat) from the sharp cut at X (Lemma 6 of designB)
    print("          rough explicit threshold (leading terms only: (J sqrt c - 1) L >= e1 e^{ell/4} c^{1/4} sqrt L, e1 = %s; O(1) terms ignored):"%mp.nstr(e1,4))
    for cc in [0.7615,0.762,0.765,0.77,0.775]:
        a=J*mp.sqrt(cc)-1
        if a>0:
            L0=(e1*mp.e**(ell/4)*cc**0.25/a)**2
            print("             c = %.4f: log n >~ %s  (n >~ 10^%s)"%(cc,mp.nstr(L0,4),mp.nstr(L0/mp.log(10),4)))
