"""Independent floating check of formal0760 certificates (mpmath quadrature from the kappa_n alone, no closed forms).
   phi(L) = W(L) e^{-beta L} (L = log(x/n) >= 0),  W(L) = sum kappa_n L^(n-1)/(n-1)!,   K(beta+it) = sum kappa_n (beta+it)^-n.
   Nhat = int_ell^inf W e^{-(beta+1/2)L} dL - int_0^ell |W| e^{-(beta+1/2)L} dL,   Ihat = (1/2pi) int |K(beta+it)| dt,
   c* = e^{-ell} (Ihat/Nhat)^2 (= J^-2 in the normalisation of inside.md);  also |K| = G at sample points.
   usage: formal0760_check.py certificate.json [...]"""
import sys, json
from fractions import Fraction as Fr
import mpmath as mp
def main(fn):
    d=json.load(open(fn)); beta=Fr(d["beta"]); ell=Fr(d["ell"]); Ls=[Fr(x) for x in d["L"]]; m=d["m"]
    mp.mp.dps=70 if m<=30 else 260
    kap={int(n):mp.mpf(Fr(v).numerator)/Fr(v).denominator for n,v in d["kappa"].items()}
    e={int(k):mp.mpf(Fr(v).numerator)/Fr(v).denominator for k,v in d["e"].items()}
    b=mp.mpf(beta.numerator)/beta.denominator; l=mp.mpf(ell.numerator)/ell.denominator; r=b+mp.mpf(1)/2
    W=lambda L: sum(k*L**(n-1)/mp.factorial(n-1) for n,k in kap.items())
    K=lambda t: sum(k/(b+1j*t)**n for n,k in kap.items())
    G=lambda t: sum(ek*mp.re(1/(b+1j*t)**k) for k,ek in e.items())
    pts=[mp.mpf(0)]+[mp.mpf(x.numerator)/x.denominator for x in Ls]+[l]
    # locate the actual sign changes of W on (0, ell) on a grid (independent of the certified pattern)
    grid=[l*i/600 for i in range(1,600)]; sg=[mp.sign(W(x)) for x in grid]
    roots=[grid[i] for i in range(1,len(grid)) if sg[i]!=sg[i-1]]
    Nneg=mp.quad(lambda L: abs(W(L))*mp.exp(-r*L), pts)
    Npos=mp.quad(lambda L: W(L)*mp.exp(-r*L), [l,l+2,l+5,l+10,l+20,l+40,mp.inf])
    Nhat=Npos-Nneg
    Ihat=mp.quad(lambda t: abs(K(t)), [0,1,2,4,7,10,15,20,30,45,70,110,200,500,mp.inf])/mp.pi
    cs=mp.exp(-l)*(Ihat/Nhat)**2
    dev=max(abs(abs(K(t))-G(t))/abs(K(t)) for t in [0,0.3,1,2.5,7,20,60])
    print("%s: sign changes of W observed near L = %s (certified zeros %s);  Nhat = %s  Ihat = %s (certificate e_1/2 = %s)"%(d["name"],[mp.nstr(x,4) for x in roots],[str(x) for x in Ls],mp.nstr(Nhat,12),mp.nstr(Ihat,12),mp.nstr(e[1]/2,12)))
    print("   c* = %s   (certificate: %.9f);   max rel |G - |K|| at 7 sample points: %s"%(mp.nstr(cs,10),d["cstar_upper"],mp.nstr(dev,3)))
if __name__=="__main__":
    for fn in sys.argv[1:]: main(fn)
