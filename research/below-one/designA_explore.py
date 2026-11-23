import numpy as np, warnings, json
warnings.filterwarnings("ignore")
from scipy import optimize
from math import factorial, pi
t=np.concatenate([np.linspace(0,40,8001),np.geomspace(40,20000,4000)[1:]])
u=np.linspace(0,1,2001)
out={}
def run(K,kmin=2):
    ks=list(range(kmin,K+1))
    basis=[]
    for k in ks:
        r=factorial(k)*np.ones_like(t,dtype=complex)
        for j in range(k+1): r=r/(0.5+j+1j*t)
        basis.append(r)
    basis=np.array(basis)
    def J(p,full=False):
        c=p[:-1]; lam=1/(1+np.exp(-p[-1]))
        I=np.trapz(np.abs(c@basis),t)/pi
        w=sum(ci*(1-u)**k for ci,k in zip(c,ks))
        pen=1e4*np.sum(np.minimum(w-1e-4*(1-u)**2*abs(w[0]),0)**2)/w[0]**2
        tot=sum(ci/(k+1) for ci,k in zip(c,ks))
        upto=sum(ci*(1-(1-lam)**(k+1))/(k+1) for ci,k in zip(c,ks))
        D=2*upto-tot
        if D<=1e-6: return 1e6
        return lam*I*I/D**2+pen
    best=(9,None)
    for b0 in ks[-3:]:
        p0=np.zeros(len(ks)+1); p0[ks.index(b0)]=1; p0[-1]=np.log(0.4/0.6)
        r=optimize.minimize(J,p0,method='BFGS',options={'maxiter':300})
        for _ in range(3):
            r=optimize.minimize(J,r.x,method='Nelder-Mead',options={'maxiter':40000,'xatol':1e-9,'fatol':1e-11})
        if r.fun<best[0]: best=(r.fun,r.x)
    x=best[1]
    w=sum(ci*(1-u)**k for ci,k in zip(x[:-1],ks)); c=x[:-1]/w[0]; w=w/w[0]
    lam=1/(1+np.exp(-x[-1]))
    print(K,"c_inf=%.5f lam=%.4f"%(best[0],lam),"min w/(1-u)^2=%.3e"%((w[:-1]/(1-u[:-1])**2).min()),"monotone:",bool(np.all(np.diff(w)<=1e-12)))
    print("  coeffs (k=2..K), w(0)=1:",[float("%.6f"%v) for v in c])
    print("  w at u=0,.1,...:",np.round(w[::200],4))
    out[K]=dict(c=list(map(float,c)),lam=float(lam))
for K in (4,6,8): run(K)
json.dump(out,open("weights.json","w"))
