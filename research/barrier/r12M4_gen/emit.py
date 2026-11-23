from gen import *
def dec(fr):
    s=str(float(fr))
    assert Fr(s)==fr, (s,fr)
    return s
H_decl="(hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)\n    (hC : R11ChiExplicit) (hG : R11ZeroSumGain)"
H_use="hGRH hZ hA hC hG"
def emit_row(name,c,N):
    r,err=pieces('1.093','1.84','1.1734',c,N*2.30257)
    assert r,(name,err)
    k,W0,out=r
    ks=dec(k)
    L=[]
    L.append(f"theorem {name} {H_decl} :\n    ∀ n : ℕ, (10 : ℝ) ^ {N} ≤ n → R12Bound {c} n := by")
    L.append("  intro n hn")
    L.append("  have hL := r11Asm_log_ge_of_pow hn")
    L.append(f"  have hn0 : (((({int(W0*100)} : ℕ) : ℝ) / 100) ^ 2 ≤ {ks} * Real.log n) := by\n    norm_num at hL ⊢; linarith")
    ind="  "
    for idx,(lo_,hi,l1,p,marg) in enumerate(out):
        A=int(lo_*100); pp=int(l1*100)
        assert lo_**4>=250 and lo_>=3
        hname=f"hn{idx}"
        if hi is not None:
            L.append(f"{ind}by_cases h{idx} : √({ks} * Real.log n) ≤ {dec(hi)}")
            P=f"(fun W => W ≤ ({dec(hi)} : ℝ))"
            ind2=ind+"  "
            L.append(f"{ind}· refine r12_rowB {H_use} (c := {c}) (k := {ks})")
            hP=f"h{idx}"
            intro="intro W h0 h1\n"+ind2+"have h1' : W ≤ "+dec(hi)+" := h1"
        else:
            P="(fun _ => True)"
            ind2=ind
            L.append(f"{ind}refine r12_rowB {H_use} (c := {c}) (k := {ks})")
            hP="trivial"
            intro="intro W h0 _"
        L.append(f"{ind2}    (W₀ := (({A} : ℕ) : ℝ) / 100) (l₁ := (({pp} : ℕ) : ℝ) / 100) {P}")
        L.append(f"{ind2}    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
        L.append(f"{ind2}    (r11Asm_log4_le {A} {pp} (by norm_num) (by decide +kernel)) (by norm_num) ?_ n {hname} {hP}")
        L.append(f"{ind2}{intro}")
        L.append(f"{ind2}norm_num [r12Err] at h0 ⊢")
        L.append(f"{ind2}nlinarith [sq_nonneg (W - {dec(p)})]")
        if hi is not None:
            L.append(f"{ind}· have hn{idx+1} : (((({int(hi*100)} : ℕ) : ℝ) / 100) ^ 2 ≤ {ks} * Real.log n) := by")
            L.append(f"{ind}    have := (Real.lt_sqrt (by norm_num)).mp (not_le.mp h{idx})")
            L.append(f"{ind}    norm_num at this ⊢; linarith")
            ind=ind+"  "
    return "\n".join(L)+"\n", [(float(lo_), hi and float(hi), float(l1), round(m,3)) for lo_,hi,l1,p,m in out]
out=[]
for c,N,nm in (('0.75',10,'75'),('0.72',10,'72'),('0.7',11,'70'),('0.68',11,'68'),('0.66',12,'66'),('0.65',13,'65')):
    s,i=emit_row(f"r12_row_{nm}",c,N)
    out.append(s); print(c,N,i)
open("rows.lean","w").write("\n".join(out))
# eventual row
k=Fr('0.80106'); W0=Fr(10000); l1=Fr(37)
assert k*k<=Fr('0.6417')
ik=1/k; al=Dc-6*ik
E_=Err(Fr('1.093'),Fr('1.84'),Fr('1.1734'),ik,W0,l1)
f=lambda w: al*w*w-e1*w+K0
print("eventual: al",float(al),"Err",float(E_),"f(W0)",float(f(W0)),"f'(W0)",float(2*al*W0-e1), "k^2", float(k*k))
