from gen import *
def dec(fr):
    s=str(float(fr))
    assert Fr(s)==fr, (s,fr)
    return s
def emit_row(name, wrapper, extra_hyp, a,b,d,c,N, hyps_decl, hyps_use):
    r,err=pieces(a,b,d,c,N*2.30257)
    assert r,(name,err)
    k,W0,out=r
    ks=dec(k)
    L=[]
    L.append(f"theorem {name} {hyps_decl} :\n    ∀ n : ℕ, (10 : ℝ) ^ {N} ≤ n → R11Bound {c} n := by")
    L.append("  intro n hn")
    L.append("  have hL := r11Asm_log_ge_of_pow hn")
    L.append(f"  have hn0 : (((({int(W0*100)} : ℕ) : ℝ) / 100) ^ 2 ≤ {ks} * Real.log n) := by\n    norm_num at hL ⊢; linarith")
    ind="  "
    for idx,(lo,hi,l1,p,marg) in enumerate(out):
        A=int(lo*100); pp=int(l1*100)
        assert lo**4>=250
        hname=f"hn{idx}"
        if hi is not None:
            L.append(f"{ind}by_cases h{idx} : √({ks} * Real.log n) ≤ {dec(hi)}")
            P=f"(fun W => W ≤ ({dec(hi)} : ℝ))"
            ind2=ind+"  "
            L.append(f"{ind}· refine {wrapper} {hyps_use} (c := {c}) (k := {ks})")
            hP=f"h{idx}"
            intro="intro W h0 h1\n"+ind2+"have h1' : W ≤ "+dec(hi)+" := h1"
        else:
            P="(fun _ => True)"
            ind2=ind
            L.append(f"{ind}refine {wrapper} {hyps_use} (c := {c}) (k := {ks})")
            hP="trivial"
            intro="intro W h0 _"
        L.append(f"{ind2}    (W₀ := (({A} : ℕ) : ℝ) / 100) (l₁ := (({pp} : ℕ) : ℝ) / 100) {P}")
        L.append(f"{ind2}    (by norm_num) (by norm_num) (by norm_num) (by norm_num){extra_hyp}")
        L.append(f"{ind2}    (r11Asm_log4_le {A} {pp} (by norm_num) (by decide +kernel)) (by norm_num) ?_ n {hname} {hP}")
        L.append(f"{ind2}{intro}")
        L.append(f"{ind2}norm_num [r11AsmErr] at h0 ⊢")
        L.append(f"{ind2}nlinarith [sq_nonneg (W - {dec(p)})]")
        if hi is not None:
            L.append(f"{ind}· have hn{idx+1} : (((({int(hi*100)} : ℕ) : ℝ) / 100) ^ 2 ≤ {ks} * Real.log n) := by")
            L.append(f"{ind}    have := (Real.lt_sqrt (by norm_num)).mp (not_le.mp h{idx})")
            L.append(f"{ind}    norm_num at this ⊢; linarith")
            ind=ind+"  "
    return "\n".join(L)+"\n", [(float(lo), hi and float(hi), float(l1), round(m,3)) for lo,hi,l1,p,m in out]

H_decl="(hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)\n    (hC : R11ChiExplicit) (hG : R11ZeroSumGain)"
H_use="hGRH hZ hA hC hG"
out=[]
info=[]
for c,N,nm in (('0.95',12,'95'),('0.9',14,'90'),('0.85',16,'85'),('0.8',19,'80')):
    s,i=emit_row(f"r11Asm_rowA_{nm}","r11Asm_rowA","",'2','0','0',c,N,H_decl+" (hT : R11Tail 2)",H_use+" hT")
    out.append(s); info.append((c,N,i))
for c,N,nm in (('0.95',9,'95'),('0.9',10,'90'),('0.85',11,'85'),('0.8',13,'80'),('0.79',13,'79'),('0.78',14,'78')):
    s,i=emit_row(f"r11Asm_rowB_{nm}","r11Asm_rowB"," (by norm_num)",'1.093','1.84','1.1734',c,N,H_decl,H_use)
    out.append(s); info.append((c,N,i))
open("rows.lean","w").write("\n".join(out))
for x in info: print(x)
