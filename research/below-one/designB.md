# Design B: an explicit least-non-residue constant c < 1 under GRH from the rational kernel 6/(s+1)⁴

Files: `designB.md` (this proof), `designB_main.py` (all constants and the table; output in §8),
`designB_check.py` (numerical sanity checks of the three analytic identities; output in §8),
`designB_explore.py` (reduced functional for rational kernel families; output in §1).

## 0. Result

**Theorem A.** Assume RH for ζ and GRH for Dirichlet L-functions. Let n ≥ N₀ and let χ be a non-principal
Dirichlet character mod n. Then there is an integer 1 ≤ a < c·(log n)² with χ(a) ≠ 1, for each pair

| c    | 0.95 | 0.90 | 0.85 | 0.80 | 0.79 | 0.78 | 0.779 |
|------|------|------|------|------|------|------|-------|
| N₀   | 10⁸  | 10⁹  | 10¹⁰ | 10¹¹ | 10¹³ | 10⁴³ | 10⁷⁰⁵ |

(exact thresholds log N₀ = 18.06, 19.67, 21.78, 25.23, 28.07, 98.01, 1622.01; §8).

**Theorem B (explicit rate).** Same hypotheses, L = log n, c∞ := 3/(4D²) ≤ 0.777135 (D = 0.982387, §5).
For L ≥ L₁ the least a with χ(a) ≠ 1 satisfies

    a < c∞ · (L + 0.238·√L − k)²,     (L₁, k) ∈ {(30, 0), (50, 4), (100, 7), (200, 9), (1000, 11), (10⁴, 12)}.

So c(n) ≤ c∞(1 + 0.238/√(log n))², c(n) → c∞ < 0.7772. The limit of the construction with the optimal
λ = 0.3261 instead of λ = 1/3 is 0.77677 (not used: λ = 1/3 gives x = 3X).

The construction is all-rational: the only kernel is K(s) = 6/(s+1)⁴, i.e. the weight
√n·log³(x/n) on n < x = 3X. Its modulus on the critical line is the rational function 6/(1+t²)², so the
zero sum Σ_γ |K(iγ)| is given by an **exact** partial-fraction identity at the real point σ = 3/2
(Lemma 4): no majorant, no zero counting, no S(t,χ), no Γ on vertical lines, no positivity certificate.
c∞ = 0.777 is *below* the Γ-kernel value 0.7934 of LLS and 2.3% above the CMQR barrier 0.7596.

Why N₀ is so small compared with the referee's estimate (10⁹⁰ and up for the Γ kernel): the O(1) term of
the zero-sum identity is −Re Σ Λ(n)χ(n)(1+log n)n^{−3/2}; under the contradiction hypothesis χ(n) = 1 for
n < X this is ≈ −(F₀+F₁) = −5.36 rather than the worst case +5.36 (Lemma 4). In units of log q the
"constant" is −κ = −12.69 instead of about +9. This is legitimate (it is the hypothesis, used once more)
and it is the single most valuable O(1) term in the proof.

## 1. Design: the reduced functional on rational kernels

Notation of BRIEF.md: φ(v) = K̃(e^v), K(it) = φ̂(t) = ∫φ(v)e^{itv}dv, I = (1/2π)∫|K(it)|dt, λ = e^ℓ,
c = λ(h−1)²I² / (h∫_{v<ℓ} φe^{v/2} − ∫φe^{v/2})².

**1.1 A barrier: one-sided kernels with all of their support counted give c ≥ 1.** If K̃ is supported on
u ≤ λ (so that only n ≤ X occur and no positivity is needed), then for every h the functional is
c = λ(I/K(½))², and after scaling λ = 1. Claim: K(½) ≤ I, i.e. c ≥ 1, with equality for K(s) = 1/(s+½)²
(K̃(u) = √u·log(1/u), Bach's kernel). Proof: for supp φ ⊂ (−∞,0] and any ψ with ψ = e^{v/2} on v < 0,
∫φe^{v/2} = (1/2π)∫φ̂·conj(ψ̂) ≤ I·‖ψ̂‖_∞; take ψ = e^{v/2}1_{v<0} − δ₀, ψ̂(t) = 1/(½+it) − 1 = (½−it)/(½+it),
of modulus 1. (This is Nehari's theorem for the rank-one Hankel operator with kernel e^{−(x+y)/2}, norm 1.)
So the natural family "K̃(u) = u^β(1−u)^k on (0,1) with x = X" suggested in the brief can never beat 1.

**1.2 The way round it: let the support overshoot X.** Keep K̃ ≥ 0 supported on (0,1) but take
x = X/λ with λ < 1. The terms X ≤ n < x are handled by positivity (Re(1+χ(n)) ≥ 0), exactly as in LLS.
Numerics (`designB_explore.py`; h = 2; floating point):

```
1. Reference: Gamma kernel K(s)=Gamma(s+1/2) (LLS), h=2
   I = 0.470888, optimal lambda = 2.4773, c_inf = 0.79342
2. One-sided kernel with ALL its support counted (support u<1, lambda=1): c = (I/K(1/2))^2 >= 1
   (Nehari/Hankel duality, see designB.md section 1; equality for K=1/(s+1/2)^2: I=1, K(1/2)=1, c=1)
3. Pure powers K(s) = (k-1)!/(s+a)^k, Ktilde(u) = u^a log^{k-1}(1/u) on (0,1), support beyond X (lambda<1)
   k : c_inf at a=3/4 (sigma=5/4), a=1 (sigma=3/2), a=3/2 (sigma=2) [lambda optimised] | free optimum
   k=2: 0.9905 (lam=0.824)  1.1895 (lam=0.878)  1.7184 (lam=0.932) | a=0.500 lam=0.730 c=0.86346 <- |K(it)| rational
   k=3: 0.7772 (lam=0.472)  0.8260 (lam=0.576)  1.0396 (lam=0.712) | a=0.718 lam=0.457 c=0.77634 
   k=4: 0.8095 (lam=0.242)  0.7768 (lam=0.341)  0.8756 (lam=0.498) | a=0.961 lam=0.326 c=0.77602 <- |K(it)| rational
   k=5: 0.9168 (lam=0.118)  0.8011 (lam=0.192)  0.8192 (lam=0.335) | a=1.172 lam=0.243 c=0.78665 
   k=6: 1.0766 (lam=0.056)  0.8607 (lam=0.106)  0.8044 (lam=0.219) | a=1.361 lam=0.187 c=0.79895 <- |K(it)| rational
   k=7: 1.2886 (lam=0.026)  0.9452 (lam=0.057)  0.8111 (lam=0.141) | a=1.533 lam=0.147 c=0.81082 
   k=8: 1.5599 (lam=0.012)  1.0518 (lam=0.031)  0.8314 (lam=0.090) | a=1.692 lam=0.118 c=0.82177 <- |K(it)| rational
   chosen: k=4, a=1, lambda=1/3: c_inf = 0.777134  (optimal lambda for a=1: see row k=4)
4. The chosen kernel for index h (h characters chi^j; D_h = (2h/3) lam^{3/2} P(log 1/lam) - 32/27)
   h=2   c_inf = 0.7768 at lambda = 0.341 ;  at lambda=1/3: 0.7771
   h=3   c_inf = 0.6837 at lambda = 0.270 ;  at lambda=1/3: 0.7027
   h=4   c_inf = 0.6408 at lambda = 0.238 ;  at lambda=1/3: 0.6803
   h=5   c_inf = 0.6158 at lambda = 0.220 ;  at lambda=1/3: 0.6695
   h=10  c_inf = 0.5665 at lambda = 0.183 ;  at lambda=1/3: 0.6520
   h=100 c_inf = 0.5218 at lambda = 0.149 ;  at lambda=1/3: 0.6397
5. Beta kernels Ktilde(u) = u^beta (1-u)^k on (0,1): K(s) = k!/prod_{j=0..k}(s+beta+j)
   beta=0.75 k=1: c_inf = 1.3132 (lambda=0.902)
   beta=1.00 k=1: c_inf = 1.5973 (lambda=0.927)
   beta=0.75 k=2: c_inf = 1.0000 (lambda=0.722)
   beta=1.00 k=2: c_inf = 1.1580 (lambda=0.768)
   beta=1.50 k=2: c_inf = 1.5240 (lambda=0.829)
   beta=1.00 k=3: c_inf = 1.0489 (lambda=0.642)
   beta=1.50 k=3: c_inf = 1.3304 (lambda=0.715)
   beta=2.00 k=3: c_inf = 1.6479 (lambda=0.765)
   beta=1.50 k=4: c_inf = 1.2464 (lambda=0.623)
   beta=2.00 k=4: c_inf = 1.5157 (lambda=0.679)
   beta=2.00 k=6: c_inf = 1.3966 (lambda=0.549)
   beta=3.00 k=6: c_inf = 1.8872 (lambda=0.631)
6. Polynomial numerators: phi(v) = e^{v} * sum_{j<J} theta_j v^j (v<0), K(s) = N(s)/(s+1)^J (convex programme)
   J=4: accurate re-evaluation c_inf = 0.77680 at lambda=0.333 (min phi on (ell,0) = 0.00e+00)
        majorant G = sum_{k<=3} e_k/(1+t^2)^k: int G/int|K| = 1.00106  -> c_inf(with G) = 0.77845
        majorant G = sum_{k<=4} e_k/(1+t^2)^k: int G/int|K| = 1.00078  -> c_inf(with G) = 0.77801
        majorant G = sum_{k<=8} e_k/(1+t^2)^k: int G/int|K| = 1.00036  -> c_inf(with G) = 0.77736
   J=5: accurate re-evaluation c_inf = 0.77621 at lambda=0.333 (min phi on (ell,0) = 0.00e+00)
        majorant G = sum_{k<=3} e_k/(1+t^2)^k: int G/int|K| = 1.00176  -> c_inf(with G) = 0.77894
        majorant G = sum_{k<=5} e_k/(1+t^2)^k: int G/int|K| = 1.00081  -> c_inf(with G) = 0.77747
        majorant G = sum_{k<=9} e_k/(1+t^2)^k: int G/int|K| = 1.00042  -> c_inf(with G) = 0.77686
   J=6: accurate re-evaluation c_inf = 0.76433 at lambda=0.407 (min phi on (ell,0) = 0.00e+00)
        majorant G = sum_{k<=4} e_k/(1+t^2)^k: int G/int|K| = 1.01855  -> c_inf(with G) = 0.79295
        majorant G = sum_{k<=6} e_k/(1+t^2)^k: int G/int|K| = 1.00430  -> c_inf(with G) = 0.77092
        majorant G = sum_{k<=10} e_k/(1+t^2)^k: int G/int|K| = 1.00256  -> c_inf(with G) = 0.76825
   J=8: accurate re-evaluation c_inf = 0.76417 at lambda=0.407 (min phi on (ell,0) = 0.00e+00)
        majorant G = sum_{k<=5} e_k/(1+t^2)^k: int G/int|K| = 1.00719  -> c_inf(with G) = 0.77520
        majorant G = sum_{k<=8} e_k/(1+t^2)^k: int G/int|K| = 1.00422  -> c_inf(with G) = 0.77064
        majorant G = sum_{k<=12} e_k/(1+t^2)^k: int G/int|K| = 1.00280  -> c_inf(with G) = 0.76845
```

Reading: (i) pure powers with even k have rational modulus; k = 4, a = 1 gives 0.7768, better than the Γ kernel
(0.7934). (ii) The beta kernels u^β(1−u)^k do not beat 1 (their K has simple poles spread over β, β+1, …). (iii) The
"free optimum" in row k = 2 sits on the boundary a = ½ (σ = 1), which is not usable. (iv) Polynomial numerators
reach 0.7642 (J = 6, 8; accurate re-evaluation of the discretised optimum), consistent with the CMQR barrier
0.7596; their modulus is not rational, and the best rational majorant found costs 0.3–0.4% in I, leaving 0.768.

**1.3 Exact modulus.** For K(s) = (k−1)!/(s+a)^k with k = 2m even, |K(it)| = (k−1)!/(a²+t²)^m is an even
rational function with poles at t = ±ia, and (a²+t²)^{−m} is a finite real combination of
Re (a−it)^{−j}, j ≤ m; hence Σ_γ|K(iγ)| is a combination of Σ_ρ Re (σ−ρ)^{−j} at σ = ½+a, i.e. of
(ξ'/ξ)^{(j−1)}(σ,χ). With a = 1 this is σ = 3/2, where the Lean development already has Dirichlet-series
numerics. More generally K = M·U with M ≥ 0 rational on the line and U all-pass (Blaschke) has an exact
zero sum; within K(s) = Q(−s²)(a−s)^r/(a+s)^{2m+r} a search found nothing better than the pure power
k = 4, a ≈ 1 (c∞ = 0.7760 at a = 0.96; 0.7768 at a = 1).

**1.4 Choice.** K(s) = 6/(s+1)⁴, λ = 1/3: c∞ = 0.77684 (0.777135 with the rounded constant D).
Loss ∫G/∫|K| = 1 (G = |K|). Kernels with non-rational modulus (odd k, polynomial numerators) need a
majorant G = Σ_k e_k/(1+t²)^k ≥ |K(it)|; the LP in `designB_explore.py` quantifies that loss (table
above): the gain over 0.7768 is 1.6% in c before the majorant loss and 1.1% after
(0.7642 resp. 0.768), so it is not worth a polynomial-positivity certificate for G² − |K|² ≥ 0. Two-sided rational kernels (poles on both sides) gave no further gain.

## 2. Standing notation and the analytic facts used

Λ = von Mangoldt. For y > 1 and j ∈ {0,1,2,3}:

    A_j(y) := Σ_{n<y} Λ(n) √n · log^j(y/n),        Φ_χ(y) := Σ_{n<y} Λ(n) χ(n) √n · log³(y/n).

χ̃ denotes a primitive character mod q > 1, 𝔞 ∈ {0,1} its parity (χ̃(−1) = (−1)^𝔞), ψ the digamma function,
ρ = ½+iγ the non-trivial zeros (GRH), always counted with multiplicity.
F_k := Σ_n Λ(n) log^k n · n^{−3/2} = (−1)^{k+1}(ζ'/ζ)^{(k)}(3/2):
F₀ = 1.505235…, F₁ = 3.854962…, F₂ = 15.930203…, F₃ = 95.949549….

Facts used (all standard; (F1)–(F3) are in the Lean development for the kernels 1/s², 1/(s(s+1))):

* (F1) Hadamard partial fractions. For primitive χ̃ mod q > 1, ξ(s,χ̃) = (q/π)^{(s+𝔞)/2}Γ((s+𝔞)/2)L(s,χ̃):
  ξ'/ξ(s,χ̃) = B(χ̃) + Σ_ρ (1/(s−ρ) + 1/ρ), Re B(χ̃) = −Σ_ρ Re 1/ρ. Hence for real σ:
  Σ_ρ Re 1/(σ−ρ) = Re ξ'/ξ(σ,χ̃), and by differentiation Σ_ρ 1/(σ−ρ)² = −(ξ'/ξ)'(σ,χ̃).
  For ζ: Σ_ρ Re 1/(σ−ρ) = ζ'/ζ(σ) + 1/(σ−1) − ½log π + ½ψ(σ/2+1), and
  Σ_ρ 1/(σ−ρ)² = −(ζ'/ζ)'(σ) + 1/(σ−1)² − ¼ψ'(σ/2+1).
* (F2) Functional equation ξ'/ξ(s,χ̃) = −ξ'/ξ(1−s, conj χ̃), and the analogue for ζ.
* (F3) Perron: for c > 0, j ≥ 1, y > 0: (1/2πi)∫_{(c)} y^s s^{−j−1} ds = log^j(y)/j! if y ≥ 1, 0 if y ≤ 1;
  and for w ≠ 0, Re w < c, y ≥ 1:
  (1/2πi)∫_{(c)} y^s/(s^{j+1}(s−w)) ds = y^w/w^{j+1} − Σ_{i=0}^{j} (log^i y/i!)·w^{i−j−1}.
* (F4) Chebyshev: ψ(t) := Σ_{n≤t}Λ(n) ≤ c₀·t for all t > 0 with c₀ = 1.04
  (Rosser–Schoenfeld 1962, Thm 12: ψ(t) < 1.03883 t). Only used in Lemma 5; any c₀ works with a
  slightly different table.
* (F5) Numerics: F₀, F₁ (to ±10⁻⁶, lower bounds needed), F₂, F₃ (upper bounds), ψ and ψ', ψ'', ψ''' at
  ±1/4, 3/4, 5/4, 7/4, log π, log 3, and the values (ζ'/ζ)^{(k)}(−1/2), k ≤ 3 (or, via (F2), in terms of
  the previous ones).

## 3. Explicit formulas

**Lemma 1 (ζ zero sums).** Under RH, with Z_k := Σ_γ (1+γ²)^{−k/2} over the zeros ½+iγ of ζ:
Z₂ = ζ'/ζ(3/2) + 2 − ½log π + ½ψ(7/4) ≤ 0.046136;
Z₄ = ½[Z₂ + (4 − F₁ − ¼ψ'(7/4))] ≤ 0.000074; Z₃ ≤ √(Z₂Z₄) ≤ 0.001845.

*Proof.* 3/2 − ρ = 1 − iγ. Re 1/(1−iγ) = 1/(1+γ²), and Re 1/(1−iγ)² = (1−γ²)/(1+γ²)² = 2/(1+γ²)² − 1/(1+γ²),
so 1/(1+γ²)² = ½[Re(1−iγ)^{−1} + Re(1−iγ)^{−2}]. Apply (F1) for ζ at σ = 3/2 ((ζ'/ζ)'(3/2) = F₁).
Z₃ by Cauchy–Schwarz. ∎ (Numerical check against the first 400 zeros: §8, (C3).)

**Lemma 2 (explicit formula, ζ).** Under RH, for y > 1 and j ∈ {1,2,3}, with g_ζ := −ζ'/ζ,

    A_j(y) = j!(2/3)^{j+1} y^{3/2} − j! Σ_ρ y^{ρ+1/2}/(ρ+½)^{j+1} + Σ_{i=0}^{j} C(j,i) log^i y · g_ζ^{(j−i)}(−½)
             − j! Σ_{m≥1} y^{½−2m}/(½−2m)^{j+1}.

Consequently, with γ_k ≥ |g_ζ^{(k)}(−½)| (γ₀ = 1.735827, γ₁ = 0.145038, γ₂ = 1.255863, γ₃ = 0.050451) and
r_j(y) := Σ_{i=0}^{j} C(j,i) γ_{j−i} log^i y + 0.64·j!,

    | A_j(y) − j!(2/3)^{j+1} y^{3/2} | ≤ j!·Z_{j+1}·y + r_j(y).                                (3.1)

*Proof.* −ζ'/ζ(s−½) = Σ Λ(n)√n·n^{−s} for Re s > 3/2, so by (F3) A_j(y)/j! = (1/2πi)∫_{(2)} −ζ'/ζ(s−½) y^s s^{−j−1} ds.
Shift the contour to −∞ (or integrate the Hadamard expansion termwise with (F3)); residues: s = 3/2 (pole of ζ):
y^{3/2}(2/3)^{j+1}; s = ρ+½ = 1+iγ: −y^{ρ+1/2}/(ρ+½)^{j+1}; s = ½−2m (trivial zeros, m ≥ 1): −y^{½−2m}/(½−2m)^{j+1};
s = 0 (pole of order j+1; ζ'/ζ is regular at −½): (1/j!)·d^j/ds^j[g_ζ(s−½)y^s]_{s=0}. All sums converge absolutely
since j ≥ 1. For (3.1): |y^{ρ+1/2}| = y, |ρ+½|^{j+1} = (1+γ²)^{(j+1)/2}; and
Σ_{m≥1}(2m−½)^{−j−1} ≤ Σ_{m≥1}(2m−½)^{−2} = ¼ψ'(3/4) < 0.64, y^{½−2m} ≤ 1. ∎
(g_ζ^{(k)}(−½) is computed directly and through (F2):
ζ'/ζ(z) = log π − ½ψ(z/2) − ½ψ((1−z)/2) − ζ'/ζ(1−z); both agree to 15 digits. Formula checked numerically
at y = 300.5: §8, (C3).)

**Lemma 3 (explicit formula, L).** Assume GRH; χ̃ primitive mod q > 1, g_χ := −L'/L(·,χ̃), y > 1. Then

    Φ_χ̃(y) = −6 Σ_ρ y^{ρ+1/2}/(ρ+½)⁴ + Σ_{i=0}^{3} C(3,i) log^i y · g_χ^{(3−i)}(−½) − 6 Σ_{m≥0} y^{s_m}/s_m⁴,
    s_m := ½ − 𝔞 − 2m,

and therefore

    Re Φ_χ̃(y) ≤ 6y·S₄(χ̃) + (log q + G₀) log³y + 3G₁ log²y + 3G₂ log y + G₃,                 (3.2)

S₄(χ̃) := Σ_γ (1+γ²)^{−2}, with G₀ = 1.274646, G₁ = 9.125903, G₂ = 32.262139, G₃ = 194.419965.

*Proof.* As Lemma 2 with −L'/L(s−½,χ̃): no pole at s = 3/2; the trivial zeros of L(z,χ̃) are z = −𝔞−2m, m ≥ 0
(this includes z = 0 for even χ̃), i.e. s = s_m ≠ 0, residue −y^{s_m}/s_m⁴ (×6). Since s_m is real and s_m⁴ > 0, the
trivial-zero sum contributes ≤ 0 to Re Φ and is dropped (for even χ̃ the term m = 0 is −96√y: a free gain).
|y^{ρ+1/2}/(ρ+½)⁴| = y/(1+γ²)². For the residue at s = 0 use (F2):

    g_χ(z) = log(q/π) + ½ψ((z+𝔞)/2) + ½ψ((1−z+𝔞)/2) + L'/L(1−z, conj χ̃),
    g_χ^{(k)}(z) = 2^{−k−1}ψ^{(k)}((z+𝔞)/2) + (−1)^k 2^{−k−1}ψ^{(k)}((1−z+𝔞)/2) + (−1)^k (L'/L)^{(k)}(1−z, conj χ̃)   (k ≥ 1).

At z = −½ the arguments are (−½+𝔞)/2 ∈ {−¼, ¼}, (3/2+𝔞)/2 ∈ {¾, 5/4}, and |(L'/L)^{(k)}(3/2, conj χ̃)| ≤ F_k. So
Re g_χ(−½) ≤ log q + G₀ and |g_χ^{(k)}(−½)| ≤ G_k with
G₀ := max_𝔞[−log π + ½ψ((−½+𝔞)/2) + ½ψ((3/2+𝔞)/2)] + F₀, G_k := max_𝔞 2^{−k−1}[|ψ^{(k)}((−½+𝔞)/2)| + |ψ^{(k)}((3/2+𝔞)/2)|] + F_k. ∎
(Checked numerically for the characters mod 3 and mod 5 with their first ≈25 zeros: §8, (C2).)

## 4. The zero sum: an exact identity and the gain from the hypothesis

**Lemma 4.** Assume GRH; χ̃ primitive mod q > 1. Then

    S₄(χ̃) = Σ_γ 1/(1+γ²)² = ¼log(q/π) + ¼ψ((3/2+𝔞)/2) − ⅛ψ'((3/2+𝔞)/2) − ½ Σ_n Λ(n) Re χ̃(n) (1+log n) n^{−3/2}.   (4.1)

If moreover χ̃(n) = 1 for all prime powers n < X, then with
T(X) := Σ_{n≥X} Λ(n)(1+log n)n^{−3/2} and κ := min_𝔞 [log π − ψ((3/2+𝔞)/2) + ½ψ'((3/2+𝔞)/2)] + 2(F₀+F₁) ≥ 12.691241
(the minimum is at 𝔞 = 1; 𝔞 = 0 gives 14.2219),

    S₄(χ̃) ≤ ¼ ( log q − κ + 4T(X) ).                                                             (4.2)

*Proof.* As in Lemma 1, 1/(1+γ²)² = ½[Re(3/2−ρ)^{−1} + Re(3/2−ρ)^{−2}]. By (F1),
Σ_ρ Re(3/2−ρ)^{−1} = ½log(q/π) + ½ψ((3/2+𝔞)/2) + Re L'/L(3/2,χ̃) and
Σ_ρ Re(3/2−ρ)^{−2} = −¼ψ'((3/2+𝔞)/2) − Re (L'/L)'(3/2,χ̃), with L'/L(s) = −ΣΛ(n)χ̃(n)n^{−s},
(L'/L)'(s) = ΣΛ(n)χ̃(n) log n·n^{−s}. This is (4.1). For (4.2): Re χ̃(n) = 1 for n < X and ≥ −1 for n ≥ X, so the
Dirichlet series in (4.1) is ≥ (F₀+F₁) − 2T(X). ∎ (Identity (4.1) checked against zeros: §8, (C1).)

**Lemma 5.** For X ≥ 1: T(X) ≤ c₀(3 log X + 7)/√X.

*Proof.* f(t) = (1+log t)t^{−3/2} is decreasing on [1,∞). Partial summation and (F4):
T(X) = −f(X)ψ(X⁻) + ∫_X^∞ ψ(t)(−f'(t))dt ≤ c₀∫_X^∞ t(−f'(t))dt = c₀[X f(X) + ∫_X^∞ f] = c₀[(1+log X) + 2(log X+3)]/√X. ∎

## 5. The prime side: sharp cut-off at X by differencing

Fix λ = 1/3, ℓ₀ = log 3, and for X > 1 put x = X/λ = 3X. Define

    T_<(X) := Σ_{n<X} Λ(n)√n·log³(x/n),   P(ℓ) := ℓ³ + 2ℓ² + (8/3)ℓ + 16/9,
    D := (4/3)λ^{3/2}P(ℓ₀) − 32/27 ≥ 0.982387,   δ₀ := 2√Z₂ ≤ 0.4296,
    e₁ := 4ℓ₀³√Z₂·λ^{5/4} ≤ 0.288544,   e₂ := 2λ(3ℓ₀²Z₂ + 6ℓ₀Z₃ + 6Z₄) + 6Z₄ ≤ 0.120216,
    ρ*(x) := 2ℓ₀³(γ₀+1) + 6ℓ₀² r₁(x) + 6ℓ₀ r₂(x) + 3 r₃(x).

**Lemma 6 (sharp sum from smooth sums).** Under RH, for X ≥ 45 and δ := δ₀X^{−1/4}, Y := Xe^{−δ}:

    A₀(X) = Σ_{n<X} Λ(n)√n ≥ (A₁(X) − A₁(Y))/δ ≥ (2/3)X^{3/2} − 2√Z₂·X^{5/4} − γ₀ − 1.

*Proof.* A₁(X) − A₁(Y) = δ·Σ_{n<Y}Λ(n)√n + Σ_{Y≤n<X}Λ(n)√n·log(X/n) ≤ δ·A₀(X), because Λ ≥ 0 and log(X/n) ≤ δ for n ≥ Y.
By Lemma 2 (exact formula, j = 1): the main terms give (4/9)X^{3/2}(1−e^{−3δ/2}) ≥ (4/9)X^{3/2}(3δ/2 − 9δ²/8);
the zero sums are ≥ −Z₂(X+Y) ≥ −2Z₂X; the residues at s = 0 give exactly δ·g_ζ(−½) ≥ −δγ₀; the trivial zeros
≥ −0.64(X^{−3/2}+Y^{−3/2}) ≥ −1.28e^{3/2}X^{−3/2} (δ ≤ 1). Divide by δ:
A₀(X) ≥ (2/3)X^{3/2} − (δ₀/2 + 2Z₂/δ₀)X^{5/4} − γ₀ − 1.28e^{3/2}X^{−5/4}/δ₀, and δ₀/2 + 2Z₂/δ₀ = 2√Z₂; the last term is < 1 for X ≥ 45. ∎

**Lemma 7 (prime side).** Under RH, for X ≥ 45:

    2T_<(X) − A₃(x) ≥ D·x^{3/2} − e₁·x^{5/4} − e₂·x − ρ*(x).

*Proof.* log(x/n) = ℓ₀ + log(X/n), so T_< = ℓ₀³A₀(X) + 3ℓ₀²A₁(X) + 3ℓ₀A₂(X) + A₃(X). Insert Lemma 6 and the lower
bounds (3.1) for A₁, A₂, A₃ at X, and the upper bound (3.1) for A₃(x):
main terms 2X^{3/2}[(2/3)ℓ₀³ + (4/9)·3ℓ₀² + (16/27)·3ℓ₀ + 32/27] − (32/27)x^{3/2} = D·x^{3/2} (X = λx);
X^{5/4}-term 2ℓ₀³·2√Z₂·X^{5/4} = e₁x^{5/4}; linear terms 2X(3ℓ₀²Z₂ + 3ℓ₀·2Z₃ + 6Z₄) + 6Z₄x = e₂x; the rest is
≤ 2ℓ₀³(γ₀+1) + 6ℓ₀²r₁(X) + 6ℓ₀r₂(X) + 2r₃(X) + r₃(x) ≤ ρ*(x) (r_j increasing, 1 < X < x). ∎

Remark. The cut-off at X is intrinsic; Lemma 6 pays 2√Z₂·X^{5/4} for it, i.e. a relative x^{−1/4}. With
Schoenfeld's |ψ(X)−X| ≤ √X log²X/(8π) the loss would be O(X log²X) (relative x^{−1/2}log²x), which is
asymptotically better but not smaller for X ≤ 10⁵, and is not needed for the table.

## 6. Assembly

**Lemma 8 (the basic inequality).** Assume RH and GRH. Let χ be a non-principal character mod n, induced
by the primitive χ̃ mod q | n, and let X ≥ 45 be real with χ(a) = 1 for all integers 1 ≤ a < X. Then with
x = 3X and L := log n,

    D√x − e₁x^{1/4} − e₂ + (3/2)κ ≤ (3/2)L + 6T(X) + L·log³x/x + [G₀log³x + 3G₁log²x + 3G₂log x + G₃ + ρ*(x)]/x.   (6.1)

*Proof.* Every a < X is coprime to n and χ̃(a) = χ(a) = 1; q > 1. For every m, Re(1+χ̃(m)) ≥ 0, and
√m·log³(x/m) ≥ 0 for m < x. Hence

    A₃(x) + Re Φ_χ̃(x) = Σ_{m<x} Λ(m)(1+Re χ̃(m))√m·log³(x/m) ≥ 2 Σ_{m<X} Λ(m)√m·log³(x/m) = 2T_<(X).

So 2T_< − A₃(x) ≤ Re Φ_χ̃(x). Bound the left side by Lemma 7, the right side by (3.2), S₄ by (4.2) (legitimate:
χ̃(m) = 1 for m < X), use log q ≤ L (all coefficients of log q are positive), and divide by x:
D√x − e₁x^{1/4} − e₂ − ρ*/x ≤ (3/2)(L − κ + 4T(X)) + [(L+G₀)log³x + 3G₁log²x + 3G₂log x + G₃]/x. ∎

Note that the constants do not depend on q: the inequality is uniform in the conductor (referee's point 4).

**Lemma 9 (from (6.1) to c).** Let c > c∞ := 3/(4D²), α := D√(3c) − 3/2 > 0, β := e₁(3c)^{1/4},
Err_c(L) := 6T(cL²) + L log³x/x + [G₀log³x + 3G₁log²x + 3G₂log x + G₃ + ρ*(x)]/x at x = 3cL².
Let L₀ satisfy 3cL₀² ≥ 404 and

    min_{w ≥ √L₀} (αw² − βw) + (3/2)κ − e₂ − Err_c(L₀) > 0.                                        (6.2)

Then for every n with log n ≥ L₀ and every non-principal χ mod n there is 1 ≤ a < c log²n with χ(a) ≠ 1.

*Proof.* Suppose not, for some n with L = log n ≥ L₀; apply Lemma 8 with X = cL² (X ≥ 404/3 > 45), √x = √(3c)·L.
(6.1) reads α L − β√L + (3/2)κ − e₂ ≤ Err_c(L). Err_c is non-increasing in L for x ≥ 404 > e⁶:
T(cL²) by Lemma 5's bound ((3 log X+7)/√X is decreasing for X ≥ 1; we use the bound of Lemma 5 in place of T),
L log³x/x = (3c)^{−1/2} log³x/√x is decreasing for x > e⁶, and log^i x/x (i ≤ 3) is decreasing for x ≥ e³.
So Err_c(L) ≤ Err_c(L₀), contradicting (6.2). ∎

*Proof of Theorem A.* `designB_main.py` evaluates (6.2) with the outward-rounded constants; the smallest
passing L₀ are 18.06, 19.67, 21.78, 25.23, 28.07, 98.01, 1622.01 for c = 0.95, …, 0.779; each is below
log of the N₀ in the table. ∎

**Corollary 10 (= Theorem B).** Let b = 0.238 ≥ (2/3)e₁(3c∞)^{1/4} (= 0.23770), k ≥ 0, L₁ > k, θ := k/L₁,
x₁ := 3c∞(L₁−k)² ≥ 404, and suppose

    (3/2)(κ − k) − e₂ − e₁(3c∞)^{1/4}·b/2 − E* > 0,
    E* := 6c₀(3 log(x₁/3)+7)/√(x₁/3) + (3c∞)^{−1/2}(1−θ)^{−1} log³x₁/√x₁ + [G₀log³x₁ + 3G₁log²x₁ + 3G₂log x₁ + G₃ + ρ*(x₁)]/x₁.

Then for log n = L ≥ L₁ there is a < c∞(L + b√L − k)² with χ(a) ≠ 1.

*Proof.* Suppose not and apply Lemma 8 with X = c∞(L+b√L−k)²: D√x = D√(3c∞)(L+b√L−k) = (3/2)(L+b√L−k).
x^{1/4} = (3c∞)^{1/4}(L+b√L−k)^{1/2} ≤ (3c∞)^{1/4}(√L + b/2). So the left side of (6.1) minus (3/2)L is
≥ (3/2)(κ−k) − e₂ − e₁(3c∞)^{1/4}b/2 + [(3/2)b − e₁(3c∞)^{1/4}]√L, and the bracket is ≥ 0. On the right,
x ≥ 3c∞(L−k)² ≥ max(x₁, 3c∞(1−θ)²L²), so L ≤ √x/((1−θ)√(3c∞)) and every term is ≤ its value in E* (monotonicity
as in Lemma 9). Contradiction. The margins for the six pairs (L₁,k) are computed in §8 (all > 0.34). ∎

## 7. Index h (optional refinement; not needed for Theorems A, B)

Let h = ord χ ≥ 2 and χ̃_j the primitive character inducing χ^j (0 ≤ j < h; χ̃₀ = 1, L-function ζ).

**Lemma 11.** For every prime power m, Σ_{j=0}^{h−1} χ̃_j(m) is a non-negative integer.
*Proof.* m = p^r. If p ∤ n, χ̃_j(m) = χ(m)^j and the sum is h or 0. If p | n, let U = {j mod h : p ∤ cond χ^j}; U is
a subgroup of ℤ/h (χ^j is unramified at p iff it is trivial on the subgroup {u ≡ 1 mod n/p^{v_p(n)}} of (ℤ/n)^×).
Fix p' ≡ p mod n/p^{v_p(n)} with (p',n) = 1. For j ∈ U, χ̃_j(m) = χ(p'^r)^j, and χ̃_j(m) = 0 for j ∉ U. A
character sum over the group U: |U| or 0. ∎

Then h·T_<(X) ≤ A₃(x) + Σ_{j≥1} Re Φ_{χ̃_j}(x), each χ̃_j (j ≥ 1) is primitive of conductor q_j | n, q_j > 1, with
χ̃_j(a) = 1 for a < X, so Lemmas 3–5 apply to each. Dividing by h−1, Lemma 8 holds with D replaced by

    D^{(h)} := [(2h/3)λ^{3/2}P(ℓ₀) − 32/27]/(h−1) ≥ D

and e₁, e₂, ρ* multiplied by h/(2(h−1)) ≤ 1 (so the old values remain valid). c∞(h) = 3/(4(D^{(h)})²) at λ = 1/3,
or better with λ re-optimised (table in §1, item 4). h = 2 is the worst case.

## 8. Script output

### designB_main.py

```
== Dirichlet series at 3/2 ==
  F_0 = 1.50523535579   (direct prime sum + PNT tail: 1.5052356)
  F_1 = 3.85496291568   (direct prime sum + PNT tail: 3.8549664)
  F_2 = 15.9302038
  F_3 = 95.9495491062
== zeta zero sums ==
  Z2 <= 0.046136   Z3 <= 0.001845   Z4 <= 0.000074
== |g_zeta^(k)(-1/2)| ==
  k=0: value -1.73582612142   gamma_0 = 1.735827
  k=1: value 0.145037084324   gamma_1 = 0.145038
  k=2: value -1.2558621041   gamma_2 = 1.255863
  k=3: value 0.0504508938277   gamma_3 = 0.050451
== L-function side ==
  parity a=0: kappa_a = 14.22192459 ; Re g_chi(-1/2) - log q <= 1.2746452
  parity a=1: kappa_a = 12.691242 ; Re g_chi(-1/2) - log q <= -1.8669474
  kappa = 12.691241 ;  G0..G3 = ['1.274646', '9.125903', '32.262139', '194.419965']
== kernel K(s)=6/(s+1)^4, lambda=1/3 ==
  D = 0.982387   c_inf = 9*lambda/(4 D^2) = 0.77713425   delta0 = 0.429586   e1 = 0.288544   e2 = 0.120216
== Table: least-witness bound a < c (log n)^2 for all n >= N0 = exp(L0) ==
   (L0 = smallest value, on a grid of step 0.01, passing the rigorous test of Lemma 8)
  c = 0.95   L0 = log N0 = 18.06   N0 = 6.972e+7   (X0 = c L0^2 = 309.86, x0 = 929.57, margin H-bound = 0.002996)
  c = 0.90   L0 = log N0 = 19.67   N0 = 3.488e+8   (X0 = c L0^2 = 348.22, x0 = 1044.7, margin H-bound = 0.004195)
  c = 0.85   L0 = log N0 = 21.78   N0 = 2.877e+9   (X0 = c L0^2 = 403.21, x0 = 1209.6, margin H-bound = 0.003049)
  c = 0.80   L0 = log N0 = 25.23   N0 = 9.063e+10  (X0 = c L0^2 = 509.24, x0 = 1527.7, margin H-bound = 0.2248)
  c = 0.79   L0 = log N0 = 28.07   N0 = 1.551e+12  (X0 = c L0^2 = 622.46, x0 = 1867.4, margin H-bound = 1.042)
  c = 0.78   L0 = log N0 = 98.01   N0 = 3.675e+42  (X0 = c L0^2 = 7492.6, x0 = 22478.0, margin H-bound = 8.299)
  c = 0.779  L0 = log N0 = 1622.01 N0 = 2.691e+704 (X0 = c L0^2 = 2.0495e+6, x0 = 6.1485e+6, margin H-bound = 6.233)
  c = 0.778 : test fails for all L0 < 4000 (alpha = 0.00083529)
  c = 0.7775 : test fails for all L0 < 4000 (alpha = 0.00035294)
== c at or below c_inf: valid on a bounded range exp(30) <= n <= exp(L1) ==
  c = 0.777   valid for 30 <= log n <= 77.9782
  c = 0.775   valid for 30 <= log n <= 70.5926
  c = 0.77    valid for 30 <= log n <= 57.281
  c = 0.76    valid for 30 <= log n <= 41.2482
  c = 0.75    valid for 30 <= log n <= 32.1641
== explicit shape (Corollary 10): a < c_inf (L + b sqrt(L) - k)^2 for L >= L1 ==
  c_inf = 3/(4 D^2) = 0.77713425 ; b = 0.238  (>= (2/3) e1 (c_inf/lambda)^(1/4) = 0.237698)
  L1 = 30     k = 0   margin = 3.1275
  L1 = 50     k = 4   margin = 0.49073
  L1 = 100    k = 7   margin = 0.41964
  L1 = 200    k = 9   margin = 0.34442
  L1 = 1000   k = 11  margin = 0.64384
  L1 = 10000  k = 12  margin = 0.52295
== sample values of H(L, c) (no rigor needed: illustrates sizes) ==
  L = 15    H(c=0.8) = -7.3605    H(c=0.85) = -5.9209    H(c=0.9) = -4.5633    H(c=0.95) = -3.278   
  L = 20    H(c=0.8) = -2.7552    H(c=0.85) = -1.2088    H(c=0.9) = 0.2584     H(c=0.95) = 1.6556   
  L = 30    H(c=0.8) = 2.1045     H(c=0.85) = 3.979      H(c=0.9) = 5.7714     H(c=0.95) = 7.4907   
  L = 50    H(c=0.8) = 6.3931     H(c=0.85) = 9.0723     H(c=0.9) = 11.652     H(c=0.95) = 14.143   
  L = 100   H(c=0.8) = 10.363     H(c=0.85) = 15.252     H(c=0.9) = 19.984     H(c=0.95) = 24.573   
  L = 230   H(c=0.8) = 14.247     H(c=0.85) = 25.103     H(c=0.9) = 35.635     H(c=0.95) = 45.87    
  L = 1000  H(c=0.8) = 27.8       H(c=0.85) = 74.537     H(c=0.9) = 119.92     H(c=0.95) = 164.05   
  L = 10000 H(c=0.8) = 201.73     H(c=0.85) = 669.59     H(c=0.9) = 1123.9     H(c=0.95) = 1565.7
```

### designB_check.py (sanity checks; zeros located numerically)

```
Checks for the odd character mod 3 and the even character mod 5:
  (C1) q=3 a=1: #zeros(0<g<60)=23  S4(zeros)+tail=0.0006740515249   (P1+P2)/2=0.0006739914275
  (C2) Phi_chi(60.5): direct=-43.3648691  explicit formula=-43.36504442  (zero tail error <~ 0.000985)
       g^(0)(-1/2): direct=-2.024065794  via functional equation=-2.024065794
       g^(1)(-1/2): direct=4.1879605  via functional equation=4.1879605
       g^(2)(-1/2): direct=-16.16994523  via functional equation=-16.16994523
       g^(3)(-1/2): direct=96.17753627  via functional equation=96.17753627
  (C1) q=5 a=0: #zeros(0<g<60)=27  S4(zeros)+tail=0.001384532352   (P1+P2)/2=0.001384564284
  (C2) Phi_chi(60.5): direct=-106.636973  explicit formula=-106.6370255  (zero tail error <~ 0.00108)
       g^(0)(-1/2): direct=1.844927973  via functional equation=1.844927973
       g^(1)(-1/2): direct=4.482734641  via functional equation=4.482734641
       g^(2)(-1/2): direct=15.32906135  via functional equation=15.32906135
       g^(3)(-1/2): direct=97.24235141  via functional equation=97.24235141
Zeta checks:
  (C3) Z2: zeros(+tail)=0.046138493  Hadamard=0.046135928 ;  Z4: zeros=7.3770766e-5  Hadamard=7.3772455e-5
  (C3) A_1(300.5): direct=2309.2801827  explicit formula=2309.278083
  (C3) A_2(300.5): direct=3030.50859785  explicit formula=3030.50860742
  (C3) A_3(300.5): direct=5844.058221  explicit formula=5844.05822103
```

## 9. What a formalization needs, and what I am unsure about

Analytic inputs, in order of cost:

1. Lemma 3/Lemma 2: Perron + Hadamard termwise for the kernel x^s/s⁴ (and 1/s², 1/s³ for ζ) with the
   Dirichlet series shifted by ½, i.e. the integrand −L'/L(s−½)x^s/s^{j+1} on Re s = 2. This is the existing
   1/s² machinery with a higher-order pole at 0; (F3) is a one-line residue computation. The residue at
   s = 0 needs g^{(k)}(−½), k ≤ 3. Via (F2) these are polygamma values at ±¼, ¾, 5/4 plus Dirichlet series at
   3/2. Alternative without (F2): differentiate the Hadamard expansion at z = −½ directly (Re(−½−ρ)^{−1}
   = −1/(1+γ²), so the same sums S₂, S₄ appear); the bounds G_k are very far from critical (they are
   divided by x ≥ 900).
2. Lemma 4: the identity is two lines from (F1); needs ψ(¾), ψ(5/4), ψ'(¾), ψ'(5/4) and **lower** bounds
   F₀ ≥ 1.505235, F₁ ≥ 3.854962 (a finite partial sum suffices since all terms are ≥ 0: e.g. the partial
   sums up to 10⁴ give F₀+F₁ within 0.14, costing 0.28 in κ; the table moves slightly).
3. Lemma 5: Chebyshev ψ(t) ≤ c₀t. With c₀ = 1.1 or 2 the table moves by a few units in log N₀.
4. Lemmas 6–9: elementary real analysis.

No Γ or ψ on vertical lines, no Stirling, no majorant certificate, no zero counting.

Points to double-check (ranked by my own doubt):

* **(a) Use of the hypothesis inside the zero-sum identity (Lemma 4, (4.2)).** I believe this is correct
  (the hypothesis says exactly Re χ̃(n) = 1 for n < X) and it is what makes N₀ small. If one refuses it and
  uses |L'/L| ≤ F, κ drops from 12.69 to 12.69 − 4(F₀+F₁) = −8.75 and the thresholds become roughly
  log N₀ ≈ 130 (c = 0.95), 180 (0.90), 310 (0.85), 1200 (0.80): still far below the referee's estimates,
  because there is no majorant loss and no pole-at-(−½) term (the kernel's pole is at s = −1, where
  L'/L(−½) is multiplied by log³x/x). These fallback figures are estimates from the leading terms of (6.1),
  not script output.
* **(b) Numerics are 40-digit mpmath with outward rounding at 10⁻⁶, not interval arithmetic.** Derivatives
  of ζ'/ζ are by numerical differentiation; F₀, F₁ are cross-checked by direct prime sums (7 digits),
  g_ζ^{(k)}(−½) two ways (15 digits). F₂, F₃ are not cross-checked independently but enter only G₂, G₃.
* **(c) The explicit formulas (Lemmas 2, 3) are stated with the standard contour-shift proof only
  sketched.** They are confirmed numerically to 6–10 digits (§8), including signs of the trivial-zero terms.
* **(d) The thresholds for c = 0.95, 0.90, 0.85 are set by the requirement x ≥ 404 and the size of Err near
  L ≈ 18–22, where the margin in (6.2) is thin (10⁻³); the table rounds N₀ up to the next power of 10, which
  restores a margin (e.g. H = +0.26 at L = 20, c = 0.9).
* **(e) Section 1 is floating point** and the convex programmes are discretised; values there are design
  evidence only. In particular any value below the CMQR barrier 0.7596 would be a discretisation artefact.
