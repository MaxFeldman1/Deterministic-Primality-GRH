# formal0760: matching the Python record 0.76076 with an exact-modulus certificate (design for Round 14)

Status: research + design. **No Lean was written, edited or built** (builds run on the remote box; I did not touch it).
"Certified" = exact rational arithmetic (`formal0760_certificate.py`, stdlib only); "float" = numpy/scipy/cvxpy.

| file | role | status |
|---|---|---|
| `formal0760_family.py` → `formal0760_convex.out`, `formal0760_family.out`, `formal0760_family2.out` | convex reference values; family (E_p) for any single pole β, p reflected zeros | float |
| `formal0760_twopole.py` / `.out` | option (a): convex reference with two poles | float |
| `formal0760_design.py` → `formal0760_testfn_*.json` (`formal0760_init_*.npy` = cached optimiser states) | explicit test functions with exact rational sign changes, integer coefficients | float → integer data |
| **`formal0760_certificate.py`** / `.out` → `formal0760_certificate_*.json` | **exact certificate** (κ_n, e_k, ζ_a, W̃, Bernstein cells, N̂ bound) | exact (Fractions), 10–60 s each |
| `formal0760_check.py` / `.out` | independent mpmath quadrature of N̂, Î from the κ_n alone; \|K\| = G at sample points | float (70–260 digits) |

Regression: `formal0760_certificate.py` on formal076's design B reproduces c\* = 0.761142923 exactly.

Reproduce (float scripts need a venv with numpy, scipy, cvxpy, clarabel; certificate and check need python3 + mpmath):
`formal0760_design.py b3m24 3 9 5 2 2 5 5 6 20 12` (name β ℓ_num ℓ_den p L₁ L₂ d₀ digits; b3m22: `… 18 9`, b3m19: `… 15 9`,
b2m23: `b2m23 2 9 5 2 2 5 5 6 19 9`, b1m44: `b1m44 1 9 5 2 2 5 5 6 40 28`, b1m32: `… 28 22`, b1p1m23: `b1p1m23 1 11 8 1 2 5 20 16`),
then `formal0760_certificate.py formal0760_testfn_<name>.json` and `formal0760_check.py formal0760_certificate_<name>.json`.

## 0. Results

1. **Two things are missing in Round 13, and only two.** (i) A second sign change (formal076 has p = 1; the
   limit of p = 1 is 0.76083, of p = 2 at ℓ = 9/5 it is 0.760755). (ii) The pole position: β = 1 (weights
   √n·log^j) converges slowly. Both are removed inside the exact-modulus family, with *polynomial* weights,
   exact rational zeros and a rational Î — no majorant, no positivity certificate in t.
2. **Certified constants** (exact; last column with 9-digit exponential enclosures as Lean would use):

   | name | option | pole (Perron variable s) | weights on n < x = e^ℓ X | ℓ, exact zeros L_i | m (pole order 2m) | certified c\* | 9-digit exp | largest integers (digits) |
   |---|---|---|---|---|---|---|---|---|
   | **b3m24** | **(b) β = 3** | s = −2 | √n·(n/x)²·W(log(x/n)) | 9/5; 2/5, 5/6 | 24 (48) | **0.7607585** | 0.7607585 | 170 |
   | b3m22 | (b) β = 3 | s = −2 | same | same | 22 (44) | 0.7607627 | 0.7607628 | 147 |
   | b3m19 | (b) β = 3 | s = −2 | same | same | 19 (38) | 0.7607740 | 0.7607740 | 124 |
   | b2m23 | (b) β = 2 | s = −1 | √n·(n/x)·W | same | 23 (46) | 0.7607748 | 0.7607748 | 166 |
   | b1m44 | (c) β = 1, p = 2 | s = 0 | √n·W (Round 13 weights) | same | 44 (88) | 0.7607742 | 0.7607743 | 450 |
   | b1m32 | (c) β = 1, p = 2 | s = 0 | √n·W | same | 32 (64) | 0.7608002 | 0.7608003 | 321 |
   | b1p1m23 | (c₀) β = 1, p = 1 | s = 0 | √n·W | 11/8; 2/5 | 23 (46) | 0.7609161 | 0.7609161 | 124 |

   Reference points: Round 13 (formal076 B) 0.7611430; Python record (inside.md, β = 2, non-rational modulus,
   interval arithmetic) 0.7607618; unrestricted optimum 0.76075; dual barrier 0.76071.
   **b3m24 beats the Python record by 3·10⁻⁶ and is ≈ 7·10⁻⁶ above the numerical optimum 0.760752; b3m22 matches the record to 10⁻⁶.**
3. **Option (b) needs no new Perron theory.** The kernel s^{−(j+1)} is homogeneous, so the substitution
   s + (β−1) = β·s″ maps "pole at s = −(β−1), zeros on Re s = 1" to "pole at s″ = 0, zeros at s″ = 1 + iγ/β":
   the same line and the same kernel as Round 13. `r11Chi_perron j`, `r11Chi_perron_inv_sub`,
   `r11Chi_perron_hasSum_poles`, `r11Chi_decomp`, `r13Cert_modulus_of_factor` (Lemma E on Re s″ = 1), `r13W`,
   `r13K`, `r13G` are reused as they stand. What changes is arithmetic: Dirichlet series in n^β (one lemma), the
   zero sums are taken at centre β + ½ instead of 3/2, and the ζ side carries the factor (n/x)^{β−1}.
4. **Option (a) (two poles) is dominated**: at equal total pole order the two-pole convex optimum is no better
   than the best single pole (§2.3), its weights are exponential polynomials (no exact rational zeros, no
   Bernstein certificate), and it needs everything (b) needs plus mixed partial fractions and two centres.
5. **Option (c) (β = 1, larger m) is the cheapest in new Lean but the most expensive certificate**: with a
   second sign change, m = 44 gives 0.7607742 (identities of degree 88, 450-digit integers); 0.76076 needs
   m ≈ 60. With the *existing* `R13Cert` (p = 1) and zero new Lean, a regenerated instance gives 0.76092.
6. **Recommendation: (b) with β = 3, p = 2, done in two stages** (§4): Stage 1 = certificate/assembly
   generalised to several cells, general Q and a parameter β (≈ 1200–1500 lines; at β = 1 it is closed by the
   proved P1–P3 and already yields (c)); Stage 2 = the three analytic Props at β = 3 (≈ 1100–1300 lines).
   Target theorem: **∀ c > 0.76076, eventually every χ ≠ 1 mod n has χ(a) ≠ 1 for some a < c·log²n**
   (b3m24; margin 1.5·10⁻⁶ with 9-digit exponentials). Fallback with smaller data: b3m19, "∀ c > 0.76078".

## 1. Mathematics

### 1.1 Family (E_{p,β})

Perron variable s (zeros of L at s = ρ+½ = 1+iγ), a := β−1 ∈ ℕ, σ := s + a (pole at σ = 0, zeros on Re σ = β).

    weight of n < x:  w(n) = √n·(n/x)^a·W(log(x/n)),   W(L) = Σ_n κ_n L^{n−1}/(n−1)!,
    Σ_{n<x} Λ(n)χ(n)w(n) = (1/2πi)∫_{(2)} −L'/L(s−½,χ)·K(s+a)·x^s ds,   K(σ) = Σ_{n=4}^{2m} κ_n σ^{−n}.

The line Re s = 2 is unchanged (the Dirichlet series is the same; only the kernel moved).

    K = Q·H₀²,   H₀(σ) = Σ_{i=p+2}^{m} h_i σ^{−i},   Q = Σ_{a=0}^{p} ζ_a·(−(σ−β)²)^a,  ζ_p = 1,  ζ_a ≥ 0.

**Lemma E′.** For σ = β+it: conj σ = 2β−σ and −(σ−β)² = t², so

    |K(β+it)| = (Σ_a ζ_a t^{2a})·H₀(σ)H₀(2β−σ) = Σ_{k=1}^m e_k·Re(β+it)^{−k} =: G(t) ≥ 0,
    e_k/2 = Σ_{i≥k, l} Q_{il}·C(i+l−k−1, l−1)/(2β)^{i+l−k},   Q_{il} = Σ_a ζ_a g^{(a)}_i g^{(a)}_l,   Σ_i g^{(a)}_i σ^{−i} := (σ−β)^a H₀(σ),
    Î := (1/2π)∫G = e₁/2,     Σ_ρ G(γ) = Σ_k e_k Σ_ρ Re(β+½−ρ)^{−k} = Î·log q + O(1).

Proof as formal076 Lemma E; ζ_a ≥ 0 is a sufficient (and here satisfied) form of Q(−t²) ≥ 0. For p = 2 the zeros of
K in Re s_in > 0 are a complex pair 7.6 ± 2.2i, so Q(−T) = T² + 2(a²−b²)T + (a²+b²)² has positive coefficients.

**Exact sign changes.** W = Σ_a ζ_a W_a with W_a ∈ ℚ[L] (W_a ↔ (−(σ−β)²)^a H₀²). Given rationals
0 < L_1 < … < L_p < ℓ, the p linear equations W(L_i) = 0 determine ζ_0..ζ_{p−1} ∈ ℚ. Then
W = L³·∏(L−L_i)·W̃ exactly, and the sign pattern "(−1)^{p−i} on [L_i, L_{i+1}]" (L_0 = 0, L_{p+1} = ℓ) is W̃ > 0
on [0, ℓ]: one Bernstein certificate, no subdivision (all seven designs: one cell, min/max coefficient ≥ 9·10⁻⁴).
Because W is still a *polynomial* for every β (the factor (n/x)^a is positive and sits outside), this works for any
single pole. It fails for two poles.

**Functional.** With r := β+½ and R(L) := Σ_n κ_n Σ_{i<n} (L^i/i!)·r^{−(n−i)}: ∫_L^∞ W(τ)e^{−rτ}dτ = e^{−rL}R(L) =: F(L),

    N̂ = F(ℓ) − Σ_{i=0}^{p} (−1)^{p−i}(F(L_i) − F(L_{i+1})),      c* = e^{−ℓ}·(Î/N̂)².

(p = 1, β = 1 is formal076 (1.1).) In inside.md's normalisation φ(v) = W(ℓ−v)e^{−β(ℓ−v)}1_{v<ℓ}, K̂ = e^{itℓ}K(β+it),
N(φ) = e^{ℓ/2}N̂, I(φ) = Î, so c\* = J(φ)⁻² for every β; `formal0760_check.py` confirms this by direct quadrature.

**Asymptotic theorem** (GRH; formal076 §1 with (n/x)^a carried along): χ(n) = 1 for n < X, x = e^ℓX.
Positivity with signs gives Re Σ_{n<x}Λχ̃w ≥ Σ_{n<X}Λw − Σ_{X≤n<x}Λ|w|; the right side is x^{3/2}N̂ + O(x^{5/4})
(RH for ζ, P1β below); the left side is −Σ_ρ x^{ρ+½}K(ρ+½+a) + O((log q+1)log^{2m−1}x + √x) (P2β) and
|Σ_ρ| ≤ x·Σ_ρ G(γ) = x(Î·log q + O(1)) (P3β). Hence √x·N̂ ≤ Î·log n + o(log n), false for X = c·log²n, c > c\*.

### 1.2 The change of variables (why (b) is cheap)

Put s″ := σ/β = (s+a)/β and L″ := β·log(x/n). Then

    (β·log(x/n))^j/j!  ↔  β^j/(s+a)^{j+1} = (1/β)·1/s″^{j+1},      zeros: s″ = 1 + iγ/β,      conj s″ = 2 − s″ on them.

So with θ_j, W, K, G literally Round 13's `r13W`, `r13K`, `r13G` in the variables (L″, s″):

    weight of n:  √n·(n/x)^a·r13W θ J (β·log(x/n)),          kernel in s:  (1/β)·r13K θ J ((s+a)/β),
    |kernel at ρ+½| = (1/β)·r13G e m (γ/β),     Σ_ρ Re(1+iγ/β)^{−k} = β^k·Σ_ρ Re(β+½−ρ)^{−k},
    ζ side:  ∫_L^∞ W(βτ)e^{−(a+3/2)τ}dτ = (1/β)·e^{−κL″}R_κ(L″),   κ := 1 + 1/(2β),   R_κ := r13R with 2/3 replaced by 1/κ.

`R13Cert.modulus` and `r13Cert_modulus_of_factor` are statements about `r13K` on Re s″ = 1 and do not see β at all.
β enters only through κ in R, through e^{−κL″}, through e^{−ℓ} = e^{−ℓ″/β}, and through the three Props.
The integer data are given in this scaled variable (`"scaled": true` in the json: h_i multiplies (β/σ)^i = s″^{−i});
the dynamic range of the h_i is then ≤ 10⁹–10¹², against 10¹¹ more in powers of 1/σ.

Perron side: for f(n) = Λ(n)χ(n)n^{a+½} the series Σ f(n)(n^β)^{−s″} = D(βs″−a), D = `LSeries (r11Chi_coeff χ)`, is
absolutely convergent on Re s″ = 2 (Re(βs″−a) = β+1 > 3/2), and

    Φ^{(a)}_{χ,j}(y) := Σ_{n<y}Λ(n)χ(n)√n(n/y)^a log^j(y/n) = j!·β^{−j}·y^{−a}·r11Chi_perron j (s″ ↦ D(βs″−a)) (y^β).

Poles of s″ ↦ D(βs″−a): w″ = (ρ+½+a)/β with residue −m_ρ/β. Re w″ ≤ (3/2+a)/(1+a) ≤ 3/2, which is exactly the
hypothesis of `r11Chi_perron_hasSum_poles`; `r11Chi_perron_inv_sub` gives Y^{w″}/w″^{j+1} with Y^{w″} = y^{ρ+½+a}.
Trivial zeros: w″ = (a+½−2k−κ_χ)/β, never 0 for integer a (ρ = −a−½ is not an integer), |w″| ≥ 1/(2β).

## 2. Numerics (float)

### 2.1 Convex reference (`formal0760_convex.out`): best kernel with one pole of order D+2 at −β, support v < c

```
            c = 1.375 (p=1)           c = log 6 (p=2)                c = 2 (p=3)
            D=24     D=40     D=100   D=24     D=32     D=40    D=100   D=32     D=48    D=100
 beta=1     0.760943 0.760847 0.760831 0.760891 0.760823 0.760788 0.760756 0.760820 0.760782 0.760754
 beta=1.5   0.760860 0.760843 0.760828 0.760793 0.760769 0.760762 0.760755 0.760782 0.760760 0.760753
 beta=2     0.760844 0.760835 0.760826 0.760770 0.760761 0.760758 0.760755 0.760762 0.760755 0.760752
 beta=3     0.760851 0.760829 0.760824 0.760785 0.760756 0.760755 0.760755 0.760755 0.760753 0.760752
```

One sign change cannot go below 0.76082; two (ℓ ≈ 1.8) reach 0.760755; three (ℓ = 2) 0.760752. The third is
not worth a third cell.

### 2.2 Family (E_{p,β}) (`formal0760_family.out`, `formal0760_family2.out`)

q = (1+z)²r₀²·F·F^# with F monic of degree p (its roots = zeros of K in Re s_in > 0), true N (with |φ|) by
Gauss quadrature, analytic gradient, L-BFGS + BFGS from the outer square root of the convex optimum, restarts,
continuation in the degree. m = deg r₀ + p + 2. (β = 1, p = 1, m = 14 reproduces formal076's 0.761143.)

```
 p = 2, ell = 1.8      m=16     m=18     m=19     m=20     m=22     m=24     m=26     m=32     m=44     m=60
 beta = 1                                                                    (0.76081 at m=28) 0.760800 0.760774 0.760760
 beta = 2              0.760811 0.760797 0.760797 0.760794 0.760779 0.760771 0.760770
 beta = 3              0.760864 0.760809 0.760774 0.760773 0.760762 0.760758 0.760757
 beta = 4              0.762315 0.761288 0.761067 0.760920 0.760837 0.760784 0.760764
 p = 1, ell = 1.375:   beta = 1: m=23 0.760915, m=31 0.760901;   beta = 3: m=19 0.760853, m=23 0.760836
 p = 3, ell = 2:       beta = 3: m=22 0.760761, m=25 0.760758    (no better than p = 2 at equal m)
```

The exact-modulus restriction (outer part a perfect square) costs roughly a factor 2 in degree against the convex
family, as expected from the parameter count. β = 3 is the best integer pole; β = 2 needs ≈ 4 more in m;
β = 1 needs twice the order, and its coefficients need 22–28 digits instead of 9–12 (cancellation in powers of 1/s).
These are local optima of a non-convex problem; a better point of the same size would only lower c\*.
Some optima (not the ones used) have extra tiny sign changes near L = 0; the designs below were checked to have
exactly p.

### 2.3 Two poles (`formal0760_twopole.out`), convex reference at ℓ = 1.8

```
 total pole order   single beta=1  beta=2    beta=3  |  {1,2}     {1,3}     {2,3}     {2,4}     {1.5,4}
        24           0.760907     0.760780  0.760845 |  0.760856  0.760807  0.760833  0.760881  0.760788
        32           0.760827     0.760766  0.760758 |  0.760797  0.760774  0.760766  0.760769  0.760766
        40           0.760791     0.760761  0.760759 |  0.760779  0.760767  0.760765  0.760760  0.760761
```

(Different quadrature from §2.1, accuracy ≈ 10⁻⁵; the union of the two bases is orthonormalised by an SVD with
cut-off 10⁻¹⁰.) No pole pair beats the best single pole at equal order. A second pole buys nothing.

## 3. Certificates (`formal0760_certificate.out`)

Data of the recommended function **b3m24** (`formal0760_testfn_b3m24.json`): β = 3, ℓ = 9/5, L₁ = 2/5, L₂ = 5/6,

    H₀ = Σ_{i=4}^{24} h_i·(3/σ)^i,  σ = s+2,   h₄..h₂₄ =
      41000, −223418, 4293007, −40378475, 306400525, −1817619561, 8423505818, −30894447319, 90984731418,
      −217747567180, 427034031319, −689362492266, 916536632619, −1000000000000, 887892720635, −632388834529,
      353147427928, −149129525486, 44829300830, −8558762495, 781045660
    Q = ζ₀ + ζ₁·(−(σ−3)²) + (σ−3)⁴,   ζ₀ = 4056.42…, ζ₁ = 108.659… (rationals, 146/142 digits), from W(2/5) = W(5/6) = 0.

b3m22 and b3m19: same ℓ, L_i, 9-digit h (in the json files).

```
b3m24: beta = 3 (pole at s = -2; weights sqrt(n) (n/x)^2 log^j(x/n), 3 <= j <= 47), p = 2, m = 24 (pole order 48), ell = 9/5, L = ['2/5', '5/6']
  (a) Q(-T) = sum zeta_a T^a, zeta = ['4056.42', '108.659', '1']  (all > 0)
  (b) W = L^3 prod(L - L_i) Wt, deg Wt = 42; Bernstein: all coefficients > 0 on 1 cell(s) [0,9/5] (min/max 6.8e-03)
  (c) |K(beta+it)| = G(t) = sum_{k<=24} e_k Re(beta+it)^-k: identities of degree 48 verified
  (d) terms coef*R(L_i)/Ihat: -0.550, 4.457, -20.319, 553.350   (times e^0, e^-7/5, e^-35/12, e^-63/10: sum 0.466, no cancellation problem)
  RESULT: c* in [0.760758470, 0.760758470];   9-digit exp enclosures: [0.760758455, 0.760758491]
  sizes in the scaled variable: |h_i| <= 10^12; kappa''_n integers <= 170 digits; e''_k <= (168, 151) digits
```

What is checked, exactly (all by rational arithmetic): (a) ζ_a > 0; (b) the exact division W = L³∏(L−L_i)W̃ and
positivity of the Bernstein coefficients of W̃ on [0, ℓ]; (c) the two polynomial identities of Lemma E′
(Q·P₀(σ)P₀(2β−σ) = Σ_k (e_k/2)(σ^{m−k}(2β−σ)^m + σ^m(2β−σ)^{m−k}) and K·σ^{2m} = Q·P₀²) and Î = e₁/2;
(d) N̂ with Taylor enclosures of e^{(β+½)L_i}, e^{ℓ}. Exponentials needed for β = 3: e^{7/5}, e^{35/12}, e^{63/10}, e^{9/5}.

Independent check (`formal0760_check.out`): quadrature of ∫W e^{−rL} with |W| on [0, ℓ] and of (1/2π)∫|K(β+it)|dt
from the κ_n alone reproduces every certified c\* to all printed digits and finds the sign changes where
they were imposed; |G − |K||/|K| ≤ 10⁻⁵⁶ at 7 sample points.

Rounding: b3m22 with 8-digit h gives 0.7607679, with 9 digits 0.7607627 (float optimum 0.760763); b3m24 needs 12
digits (9 digits: 0.76080). β = 1: m = 23 needs 16, m = 32 needs 22, m = 44 needs 28 digits.

Lean cost (estimate, **not measured**): Round 13's instance has identities of degree 28 with 60-digit integers,
proved by `simp only [Finset.sum_range_succ, …]; push_cast; ring` and `norm_num`. b3m24 is degree 48 with
170-digit integers: about 3× the number of monomials and 3× the digit length. b1m44 is degree 88 with 450-digit
integers: about 10× and 7.5×. If `ring` becomes the bottleneck, the identities can be moved to `List ℤ`
convolutions and `decide +kernel` (formal076 §3.3); b3m19 (degree 38, 124 digits) is the low-risk instance.

## 4. Lean plans

Common to (b) and (c) — **Stage 1** (certificate and assembly, parametrised by β ∈ ℕ, β ≥ 1; a := β−1):

```lean
/-- Φ^{(a)}_{χ,j}(y) = ∑_{n<y} Λ(n) χ(n) √n (n/y)^a log^j(y/n)   (a = 0: r13Phi). -/
noncomputable def r14Phi {N : ℕ} (χ : DirichletCharacter ℂ N) (a j : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈y⌉₊, (Λ n : ℂ) * χ (n : ZMod N) *
    ((Real.sqrt n * ((n : ℝ) / y) ^ a * Real.log (y / n) ^ j : ℝ) : ℂ)
/-- A^{(a)}_i(Y) = ∑_{n<Y} Λ(n) √n (n/Y)^a log^i(Y/n)   (a = 0: r11A). -/
noncomputable def r14A (a i : ℕ) (Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌈Y⌉₊, Λ n * Real.sqrt n * ((n : ℝ) / Y) ^ a * Real.log (Y / n) ^ i
/-- R_κ(L) (r13R is κ = 3/2). -/
noncomputable def r14R (κ : ℝ) (θ : ℕ → ℝ) (J : ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), θ j * ∑ i ∈ Finset.range (j + 1), L ^ i / i.factorial * (1 / κ) ^ (j + 1 - i)
/-- F(L) = e^{-κL} R_κ(L). -/
noncomputable def r14F (κ : ℝ) (θ : ℕ → ℝ) (J : ℕ) (L : ℝ) : ℝ := Real.exp (-(κ * L)) * r14R κ θ J L

/-- Certificate in the scaled variables (L″ = β·log(x/n), s″ = (s+β−1)/β). `b 0 = 0 < b 1 < … < b (p+1) = ℓ″`;
`W` has sign `(-1)^(p-i)` on `[b i, b (i+1)]`. `β = 1, p = 1` is `R13Cert`. -/
structure R14Cert (β p J m : ℕ) (θ e : ℕ → ℝ) (b : ℕ → ℝ) (N₀ : ℝ) : Prop where
  beta    : 1 ≤ β
  low     : ∀ j, j < 3 → θ j = 0
  b0      : b 0 = 0
  mono    : ∀ i, i ≤ p → b i < b (i + 1)
  cell    : ∀ i, i ≤ p → ∀ L, b i ≤ L → L ≤ b (i + 1) → 0 ≤ (-1) ^ (p - i) * r13W θ J L
  modulus : ∀ t : ℝ, ‖r13K θ J (1 + (t : ℂ) * I)‖ ≤ r13G e m t
  e1pos   : 0 < e 1
  num     : 0 < N₀ ∧ N₀ ≤ r14F (1 + 1 / (2 * β)) θ J (b (p + 1))
              - ∑ i ∈ Finset.range (p + 1), (-1) ^ (p - i) *
                  (r14F (1 + 1 / (2 * β)) θ J (b i) - r14F (1 + 1 / (2 * β)) θ J (b (i + 1)))

def R14ZetaSmooth (a : ℕ) : Prop := DirichletLZerosOnLine → ∀ i : ℕ, ∃ C : ℝ, ∀ Y : ℝ, 1 ≤ Y →
  |r14A a i Y - (i.factorial : ℝ) * (1 / ((a : ℝ) + 3 / 2)) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)| ≤ C * Y ^ ((5 : ℝ) / 4)
def R14ChiExplicit (a : ℕ) : Prop := DirichletLZerosOnLine → ∀ j : ℕ, 3 ≤ j → ∃ C : ℝ,
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ y : ℝ, 1 ≤ y →
    ‖r14Phi χ a j y + (j.factorial : ℂ) *
        ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + a) ^ (j + 1)‖
      ≤ C * (Real.log q + 1) * (1 + Real.log y) ^ j + C * Real.sqrt y
def R14ZeroPow (a : ℕ) : Prop := DirichletLZerosOnLine →
  (∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ)).re ≤ Real.log q / 2 + C) ∧
  (∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      |∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re| ≤ C)

/-- Main theorem of Round 14 (c* = e^{-ℓ″/β} (β e₁/(2N₀))²; the weight of n is √n (n/x)^a W(β log(x/n))). -/
theorem r14A_eventually (hGRH : DirichletLZerosOnLine) (hZ : R14ZetaSmooth (β - 1)) (hC : R14ChiExplicit (β - 1))
    (hP : R14ZeroPow (β - 1)) (cert : R14Cert β p J m θ e b N₀) :
    ∀ c : ℝ, Real.exp (-(b (p + 1) / β)) * (β * e 1 / (2 * N₀)) ^ 2 < c → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R11Bound c n
```

(The normalisation of `num` and of the constant must be re-derived by whoever writes the assembly; the Python
script works in the unscaled variables, where c\* = e^{−ℓ}(Î/N̂)², and the two agree by §1.2.)

Stage 1 pieces and reuse:

| piece | content | reuses | lines (est.) |
|---|---|---|---|
| `R14Defs` | the above; `r14Phi χ 0 = r13Phi χ`, `r14A 0 = r11A`, `R14ZetaSmooth 0 ↔ R13ZetaSmooth` etc. | — | 150 |
| `R14CertGen` | Lemma E with Q = Σ ζ_a(−(s−1)²)^a, ζ_a ≥ 0 (replace `hfac` by a `Finset.sum`; the rest of the 90-line proof is unchanged); τ-recurrence for `r14R` with 1/κ | `r13Cert_modulus_of_factor`, `r13Cert_tau` | 250 |
| `R14AsmSum` | signed positivity over p+1 cells (induction on cells; the breakpoint terms telescope); binomial re-expansion with the factor (n/x)^a = e^{−aλ}(n/Y)^a; ζ main term from `R14ZetaSmooth` | `r13A_sum_ge`, `r13A_binom`, `r13A_R_eq`, `r13A_zeta_one` as templates | 500 |
| `R14AsmChi`, `R14Asm` | zero sum through the modulus at t = γ/β (‖x^{ρ+½}‖ = x, factor β^k from Re(1+iγ/β)^{−k}); final `eventually` argument (unchanged) | `r13A_zero_sum_le`, `r13A_chi`, `r13A_ev_aux` (as is) | 450 |
| generator + instance | as `r13Cert_gen`; Bernstein form in two variables as `r13Cert_bernB` | `research/barrier/r13Cert_gen` | 150 + ≈ 400 generated |

At β = 1 the three hypotheses are `r13Z_main`, `r13C_main`, `r13P_main`, so Stage 1 alone proves (c).

**Stage 2** (the analytic Props for a = β−1 ≥ 1; independent of each other):

| Prop | proof | reuses | lines (est.) |
|---|---|---|---|
| `R14ZeroPow a` | k = 1: `re_logDeriv_eq_tsum_of_growth` at s = a+3/2 (already general in s), \|L'/L(σ)\| ≤ `r11Chi_F 0` for σ ≥ 3/2, Γ-term two-valued as `r13P_gamma_le`. k ≥ 2: `r13P_deriv_identity` on the ball B(a+3/2, ¼): needs `r11Chi_PoleHyp` instances for zeros and Γ-poles on that ball (the structure takes U as a parameter) and the constant identity there | `R11ChiDeriv` (`r11Chi_pole_hasDerivAt` any m), `R13ZeroPow` as template | 300–350 |
| `R14ZetaSmooth a` | i = 0 by Abel summation (`sum_mul_eq_sub_integral_mul`, f(t) = t^a) from `R13ZetaSmooth` at i = 0; i ≥ 1 by the derivative induction of `r13Z_step` with the extra factor n^a (Y·d/dY[Y^aA^{(a)}_i] = i·Y^aA^{(a)}_{i−1}) | `r13Z_step`, `r13Z_mvt`, `r13Z_hasDerivAt_sum` as templates | 350–400 |
| `R14ChiExplicit a` | (i) `r14C_perron_gen`: `r11Chi_perron j (fun s => ∑' n, f n * (n:ℂ)^(-(β*s))) Y = ∑_{n^β<Y} f n · log^j(Y/n^β)/j!` — the proof of `r11Chi_perron_LSeries` with n replaced by n^β (it only uses `r11Chi_mellinInv_pow` at x = n^β/Y and a dominated sum); (ii) decomposition of s″ ↦ D(βs″−a) from `r11Chi_decomp` at βs″−a and at β+1 (difference of the two anchors is O(m_ρ/\|ρ\|²), summable); (iii) `r11Chi_perron_hasSum_poles` (Re w″ ≤ 3/2 ✓) and `r11Chi_perron_inv_sub`; (iv) bounds as `r13C_norm_N_le` with \|w″\| ≥ 1/(2β) instead of ½ and \|w″\| ≤ \|2−w″\| (Re w″ ≤ 1 under GRH) | `R11ChiPerron`, `R11ChiFormula`, `R13Chi` as template | 500–600 |

Per option:

| | (a) two poles | (b) β = 3, p = 2 | (c) β = 1, p = 2 | (c₀) β = 1, p = 1 |
|---|---|---|---|---|
| best certified c\* | not built (convex bound no better than (b)) | **0.7607585** (m = 24), 0.7607627 (22), 0.7607740 (19) | 0.7607742 (m = 44), 0.7608002 (32) | 0.7609161 (m = 23) |
| certificate | exponential polynomials: no exact zeros, sign cells need Taylor enclosures with ε-padding | degree 48, 170 digits (38, 124 for m = 19) | degree 88, 450 digits | degree 46, 124 digits |
| new Lean | Stage 1 + Stage 2 at two centres + mixed partial fractions + non-polynomial cells: ≳ 4000 | Stage 1 + Stage 2: **2600–3000** | Stage 1: **1400–1600** | **0** (one generated file, existing `R13Cert`/`r13A_eventually`) |
| risk | high | medium (P2β; certificate ≈ 3× Round 13) | certificate size (`ring` on degree 88 / 450 digits is untested) | none |

**Recommendation: (b), β = 3, staged.** Order of work: (1) regenerate a p = 1 instance with the existing
pipeline (free: "∀ c > 0.76092"); (2) Stage 1 with β as a parameter — nothing is redone later — and, if the
kernel accepts it, the instance b1m44 ("∀ c > 0.76078", no new analysis); (3) Stage 2 at a = 2 in three parallel
files, then the instance b3m24 ("∀ c > 0.76076") or b3m19 ("∀ c > 0.76078", small data). (b) is the only option
that reaches the target "within 10⁻⁵ of 0.76075" with a certificate of Round-13 size; (c) cannot get there
below m ≈ 60 (pole order 120).

## 5. Risks and open points

* **Nothing was compiled.** Line counts are extrapolated from Round 13 (2154 lines for the same shape of work).
  The statements in §4 are designs: in particular the normalisation in `R14Cert.num` / `r14A_eventually`, the
  exact error shape in `R14ChiExplicit` (only "o(x log q) for x ≍ log²q" is needed), and the hypothesis
  |w″| ≥ 1/(2β) in the analogue of `r13C_norm_N_le` should be re-derived by the prover.
* **The scaling argument of §1.2 is a proof sketch.** Its ingredients are elementary (homogeneity of s^{−(j+1)},
  absolute convergence on Re s″ = 2, Re w″ ≤ 3/2), and the resulting formula for c\* is confirmed numerically by
  an independent quadrature, but the uniform error terms were not written out.
* **Trivial zeros.** a must avoid a + ½ ∈ ℕ (a double pole at s = −a for one parity); integer a is safe. This rules
  out β = 5/2, not β = 3.
* **Certificate cost in Lean is unmeasured** (§3). b3m19 is the safe instance; b3m24 the ambitious one.
* **Optimality.** All designs are local optima; the β = 3, p = 2 limit at ℓ = 9/5 is 0.760755, so m = 24 leaves
  3·10⁻⁶. p = 3 or ℓ = 2 would gain at most another 3·10⁻⁶ and is not worth a third cell.
* The two-pole comparison (§2.3) is for the convex family, with a truncated basis; it shows no advantage, it does
  not prove that none exists at much higher order.
* As in Round 13, the statement is asymptotic (no N₀) and holds for all non-principal χ.
