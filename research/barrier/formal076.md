# formal076: a formalizable asymptotic record below CMQR's 0.7615 (index 2, GRH)

Status: research + design. No Lean was written or built. All numbers below are reproduced by the scripts in this
directory; "certified" means exact rational arithmetic (`formal076_certificate.py`, stdlib only).

| file | role | status |
|---|---|---|
| `formal076_joint.py` / `.out` | Task 1 as posed: joint SOCP over (φ, rational majorant G) | float (cvxpy + Clarabel) |
| `formal076_family.py` / `.out` | the "exact modulus" family (E): convex reference values, designs A and B vs degree | float |
| `formal076_design.py` / `.out` | local optimisation, conversion to the basis s^{-i}, rounding to integers → `formal076_testfn_{A,B}.json` | float → integer data |
| **`formal076_certificate.py`** / `.out` | **exact certificate** for both test functions → `formal076_certificate_{A,B}.json` (κ_n, e_k, Z, Bernstein cells) | exact (Fractions), 7 s |
| `formal076_check.py` / `.out` | independent mpmath quadrature of N̂, Î, |K| = G; designB sanity; rough N₀ | float |

The float scripts need the scratch venv (numpy, scipy, cvxpy, clarabel, mpmath); the certificate needs nothing.

## 0. Results

1. **The majorant can be avoided altogether.** A one-sided rational kernel has a *rational* modulus on the
   critical line iff its zeros, reflected into one half-plane, have even multiplicity (§1). For
   K(s) = Q((s−1)²)·H₀(s)², H₀ = P₀(s)/s^m (Perron variable s, zeros at s = 1+iγ, single pole at s = 0, i.e.
   weights √n·log^j(x/n) exactly as in designB), |K(1+it)| = Q(−t²)|H₀(1+it)|² is a polynomial in t² over
   (1+t²)^m. So G = |K|: no cone constraint, no polynomial positivity certificate, no loss, and
   Î = (1/2π)∫|K| is a rational number. Everything lives at the single point σ = 3/2 already used in Round 11.
   This family is dense (inner–outer factorisation), and the joint SOCP of Task 1 converges to it by itself
   (its optimum has ∫G/∫|K| − 1 ≈ 10⁻⁵).
2. **Certified constants** (exact arithmetic, §3):

   | design | kernel | x | sign pattern of the weight on [X, x) | pole order | **certified c\*** |
   |---|---|---|---|---|---|
   | **B** | (Z − (s−1)²)·H₀², m = 14 | e^{11/8}X ≈ 3.955X | + on [X, e^{39/40}X], − beyond (exact rational root L₁ = 2/5) | 28 | **0.7611430** |
   | A (fallback) | H², m = 15 | e^{11/10}X ≈ 3.004X | + (LLS/designB positivity, nothing new) | 30 | 0.7614062 |

   With 6-digit enclosures of three exponentials (what Lean would use): c\*(B) ≤ 0.761162, c\*(A) ≤ 0.761408.
   Target theorem: **∀ c > 0.7612, eventually every χ ≠ 1 mod n has χ(a) ≠ 1 for some a < c log²n** (design B);
   design A gives "∀ c > 0.76145" with strictly less new Lean.
3. **Limits of the approach** (float, §2): design A (φ ≥ 0 beyond X) cannot go below 0.76121; design B
   (one sign change, x ≈ 4X) has limit 0.76083; the unrestricted CMQR value is 0.76075. With the pole fixed
   at β = 1 (forced by the infrastructure: √n-weights, Perron line Re s = 2) convergence in m is slow:
   B reaches 0.76114 at m = 14 and only 0.76111 at m = 17.
4. **Certificate cost.** Three polynomial identities of degree ≤ 28 with integer coefficients of ≤ 60 digits,
   24 Bernstein coefficients (one cell, all positive, min/max = 0.37), three exp enclosures, one rational
   inequality. No Sturm sequence, no SOS, no interval subdivision.
5. **Lean plan** (§4): three analytic Props generalising Round 11 from j ≤ 3 to all j with *existential*
   constants, one assembly theorem parametrised by a certificate, one generated instance file.
   Estimated 2000–2600 new lines. An explicit-N₀ version is **not** cheap and not worthwhile (§5).

## 1. The family (E): kernels with exactly rational modulus

Conventions = designB: weights w(n) = √n·W(log(x/n)) on n < x, W(L) = Σ_{j=3}^{2m−1} θ_j L^j/j!,
K(s) = Σ_j θ_j s^{−(j+1)} = Σ_{n=4}^{2m} κ_n s^{−n} (κ_n = θ_{n−1}), so that

    Σ_{n<x} Λ(n)χ(n)w(n) = (1/2πi)∫_{(2)} −L'/L(s−½,χ)·K(s)·x^s ds,   zeros at s = ρ+½ = 1+iγ.

inside.md's variables: s_in = s−1, β = 1, u = 1/s, z = 2u−1, c = ℓ = log(x/X), v = ℓ − L.

**Lemma E (exact modulus).** Let H₀(s) = Σ_{i=i₀}^m h_i s^{−i} with real h_i, Z ≥ 0, K = (Z − (s−1)²)·H₀(s)².
Then for real t, with s = 1+it (so s̄ = 2−s and (s−1)² = −t²):

    |K(1+it)| = (Z+t²)·H₀(s)H₀(2−s) =: G(t) ≥ 0,     G(t) = Σ_{k=1}^m e_k·Re (1+it)^{−k},

    e_a/2 = Σ_{i≥a, k} Q_{ik}·C(i+k−a−1, k−1)/2^{i+k−a},   Q_{ik} = g_i g_k + Z h_i h_k,   Σ g_i s^{−i} := (s−1)H₀(s),

    Î := (1/2π)∫G = e₁/2 = Σ_{i,k} Q_{ik}·C(i+k−2, i−1)/2^{i+k−1}.

*Proof.* H₀ has real coefficients, so conj H₀(s) = H₀(s̄) = H₀(2−s) and |H₀|² = H₀(s)H₀(2−s);
t²|H₀|² = [(s−1)H₀(s)]·[(1−s)H₀(2−s)]. Partial fractions of s^{−i}(2−s)^{−k} at s = 0 and s = 2 are symmetric
under s ↔ 2−s after symmetrising in (i,k), and s^{−a} + (2−s)^{−a} = 2Re s^{−a} on the line.
(1/2π)∫Re(1+it)^{−k}dt = ½·[k = 1]. ∎ (Z = 0, i₀ = 2 is design A; more generally any real Q with Q(−t²) ≥ 0 works,
e.g. a complex-conjugate pair of zeros of K in Re s_in > 0.)

Why this is the whole story: K is in the Hardy space H¹ of the half-plane; K = (singular inner x^s)·(Blaschke)·(outer),
and |K| = |outer|. |K| is rational iff the outer part is a perfect square up to the reflected Blaschke zeros. With
H₀ free and Q carrying the zeros of K in Re s_in > 0 together with their mirror images the family is dense.
designB §1.3 looked at K = Q(−s²)(a−s)^r/(a+s)^{2m+r} only, i.e. without the square factor P₀², and found nothing.

**The functional.** With λ = e^{−ℓ} = X/x and R(L) := Σ_n κ_n Σ_{i<n} (L^i/i!)(2/3)^{n−i}:

    ∫_0^{e^{−L}} W(log 1/t)√t dt = e^{−3L/2}·R(L).

If W ≤ 0 on [0, L₁] and W ≥ 0 on [L₁, ℓ] (L₁ = 0: design A):

    N̂ := ∫_0^λ W√t − ∫_λ^1 |W|√t = 2e^{−3ℓ/2}R(ℓ) − 2e^{−3L₁/2}R(L₁) + R(0),      c* = e^{−ℓ}·(Î/N̂)².     (1.1)

(designB: K = 6/s⁴, ℓ = log 3 gives N̂ = D, Î = 3/2, c* = 3/(4D²) = 0.777134; `formal076_check.py` (3).)
ℓ and L₁ are taken *rational*: then R(ℓ), R(L₁), R(0), Î are rationals and the only transcendental inputs are
e^{3ℓ/2}, e^{3L₁/2}, e^{ℓ}.

**Exact sign change.** K = Z·H₀² − (s−1)²H₀², so W = Z·W_b − W_a with W_a, W_b ∈ ℚ[L]. Put
Z := W_a(L₁)/W_b(L₁) ∈ ℚ. Then W(L₁) = 0 *exactly* at the rational point L₁, W = L³(L−L₁)·W̃, and the sign
pattern is equivalent to W̃ > 0 on [0, ℓ]. Consequences: |W| is ±W on two cells with the rational-exponent
breakpoint X₁ = x·e^{−L₁}; no ε-padding; and the sharp-cut-off loss at X₁ vanishes identically (the coefficient of
A₀(X₁) is W(L₁) = 0).

**Asymptotic theorem behind (1.1)** (GRH; proof = designB Lemmas 2–8 with general j, constants not tracked).
Suppose χ(a) = 1 for all a < X; χ̃ primitive mod q | n inducing χ; x = e^ℓX, X₁ = e^{−L₁}x.
* Positivity with signs: Re χ̃(n)·w(n) ≥ −|w(n)| for n ≥ X, χ̃(n) = 1 for n < X:
  Re Σ_{n<x}Λχ̃w ≥ Σ_{n<X}Λw − Σ_{X≤n<x}Λ|w| = 2A(X) − 2A(X₁) + A(x),  A(Y) := Σ_{n<Y}Λ(n)√n·W(log(x/n)).
* ζ side (RH): A(Y) = Σ_j (θ_j/j!)Σ_i C(j,i) log^{j−i}(x/Y)·A_i(Y), A_i = `r11A i`, and
  A_i(Y) = i!(2/3)^{i+1}Y^{3/2} + O_i(Y^{5/4}). So the right side is x^{3/2}N̂ + O(x^{5/4}).
* χ side: Σ_{n<x}Λχ̃w = −Σ_ρ x^{ρ+½}K(ρ+½) + O((log q + 1)·log^{2m−1}x + √x), uniformly in χ̃; and
  |Σ_ρ x^{ρ+½}K(ρ+½)| ≤ x·Σ_ρ G(γ) = x·Σ_k e_k Σ_ρ Re(3/2−ρ)^{−k} = x·(Î·log q + O(1))
  (k = 1: Hadamard at 3/2; k ≥ 2: derivatives of it, bounded by Σ Λ(n)log^{k−1}n·n^{−3/2}/(k−1)! + ζ(k)-type sums).
* Hence √x·N̂ ≤ Î·log n + o(log n); with X = c·log²n this fails for large n as soon as c > c*. ∎

## 2. Task 1: numerics (floating point)

### 2.1 The joint SOCP as posed (`formal076_joint.out`)

φ in the Hardy family β = 2, c = 2, D = 32 (optimum without majorant: 0.760762); G = Σ e_{jk} Re(a_j+it)^{−k};
constraint G ≥ |K| on 1500 nodes, G rescaled by the worst violation on 30000 nodes.

```
 a_j=[1]              K<= 4 ( 4 terms): c* = 0.765501   loss int G/int|K| - 1 = 1.32e-03
 a_j=[1]              K<= 8 ( 8 terms): c* = 0.761810   1.90e-05
 a_j=[1]              K<=12 (12 terms): c* = 0.761120   6.17e-06
 a_j=[1]              K<=16 (16 terms): c* = 0.761050   2.01e-05
 a_j=[2]              K<= 8 ( 8 terms): c* = 0.761463   3.26e-05
 a_j=[2]              K<=16 (16 terms): c* = 0.760813   3.13e-06
 a_j=[1, 2]           K<= 8 (16 terms): c* = 0.760870   6.38e-06
 a_j=[1, 2]           K<=12 (24 terms): c* = 0.760820   4.86e-06
 a_j=[.75,1,1.5,2,3]  K<= 6 (30 terms): c* = 0.760822   7.04e-06
 a_j=[.75,1,1.5,2,3,4,6] K<=8 (56):     c* = 0.760792   1.03e-05
```

Answers: **< 0.7615 yes (8 terms at a = 2, 12 terms at a = 1); < 0.7612 yes (12 terms at a = 1); 0.7608 with 16–24 terms.**
The fixed-φ majorant loss of designB §1.4 (0.3–0.4%) disappears under joint optimisation (10⁻⁵): the optimiser
moves φ until |K| is (nearly) in the span of the G-basis, i.e. into family (E). Caveats: these φ have β = 2 (pole at
s_in = −2: weights n^{3/2}log^j, outside our Perron set-up), the basis Re(a+it)^{−k} is ill-conditioned for k > 12
(Clarabel stalls; the numbers are feasible points, not optima), and the route needs the positivity certificate
G² − |K|² ≥ 0: after clearing denominators a polynomial in T = t² of degree D+2 = 34 (a = β) up to 2K+D+2 = 66,
tangent to zero at ≈ K points (relative gap 10⁻⁶ after rescaling). I did not build that certificate, because
family (E) makes it unnecessary. For scale: the Euclidean Sturm chain of the much easier degree-23 polynomial W̃
of §3 already contains integers of 26 000 digits.

### 2.2 Family (E) at β = 1 (`formal076_family.out`)

Convex reference (all q of degree D, (1+z)² | q, β = 1): what any kernel with support v < c can reach.

```
  c = log 3  : phi >= 0: 0.761207   with |phi|: 0.761207   (no zero of K in Re s_in > 0: outer)
  c = 11/8   : phi >= 0: 0.761218   with |phi|: 0.760836   (one real zero, s_in ~ 8.5)
  c = log 4  : phi >= 0: 0.761214   with |phi|: 0.760826
  c = log 6  : phi >= 0: 0.761268   with |phi|: 0.760762   (a complex pair)
  c = 2      : phi >= 0: 0.761257   with |phi|: 0.760757
```

Design A (K = H², H = u·(1+z)r₁(z), deg r = d, m = d+1). For a fixed sign pattern N is a quadratic form in r and
I = ½|r|², so the optimum is the top eigenvalue of a Hankel matrix (Nehari); the optimum has φ ≥ 0 by itself.

```
  c = log 3, beta=1.0: d=4: 0.766343  d=6: 0.762998  d=8: 0.761878  d=10: 0.761830  d=12: 0.761649  d=14: 0.761408  d=16: 0.761300  d=20: 0.761282
             beta=1.5: d=4: 0.763312  d=6: 0.762154  d=8: 0.761708  d=10: 0.761335  d=12: 0.761289  d=14: 0.761277  d=16: 0.761250  d=20: 0.761241
             beta=2.0: d=4: 0.778625  d=6: 0.764769  d=8: 0.761655  d=10: 0.761300  d=12: 0.761249  d=14: 0.761246  d=16: 0.761237  d=20: 0.761215
  c = 11/10, beta=1  : d=10: 0.761824  d=12: 0.761644  d=13: 0.761513  d=14: 0.761406  d=15: 0.761336  d=16: 0.761300  d=18: 0.761284  d=20: 0.761282
```

Design B (K = (Z−(s−1)²)H₀², H₀ = u³r₀(z), deg r₀ = d₀, m = d₀+3; non-convex, local optimisation started from the
outer square root of the convex optimum; ℓ = 11/8, the best of {1.25, 1.3, 1.33, 1.375}; ℓ must stay below the
second sign change v ≈ 1.396):

```
  d0= 8 m=11: 0.761666     d0=10 m=13: 0.761218     d0=11 m=14: 0.761143     d0=12 m=15: 0.761128     d0=14 m=17: 0.761113
```

Reading. (i) < 0.7615 needs m ≥ 15 with A or m ≥ 12 with B; < 0.7612 needs B with m ≥ 14. (ii) β = 3/2 or 2 would
halve the degree (A: 0.76134 at d = 10) but needs weights n·log^j or n^{3/2}log^j: Dirichlet series absolutely
convergent only for Re s > 2 resp. 5/2, so `r11Chi_perron` (line Re s = 2) and everything centred at 3/2 would have to
be redone. Not recommended. (iii) The B values are local optima (several restarts agree to 10⁻⁶); the plateau
0.76111–0.76114 for m = 14…17 is real slowness of the Laguerre expansion at β = 1, not optimiser noise, as far as
I can tell.

## 3. Task 2: the certificates (`formal076_certificate.out`)

### 3.1 Data

**Design B** (`formal076_testfn_B.json`): ℓ = 11/8, L₁ = 2/5, m = 14,

    H₀(s) = Σ_{i=3}^{14} h_i s^{−i},  h₃..h₁₄ = 13876, 25555, −355840, 1490840, −3910567, 7274091, −9941194, 10000000,
                                              −7241712, 3585379, −1089115, 153374
    Z = W_a(2/5)/W_b(2/5) = 324739439977465272138434392496673496371641728/3326576759504470868502439836173349842092333
      = 97.619704415…        (K vanishes at s = 1 ± √Z = 1 ± 9.8803)
    K(s) = (Z − (s−1)²)·H₀(s)² = Σ_{n=4}^{28} κ_n s^{−n},   κ₄ = −h₃² = −192543376.

**Design A** (`formal076_testfn_A.json`): ℓ = 11/10, m = 15, K = H², H = Σ_{i=2}^{15} h_i s^{−i},

    h₂..h₁₅ = 922, −814, 27485, −197252, 821338, −2369416, 5052088, −8154864, 10000000, −9205428, 6179393, −2861562, 818453, −109081.

All derived exact data (κ_n, e_k, Î, W̃, N-bound) are in `formal076_certificate_{A,B}.json`.

### 3.2 What is checked, exactly

```
design B: m = 14 (K has a pole of order 28 at s = 0; weights sqrt(n) log^j(x/n), 3 <= j <= 27), ell = 11/8, x = e^ell X
  L1 = 2/5,  Z = 97.619704415250 (rational, digits num/den = (45, 43))
  (a) W(L) = L^3 (L - L1) Wt(L), deg Wt = 23; Sturm: Wt has no root in [0, ell], Wt(0) = 8.023e+07 > 0  (largest integer in the Sturm chain: 10^26354)
      Bernstein certificate: all 24 Bernstein coefficients > 0 on each of 1 cell(s): [0,11/8]   (min/max coefficient 3.7e-01)
  (b) |K(1+it)| = G(t) = sum_{k<=14} e_k Re(1+it)^-k : polynomial identity of degree 28 in s verified exactly; G >= 0 structurally
  (c) Ihat = e_1/2 = 461906597.594 (exact rational);   Nhat in [266221791.997, 266221791.997]
  RESULT: c* = e^{-ell} (Ihat/Nhat)^2 in [0.761142923, 0.761142923];   J >= 1.14621713
  sizes: after clearing denominators the 25 coefficients kappa_n are integers with <= 60 digits; e_k: <= (59, 50) digits (num/den)
design A: m = 15 (pole of order 30; 3 <= j <= 29), ell = 11/10
  (a) W(L) = L^3 Wt(L), deg Wt = 26; no root in [0, ell]; Bernstein: all 27 coefficients > 0 on [0,11/10] (min/max 6.2e-01)
  (b) identity of degree 30 verified exactly      (c) Ihat = 345809.770362, Nhat = 228647.84628
  RESULT: c* in [0.761406112, 0.761406112];   sizes: kappa_n integers <= 15 digits; e_k <= (15, 7) digits
```

* **(a) N̂.** W = L³(L−L₁)W̃ is exact division in ℚ[L]. W̃ > 0 on [0,ℓ]: its 24 Bernstein coefficients on [0, ℓ]
  (degree 23, no elevation, no subdivision) are all positive — a one-line Lean proof once the identity
  ℓ²³·W̃(L) = Σ_k b_k C(23,k) L^k(ℓ−L)^{23−k} is checked. (The script also runs a Sturm count as a cross-check; it is
  1000× more expensive and not needed.) Then (1.1) with rational R(ℓ), R(L₁), R(0) and Taylor enclosures of the
  exponentials. Lean-sized inputs: e^{33/16} ≤ 7.86561, e^{3/5} ≥ 1.82211, e^{11/8} ≥ 3.95507 give c\*(B) ≤ 0.7611618;
  nine digits (7.865609274, 1.8221188, 3.955076722) give 0.7611429. Design A: e^{33/20} ≤ 5.20698, e^{11/10} ≥ 3.00416
  give 0.7614077. Relative sizes: R(ℓ)/Î = 4.9345, R(L₁)/Î = 1.2359, R(0)/Î = 0.6782 — no cancellation problem.
* **(b) G ≥ |K|** is the *identity* of Lemma E: (Z−(s−1)²)·P₀(s)P₀(2−s) = Σ_a (e_a/2)(s^{m−a}(2−s)^m + s^m(2−s)^{m−a}),
  P₀ = s^mH₀, degree 2m = 28, together with κ = coefficients of (Z−(s−1)²)H₀² (degree 26). G ≥ 0 is structural.
  There is no inequality in t to certify.
* **(c) ∫G**: Î = e₁/2, a rational.
* Independent check (`formal076_check.out`): mpmath quadrature of ∫W√t with |W| and of (1/2π)∫|K(1+it)| from the κ_n
  alone gives c\* = 0.7611429226 (B), 0.7614061125 (A); |G − |K||/|K| ≤ 6·10⁻¹² at 7 sample points.

Rounding: h was optimised in the z-basis, converted to powers of 1/s and rounded to 7–8 significant digits
(integers ≤ 10⁷). The basis change amplifies by ≈ 10⁵ but the optimum is stationary: 6 digits already give
0.7611440, 5 digits 0.76135, 4 digits fail (0.786).

### 3.3 Cost in Lean (estimate; not measured — no Lean was run)

Recommended encoding: polynomials as `List ℤ` (after clearing the one denominator den(Z)·27!-type constant per
identity), a generic lemma "list convolution evaluates to the product", and `decide +kernel` (or `by rfl` on `ℤ`
lists) for: (1) κ = (Z−(s−1)²)⋆h⋆h (12×12 convolution, then ×quadratic); (2) the partial-fraction identity
(Σ of 14 products of a monomial with (2−s)^{≤14}); (3) the L³(L−L₁)W̃ factorisation and the Bernstein identity
(24 terms); (4) R(ℓ), R(L₁), R(0) ∈ ℚ (25×27 terms each). About 10⁴ multiplications of integers of ≤ 75 digits in
total; kernel GMP arithmetic should do this well under a second; `norm_num [Finset.sum_range_succ]` on the same
sums is the fallback and would be the slow path (minutes). Python does all four in 20 ms.
Design A is the same with 15-digit integers and no Z.

## 4. Task 3: formalization plan

Everything is at β = 1, σ = 3/2, Perron line Re s = 2, hypothesis `DirichletLZerosOnLine` as in Round 11.
Constants are existential: no certified F_k, ψ^{(k)}, γ_k for large k are needed.

### 4.1 New definitions (`R13Defs.lean`)

```lean
/-- Φ_{χ,j}(y) = ∑_{n<y} Λ(n) χ(n) √n log^j(y/n)  (r11Phi is j = 3). -/
noncomputable def r13Phi {N : ℕ} (χ : DirichletCharacter ℂ N) (j : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈y⌉₊, (Λ n : ℂ) * χ (n : ZMod N) * ((Real.sqrt n * Real.log (y / n) ^ j : ℝ) : ℂ)
noncomputable def r13W (θ : ℕ → ℝ) (J : ℕ) (L : ℝ) : ℝ := ∑ j ∈ Finset.range (J + 1), θ j * L ^ j / j.factorial
noncomputable def r13K (θ : ℕ → ℝ) (J : ℕ) (s : ℂ) : ℂ := ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) / s ^ (j + 1)
noncomputable def r13R (θ : ℕ → ℝ) (J : ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), θ j * ∑ i ∈ Finset.range (j + 1), L ^ i / i.factorial * (2 / 3) ^ (j + 1 - i)
/-- A(Y) = ∑_{n<Y} Λ(n) √n W(log(x/n)). -/
noncomputable def r13A (θ : ℕ → ℝ) (J : ℕ) (x Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌈Y⌉₊, Λ n * Real.sqrt n * r13W θ J (Real.log (x / n))
noncomputable def r13G (e : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 m, e k * ((1 : ℂ) / (1 + t * I) ^ k).re

/-- The numerical certificate. `L₁ = 0` is design A (no sign change). -/
structure R13Cert (J m : ℕ) (θ e : ℕ → ℝ) (ℓ L₁ N₀ : ℝ) : Prop where
  low     : ∀ j, j < 3 → θ j = 0
  range   : 0 ≤ L₁ ∧ L₁ < ℓ
  negCell : ∀ L, 0 ≤ L → L ≤ L₁ → r13W θ J L ≤ 0
  posCell : ∀ L, L₁ ≤ L → L ≤ ℓ → 0 ≤ r13W θ J L
  modulus : ∀ t : ℝ, ‖r13K θ J (1 + t * I)‖ ≤ r13G e m t
  e1pos   : 0 < e 1
  num     : 0 < N₀ ∧ N₀ ≤ 2 * Real.exp (-(3 * ℓ / 2)) * r13R θ J ℓ
                          - 2 * Real.exp (-(3 * L₁ / 2)) * r13R θ J L₁ + r13R θ J 0
```

### 4.2 New analytic Props (statements; all uniform in χ, constants existential)

```lean
/-- (P1) ζ side, all orders, sharp cut-off included (i = 0).  RH. -/
def R13ZetaSmooth : Prop := DirichletLZerosOnLine → ∀ i : ℕ, ∃ C : ℝ, ∀ Y : ℝ, 1 ≤ Y →
  |r11A i Y - (i.factorial : ℝ) * (2 / 3) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)| ≤ C * Y ^ ((5 : ℝ) / 4)

/-- (P2) χ explicit formula of every order j ≥ 3 (designB Lemma 3 without constants).  GRH. -/
def R13ChiExplicit : Prop := DirichletLZerosOnLine → ∀ j : ℕ, 3 ≤ j → ∃ C : ℝ,
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ y : ℝ, 1 ≤ y →
    ‖r13Phi χ j y + (j.factorial : ℂ) * ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1)‖
      ≤ C * (Real.log q + 1) * (1 + Real.log y) ^ j + C * Real.sqrt y

/-- (P3) zero sums at 3/2 of every order.  GRH. -/
def R13ZeroPow : Prop := DirichletLZerosOnLine →
  (∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ)).re ≤ Real.log q / 2 + C) ∧
  (∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      |∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re| ≤ C)
```

How each reduces to what exists:

* **P1.** i = 1,2,3: `R11ZetaExplicit` + `R11ZetaZ` (proved). i = 0: lower bound is `r11Asm_A0_ge`; the upper bound
  is its mirror image (difference A₁(Xe^{δ}) − A₁(X) ≥ δ·A₀(X)). i ≥ 4: induction with
  A_i(Y) = i·∫_1^Y A_{i−1}(u) du/u (termwise: log^i(Y/n) = i∫_n^Y log^{i−1}(u/n)du/u), which turns the bound for i−1
  into the bound for i. Alternative: redo `R11ZetaX*` with `r11Chi_perron j` instead of the hard-coded k ∈ {2,3,4}
  kernels. ≈ 350–450 lines. (Only i ≤ 27 is used; a general ∀ i is no harder.)
* **P2.** `r11Chi_perron_LSeries`, `r11Chi_perron_inv_sub`, `r11Chi_perron_hasSum_poles` are already stated for all
  j ≥ 3; `r11Chi_decomp` is independent of j. What is j = 3-specific is `r11Chi_perron_pole3`, `r11Chi_Phi_formula`
  and all of `R11ChiBound`. General j: each pole w contributes y^w/w^{j+1} − Σ_{i≤j}(log^i y/i!)w^{i−j−1} − (log^j y/j!)/(2−w);
  bound the non-oscillating part by (1+log y)^j·2/|w|² for |w| ≥ ½ (zeros: |w| ≥ 1, |2−w| = |w| on the line; trivial
  zeros: real w ≤ ½, |w| ≥ ½, y^w ≤ √y) and sum with `r11Chi_summable_zero_weight`, `r11Chi_summable_gamma_weight`;
  Σ_ρ m_ρ/|ρ+½|² = Z₂(χ) ≤ ½log q + C by P3 (k = 1). ≈ 500–700 lines.
* **P3.** k = 1: `r11Zs_Z2_eq`-type identity (Re ξ'/ξ(3/2)) with |L'/L(3/2,χ)| ≤ −ζ'/ζ(3/2). k ≥ 2: generalise
  `r11Chi_zeroPow_eq` from k ≤ 3 to all k by induction with the already generic `r11Chi_pole_hasDerivAt` (any m),
  `r11Chi_norm_LSeries_logMul_le`, `r11Chi_summable_zeroPow`, `r11Chi_summable_gammaPow` (all stated for general k).
  ≈ 200–300 lines.

### 4.3 Assembly (`R13Asm.lean`)

```lean
/-- signed positivity (generalises `r11Asm_sum_ge`): with A(Y) := ∑_{n<Y} Λ(n) √n W(log(x/n)), -/
theorem r13Asm_sum_ge {q : ℕ} (χ : DirichletCharacter ℂ q) {X x : ℝ} (cert : R13Cert J m θ e ℓ L₁ N₀)
    (hx : x = Real.exp ℓ * X) (h1 : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → χ (a : ZMod q) = 1) :
    2 * r13A θ J x X - 2 * r13A θ J x (Real.exp (-L₁) * x) + r13A θ J x x
      ≤ ∑ j ∈ Finset.range (J + 1), θ j / j.factorial * (r13Phi χ j x).re

/-- ζ side: main term of the left side. -/
theorem r13Asm_zeta (hGRH) (hZ : R13ZetaSmooth) (cert) : ∃ C, ∀ X ≥ 1, ∀ x, x = Real.exp ℓ * X →
    N₀ * x ^ ((3 : ℝ) / 2) - C * x ^ ((5 : ℝ) / 4)
      ≤ 2 * r13A θ J x X - 2 * r13A θ J x (Real.exp (-L₁) * x) + r13A θ J x x

/-- χ side: zero sum through the exact modulus. -/
theorem r13Asm_chi (hGRH) (hC : R13ChiExplicit) (hP : R13ZeroPow) (cert) : ∃ C, ∀ q χ (primitive, ≠ 1), ∀ x ≥ 1,
    ∑ j ∈ Finset.range (J + 1), θ j / j.factorial * (r13Phi χ j x).re
      ≤ x * (e 1 / 2 * Real.log q + C) + C * (Real.log q + 1) * (1 + Real.log x) ^ J + C * Real.sqrt x

/-- Main theorem. -/
theorem r13_eventually (hGRH : DirichletLZerosOnLine) (hZ : R13ZetaSmooth) (hC : R13ChiExplicit) (hP : R13ZeroPow)
    (cert : R13Cert J m θ e ℓ L₁ N₀) :
    ∀ c : ℝ, Real.exp (-ℓ) * (e 1 / (2 * N₀)) ^ 2 < c → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R11Bound c n

/-- Instance (generated file `R13Cert076.lean`). -/
theorem r13_record (hGRH : DirichletLZerosOnLine) : ∀ c : ℝ, 0.7612 < c → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R11Bound c n
```

Pieces: reduction to the primitive χ̃ and coprimality as in `r11Asm_core` / `llsElem_no_witness_facts`; binomial
re-expansion log(x/n) = log(x/Y) + log(Y/n) (as `r11Asm_Tlt_ge`, now an identity for every j); `‖x^{ρ+½}‖ = x` and
`cert.modulus` at t = γ (existing `r11Zx`/`r11Zs` line facts); the final limit: √x·N₀ ≤ (e₁/2)·log n + o(log n) with
x = e^ℓ·c·log²n — a `Filter.Tendsto`/`eventually` argument (Round 11 did the analogue with explicit numbers via
`nlinarith`; here it is cleaner to prove ∃ N abstractly). ≈ 500–600 lines.

Certificate file: helper lemma `r13_modulus_of_factor` (Lemma E: from the two polynomial identities to
`cert.modulus`, using conj s = 2 − s on the line), `r13_cells_of_bernstein`, three exp enclosures
(Taylor with remainder; cf. `r11Asm_exp_neg_le`, `r11Asm_log_le`), and the generated integer lists. ≈ 300 lines of
generic code + ≈ 150 generated.

### 4.4 Effort and order of work

| item | new lines (est.) | difficulty | reuses |
|---|---|---|---|
| P3 `R13ZeroPow` | 200–300 | low | `R11ChiDeriv` (generic in m), `R11ZeroSumHad` |
| P1 `R13ZetaSmooth` | 350–450 | low–medium | `R11ZetaExplicit`, `r11Asm_A0_ge` |
| P2 `R13ChiExplicit` | 500–700 | medium | `R11ChiPerron` (general j), `R11ChiFormula` |
| assembly `r13_eventually` | 500–600 | medium | `R11AsmCore`, `LLSElem` |
| certificate + instance | 450 | low (mechanical) | generators in `r11Asm_gen`, `r12M4_gen` style |
| **total** | **2000–2500** | | |

P1, P2, P3 and the certificate are independent (four parallel agents); the assembly needs only their statements.
Design A needs the same P1–P3 and the same assembly (L₁ = 0), so it is a free by-product, not a shortcut:
the sign cell costs ≈ 60 extra lines in `r13Asm_sum_ge` and nothing analytic.

## 5. Explicit N₀: not cheap, and not worth it

Machinery-wise an explicit version is designB with 25 values of j instead of one: explicit constants in P1–P3 for all
j ≤ 27 (F_k = ΣΛ log^k n·n^{−3/2} for k ≤ 27, ψ^{(k)}, Z_k; crude analytic bounds would do because they multiply
lower-order terms) and the hypothesis gain −κ in the k = 1, 2 zero sums. But the outcome is poor, because the margin
c − c\* is tiny and the sharp cut-off at X costs a relative x^{−1/4} (designB Lemma 6; coefficient
e₁ = 4W(ℓ)√Z₂·e^{−5ℓ/4}/Î = 0.174; the cut at X₁ is free since W(L₁) = 0). Leading-term estimate
(J√c − 1)·L ≥ e₁e^{ℓ/4}c^{1/4}√L, O(1) terms ignored, **not certified** (`formal076_check.out`):

    c = 0.7615: n ≳ 10^415000     c = 0.762: 10^72000     c = 0.765: 10^3600     c = 0.77: 10^680     c = 0.775: 10^280

(designB: c = 0.78 from 10⁴³, 0.779 from 10⁷⁰⁵.) In addition the residue terms (log q)·log^{27}x/x are only negligible
for astronomically large x and would need care. Replacing Lemma 6 by Schoenfeld's ψ(X) = X + O(√X log²X) would
improve the exponent but not make the thresholds interesting. Recommendation: asymptotic statement only.

## 6. Risks and open points

* **Unverified in Lean.** Nothing was compiled. The three Props are stated so that Round 11's proofs generalise
  line by line, but P2's uniform bound (C·(log q+1)(1+log y)^j + C√y) should be re-derived by whoever proves it; if
  a different shape comes out the assembly only needs "= o(x log q) for x ≍ log²q".
* **Lemma E and (1.1)** are checked exactly as identities and numerically by independent quadrature; the
  asymptotic theorem of §1 is a proof sketch in designB's framework (the same steps, general j), not refereed.
* **Certificate cost in the kernel** is an estimate (§3.3). If `decide +kernel` on 60-digit integer lists is
  slower than expected, design A (15-digit integers) is immune, and B can be re-rounded: L₁ = 2/5 and
  7-digit h are what make Z a 45/43-digit rational.
* **Optimality.** Design B at m = 14 is a local optimum of a non-convex problem; a better point of the same size
  would only improve c\*. The gap to the limit 0.76083 at ℓ = 11/8 is due to β = 1; reaching 0.7609 would need
  m ≳ 25 or a second pole (β = 2), i.e. new Perron infrastructure.
* **Exp enclosures.** The 6-digit bounds leave 3.8·10⁻⁵ of room below 0.7612; with 4-digit bounds the claim
  0.7612 fails (0.76123), so the instance must use ≥ 6 digits (Taylor to ≈ 12 terms).
* The statement proved is for all non-principal χ (index 2 is the worst case, as in designB §7); no gain for
  higher index was computed here.
