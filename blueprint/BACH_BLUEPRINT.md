# Blueprint: GRH ⟹ Bach's bound with an explicit constant

Lean counterpart: `lean/DetPrimality/Bach/Blueprint.lean` (namespace `DetPrimality.Bach`).
Target: `grh_implies_bach : GRHImpliesBach 1024`, i.e.

> `DirichletLZerosOnLine → BachBound 1024`: for `n > 2`, every proper subgroup `H < (ℤ/n)ˣ`
> misses some unit `a < 1024 (log n)²`.

Status tags: **[PROVED]** = fully proved in Lean, compiles; **[DEEP]** = sorried analytic input;
**[NUM]** = sorried numerical fact. As of this writing there are exactly 4 sorries
(3 DEEP, 1 NUM); everything else, including the whole assembly, is proved.

The constant `c = 1024` is what the *crude elementary inputs currently in Mathlib* give
comfortably. §8 explains how the same skeleton yields `c ≈ 70` and below (only elementary lemmas
change; the deep inputs §2–§3 are constant-optimal already).

---

## 0. Notation and strategy

* `Λ` von Mangoldt. `χ` a Dirichlet character mod `n`, `χ ≠ 1`; `χ*` the primitive character
  mod `q = cond χ` inducing it (`q ∣ n`, `q ≥ 3`). `a ∈ {0,1}` the parity of `χ*`.
* `L(s,χ)` = `DirichletCharacter.LFunction χ`; `γ_χ(s) = Γ_ℝ(s+a)` = `gammaFactor χ`,
  `Γ_ℝ(s) = π^{-s/2}Γ(s/2)`; completed `Λ(s,χ) = γ_χ(s) L(s,χ)` = `completedLFunction χ`
  (Mathlib's normalisation, **no** `q^{s/2}`), functional equation
  `Λ(1-s,χ) = q^{s-1/2} ε(χ) Λ(s,χ̄)` (`IsPrimitive.completedLFunction_one_sub`).
* Zeros: `ρ` runs over zeros of `L(s,χ*)` with `0 < Re ρ < 1`, with multiplicity
  (`zeroOrd χ ρ`, defined via `analyticOrderNatAt`; sums over zeros are `∑' ρ : ℂ, zeroOrd χ ρ * f ρ`).
  For primitive `χ ≠ 1` these are exactly the zeros of the entire function `Λ(s,χ)`.
* Smoothed sums (Bach's weight `(1 - m/x)`, whose Mellin transform `1/(s(s+1))` makes the zero
  sum absolutely convergent):
  `S(x,χ) = ∑_{m<x} Λ(m)χ(m)(1-m/x)` (`smoothPsi`), `ψ₁(x) = ∑_{m<x} Λ(m)(1-m/x)` (`psiOne`).
* `T(χ) = ∑_ρ 1/|ρ(ρ+1)|` (`zeroSum`).

Strategy (Ankeny–Montgomery–Bach). Suppose `χ(a) = 1` for every unit `a < x`. Then
`Re S(x,χ*) ≈ ψ₁(x) ≫ x`, while GRH + the explicit formula give `|S(x,χ*)| ≤ (√x+5)(log q+2)+…`.
For `x = c (log n)²` this is a contradiction.

GRH is used only for the *primitive* character `χ*` mod `q` (the hypothesis
`DirichletLZerosOnLine` covers all characters, so no separate reduction lemma is needed for the
hypothesis); and RH for ζ is **not** used (the main term comes from Chebyshev, unconditionally).

---

## 1. Definitions [PROVED / compile]

`zeroOrd`, `smoothPsi`, `psiOne`, `noncoprimeSum n x = ∑_{m<x, (m,n)>1} Λ(m)`, `zeroSum`.

---

## 2. Hadamard input (unconditional, primitive `χ ≠ 1` mod `q`)

### 2.1 `summable_zeroOrd_div_normSq` [DEEP]
`∑_ρ 1/|ρ|² < ∞`.

*Proof.* `Λ(s,χ)` is entire of order 1: `|Λ(s,χ)| ≤ exp(C|s| log(q|s|))` (Stirling for `Γ_ℝ`,
`|L(s)| ≤ ζ(2)` on `Re s = 2`, functional equation, Phragmén–Lindelöf in the strip). Jensen's
formula then gives `#{ρ : |ρ| ≤ R} ≤ C' R log(qR)`, and partial summation gives
`∑ |ρ|^{-1-ε} < ∞`. (All zeros have `ρ ≠ 0`.)

*Mathlib.* `Mathlib/Analysis/Complex/JensenFormula.lean` (Jensen), `PhragmenLindelof.lean`,
`Hadamard.lean` (three lines) exist. Missing: growth bound for `completedLFunction` (needs
Stirling-type bound for `Complex.Gamma` in vertical strips — not in Mathlib), zero counting.
*Size:* ~800–1500 lines.

### 2.2 `re_logDeriv_eq_tsum` [DEEP]
For `Re s > 1`:
`Re( L'/L(s,χ) + γ_χ'/γ_χ(s) ) = -½ log q + ∑_ρ Re 1/(s-ρ)`.

*Proof.* Hadamard factorisation for the order-1 entire function `Λ(s,χ)` (`Λ(0,χ) ≠ 0`):
`Λ'/Λ(s,χ) = B(χ) + ∑_ρ (1/(s-ρ) + 1/ρ)`, absolutely convergent by 2.1.
Zeros of `Λ(·,χ̄)` are `{ρ̄} = {1-ρ}` and `B(χ̄) = conj B(χ)`. Logarithmic derivative of the
functional equation: `-Λ'/Λ(1-s,χ) = log q + Λ'/Λ(s,χ̄)`. Substituting the partial fractions and
using `1/(s-(1-ρ)) = -1/(1-s-ρ)`:
`-B(χ) - B(χ̄) - log q = ∑_ρ (1/ρ + 1/ρ̄) = 2 ∑_ρ Re(1/ρ)`,
so `Re B(χ) = -½ log q - ∑_ρ Re(1/ρ)` and `Re Λ'/Λ(s,χ) = -½ log q + ∑_ρ Re 1/(s-ρ)`
(the last series converges absolutely since `Re 1/(s-ρ) = (σ-β)/|s-ρ|²`).
(Cross-check with Davenport ch. 12, (17)–(18): there `ξ` contains `q^{s/2}`, whence the shift
`½ log q`.)

*Mathlib.* No Hadamard factorisation, no Weierstrass products for entire functions. The
functional equation and entireness (`differentiable_completedLFunction`) are there.
*Size:* general Hadamard for order ≤ 1: ~1500–2500 lines (the PNT+ project has partial
material; not at the pinned Mathlib commit). Given Hadamard, 2.2 is ~200 lines.

A Hadamard-free route to 2.1–2.2 exists (Borel–Carathéodory + Jensen local partial fractions
à la Titchmarsh §3.9/Davenport ch. 15–16, i.e. `L'/L(s) = ∑_{|ρ-s₀|<1} 1/(s-ρ) + O(log q|t|)`)
but it gives the identity only up to `O(·)` and cannot produce the sharp `-½ log q`; for a good
constant the global Hadamard formula is the right tool.

### 2.3 Difference form (used in §3)
`Λ'/Λ(s) - Λ'/Λ(2) = ∑_ρ (1/(s-ρ) - 1/(2-ρ))` for `s` not a zero. Immediate from Hadamard;
not stated separately in Lean (it is internal to the proof of `explicit_formula_bound`).

---

## 3. Smoothed explicit formula: `explicit_formula_bound` [DEEP]

**Statement.** `χ` primitive mod `q`, `χ ≠ 1`, `x ≥ 1`. Then

`| S(x,χ) + (L'/L)(2,χ)·(1 - 1/x) + ∑_ρ [ x^ρ/(ρ(ρ+1)) - 2/(ρ(2-ρ)) + 3/((ρ+1)(2-ρ)x) ] | ≤ log x + 4.`

(Unconditional. In fact the left side equals `|I_Γ(x)|` for the explicit function `I_Γ` below,
and `|I_Γ(x)| ≤ log x + 2`.)

**Proof.**

*Step 1 (Perron for the kernel `K(s) = 1/(s(s+1))`).* `K` is the Mellin transform of
`k(y) = (1-y)₊`: `∫₀¹ (1-y) y^{s-1} dy = 1/s - 1/(s+1)`. `k` is continuous and `K` is
integrable on `Re s = 2`, so `mellinInv_mellin_eq` gives `k(y) = (1/2πi)∫_{(2)} K(s) y^{-s} ds`.
With `y = m/x`, multiplying by `Λ(m)χ(m)` and summing (Fubini; `∑ Λ(m) m^{-2} < ∞`):

`S(x,χ) = (1/2πi) ∫_{(2)} (-L'/L)(s,χ) x^s K(s) ds`   (uses `LSeries_twist_vonMangoldt_eq`).

Write `I[g](x) := (1/2πi)∫_{(2)} g(s) x^s K(s) ds`.

*Step 2 (decomposition of `-L'/L`).* With `G = γ_χ'/γ_χ`, `-L'/L = G - Λ'/Λ`, so by 2.3

`-L'/L(s) = -L'/L(2) + (G(s) - G(2)) - ∑_ρ (1/(s-ρ) - 1/(2-ρ))`.

`G(s) = -½ log π + ½ ψ((s+a)/2)` (ψ = digamma), and from `ψ(z) - ψ(z₀) = ∑_{k≥0} (1/(k+z₀) - 1/(k+z))`:

`G(s) - G(2) = ∑_{k≥0} (1/(2-w_k) - 1/(s-w_k))`,   `w_k = -(a+2k)` (the trivial zeros).

*Step 3 (termwise inverse transforms).* All by Mellin inversion of explicit continuous functions
supported on `(0,1]` (or residues):
* `I[1](x) = 1 - 1/x`.
* For `w ∉ {0,-1}`, `Re w < 2`: `I[1/(s-w)](x) = x^w/(w(w+1)) - 1/w + 1/((w+1)x)`
  (`1/(s(s+1)(s-w))` is the Mellin transform of
  `y ↦ [-1/w + y/(w+1) + y^{-w}/(w(w+1))]·1_{y<1}`, continuous since the bracket vanishes at 1).
* `I[1/s](x) = log x - 1 + 1/x`,  `I[1/(s+1)](x) = 1 - (log x + 1)/x`.

Hence for a nontrivial zero:
`I[1/(s-ρ) - 1/(2-ρ)] = x^ρ/(ρ(ρ+1)) - 2/(ρ(2-ρ)) + 3/((ρ+1)(2-ρ)x)`
(using `-1/ρ - 1/(2-ρ) = -2/(ρ(2-ρ))`, `1/(ρ+1) + 1/(2-ρ) = 3/((ρ+1)(2-ρ))`).
Interchange of `∑_ρ` and `∫`: `|1/(s-ρ) - 1/(2-ρ)| = |s-2|/(|s-ρ||2-ρ|)`, and
`∑_ρ ∫ |s-2| |K(s)| / (|s-ρ||2-ρ|) |dt| ≪ ∑_ρ log(2+|γ|)/|ρ|² < ∞` (2.1 with exponent `1+ε`,
or simply use that `∫ dt/((1+|t|)(1+|t-γ|)) ≪ log(2+|γ|)/(1+|γ|)`).

*Step 4 (the Γ-term).* `I_Γ(x) := I[G - G(2)](x) = ∑_{k≥0} J_k`, where for `m = a+2k ≥ 2`
`J_k = -2/(m(m+2)) + 3/((m-1)(m+2)x) - x^{-m}/(m(m-1))`,
and for `k = 0`:
`a = 0`: `J_0 = 3/2 - log x - 3/(2x)`;  `a = 1`: `J_0 = -2/3 + (log x)/x + 2/(3x)`.
Using `∑_{m≥2 even} 2/(m(m+2)) = 1/2`, `∑_{m≥2 even} 3/((m-1)(m+2)) = log 2 + 1/2`,
`∑_{m≥2 even} 1/(m(m-1)) = log 2` (and the odd analogues `1/3`, `≈0.64`, `1 - log 2`), for `x ≥ 1`:
* `a = 0`: `I_Γ(x) = 1 - log x + (log 2 - 1)/x - ∑_{m even ≥2} x^{-m}/(m(m-1))`, so `|I_Γ| ≤ log x + 1`;
* `a = 1`: `I_Γ(x) = -1 + (log x)/x + c₁/x - ∑_{m odd ≥3} x^{-m}/(m(m-1))`, `c₁ = 2 - log 2 ≈ 1.307`, so `|I_Γ| ≤ 2`.
(Sanity: every `I[·](1) = 0`, and indeed all displayed expressions vanish at `x = 1`.)

*Step 5.* `S = I[-L'/L] = -L'/L(2)(1-1/x) + I_Γ - ∑_ρ I[1/(s-ρ) - 1/(2-ρ)]`. ∎

*Mathlib.* Mellin inversion `mellinInv_mellin_eq` ✔, `mellin` of power functions ✔,
`LSeries_twist_vonMangoldt_eq`, `LFunction_eq_completed_div_gammaFactor` ✔,
`Complex.digamma` exists but only with `digamma_one`, `digamma_one_half`,
`digamma_apply_add_one` — the series `ψ(z)-ψ(z₀) = ∑ (1/(k+z₀) - 1/(k+z))` is **missing**
(derivable from `GammaSeq_tendsto_Gamma` + locally uniform convergence of log-derivatives,
`Mathlib/Analysis/Calculus/LogDerivUniformlyOn.lean`). *Size:* Step 1 ~300 lines, digamma
series ~300, Steps 3–5 ~600 (Fubini/dominated convergence bookkeeping). Total ~1200–1500.

---

## 4. Numerical inputs

### 4.1 `norm_logDeriv_LFunction_two_le` [PROVED modulo 4.1a]
`|L'/L(2,χ)| ≤ ∑ Λ(n)/n² ≤ 1` for every `χ`. The comparison with the Dirichlet series is proved.

### 4.1a `tsum_vonMangoldt_term_two_le` [NUM]
`∑ Λ(n) n^{-2} ≤ 1` (true value `-ζ'/ζ(2) = 0.5699…`). Suggested proof: `Λ(n) ≤ log n`,
`log t/t²` decreasing for `t ≥ √e`, so
`∑ ≤ log 2/4 + log 3/9 + ∫₃^∞ log t/t² dt = 0.1733 + 0.1221 + (log 3 + 1)/3 = 0.995`.
(Tight; alternatively bound `∑_p log p/(p²-1)` with the first few primes explicit.) ~150 lines.
If only `≤ 3/2` is proved, everything downstream survives with `log q + 3` in 5.1 (the final
inequality 7.2 still holds for `L ≥ 9`).

### 4.2 `logDeriv_Gammaℝ`, `re_logDeriv_gammaFactor_two_nonpos` [PROVED]
`Γ_ℝ'/Γ_ℝ(s) = -½ log π + ½ ψ(s/2)` (`Re s > 0`), hence
`G(2) = -(log π + γ)/2 ≈ -0.861` (even), `(2 - log π - 2 log 2 - γ)/2 ≈ -0.554` (odd); both `≤ 0`.

---

## 5. Consequences of GRH

### 5.0 `re_eq_half_of_zeroOrd_ne_zero`, `zero_facts` [PROVED]
Under `DirichletLZerosOnLine`, `zeroOrd χ ρ ≠ 0 ⟹ Re ρ = 1/2`. Then, with `ρ = 1/2 + iγ`:
`|ρ|² = 1/4+γ²`, `|ρ+1|² = |2-ρ|² = 9/4+γ²`, `|ρ| ≤ |ρ+1| ≤ 3|ρ|`, `Re 1/(2-ρ) = (3/2)/|ρ+1|²`.

### 5.1 `zeroSum_le` [PROVED from 2.1, 2.2, 4.1, 4.2]
`T(χ) = ∑_ρ 1/|ρ(ρ+1)| ≤ log q + 2`.

*Proof.* `1/(|ρ||ρ+1|) ≤ 3/|ρ+1|² = 2 Re 1/(2-ρ)` (as `|ρ+1| ≤ 3|ρ|`). Sum and apply 2.2 at `s = 2`:
`T ≤ 2[½ log q + Re L'/L(2) + Re G(2)] ≤ log q + 2·1 + 0`.
(True numerics give `T ≤ log q + 0.04`; Bach's choice of the evaluation point optimises the
leading constant: evaluating at `s = 1/2 + √3/2 … 3/2` gives `T ≤ (2/3) log q + O(1)`.)

### 5.2 `norm_smoothPsi_le` ("Theorem A") [PROVED from 3, 5.1, 4.1]
For primitive `χ ≠ 1` mod `q`, `x ≥ 1`:
`|S(x,χ)| ≤ (√x + 5)(log q + 2) + log x + 5`.

*Proof.* By 5.0, `|x^ρ| = √x`, so each zero term in §3 is at most
`√x/|ρ(ρ+1)| + 2/|ρ(ρ+1)| + 3/(|ρ+1|² x) ≤ (√x + 5)/|ρ(ρ+1)|`. Hence the zero sum is
`≤ (√x+5) T(χ)`; add `|L'/L(2)|·|1-1/x| ≤ 1` and `log x + 4`. ∎

---

## 6. Elementary prime number inputs [all PROVED]

### 6.1 `psiOne_lower`
`ψ₁(x) ≥ ψ(x/2)/2 ≥ ((x/2 - 1) log 2 - log(x/2 + 2))/2` (`x > 0`).
(`1 - m/x ≥ 1/2` for `m ≤ x/2`; `Chebyshev.psi_ge'`.)

### 6.2 `noncoprimeSum_le`
`∑_{m<x,(m,n)>1} Λ(m) ≤ log n + (ψ(x) - θ(x)) ≤ log n + 3(log 4 + 4)√x` (`n ≥ 1`, `x ≥ 1`).
(Primes `p ∣ n` contribute `≤ ∑_{p∣n} log p ≤ log n`; non-primes contribute `≤ ψ - θ ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5}) ≤ 3ψ(√x)`,
and `ψ(y) ≤ (log 4 + 4) y`: `Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi`, `psi_le_const_mul_self`.)

### 6.3 `re_smoothPsi_primitive_lower` (reduction imprimitive → primitive)
If `χ(a) = 1` for all units `a < x` of `ℤ/n`, then
`Re S(x,χ*) ≥ ψ₁(x) - 2 ∑_{m<x,(m,n)>1} Λ(m)`.
(For `(m,n) = 1`, `χ*(m) = χ(m) = 1` by `primitiveCharacter_apply_of_isCoprime`; otherwise
`Re χ*(m) ≥ -1`.) No L-function of the imprimitive character is ever needed.

---

## 7. Assembly [all PROVED]

### 7.1 `nine_le_log_of_no_small_witness`
If no unit `a < 1024 (log n)²` has `χ(a) ≠ 1` (`χ ≠ 1`, `n > 2`), then `log n ≥ 9`.
(Some unit `u < n` has `χ(u) ≠ 1`, so `1024 log² n < n`; bootstrapping
`n > 1024 ⟹ log n > 6.93 ⟹ n > 8192 ⟹ log n ≥ 13 log 2 > 9`.)

### 7.2 `final_numeric`
For `L ≥ 9`, `x = 1024 L²`, `√x = 32L`:
`(32L+5)(L+2) + log x + 5 < ((x/2 - 1) log 2 - log(x/2+2))/2 - 2(L + 3(log 4 + 4)·32L)`.
(Using `log x ≤ 64L - 2`, `log 2 ∈ (0.6931471803, 0.6931471808)`: LHS-RHS reduces to
`145.4 L² - 1201 L - 12.4 > 0`, true for `L ≥ 8.3`.)

### 7.3 `bachBoundChar_of_GRH : DirichletLZerosOnLine → BachBoundChar 1024`
Assume no witness below `x = 1024 L²`, `L = log n`. By 7.1 `L ≥ 9`. With `q = cond χ ≤ n`:
`ψ₁(x) - 2·noncoprimeSum ≤ Re S(x,χ*) ≤ |S(x,χ*)| ≤ (32L+5)(L+2) + log x + 5`
(6.3, 5.2), and 6.1, 6.2 bound the left side from below by the RHS of 7.2. Contradiction.

### 7.4 `bachBound_of_bachBoundChar : BachBoundChar c → BachBound c`
`H < G = (ℤ/n)ˣ` proper; pick `g ∉ H`; a character `φ` of the finite abelian group `G/H` with
`φ(gH) ≠ 1` (`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`) gives a Dirichlet
character `χ = MulChar.ofUnitHom (φ ∘ mk)`, `χ ≠ 1`, trivial on `H`. A witness `a` for `χ` is a
unit not in `H`, and `(a mod n) ≤ a`.

### 7.5 `grh_implies_bach : GRHImpliesBach 1024` — composition of 7.3 and 7.4.

---

## 8. Improving the constant

Write the final inequality as `α x > √x (τ·L + β) + lower order`, `x = cL²`, i.e. roughly
`c > ((τ + β/L)/α)²`. Currently `α = (log 2)/4 ≈ 0.173`, `τ = 1`, `β = 2 + 6(log 4 + 4) ≈ 34`.

1. **Main term** (6.1): use `ψ₁(x) = (1/x)∫₀ˣ ψ` and `Chebyshev.psi_ge'` ⟹ `α = (log 2)/2`;
   or RH for ζ (available from `DirichletLZerosOnLine` at `N = 1`) + the ζ-analogue of §3 ⟹ `α = 1/2`.
2. **Proper prime powers** (6.2): `ψ - θ ≤ 1.43 √x` (Rosser–Schoenfeld-type; or from
   `Chebyshev.psi_le` applied at `√x`) instead of `16.2 √x` ⟹ `β ≈ 2·1.43 + 2`.
3. **Zero sum** (5.1): honest numerics (`T ≤ log q + 0.04`), and Bach's evaluation point
   ⟹ `τ = 2/3`.
With 1 (Chebyshev version) + 2: `c ≈ 70` with the small-`n` bootstrap of 7.1 (`log n ≥ 8`).
With 1 (RH version) + 2 + 3: `c ≈ 4–10`. Bach's `c = 2` needs his finer weight and numerical
verification for small conductors; not attempted.

Only §6 and §7.1–7.2 (elementary, ~200 lines) change for step 2 and the Chebyshev half of 1.

---

## 9. Ingredient inventory vs Mathlib (pinned commit 0df444a)

| Ingredient | Mathlib | Lean est. |
|---|---|---|
| `L(s,χ)` entire, `Λ(s,χ)`, functional equation (primitive) | ✔ `DirichletContinuation.lean` | — |
| `L(s,χ) ≠ 0` on `Re s ≥ 1`; `-L'/L = ∑ Λχ n^{-s}` | ✔ `Nonvanishing.lean`, `Dirichlet.lean` | — |
| Mellin inversion | ✔ `MellinInversion.lean` | Perron for `1/(s(s+1))`: ~300 |
| Chebyshev `ψ` bounds (explicit) | ✔ `NumberTheory/Chebyshev.lean` | — |
| Jensen formula, Borel–Carathéodory, Phragmén–Lindelöf | ✔ | — |
| Growth (order 1) of `completedLFunction`; Stirling in strips | ✘ | ~600–1000 |
| Zero counting / `∑ 1/|ρ|² < ∞` (2.1) | ✘ | ~500 |
| Hadamard factorisation, partial fractions of `Λ'/Λ` (2.2, 2.3) | ✘ | ~1500–2500 |
| digamma: series / partial fractions | ✘ (only `digamma_one`, `_one_half`, `_apply_add_one`) | ~300 |
| `Γ_ℝ'/Γ_ℝ` in terms of digamma, values at 2, 3 | proved here (4.2) | — |
| termwise integration for §3 | ✘ | ~600 |
| reduction imprimitive → primitive (6.3) | proved here | — |
| characters separate subgroups (7.4) | ✔ `FiniteAbelian/Duality.lean`; proved here | — |

Total remaining: roughly 4–6k lines of Lean, dominated by Hadamard factorisation.

---

## 10. Reuse of the GRH archive (`rh-archive/src`)

Inspected: `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedExplicitFormula.lean`,
`ZeroCountHolds.lean`, `FinsumMemLeOfSubset.lean` (`count_zeros_window`),
`Development/AutomorphicSpectrum/Proofs/GlobalProofs/Dirichlet*`, `Digamma*`.

* **`truncated_explicit_formula` cannot give `log²` even with explicit constants.** It is the
  *unsmoothed* formula `ψ₀(u,χ) = -∑_{|γ|<T} u^ρ/ρ + O(u log²(NuT)/T + log(Nu) + …)` with
  `T ≤ u`. Under GRH the zero sum is only `≪ √u log²(Nu)` (since `∑_{|γ|<T} 1/|ρ| ≍ log²`),
  giving least witness `≪ (log n)⁴`, not `(log n)²`. The `(1-m/x)` smoothing of §3 is essential,
  and the archive has no smoothed formula and no Hadamard product for `L(s,χ)` (grep for
  Hadamard finds only Hadamard-type determinant/matrix inequalities in the heights part).
* **Witness chasing.** Constants are assembled as `C₁+C₂+C₃`, `max C1 C2`, `4 + C₁ + C₂ + B`
  with e.g. `B = ∑' n, ‖LSeries.term Λ (3/2) n‖` (a non-numeral `tsum`), and bottom out in
  `∃`-statements several layers down (`digamma_log_bound_right_half_plane`,
  `logDeriv_LFunction_strip`, `ZetaWide.main`, `truncated_perron_psi`, …). Chasing is
  mechanically possible (each proof exhibits its witness as an expression in earlier witnesses)
  but (i) the statements are opaque `∃ C`, so one must re-state and re-prove every layer with
  the witness exposed, (ii) leaves are `tsum`s / compactness constants needing separate numeric
  bounds. Judged *not worth it*, especially given the previous bullet.
* **Directly reusable (constant-free) pieces:**
  - `GlobalTheory.T.dirichlet_logDeriv_reflection_formula` — exact log-derivative functional
    equation `L'/L(s,χ) = -log(N/π) - ½ψ((1-s+a)/2) - ½ψ((s+a)/2) - L'/L(1-s,χ⁻¹)`; useful for 2.2.
  - `ExplChiLeft.bound_right` proof pattern (`|L'/L(s,χ)| ≤ ∑ Λ(n) n^{-σ}`) — already
    re-implemented here as 4.1.
  - `GlobalTheory.Mem.An.ZeroCount` / `count_zeros_window` (`#{ρ : |γ - t| ≤ 1} ≤ C log(q(|t|+2))`):
    with *any* `C` this implies 2.1 (summability needs no explicit constant!). So **2.1 can be
    discharged from the archive without witness chasing**, if the archive is made a dependency.
* **Build cost.** The archive is 175k files with no `.lake` / no published olean cache found in
  the clone (README: "no independent build … has been published"). Importing even the
  `ZeroCount` cone means building a large part of it from source (allowed by the user, but
  expensive); Mathlib itself comes from the standard cache (same pinned commit). Recommended:
  defer; prove 2.1 together with Hadamard (2.2) directly, where it is a by-product.

---

## 11. Lean file map

| Blueprint | Lean name | Status |
|---|---|---|
| 2.1 | `summable_zeroOrd_div_normSq` | sorry (DEEP) |
| 2.2 | `re_logDeriv_eq_tsum` | sorry (DEEP) |
| 3 | `explicit_formula_bound` | sorry (DEEP) |
| 4.1a | `tsum_vonMangoldt_term_two_le` | sorry (NUM) |
| 4.1 | `norm_logDeriv_LFunction_two_le` | proved |
| 4.2 | `logDeriv_Gammaℝ`, `re_logDeriv_gammaFactor_two_nonpos` | proved |
| 5.0 | `re_eq_half_of_zeroOrd_ne_zero`, `zero_facts`, `summable_zeroSum` | proved |
| 5.1 | `zeroSum_le` | proved |
| 5.2 | `norm_smoothPsi_le` | proved |
| 6.1–6.3 | `psiOne_lower`, `noncoprimeSum_le`, `re_smoothPsi_primitive_lower` | proved |
| 7.1–7.5 | `nine_le_log_of_no_small_witness`, `final_numeric`, `bachBoundChar_of_GRH`, `bachBound_of_bachBoundChar`, `grh_implies_bach` | proved |
