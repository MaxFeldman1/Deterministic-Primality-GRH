# Referee report on designB.md (kernel 6/(s+1)⁴, c∞ = 0.7771)

Referee stance: adversarial. All derivations below were redone by hand; all numbers were recomputed with my own
code (`refereeB_identities.py`, `refereeB_table.py`, `refereeB_endtoend.py`; outputs in the matching `.out` files).
None of the designB scripts was imported or copied; outputs were compared only afterwards.
Numerics are 25–40 digit mpmath with outward padding, plus float64 for the end-to-end tests: evidence, not
interval arithmetic.

## 0. Verdict

**I found no mathematical error in designB.** Every lemma survives an independent derivation and an independent
numerical test. The small N₀ is real, and it comes from Lemma 4 (§6 below). What is not yet formalization-grade:

1. The table sits on thin margins (c = 0.80 at N₀ = 10¹¹ has margin 0.05 out of ≈ 17), so it depends on the exact
   Chebyshev constant and on sharp lower bounds for F₀, F₁. With weaker inputs it moves by 1–7 orders of magnitude.
2. Rounding of Z₃ is inconsistent (harmless, §2).
3. Theorem B is correct but its headline reading "c(n) ≤ c∞(1 + 0.238/√log n)²" is far from what Lemma 8 gives
   (§5); this is the source of the apparent inconsistency with the table, not an error.
4. The contour shifts of Lemmas 2 and 3 are only sketched in designB. I redid the residues and they are right.

| Lemma | Verdict | Remarks |
|---|---|---|
| §1.1 barrier (c ≥ 1 if all support is counted) | correct | needs φ(0) = 0, automatic when K ∈ L¹ of the line; design only |
| Lemma 1 (Z₂, Z₄, Z₃) | correct | Z₃ bound uses unrounded Z₄ |
| Lemma 2 (ζ explicit formula, (3.1)) | correct | verified at y = 20.5, 300.5, 3000.5, j = 1, 2, 3 |
| Lemma 3 (L explicit formula, (3.2)) | correct | verified for primitive characters mod 3, 4, 5, 7, 8 incl. complex ones |
| Lemma 4 ((4.1) identity, (4.2) hypothesis gain) | correct | direction of every inequality is the needed one |
| Lemma 5 (T(X) ≤ c₀(3 log X + 7)/√X) | correct | lossy by 30%; c₀ = 1.04 needs Rosser–Schoenfeld |
| Lemma 6 (sharp cut-off by differencing) | correct | tested for 2129 values of X ∈ [45, 10⁶] |
| Lemma 7 (prime side) | correct | same test |
| Lemma 8 (basic inequality), uniformity in q̃ | correct | log q̃ enters with positive coefficient only |
| Lemma 9, Theorem A table | correct | reproduced; thin margins |
| Corollary 10 / Theorem B | correct | very lossy for small k |
| Lemma 11, §7 (order h) | correct | not needed for Theorems A, B |

## 1. Explicit formulas (designB Lemmas 2, 3)

Redone from scratch. With Φ_χ̃(y) = 6·(1/2πi)∫_{(2)} (−L'/L)(s−½, χ̃) y^s s^{−4} ds and y > 1:

* The kernel pole is at s = 0 (order 4), i.e. at the point z = s − ½ = −½ of L'/L. L(−½, χ̃) ≠ 0 and ζ(−½) ≠ 0, so
  the pole of the kernel never collides with a zero. Residue: Σ_i C(3,i) log^i y · g^{(3−i)}(−½). Correct.
* Non-trivial zeros: s = ρ + ½ = 1 + iγ under GRH, residue −y^{1+iγ}/(1+iγ)⁴, modulus y/(1+γ²)². Correct.
* Trivial zeros z = −𝔞 − 2m, m ≥ 0: s_m = ½ − 𝔞 − 2m. For even χ̃ this includes z = 0 (s = ½), between the kernel
  pole and the line of integration; it is in the formula (term −96√y) and has the favourable sign. s_m⁴ > 0 for all
  m, so dropping the sum is legitimate in the upper bound (3.2).
* ζ: pole at s = 3/2 with residue (2/3)^{j+1} y^{3/2}; for j = 3 this is K(½)·x^{3/2} = (32/27)x^{3/2}, the full
  main term (not half: the v1-LLS error is not repeated). Trivial zeros s = ½ − 2m, m ≥ 1.
* Functional-equation expression of g_χ^{(k)}(−½): I rederived
  g(z) = log(q/π) + ½ψ((z+𝔞)/2) + ½ψ((1−z+𝔞)/2) + L'/L(1−z, χ̄); agrees with direct differentiation of −L'/L at −½
  to 24 digits for every character tested. G₀ … G₃ reproduced: 1.274645, 9.125903, 32.262139, 194.419963.
* Principal character: designB uses ζ itself (A₃(x), all prime powers), never χ₀ mod n, so no correction for
  primes dividing n is needed. Imprimitive χ: only the primitive χ̃ appears, and only through χ̃(m) = 1 for m < X
  and |χ̃(m)| ≤ 1. No imprimitivity error term exists in this proof. Correct.

Numerical verification (`refereeB_identities.out`; zeros located by sign changes of the completed L-function on
the line, |γ| < 80, counts match Riemann–von Mangoldt to within 1):

| object | check | agreement |
|---|---|---|
| ζ, Lemma 2, j = 3 | y = 20.5 / 300.5 / 3000.5, 400 zeros | 2·10⁻⁹ / 3·10⁻⁸ / 1·10⁻⁶ (inside the zero-tail allowance) |
| ζ, Lemma 2, j = 2 | same | 2·10⁻⁷ / 1·10⁻⁵ / 3·10⁻⁴ |
| ζ, Lemma 2, j = 1 | same | 2·10⁻⁴ / 2·10⁻³ / 0.23 (conditionally slow tail; the j = 1 formula is y·d/dy of the j = 2 one) |
| Z₂, Z₄ | zeros vs closed form | 0.0461359 vs 0.0461385 (tail estimate), 7.377246·10⁻⁵ both |
| all 12 primitive characters mod 3, 4, 5, 7, 8 (6 complex, orders 2, 3, 4, 6, both parities) | Lemma 3 at y = 7.5, 60.5, 400.5 | 2·10⁻⁷ – 4·10⁻⁴ absolute, always inside the zero-tail allowance (≤ 2.5·10⁻³); imaginary parts agree for complex χ |

## 2. Zero-sum identity and Lemma 4

* 1/(1+γ²)² = ½[Re(1−iγ)⁻¹ + Re(1−iγ)⁻²]: checked. Σ_ρ Re(σ−ρ)⁻¹ = Re ξ'/ξ(σ), Σ_ρ(σ−ρ)⁻² = −(ξ'/ξ)'(σ).
  So Σ_γ 6/(1+γ²)² = 3[Re ξ'/ξ(3/2) − Re(ξ'/ξ)'(3/2)]; the task statement's "½[…]" is the identity for
  Σ 1/(1+γ²)², which is what designB uses (S₄), with factor 6 applied afterwards. Signs and factor correct.
  Multiplicities are respected by the Hadamard product. GRH is used only for |y^{ρ+½}| = y and γ real.
* (4.1) verified against located zeros for all 12 characters: differences 2·10⁻¹⁰ – 2·10⁻⁸ (zero-tail estimate
  10⁻⁶; S₄ ranges from 0.00067 to 0.0209).
* Direction in (4.2). An upper bound for S₄ is needed. The series enters as −½·Re Σ Λ(n)χ̃(n)(1+log n)n^{−3/2}, and
  both weights 1 and log n are positive, so a lower bound for the series is needed. The hypothesis gives
  Re χ̃(n) = 1 for n < X, and Re χ̃(n) ≥ −1 holds for every n ≥ X whatever χ̃(n) is (complex, zero, n not coprime
  to the modulus). So the series is ≥ (F₀+F₁) − 2T(X). This is the needed direction for both the L'/L term and the
  derivative term. Order h > 2 and complex χ change nothing. For χ^j (§7): χ̃_j(a) = 1 for a < X as well. Correct.
* κ reproduced: 12.691245 (𝔞 = 1), 14.221927 (𝔞 = 0).
* Minor: Lemma 1 states Z₄ ≤ 0.000074 and Z₃ ≤ √(Z₂Z₄) ≤ 0.001845, but √(0.046136·0.000074) = 0.0018477. The stated
  0.001845 is true only with the unrounded Z₄ = 7.3772·10⁻⁵ (√ = 0.00184487). Effect on e₂: none at 4 digits.
* Sanity on real data (`refereeB_endtoend.out`, T3/T4): for Legendre characters with least non-residue 41–131
  (conductors up to 1.96·10¹¹), Lemma 3 applied to directly computed Φ_χ(y) forces S₄ ≥ 0.13 – 1.12, while (4.2)
  gives S₄ ≤ 2.1 – 4.3: consistent, ratio at most 0.37. Exact S₄ from (4.1) for q = 479, 1151, 1319, 1559, 2351 is
  0.23 – 0.46, below the (4.2) bound 1.5 – 1.9 and far below the no-hypothesis bound ≈ 4.

## 3. Barrier and overshoot

* §1.1: K(½) ≤ (1/2π)∫|K(it)|dt for φ supported on v ≤ 0. The proof pairs φ with e^{v/2}1_{v<0} − δ₀, whose
  transform (½−it)/(½+it) has modulus 1. It needs φ(0) = 0, which holds because φ is continuous when K is
  integrable on the line. Correct; rescaling shows c ≥ 1 for every λ. Design evidence only.
* Overshoot: A₃(x) + Re Φ_χ̃(x) = Σ_{m<x} Λ(m)(1 + Re χ̃(m))√m log³(x/m) ≥ 2T_<(X). Only 1 + Re χ̃(m) ≥ 0 is used on
  X ≤ m < x; true for complex values and for χ̃(m) = 0. Valid for every order h (it is the "h = 2 argument" with
  the two characters 1 and χ). For the h-character version, Lemma 11 (Σ_j χ̃_j(m) ∈ ℤ≥0, including p | n) is
  correct; D^{(h)} ≥ D holds because (2/3)λ^{3/2}P(ℓ₀) = 1.0838 < 32/27.

## 4. Sharp cut-off, Lemma 5, uniformity

* Lemma 6: A₁(X) − A₁(Xe^{−δ}) ≤ δ·A₀(X) is correct (Λ ≥ 0). The trivial-zero difference is in fact ≥ 0. The
  optimisation δ₀ = 2√Z₂ gives the stated 2√Z₂·X^{5/4}. Direct test: min over 2129 values of X ∈ [45, 10⁶]
  (X prime, the worst case for "n < X") of (A₀(X) − bound)/X^{5/4} is +0.30; for Lemma 7 the minimum of
  (2T_< − A₃(x) − bound)/x^{5/4} is +0.27. The bound is valid and loses almost all of e₁ = 0.2885: the true
  cut-off error is far smaller than x^{5/4}.
* Lemma 5: partial summation correct. Literature: Rosser–Schoenfeld 1962, Theorem 12: ψ(x) < 1.03883x for x > 0;
  c₀ = 1.04 is admissible. Measured T(X)/bound = 0.67 – 0.80: the proof discards −f(X)ψ(X⁻).
* Uniformity in q̃: (6.1) contains log q̃ only as (3/2 + log³x/x)·log q̃, bounded by the same with L. No term of
  the form log q̃/log log q̃, no lower bound on q̃ used. Correct.

## 5. Assembly, table, and the "inconsistency"

Constants reproduced: D = 0.982387, c∞ = 0.777134 (0.776806 at the optimal λ = 0.3406; designB's text says
"λ = 0.3261" in Theorem B and 0.341 in its own table: typo), e₁ = 0.288544, e₂ = 0.120212.

My thresholds (smallest L₀ passing (6.2), 3cL₀² ≥ 404, rounded up to 0.01):

| c | designB L₀ | mine, c₀ = 1.04 | N₀ | margin at N₀ | c₀ = 1.39 | c₀ = 2 | F₀+F₁ short by 0.14 | no hypothesis in Lemma 4 |
|---|---|---|---|---|---|---|---|---|
| 0.95 | 18.06 | 18.06 | 10⁸ | 0.33 | 10¹⁰ | 10¹² | 10⁹ | 10⁵⁹ |
| 0.90 | 19.67 | 19.67 | 10⁹ | 0.79 | 10¹¹ | 10¹³ | 10⁹ | 10⁸² |
| 0.85 | 21.78 | 21.78 | 10¹⁰ | 0.76 | 10¹² | 10¹⁵ | 10¹⁰ | 10¹⁴¹ |
| 0.80 | 25.23 | 25.23 | 10¹¹ | 0.05 | 10¹⁴ | 10¹⁸ | 10¹² | 10⁵³⁶ |
| 0.79 | 28.07 | 28.07 | 10¹³ | 0.69 | 10¹⁵ | 10²⁰ | 10¹³ | 10¹¹³⁴ |
| 0.78 | 98.01 | 97.17 | 10⁴³ | 0.09 | 10⁵⁰ | 10⁶³ | 10⁴⁷ | 10¹¹⁰⁵⁵ |

designB's table is confirmed as stated (for 0.78 and 0.779 my thresholds are slightly smaller: 97.17, 1615.04).
The margin is the slack in (6.2), whose two sides are ≈ 17–20; 0.05 at (0.80, 10¹¹) is 0.3%.

**Table vs rate formula.** There is no contradiction; both are upper bounds from the same inequality (6.1):
(3/2)(L + b√L-type terms) ≥ D√x − e₁x^{1/4} − e₂ + (3/2)κ − Err. Corollary 10 with k = 0 throws away the constant
(3/2)κ − e₂ − Err, which is ≈ +3 at L = 30 and tends to +19. The largest admissible k (my computation):

| L₁ | k_max | resulting bound on c at L = L₁ | k = 0 reading |
|---|---|---|---|
| 25.23 | 0.52 | 0.820 | 0.853 |
| 30 | 1.49 | 0.767 | 0.846 |
| 50 | 4.27 | 0.699 | 0.830 |
| 100 | 7.26 | 0.703 | 0.815 |
| 1000 | 11.43 | 0.771 | 0.789 |
| 10⁴ | 12.35 | 0.779 | 0.781 |

At L = 25.23 Corollary 10 still gives only 0.82 because it also replaces x^{1/4} by (3c∞)^{1/4}(√L + b/2) and
pays the b√L term in full; Lemma 9 at fixed c = 0.80 is the sharper evaluation. Consequences: (i) the sentence
"c(n) ≤ c∞(1 + 0.238/√log n)²" should be replaced by the form with k, or by Lemma 9; (ii) for 30 ≲ L ≲ 2000 the
proof gives c *below* c∞, down to ≈ 0.70 near L = 50–100. That is legitimate: the hypothesis gain is a constant
−κ against log q, so it helps most at moderate L. It does not contradict the CMQR barrier, which is asymptotic.

## 6. Why designB's N₀ is 80–135 orders below designA's (coordinator's question)

Write the final inequality of either design as √(c/c∞) − 1 ≥ K/L (+ lower order), K the constant against log q.

| | c∞ used | constant K (units of log q) | N₀ for c = 0.95 / 0.90 / 0.85 / 0.80 |
|---|---|---|---|
| designA (Beta kernel, majorant, \|L'/L(σ)\| ≤ −ζ'/ζ(σ)) | 0.80 – 0.82 (c_g incl. majorant loss) | ≈ +14 | 10⁹² / 10¹⁴⁴ / 10²⁸⁹ / 10²⁷⁵⁴ |
| designB with the same crude bound in Lemma 4 | 0.7771 | ≈ +8.75 + lower order | 10⁵⁹ / 10⁸² / 10¹⁴¹ / 10⁵³⁶ (my recomputation) |
| designB as written | 0.7771 | −12.69 + lower order | 10⁸ / 10⁹ / 10¹⁰ / 10¹¹ |

* Step 1 (kernel, 10⁹² → 10⁵⁹ etc.): exact modulus (no majorant loss), lower c∞, and no pole-at-(−½) constant,
  since the kernel pole sits at s = −1 where L'/L(−½) is multiplied by log³x/x.
* Step 2 (Lemma 4, 10⁵⁹ → 10⁸ etc.): replacing |Re L'/L(3/2) and its derivative| ≤ F₀, F₁ by the value forced by
  the hypothesis shifts K by exactly 4(F₀+F₁) = 21.44 and makes it negative. With K < 0 the leading inequality
  fails for every L, and N₀ is set only by where the O(log³x/√x) and T(X) terms become smaller than (3/2)κ ≈ 19,
  which happens at x ≈ 900–1500.

Step 2 is not an error and not double counting: the hypothesis "χ̃(n) = 1 for n < X" is a statement about the
Dirichlet coefficients, and (4.1) is an exact identity in those coefficients. I checked the identity against
located zeros, the sign of every term, and the end-to-end consistency on real characters with least non-residue
up to 131 (§2). designA is correct but leaves this gain unused; the same substitution would improve designA by a
comparable amount. **designB's small N₀ is justified**, subject to the numeric caveats below.

## 7. What must change before formalization

1. Replace 10-digit mpmath by certified bounds, in the right directions: lower bounds for F₀, F₁ (they enter κ
   with factor 2; a deficit of 0.14 from truncating at 10⁴ moves 0.95 → 10⁹ and 0.80 → 10¹²); upper bounds for
   Z₂, Z₄, γ_k, G_k; polygamma values at −¼, ¼, ¾, 5/4, 7/4.
2. Decide the Chebyshev input. ψ(t) ≤ 1.04t for all t > 0 is Rosser–Schoenfeld, not elementary. With an
   elementary constant 1.39 the table becomes 10¹⁰ / 10¹¹ / 10¹² / 10¹⁴; with 2 it is 10¹² / 10¹³ / 10¹⁵ / 10¹⁸.
   Better: keep −f(X)ψ(X⁻) in Lemma 5, or bound T(X) = F₀ + F₁ − (partial sum) with the RH lower bound for ψ₁
   already in Lean; either recovers the 30% loss.
3. Publish the table with a safety margin: (0.80, 10¹¹) has slack 0.3%. I recommend (0.80, 10¹²) or stating L₀.
4. Write out the contour shift for −L'/L(s−½)·y^s/s⁴ (order-4 pole at 0, trivial zero at s = ½ for even χ̃) and
   the termwise differentiation Σ_ρ(σ−ρ)⁻² = −(ξ'/ξ)'(σ).
5. Fix the Z₃ rounding, the λ-optimum typo, and restate Theorem B with k (or drop the k = 0 headline).
