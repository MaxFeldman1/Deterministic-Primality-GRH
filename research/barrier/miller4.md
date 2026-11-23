# miller4: the least Miller–Rabin witness under GRH, explicit, from index ≥ 4

Files: `miller4.md` (this note), `miller4_main.py` / `.out` (all constants and tables),
`miller4_check.py` / `.out` (numerical sanity checks K1–K3).
Sources: `beyond.md` §7 (Lemma M: strong liars lie in a subgroup of index ≥ 4), `../below-one/designB.md`
(kernel 6/(s+1)⁴; §7 index-h refinement), `../below-one/refereeB.md`, `../below-one/R11_BRIEF.md`,
`lean/DetPrimality/Bach/R11Defs.lean` (the Round-11 Props and their loosened constants).

## 0. Result

**Theorem M4.** Assume RH for ζ and GRH for Dirichlet L-functions. Let n ≥ N₀, H ≤ (ℤ/n)^* a subgroup of
index h ≥ 4. Then some integer 1 ≤ a < c·log²n is not in H (either gcd(a,n) > 1 or a mod n ∉ H), for

| c | 0.75 | 0.72 | 0.70 | 0.68 | 0.66 | 0.65 |
|---|---|---|---|---|---|---|
| N₀, Chebyshev c₀ = 2 | 10¹³ | 10¹⁴ | 10¹⁵ | 10¹⁷ | 10¹⁸ | 10²¹ |
| N₀, Chebyshev c₀ = 1.39 | 10¹⁰ | 10¹¹ | 10¹² | 10¹³ | 10¹⁴ | 10¹⁶ |

(all rows with the single choice λ = 1/4, x = 4X, and only the *loosened* Round-11 constants; thresholds
log N₀ ≥ 29.39, 32.03, 34.24, 36.99, 40.80, 47.87 resp. 22.65, 24.45, 25.92, 27.68, 30.27, 35.63; §6).
Moreover for every c > c∞ := 9λ/(4D₄²) the statement holds for all large n, with

    λ = 1/4:  D₄ = 0.936314,  c∞ ≤ 0.641623;      λ = 1/3:  D₄ = 1.049986,  c∞ ≤ 0.680291;
    λ = 6/25: c∞ ≤ 0.640854;   optimal λ = 0.2384: c∞ = 0.640836.

**Corollary (Miller).** Under the same hypotheses, every odd composite n ≥ N₀ has a strong-probable-prime
witness (a base a with n not an a-SPRP) a < c·log²n, for the same table; lim sup (least witness)/log²n ≤ 0.6417
with this kernel. (Lemma M of `beyond.md` §7: for odd composite n ≠ 9 the strong liars generate a subgroup of
index ≥ 4. If no a < X is a witness then every a < X is a liar, hence a unit in H.)

With λ = 1/3 (x = 3X, as in Round 11) the table stops at 0.69: (0.75, 10¹⁵), (0.72, 10¹⁷), (0.70, 10¹⁸),
(0.69, 10²⁰) for c₀ = 2 and 10¹², 10¹³, 10¹⁴, 10¹⁵ for c₀ = 1.39; 0.68 < c∞(1/3) is out of reach.

Comparison: h = 2 (one character, Round 11) has c∞ = 0.7771 and CMQR's barrier for one quadratic character is
0.7596, so every row of the table is below what any index-2 argument can give.

## 1. Literature

**Verdict.** No published statement was found of a GRH bound (least Miller–Rabin witness) ≤ (c + o(1))·log²n
with c < 1. Every source located that states a Miller bound gives Bach's 2·log²n. The bound with c = 0.66 is an
immediate corollary of a published theorem (LLS Thm 1.2) plus Lemma M, but nobody appears to have written it
down; the explicit table of Theorem M4 and the constant 0.6417 (< 0.66) are not in the literature found.
The negative finding rests on web searches and on reading the primary sources below; an exhaustive scan of
papers citing LLS was not possible (citation index rate-limited).

Read from primary sources (arXiv PDFs):

* **Lamzouri–Li–Soundararajan**, *Conditional bounds for the least quadratic non-residue and related problems*,
  Math. Comp. 84 (2015) 2391–2412; Corrigendum Math. Comp. 86 (2017) 2551–2554; arXiv:1309.3595v3 (corrected).
  - Thm 1.1(2): GRH, q ≥ 3000 not divisible by any prime below (log q)², H a proper subgroup of (ℤ/q)^*:
    some prime ℓ ≤ (log q)² is not in H.
  - Thm 1.2: "Let q be a large integer and let H be a subgroup of G = (ℤ/qℤ)^* with index h > 1. Then the least
    prime p not in H satisfies p < (α(h) + o(1))(log q)², where α(2) = 0.8, α(3) = 0.7 and in general α(h) = 0.66
    for all h > 3." (Proof, §6.3: 0.794 at h = 2, 0.66 at h = 4.) Thm 1.3: for h ≥ 4 a bound tending to ¼ as
    h → ∞. The corrigendum changed the constants of Thms 1.2, 1.3: cite v3 or the corrigendum.
  - No mention of Miller, witnesses or primality testing (other than the title of Bach's paper).
* **Carneiro–Milinovich–Quesada-Herrera–Ramos**, *Fourier optimization, the least quadratic non-residue, and
  the least prime in an arithmetic progression*, arXiv:2404.08380v2.
  - Thm 1: lim sup n_p/log²p ≤ 0.7615. Thm 6 / Cor 7: for one non-principal character of order ℓ,
    n_χ ≤ (c + o(1))log²q with c = 0.7615 (ℓ = 2), 0.6707 (3), 0.6131 (4), 0.5765 (5), → ¼; method limits
    0.7596, 0.6601, 0.6029, 0.5610.
  - Stated for a *single character of given order*, not for subgroups; no mention of Miller–Rabin.
* Schoof, *Four primality testing algorithms* (arXiv:0801.3840), Thm 1.2: the 2(log n)² Miller bound, via Bach
  for quadratic characters of conductor p and pq (index 2) and a separate argument for non-squarefree n.
* Wikipedia (Miller–Rabin), Kownacki arXiv:1608.07317, Pathak arXiv:2405.13316, Kandhil–Languasco–Moree
  arXiv:2607.14515: no improved Miller bound. A Wikipedia talk-page post (26 Sept 2026) asks whether even the
  c = 1 Miller corollary of LLS Thm 1.1 has a published source; no reply.

Not verified from a primary source: Bach, *Explicit bounds for primality testing and related problems*, Math.
Comp. 55 (1990) 355–380 (constants 2, 3, 1 + o(1) as quoted by LLS; which characters Bach's own Miller argument
uses was not checked); Bach's thesis, Bach–Sorenson, Burthe (Acta Arith. 80 (1997)), Alford–Granville–Pomerance,
Crandall–Pomerance Thm 3.5.13, Sorenson–Webster were not accessed.

What follows from the literature, precisely:

1. LLS Thm 1.2 + Lemma M ⇒ least Miller witness ≤ (0.66 + o(1))log²n (a prime not in H is a witness whether
   or not it divides n). Asymptotic only, no explicit N₀. This is the "immediate corollary".
2. CMQR's 0.6131 applies only when G/H has a character of order exactly 4 (more generally their order-ℓ
   constant for a character of order ℓ trivial on liars). In the Klein case of Lemma M (all v₂(p_i − 1) equal,
   ≥ 3 primes: only quadratic characters are guaranteed) a single character gives 0.7615. So **`beyond.md` §7's
   "least witness ≤ (0.6131 + o(1))log²n" is not justified as stated**: it would need a subgroup (multi-character)
   version of CMQR's theorem, which they do not state. The defensible asymptotic constants are 0.66 (LLS,
   published) and 0.6417 (this note, kernel 6/(s+1)⁴, all h characters).
3. Monier/Rabin's φ(n)/4 is a counting bound; the statement that the liars *generate* a subgroup of index ≥ 4
   needs Lemma M's own argument (brute force: true for all odd composite n < 6000 except n = 9).

## 2. Set-up

Notation of designB §2: Λ, A_j(y) = Σ_{m<y} Λ(m)√m·log^j(y/m), Φ_χ(y) = Σ_{m<y} Λ(m)χ(m)√m·log³(y/m),
Z_k = Σ_γ(1+γ²)^{−k/2} (zeros of ζ), S₄(χ̃) the same for L(s,χ̃) with k = 4, T(X) = Σ_{m≥X}Λ(m)(1+log m)m^{−3/2},
r_j(y) = Σ_{i≤j} C(j,i)γ_{j−i}log^i y + 0.64·j!.

G = (ℤ/n)^*, H ≤ G of index h ≥ 2, S := {χ mod n : χ|_H = 1} ≅ (G/H)^, |S| = h. **No structure of G/H is
used** (cyclic, Klein, or anything else): the argument takes all h characters of S at once. For χ ∈ S let χ̃ be
the primitive character inducing χ, of conductor q_χ | n; q_χ > 1 iff χ ≠ 1; for χ = 1, χ̃ is the trivial
character mod 1 (L-function ζ, Φ = A₃).

Parameters: 0 < λ < 1, ℓ := log(1/λ), x := X/λ, P(ℓ) := ℓ³ + 2ℓ² + (8/3)ℓ + 16/9,

    a(λ) := ∫₀^λ √u·log³(1/u) du = (2/3)λ^{3/2}P(ℓ)          (a(1) = 32/27 = K(½), a(λ) < 32/27 for λ < 1),
    D_h := (h·a(λ) − 32/27)/(h−1),
    E₁ := (h/(h−1))·2ℓ³√Z₂·λ^{5/4},
    E₂ := [hλ(3ℓ²Z₂ + 6ℓZ₃ + 6Z₄) + 6Z₄]/(h−1),
    ρ_h(x) := h[ℓ³(γ₀+1) + 3ℓ²r₁(x) + 3ℓr₂(x) + r₃(x)] + r₃(x).

For h = 2, λ = 1/3 these are designB's D, e₁, e₂, ρ*.

Inputs (exactly the Round-11 Props, RH/GRH assumed):

* (I1) `R11ZetaZ`: Z₂ ≤ 0.047, Z₄ ≤ 0.00012; hence Z₃ ≤ √(Z₂Z₄) ≤ 0.002375 (`r11Asm_Z3`).
* (I2) `R11ZetaExplicit`: |A_j(y) − j!(2/3)^{j+1}y^{3/2}| ≤ j!·Z_{j+1}·y + r_j(y), j = 1, 2, 3, y > 1,
  γ = (1.771, 0.148, 1.281, 0.0515).
* (I3) `R11ChiExplicit`: for primitive χ̃ ≠ 1 mod q, y > 1:
  Re Φ_χ̃(y) ≤ 6y·S₄(χ̃) + (log q + G₀)log³y + 3G₁log²y + 3G₂log y + G₃, G = (1.30, 9.31, 32.91, 198.31).
* (I4) `R11ZeroSumGain`: if χ̃(m) = 1 for all 1 ≤ m < X then S₄(χ̃) ≤ ¼(log q − κ + 4T(X)), κ = 12.4.
* (I5) `R11Tail c₀`: T(X) ≤ c₀(3 log X + 7)/√X, X ≥ 1 (c₀ = 2 or 1.39; Lean also has the sharper `r11TailS_sharp`).

## 3. Positivity over the character group

**Lemma M11.** For every prime power m = p^r, σ(m) := Σ_{χ∈S} χ̃(m) is a non-negative integer; σ(m) = h if
gcd(m, n) = 1 and m mod n ∈ H.

*Proof.* If p ∤ n: χ̃(m) = χ(m) for all χ ∈ S, and Σ_{χ∈S}χ(m) = h·1[m ∈ H] (orthogonality on G/H).
If p | n: write n = p^v·n′, p ∤ n′, K_p := ker(G → (ℤ/n′)^*), U := {χ ∈ S : χ|_{K_p} = 1}, a subgroup of S.
χ ∈ U iff χ factors through (ℤ/n′)^* iff p ∤ q_χ. For χ ∉ U, p | q_χ and χ̃(m) = 0. For χ ∈ U, χ̃(m) = χ(g) where
g ∈ G is any element with g ≡ p^r mod n′ (exists: G → (ℤ/n′)^* is onto; independent of the choice since χ is
trivial on K_p). So σ(m) = Σ_{χ∈U}χ(g) is a character sum of the group U evaluated at g (χ ↦ χ(g) is a
homomorphism U → ℂ^*): it is |U| or 0. ∎
(`miller4_check.py` (K1): 13386 sums for all odd composite n < 1500 with h ≤ 64 and all prime powers < 400.)

**Lemma M12 (the basic positivity inequality).** If every integer 1 ≤ a < X is a unit mod n lying in H, then
for x ≥ X

    A₃(x) + Σ_{χ∈S, χ≠1} Re Φ_χ̃(x) = Σ_{m<x} Λ(m)·σ(m)·√m·log³(x/m) ≥ h·T_<(X),   T_<(X) := Σ_{m<X} Λ(m)√m·log³(x/m).

*Proof.* The left side is real because σ(m) is; terms with X ≤ m < x are ≥ 0, terms with m < X have σ(m) = h. ∎

For h = 2 this is `r11Asm_sum_ge`. Note that only Σ_χ χ̃(m) ≥ 0 is used on [X, x); individual Re χ̃(m) may be
negative (they are, for complex χ), which is why one must sum over the whole group S and cannot use
1 + Re χ̃ ≥ 0 character by character with a gain.

## 4. Prime side for general (h, λ)

**Lemma M6 (= designB Lemma 6, independent of h, λ).** For X ≥ 45:
A₀(X) ≥ (2/3)X^{3/2} − 2√Z₂·X^{5/4} − γ₀ − 1. (Lean: `r11Asm_A0_ge`. With δ₀ := 2√0.047 the proof gives the
coefficient δ₀/2 + 2Z₂/δ₀ ≤ 2√0.047, and 1.28e^{3/2}X^{−5/4}/δ₀ < 1 for X ≥ 8.)

**Lemma M7.** For X ≥ 45, x = X/λ:

    h·T_<(X) − A₃(x) ≥ (h−1)[D_h·x^{3/2} − E₁·x^{5/4} − E₂·x] − ρ_h(x).

*Proof.* log(x/m) = ℓ + log(X/m): T_< = ℓ³A₀(X) + 3ℓ²A₁(X) + 3ℓA₂(X) + A₃(X). Insert M6, the lower bounds (I2) at X
and the upper bound (I2) for A₃(x):
main terms h·X^{3/2}[(2/3)ℓ³ + (4/3)ℓ² + (16/9)ℓ + 32/27] − (32/27)x^{3/2} = [h·a(λ) − 32/27]x^{3/2};
X^{5/4}: h·ℓ³·2√Z₂·λ^{5/4}x^{5/4}; linear: hX(3ℓ²Z₂ + 6ℓZ₃ + 6Z₄) + 6Z₄x;
the rest ≤ h[ℓ³(γ₀+1) + 3ℓ²r₁(X) + 3ℓr₂(X) + r₃(X)] + r₃(x) ≤ ρ_h(x) (r_j increasing). ∎
(`miller4_check.py` (K2): direct evaluation for 541–703 primes X ≤ 3·10⁵, h = 4, λ = 1/3 and 1/4: the bound
holds with slack ≥ 0.18·x^{5/4}, i.e. as for h = 2 most of E₁ is not needed.)

## 5. The basic inequality and the passage to c

**Lemma M8.** Assume RH, GRH; n > 2, H ≤ (ℤ/n)^* of index h ≥ 2, X ≥ 45 real with every integer 1 ≤ a < X a
unit in H; L := log n, x := X/λ. Then

    D_h√x − E₁x^{1/4} − E₂ + (3/2)κ ≤ (3/2)L + 6T(X) + L·log³x/x
                                        + [G₀log³x + 3G₁log²x + 3G₂log x + G₃ + ρ_h(x)/(h−1)]/x.        (M8)

*Proof.* By M12 and M7, (h−1)[D_hx^{3/2} − E₁x^{5/4} − E₂x] − ρ_h(x) ≤ Σ_{χ∈S∖1} Re Φ_χ̃(x). Each of the h − 1
characters χ̃ is primitive, non-principal, of conductor 1 < q_χ ≤ n, and χ̃(a) = χ(a) = 1 for 1 ≤ a < X (a is a
unit mod n in H). So (I3) and (I4) apply to each **with the same X**, and since log q_χ enters only with the
positive coefficients 3/2 and log³x/x, it may be replaced by L:

    Re Φ_χ̃(x) ≤ (3/2)x(L − κ + 4T(X)) + (L + G₀)log³x + 3G₁log²x + 3G₂log x + G₃      for each χ ∈ S∖1.

Sum over the h − 1 characters, divide by (h−1)x. ∎

Uniformity in the conductors: no relation between the q_χ is used (no conductor–discriminant formula), only
q_χ ≤ n; no lower bound on q_χ; the constants G, κ are uniform in q and in the parity. The same bound for each of
the h − 1 characters is what makes the right side of (M8) *identical* to designB's (6.1) apart from ρ; all of
the gain is on the left (D_h > D₂).

Monotonicity in h. D_h − a(λ) = (a(λ) − 32/27)/(h−1) < 0, so D_h increases to a(λ); E₁ ∝ h/(h−1), E₂ and ρ_h/(h−1) are decreasing in h. Hence **(M8) with the h = 4 constants holds for
every h ≥ 4** (provided D₄ ≥ 0 so nothing changes sign: only upper bounds E, ρ and a lower bound D are replaced).
The Lean statement can therefore be for an arbitrary subgroup of index ≥ 4 with a single set of constants.

**Lemma M9.** Let c > c∞ := 9λ/(4D₄²), α := D₄√(c/λ) − 3/2 > 0, β := E₁(c/λ)^{1/4},
Err(L) := 6c₀(3log X + 7)/√X + L·log³x/x + [G₀log³x + 3G₁log²x + 3G₂log x + G₃ + ρ₄(x)/3]/x at X = cL², x = X/λ.
If cL₀²/λ ≥ 404, cL₀² ≥ 45 and

    min_{w ≥ √L₀}(αw² − βw) + (3/2)κ − E₂ − Err(L₀) > 0,                                              (M9)

then for every n with log n ≥ L₀ and every H ≤ (ℤ/n)^* of index ≥ 4 some 1 ≤ a < c·log²n is not a unit in H.

*Proof.* As designB Lemma 9: √x = √(c/λ)·L; Err is non-increasing for x ≥ 404 > e⁶ (L·log³x/x = √(λ/c)·log³x/√x;
log^i x/x decreasing for x ≥ e³, i ≤ 3; (3log X+7)/√X decreasing). ∎

## 6. Numbers (`miller4_main.out`)

Reduced functional c∞(h, λ) = 9λ/(4D_h²):

| h | optimal λ | c∞ | λ = 1/3 | λ = 1/4 | λ = 6/25 | λ = 1/5 |
|---|---|---|---|---|---|---|
| 2 | 0.3406 | 0.776806 | 0.777134 | 0.853 | 0.878 | 1.053 |
| 3 | 0.2705 | 0.683702 | 0.702729 | 0.686481 | 0.690169 | 0.727 |
| 4 | 0.2384 | 0.640836 | 0.680290 | 0.641622 | 0.640852 | 0.651913 |
| 5 | 0.2197 | 0.615809 | 0.669471 | 0.620824 | 0.618152 | 0.618499 |
| 8 | 0.1921 | 0.578797 | 0.655936 | 0.595537 | 0.590697 | 0.579183 |
| ∞ | 0.1452 | 0.516787 | 0.638519 | 0.564155 | 0.556847 | 0.532337 |

(agrees with designB §1 item 4). λ = 1/4 loses 0.0008 against the optimum at h = 4 and keeps x = 4X, ℓ = 2 log 2.

Constants for h = 4 with the Round-11 inputs (D rounded down, E up):

| λ | ℓ | D₄ | c∞ | E₁ | E₂ |
|---|---|---|---|---|---|
| 1/3 | log 3 | 1.049986 | 0.680291 | 0.194156 | 0.083154 |
| 1/4 | 2 log 2 | 0.936314 | 0.641623 | 0.272276 | 0.097391 |
| 6/25 | log(25/6) | 0.917947 | 0.640854 | 0.282267 | 0.098873 |
| 1/5 | log 5 | 0.830828 | 0.651914 | 0.322351 | 0.103943 |

Thresholds: smallest L₀ passing (M9); N₀ = 10^⌈L₀/log 10⌉. Round-11 Props, h = 4:

| c | c₀ = 2: λ = 1/3 | λ = 1/4 | λ = 6/25 | c₀ = 1.39: λ = 1/3 | λ = 1/4 | λ = 6/25 | λ = 1/5 |
|---|---|---|---|---|---|---|---|
| 0.75 | 10¹⁵ (33.77) | 10¹³ (29.39) | 10¹³ (29.16) | 10¹² (26.14) | 10¹⁰ (22.65) | 10¹⁰ (22.42) | 10¹⁰ (22.04) |
| 0.72 | 10¹⁷ (37.54) | 10¹⁴ (32.03) | 10¹⁴ (31.77) | 10¹³ (28.67) | 10¹¹ (24.45) | 10¹¹ (24.19) | 10¹¹ (23.82) |
| 0.70 | 10¹⁸ (40.91) | 10¹⁵ (34.24) | 10¹⁵ (33.95) | 10¹⁴ (30.84) | 10¹² (25.92) | 10¹² (25.63) | 10¹¹ (25.27) |
| 0.69 | 10²⁰ (43.76) | 10¹⁶ (35.53) | 10¹⁶ (35.23) | 10¹⁵ (32.98) | 10¹² (26.76) | 10¹² (26.45) | 10¹² (26.11) |
| 0.68 | — | 10¹⁷ (36.99) | 10¹⁶ (36.66) | — | 10¹³ (27.68) | 10¹² (27.36) | 10¹² (27.23) |
| 0.67 | — | 10¹⁷ (38.65) | 10¹⁷ (38.29) | — | 10¹³ (28.72) | 10¹³ (28.37) | 10¹³ (29.51) |
| 0.66 | — | 10¹⁸ (40.80) | 10¹⁸ (40.43) | — | 10¹⁴ (30.27) | 10¹⁴ (29.94) | 10¹⁸ |
| 0.65 | — | 10²¹ (47.87) | 10²¹ (47.16) | — | 10¹⁶ (35.63) | 10¹⁶ (35.02) | — |
| 0.645 | — | 10³⁵ (79.99) | 10³¹ (70.67) | — | 10²⁷ (60.41) | 10²⁴ (53.03) | — |
| 0.642 | — | 10²²⁷⁰²⁵ | 10¹⁷⁵³² | — | 10²²⁷⁰²³ | 10¹⁷⁵²⁴ | — |

Margins in (M9) at the tabulated N₀ for λ = 1/4 (both sides ≈ 50–70): c₀ = 2: 0.13 (0.70), 0.72 (0.68),
0.19 (0.66), 0.11 (0.65); c₀ = 1.39: 0.85, 0.95, 0.71, 0.34. With the sharp designB constants and c₀ = 1.04
(reference, not in Lean): 10⁸, 10⁹, 10⁹, 10¹⁰, 10¹¹, 10¹² for c = 0.75, …, 0.65 at λ = 1/4.

Regression: the same script with h = 2, λ = 1/3 reproduces the brief's Round-11 table for c₀ = 2
(10¹², 10¹⁴, 10¹⁶, 10¹⁹, 10²¹) and c∞ = 0.77713.

Below N₀: the Corollary needs the least witness for odd composite n < N₀ separately. The least witness is ≤ 37
for all n < 3.3·10²⁴ (Sorenson–Webster, ψ₁₂ = 318665857834031151167461; bases = the first 12 primes), and
c·log²n > 37 as soon as log n > √(37/c), i.e. n > 1.2·10³ (c = 0.75) … 1.9·10³ (c = 0.65). So with the cited
computation the Corollary holds for **all** odd composite n ≥ 2000 for every c in the table (N₀ ≤ 10²¹ < 3.3·10²⁴);
that part is a literature computation, not something the Lean development has (it has n < 3000 by `decide`).
The Sorenson–Webster value is quoted from memory and was NOT checked against the paper in this session.

## 7. What the Lean development needs

Unchanged, sufficient as stated (no new analytic input): `R11ZetaZ`, `R11ZetaExplicit`, `R11ChiExplicit`,
`R11ZeroSumGain`, `R11Tail c₀` (or the proved `r11TailS_sharp`); reusable lemmas `r11Asm_Z3`, `r11Asm_A1/A2/A3`,
`r11Asm_A0_ge` (Lemma M6 does not depend on h or λ), `r11Asm_r1/r2/r3`, the real-analysis row machinery
`r11Asm_real`, `r11Asm_row` (after re-parametrisation). In particular (I3), (I4) are quantified over all
primitive χ ≠ 1 of every modulus q and all X ≥ 1, which is exactly what the h − 1 characters need.

New (all elementary/algebraic; no new analysis, no new numerics beyond log 2):

1. **Lemma M11** — positivity of Σ_{χ∈S}χ̃(p^r) including p | n. New. Statement suggestion: for a subgroup
   H ≤ (ZMod n)ˣ and a prime power m, 0 ≤ Re Σ_{χ : χ|_H = 1} χ.primitiveCharacter(m) and the imaginary part
   vanishes; = [G:H] for m a unit in H. Needs: values of `primitiveCharacter` at p | n when p ∤ conductor
   (factorisation through `ZMod n′`), surjectivity of units, orthogonality for the finite abelian group U.
   (Alternative that avoids p | n entirely: none found; dropping the terms with p | n is not allowed since their
   sign is the issue. One could instead bound them: Σ_{p|n, p^r<x} is not small uniformly, so M11 is needed.)
2. **Lemma M12** — the h-character version of `r11Asm_sum_ge` (sum of `r11Phi` over S).
3. **Lemma M7/M8 with (h, λ) = (4, 1/4)** — a new `core` in the style of `r11Asm_core`: `r11Asm_Tlt_ge` with
   log 4 in place of log 3 (needs a lower bound lo ≤ log 4, e.g. 1.38629), x = 4X (√4 = 2: with X = W⁴,
   √x = 2W², x^{1/4} = √2·W; alternatively X = W⁴/4), and the sum over h − 1 characters with monotonicity in h
   (or simply for general h with D_h ≥ D₄ etc.).
4. **Rows**: regenerate with `r11Asm_gen` for (α, β, constants) of §6.
5. **Lemma M** (`beyond.md` §7): strong liars lie in a subgroup of index ≥ 4 for odd composite n ≠ 9. New in
   Lean (the development has `exists_proper_subgroup_strongLiars`: proper only). Four cases: prime power;
   v₂(p₁−1) ≠ v₂(p₂−1); ≥ 3 primes; two primes with equal 2-adic valuation (uses a^{n−1} = 1). Only "index ≥ 4"
   is needed, not the shape of the quotient; it suffices to exhibit a character group of order ≥ 4 (or one
   character of order ≥ 4, or two distinct quadratic characters) trivial on liars.
6. Wrapper as `llsAsm_millerDet_eq_false_pointwise` with hypothesis "∀ H of index ≥ 4, ∃ a < c log²n, a ∉ H".

## 8. Caveats

* λ = 1/4 moves x from 3X to 4X; nothing in (I1)–(I5) depends on λ. The requirement x ≥ 404 holds at all
  tabulated thresholds (x₀ ≥ 2100).
* The table is for the R11 loosened constants; margins are 0.1–0.9 on quantities of size 50–70, as thin as in
  Round 11. The N₀ column c₀ = 1.39 assumes `R11Tail 1.39`; Lean's proved tail bound has a different shape
  (`r11TailS_sharp`) and the Round-11 rows obtained from it were better than c₀ = 1.39, so the true Lean table
  should be at least as good as the c₀ = 1.39 column, but that must be re-run with the actual statement.
* All numerics are 40-digit mpmath, not interval arithmetic.
* c∞ = 0.6417 is the limit of *this kernel* at h = 4, λ = 1/4; see §1 for what Fourier optimisation gives.

---
**Correction (lead, after reading Bach 1990 in full; see bach_check.md).** Bach does give constants below 2:
Theorem 1 has a leading coefficient 1 + o(1), and Table 1 (p. 377) gives explicit bounds (C₁ log m + C₂)² for
m ≥ m₀ (e.g. (1.170 log m − 6.364)² for m ≥ 10¹⁰, ≈ 0.80 log² m at m = 10¹⁰, ≈ 0.88 at 10¹²). Every row tends to
C₁² log² m with C₁ > 1, so Bach has no uniform c < 1 for all large m, nothing index-based, and no multi-character
averaging. The uniform explicit c < 1 (designB) and the index ≥ 4 Miller constants (0.70 for n ≥ ~10¹², c∞ ≈ 0.64)
are not in Bach. Note however that at moderate sizes (m ≈ 10¹⁰–10¹²) Bach's table is competitive with designB's
index-2 table.
