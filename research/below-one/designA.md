# Design A — explicit least-non-residue constant c < 1 under GRH via one-sided polynomial (Riesz/Beta) kernels

Author tag: `designA`. Scripts: `designA_main.py` (tables + certificates), `designA_weights.py` (weights),
`designA_rate.py` (independent re-verification of the stored certificates + explicit rate),
`designA_sanity.py` (numerical checks of the identities), `designA_explore.py` (weight optimisation, heuristic).
Outputs: `run_main.log`, `run_rate.log`, `run_sanity.log`, `designA_certificates.json`.

## 0. Result

**Theorem A.** Assume GRH for Dirichlet L-functions and RH for ζ. Let `N ≥ N₀(c)` and let χ ≠ 1 be a Dirichlet
character mod N. Then there is an integer `1 ≤ a < c·(log N)²` with `χ(a) ≠ 1`, for the pairs

| c    | log N₀ (mode S) | N₀ (mode S) | log N₀ (mode H) | N₀ (mode H) | weight (S / H) |
|------|-----------------|-------------|-----------------|-------------|----------------|
| 0.95 | 211             | 10^92       | 225             | 10^98       | (1−u)^6 |
| 0.90 | 331             | 10^144      | 355             | 10^155      | (1−u)^6 |
| 0.85 | 664             | 10^289      | 783             | 10^341      | (1−u)^10 / (1−u)^6 |
| 0.80 | 6340            | 10^2754     | 9400            | 10^4083     | (1−u)^10 |
| 0.79 | 83600           | 10^36308    | 95800           | 10^41606    | degree-8 polynomial `opt8` |

Mode S uses Schoenfeld's RH bound for ψ at one place (the sharp cut-off at X); mode H is self-contained
(Hadamard partial fractions + finitely many real numerics only). `N₀ = exp(log N₀)`, the powers of 10 are rounded up.

Best certified asymptotic constants `c_g` (fixed weight and majorant): 0.79199 for `(1−u)^10`, 0.78271 for `opt8`.
Limits of the weights themselves (floating point, not certified): `c∞ = 0.79042` for `(1−u)^10`, 0.77676 for `opt8`,
≈ 0.769 for degree 14 (§9).
An explicit rate (Corollary 2, §8): with `L = log N ≥ 100`,

    c(N) = 35.1299·( 0.1501490 + 3.8874/L + 0.01340·log²L / L )²      (weight (1−u)^10, λ = 0.213; → 0.79200)
    c(N) = 20.9277·( 0.1958505 + 3.3513/L + 0.01742·log²L / L )²      (weight (1−u)^6,  λ = 0.323; → 0.80274)

whenever the value is ≤ 1 (mode S): every χ ≠ 1 mod N has a non-residue `a < c(N) log²N`. E.g. the second gives
0.9134 at L = 300, 0.8374 at L = 1000; the first 0.8088 at L = 3000, 0.7973 at L = 10⁴.

**What changed relative to the assigned plan.** I was asked to use `K(s) = Γ(s+½)` "or a close relative you find
better". I use the Beta-function relatives
`K_b(s) = Γ(s+½)Γ(b+1)/Γ(s+b+3/2) = b!/((s+½)(s+3/2)⋯(s+b+½))`, i.e. `K̃(u) = √u (1−u)_+^b` (and polynomial
combinations). They are **rational**, the prime sums are **finite** (`n ≤ x`), `K_b → Γ(s+½)` after rescaling as
b → ∞, and the limit constants are as good or better: `c∞ = 0.8054, 0.7946, 0.7904` for b = 4, 6, 10 against
0.7934 for Γ (all for h = 2, optimal λ). The Γ kernel itself is discussed in §10. Every step of LLS §6 is made
explicit; the zero sum is bounded by a certified rational majorant (no zero counting, no S(t,χ)).

Notation shift: I write the kernel on the line Re s = ½ instead of Re s = 0:
`w(u) = K̃(u)/√u`, `W(s) = ∫₀^∞ w(u)u^{s−1}du = K(s−½)`, so `K(it) = W(½+it)` and
`Σ_n Λ(n)χ(n) n^{-1/2} K̃(n/x) = x^{-1/2} Σ_n Λ(n)χ(n) w(n/x)`.

## 1. Setting and parameters

* `N ≥ 3`, χ ≠ 1 a character mod N of order h ≥ 2, `L = log N`.
  Contradiction hypothesis **(H)**: `χ(a) = 1` for all integers `1 ≤ a < X`, where `X = c L²`.
  Consequences (given, proved in Lean): every prime factor of N is ≥ X; each `χ^j`, `1 ≤ j ≤ h−1`, is
  non-principal mod N, induced by a primitive `χ̃_j` mod `q_j`, `1 < q_j | N`, so `log q_j ≤ L`.
  **No lower bound on q_j is used anywhere** (uniformity in the conductor).
* Weight: `w(u) = Σ_{k=2}^{K} c_k (1−u)^k` for `0 ≤ u ≤ 1`, `w(u) = 0` for `u > 1`, with rational `c_k`,
  `w ≥ 0` on [0,1], `w(0) > 0`. (`k ≥ 2` gives `W(s) ≪ |s|^{-3}`.)
  `W(s) = Σ_k c_k k!/(s(s+1)⋯(s+k))`.
* `0 < λ < 1` rational, `x = X/λ`, `ε = 1/x`. Assume `x > λ^{-2}` and `X > e⁴`.
* Derived exact quantities: `D = 2∫₀^λ w − ∫₀¹ w > 0`; `w(λ)`; `V[a,b]` = total variation of w on [a,b];
  `V₁ = Σ|c_k|k ≥ ‖w'‖_∞`, `V₂ = Σ|c_k|k(k−1) ≥ ‖w''‖_∞`.
* `Z(σ) := −ζ'/ζ(σ) = Σ Λ(n)n^{-σ}` for σ > 1. For every character, `|L'/L(σ,χ)| ≤ Z(σ)`.
* For a function f on [0,∞): `Ψ_f(x,χ) = Σ_n Λ(n)χ(n) f(n/x)`, `Ψ_f(x) = Σ_n Λ(n) f(n/x)`.

## 2. Analytic inputs (complete list)

* **(A1) Hadamard partial fractions, primitive χ mod q > 1**, parity 𝔞 ∈ {0,1}: for all s that are not zeros,
  `½log(q/π) + ½ψ((s+𝔞)/2) + L'/L(s,χ) = B(χ) + Σ_ρ (1/(s−ρ) + 1/ρ)`, `Re B(χ) = −Σ_ρ Re(1/ρ)`,
  ρ over non-trivial zeros with multiplicity, `Σ_ρ |ρ|^{-2} < ∞`. Under GRH `ρ = ½ + iγ`.
* **(A2) Hadamard for ζ**: `1/s + 1/(s−1) − ½log π + ½ψ(s/2) + ζ'/ζ(s) = B + Σ_ρ (1/(s−ρ) + 1/ρ)`,
  `Re B = −Σ Re(1/ρ)`, and `Σ_ρ 1/ρ = 1 + γ₀/2 − ½log 4π = 0.0230957…` (γ₀ = Euler's constant). Under RH,
  `S₂ := Σ_ρ |ρ|^{-2} = 2Σ_ρ Re(1/ρ) = 2 + γ₀ − log 4π = 0.0461914…`.
* **(A3) Mellin inversion for truncated powers**: for `0 < β`, `m ≥ 1`, `y > 0`:
  `(1/2πi)∫_{(2)} β^{m+s} m!/(s(s+1)⋯(s+m)) y^{-s} ds = (β−y)_+^m`.
  (m = 1 is the kernel `1/(s(s+1))` already in Lean; general m is the same residue computation, or induction.)
* **(A4) Termwise integration** of the zero series in (A1)/(A2) against `F(s)x^s` on Re s = 2 for
  `F(s) ≪ |s|^{-2}` (available in Lean for `1/(s(s+1))`; on paper: `Σ_ρ |1/(s−ρ) − 1/(σ₀−ρ)| ≪ log²(|s|+2)` on
  Re s = 2 by `N(T+1) − N(T) ≪ log q(T+2)`, then dominated convergence).
* **(A5) Digamma series** `ψ(z) − ψ(z₀) = Σ_{k≥0} (1/(k+z₀) − 1/(k+z))`.
* **(N) Numerics**: upper bounds for `Z(σ)` at σ ∈ {17/16, 9/8, 5/4, 3/2, 2, 5/2, 3, 7/2, 9/2, 11/2, 13/2}, values
  of ψ at the 22 real points `(½ + w_j + 𝔞)/2`, `log π`, γ₀, `log 4π`. (For σ close to 1 the cheap bound
  `Z(σ) < 1/(σ−1)` loses only 3–4% of that term.)
* **(P) Polynomial certificates**: a Sturm-sequence (or SOS) proof that an explicit rational polynomial has no
  root in [0,∞) — one of degree ≤ 2m+K−1 ≤ 31 per row of the table, plus two small ones.
* **(S) optional**: Schoenfeld 1976, Thm 10: under RH `|ψ(y) − y| < √y log²y/(8π)` for `y ≥ 73.2`.
  Mode **H** of the scripts replaces (S) by Lemma 3′ below (self-contained from (A2)–(A4)); mode **S** uses it.

Nothing else: no Stirling, no Γ on vertical lines, no zero counting, no S(t,χ), no Beurling–Selberg.

## 3. Lemma 1 (orthogonality and the sharp cut-off)

Assume (H). Then, for every weight as in §1,

    2 Σ_{n<λx} Λ(n) w(n/x) − Ψ_w(x)  ≤  max_{1≤j≤h−1} Re Ψ_w(x, χ̃_j)  +  V[λ,1]·L.            (1.1)

*Proof.* For every n, `Σ_{j=0}^{h−1} χ^j(n)` equals h if χ(n) = 1 and 0 otherwise; it equals h for every
prime power n < X by (H). As `w ≥ 0`: `h Σ_{n<X} Λ(n)w(n/x) ≤ Σ_j Σ_n Λ(n)χ^j(n)w(n/x)` (the right side is real).
For j = 0: `Σ Λ(n)χ₀(n)w(n/x) ≤ Ψ_w(x)`. For j ≥ 1: `χ^j(n) = χ̃_j(n)` unless `(n,N) > 1`, and
`|Σ_{(n,N)>1} Λ(n)χ̃_j(n)w(n/x)| ≤ Σ_{p | N} log p Σ_{k≥1} w(p^k/x)`. Every `p | N` is ≥ X = λx, and
`p² ≥ λ²x² > x`, so only k = 1 and `λ ≤ p/x < 1` contribute, where `w ≤ sup_{[λ,1]} w ≤ V[λ,1]` (w(1) = 0);
`Σ_{p|N} log p ≤ L`. Hence

    h Σ_{n<λx} Λw − Ψ_w(x) ≤ Σ_{j=1}^{h−1} [Re Ψ_w(x,χ̃_j) + V[λ,1] L].

Write the left side as `(h−1) Σ_{n<λx} Λw − Σ_{λx≤n≤x} Λw`, divide by h−1 and use
`Σ_{λx≤n≤x} Λw ≥ 0`: the left side becomes ≥ `Σ_{n<λx} − Σ_{λx≤n≤x} = 2Σ_{n<λx} − Ψ_w(x)`. ∎

So **h = 2 is the worst case and everything below is for a single primitive character**.

## 4. Lemma 2 (explicit formula in Hadamard form)

Class 𝔉: finite combinations `f(u) = Σ_i Σ_{m≥1} d_{i,m} (β_i − u)_+^m`, `0 < β_i ≤ 1` (continuous, piecewise
polynomial, supported in [0,1]); `F(s) = Σ_{i,m} d_{i,m} β_i^{m+s} m!/(s(s+1)⋯(s+m))`.
Let `x > 1`, `ε = 1/x < min β_i`, `σ₀ > 1`, and `J_c = ∫₁^x t^{−c−1} f(t/x) dt` (c ≥ 0).

**(a) primitive χ mod q > 1, parity 𝔞**, `c_k = 2k + 𝔞`:

    Ψ_f(x,χ) = −f(ε) L'/L(σ₀,χ) + Σ_{k≥0} [ f(ε)/(c_k+σ₀) − J_{c_k} ]
               − Σ_ρ F(ρ)x^ρ + f(ε) Σ_ρ [1/ρ + 1/(σ₀−ρ)] − Σ_ρ (x^ρ/ρ) ∫₀^ε u^ρ f'(u) du.            (2.1)

**(b) ζ**:

    Ψ_f(x) = x∫_ε^1 f + f(ε)[Z(σ₀) − 1/(σ₀−1)] + Σ_{k≥1} [ f(ε)/(2k+σ₀) − J_{2k} ]
             − Σ_ρ F(ρ)x^ρ + f(ε) Σ_ρ [1/ρ + 1/(σ₀−ρ)] − Σ_ρ (x^ρ/ρ) ∫₀^ε u^ρ f'(u) du.              (2.2)

All three zero sums converge absolutely.

*Proof.* By (A3), `f(y) = (1/2πi)∫_{(2)} F(s) y^{-s} ds`, so for any Dirichlet series / Mellin transform
`G(s) = ∫₁^∞ t^{-s} dμ(t)` absolutely convergent on Re s = 2, `M[G] := (1/2πi)∫_{(2)} G(s)F(s)x^s ds = ∫ f(t/x)dμ(t)`.
In particular `M[−L'/L] = Ψ_f(x,χ)`, `M[1] = f(ε)`, and, since `1/(s+c) = ∫₁^∞ t^{-s} t^{-c-1} dt`,
`M[1/(s+c)] = J_c` (c ≥ 0), `M[1/(s−1)] = ∫₁^x f(t/x)dt = x∫_ε^1 f`, `M[1/(s−ρ)] = ∫₁^x t^{ρ−1} f(t/x) dt = x^ρ ∫_ε^1 u^{ρ−1} f(u) du`.
Subtracting (A1) at s and at σ₀ and using (A5):

    −L'/L(s,χ) = −L'/L(σ₀,χ) + Σ_{k≥0} [1/(c_k+σ₀) − 1/(s+c_k)] − Σ_ρ [1/(s−ρ) − 1/(σ₀−ρ)].

Apply M termwise. (Justification: `F(s) ≪ |s|^{-2}` on Re s = 2; the k-series converges absolutely with
`Σ_k |s−σ₀|/((c_k+σ₀)|s+c_k|) ≪ log(|s|+2)`; the ρ-series is (A4).) This gives:

    Ψ_f(x,χ) = −f(ε)L'/L(σ₀,χ) + Σ_k [f(ε)/(c_k+σ₀) − J_{c_k}] − Σ_ρ [ x^ρ∫_ε^1 u^{ρ−1}f − f(ε)/(σ₀−ρ) ].

Now `∫_ε^1 u^{ρ−1} f = F(ρ) − ∫₀^ε u^{ρ−1} f` and, f being a polynomial on [0,ε],
`∫₀^ε u^{ρ−1} f = ε^ρ f(ε)/ρ − (1/ρ)∫₀^ε u^ρ f'`; as `x^ρ ε^ρ = 1` this gives (2.1). Absolute convergence:
`|F(ρ)| ≪ |ρ|^{-2}`; `1/ρ + 1/(σ₀−ρ) = σ₀/(ρ(σ₀−ρ))`; and one more integration by parts gives

    | (x^ρ/ρ) ∫₀^ε u^ρ f' | ≤ ( ‖f'‖_{[0,ε]}/x + 0.4 ‖f''‖_{[0,ε]}/x² ) / |ρ(ρ+1)|      (Re ρ = ½).          (2.3)

For ζ, (A2) has the two extra terms `[1/(s−1) − 1/(σ₀−1)] + [1/s − 1/σ₀]`; `M[1/s] = J₀` cancels the k = 0 term
of the digamma series exactly, which gives (2.2). ∎

*Numerical check* (`designA_sanity.py`): (2.2) with f = (1−u)³, σ₀ = 2, 800 pairs of zeros, x = 30.5 and 200.3:
both sides agree to 3.2·10⁻³, which is the size (and sign) of the truncated tail `f(ε)Σ_{|γ|>T}[1/ρ + 1/(2−ρ)]`.

## 5. Lemma 3 (ζ side, RH) and Lemma 3′ (ψ from below, self-contained)

Let `κ_m = m!/∏_{j=2}^m (j+½)` (κ₁ = 1, κ₂ = 0.8, κ₃ = 0.686, …) and `κ(f) = Σ_{i,m} |d_{i,m}| β_i^{m+½} κ_m`.

**Lemma 3.** Under RH, for f ∈ 𝔉, `x ≥ 10`, `ε < min β_i`:

    | Ψ_f(x) − x∫₀¹ f | ≤ S₂ κ(f) √x + C(f,x),
    C(f,x) = 1.84 ‖f‖_∞ + |P_f(x)| + S₂( ‖f'‖_{[0,ε]} + 0.4‖f''‖_{[0,ε]}/x )/x,

where `P_f(x) = Σ_{k≥1} ( f(ε)/(2k) − J_{2k} )` satisfies `|P_f| ≤ ‖f'‖_∞ (log 2)/x + ‖f‖_∞/(2(x²−1))`, and also
`|P_f| ≤ ‖f‖_∞/(y₁² − 1)` if f is constant on `[0, y₁/x]`, `y₁ > 1`.

*Proof.* (2.2) with σ₀ = 2. `|ρ(ρ+1)⋯(ρ+m)| ≥ |ρ(ρ+1)| ∏_{j=2}^m (j+½)` and `|ρ(ρ+1)| ≥ |ρ|²`, so
`Σ_ρ |F(ρ)x^ρ| ≤ S₂ κ(f) √x`. `x∫₀^ε |f| ≤ ‖f‖_∞`. The terms with f(ε):
`Z(2) − 1 + Σ_{k≥1}(1/(2k+2) − 1/(2k)) + Σ_ρ[1/ρ + 1/(2−ρ)] = −0.43004 − 0.5 + (0.02310 + 0.06907) = −0.8379`
(`Σ_ρ 1/(2−ρ) = ξ'/ξ(2) = 3/2 − ½log π + ½ψ(1) − Z(2)`), absolute value ≤ 0.84. `P_f`:
`f(ε)/c − J_c = ∫₁^x t^{−c−1}(f(ε) − f(t/x))dt + f(ε)x^{−c}/c`, `Σ_{k≥1} t^{−2k−1} = 1/(t(t²−1))`,
`|f(ε) − f(t/x)| ≤ ‖f'‖_∞ (t−1)/x`, `∫₁^∞ dt/(t(t+1)) = log 2`, `Σ_{k≥1} x^{−2k}/(2k) ≤ 1/(2(x²−1))`. Last term: (2.3). ∎

(The scripts use the cruder `C ≤ 2.03‖f‖_∞ + ‖f‖_∞/((βx)²−1) + (V₁(log x + 0.05) + 0.02V₂/x)/x`.)

**Lemma 3′.** Under RH, for `y ≥ 10`: `ψ(y⁻) := Σ_{n<y} Λ(n) ≥ y − E_H(y)`, `E_H(y) = 2√S₂ · y^{3/4} + 2.1 ≤ 0.4299 y^{3/4} + 2.1`.

*Proof.* Take x = y (β = 1), `δ = 2√S₂ y^{−1/4} < 1` and the trapezoid `f(u) = ((1−u)_+ − (1−δ−u)_+)/δ ∈ 𝔉`.
`0 ≤ f ≤ 1_{[0,1)}`, so `ψ(y⁻) ≥ Ψ_f(y)`. `∫f = 1 − δ/2`, `κ(f) ≤ 2/δ`, f ≡ 1 on `[0, 1−δ]` and `y(1−δ) ≥ 5`, so by
Lemma 3: `Ψ_f(y) ≥ y − δy/2 − 2S₂√y/δ − (1.84 + 1/24) ≥ y − 2√S₂ y^{3/4} − 2.1`. ∎

**Lemma 3″ (principal side).** With `E₀(y)` such that `ψ(y⁻) ≥ y − E₀(y)` (mode S: `max(74, √y log²y/(8π))`;
mode H: `E_H`), and `f_λ(u) = (w(u) − w(λ))·1_{u≤λ} = Σ_{m≥1} d_m (λ−u)_+^m`, `d_m = (−1)^m w^{(m)}(λ)/m!`:

    2 Σ_{n<λx} Λ(n)w(n/x) − Ψ_w(x) ≥ xD − 2w(λ)E₀(λx) − 2[S₂κ(f_λ)√x + C(f_λ,x)] − [S₂κ(w)√x + C(w,x)].     (3.1)

*Proof.* `Σ_{n<λx} Λ(n)w(n/x) = w(λ)ψ((λx)⁻) + Ψ_{f_λ}(x)`; apply Lemma 3 to `f_λ` (lower bound) and to w (upper
bound); `∫₀^λ (w − w(λ)) + λw(λ) = ∫₀^λ w`. (`κ(w) = Σ|c_k|κ_k`, `κ(f_λ) = √λ Σ|d_m|λ^m κ_m`, `‖f_λ‖_∞ ≤ V[0,λ]`.) ∎

Remark (sharp cut-off). The term `2w(λ)E₀(λx)` is the only place where a discontinuity is met, and it is
intrinsic to the LLS argument. It carries the small factor `w(λ) ≈ 0.09–0.10`.

## 6. Lemma 4 (non-principal side, GRH)

For primitive χ mod q > 1 put `T_χ(v) := Σ_γ v/(v²+γ²)` (v > 0). By (A1) and GRH,

    T_χ(v) = Re ξ'/ξ(½+v, χ) = ½ log(q/π) + ½ ψ((½+v+𝔞)/2) + Re L'/L(½+v, χ),                          (4.1)

so `|T_χ(v) − ½log(q/π) − ½ψ((½+v+𝔞)/2)| ≤ Z(½+v)` for `v > ½`; write
`T̄(v) = ½ log q + τ(v)`, `τ(v) = max(0, −½log π + max_𝔞 ½ψ((½+v+𝔞)/2) + Z(½+v))`, so `T_χ(v) ≤ T̄(v)`.

**Lemma 4.** Under GRH, for w as in §1, `x ≥ 10`, any `v₁ > ½` (the scripts take the best of `v₁ ∈ {5/8, 3/4, 1}`), σ₀ = 3/2:

    Re Ψ_w(x,χ) ≤ √x Σ_γ |W(½+iγ)| + R(x,q),
    R(x,q) = w(ε)[ Z(3/2) + 2/3 + 1/(x−1) + 2v₁T̄(v₁) + T̄(1) ] + V₁ (log x)/x + ((V₁ + 0.4V₂/x)/x)·4v₁T̄(v₁),

and `w(ε) ≤ w(0) + V₁/x`.

*Proof.* (2.1) with f = w, σ₀ = 3/2, real parts.
(i) `−Re L'/L(3/2,χ) ≤ Z(3/2)`, and `w(ε) ≥ 0`.
(ii) Digamma sum: for `c_k > 0`, `w(ε)/(c_k+σ₀) − J_{c_k} = w(ε)[1/(c_k+σ₀) − 1/c_k] + [w(ε)/c_k − J_{c_k}]`; the first
bracket is ≤ 0. `Σ_{c_k>0} t^{−c_k−1} ≤ 1/(t²−1)` for both parities, `|w(ε) − w(t/x)| ≤ V₁(t−1)/x`, hence
`Σ_{c_k>0}[w(ε)/c_k − J_{c_k}] ≤ (V₁/x)∫₁^x dt/(t+1) + w(ε)Σ_{c≥1} x^{−c}/c ≤ V₁ log x/x + w(ε)/(x−1)`.
For 𝔞 = 0 the k = 0 term is `w(ε)/σ₀ − J₀ ≤ w(ε)/σ₀` since `J₀ ≥ 0` (w ≥ 0).
(iii) `−Re Σ_ρ W(ρ)x^ρ ≤ √x Σ_γ |W(½+iγ)|`.
(iv) `Re Σ_ρ [1/ρ + 1/(σ₀−ρ)] = Σ_γ ½/(¼+γ²) + T_χ(1)`, and for `v₁ ≥ ½`: `1/(¼+γ²) ≤ 4v₁·v₁/(v₁²+γ²)` (the
ratio `(v₁²+γ²)/(v₁(¼+γ²))` is maximal at γ = 0), so `Σ_γ 1/(¼+γ²) ≤ 4v₁T_χ(v₁)`.
(v) (2.3) with `1/|ρ(ρ+1)| ≤ 1/(¼+γ²)`. ∎

This is the "pole at s = −½" term of LLS (their `r·ξ'/ξ(0)x^{-1/2}`), of true size ≈ `w(0) log q`; we lose a
factor `v₁ + ½ ≈ 1.1–1.5` on it because we refuse to evaluate anything at σ ≤ 1.

## 7. Lemma 5 (the crux: zero sum via a certified rational majorant)

Let `v_j > ½` and `a_j ∈ ℚ` (j = 1..m) and `g(t) = Σ_j a_j v_j/(v_j² + t²)`. Suppose

    g(t) ≥ |W(½+it)|   for all real t.                                                             (5.1)

Then for every primitive χ mod q > 1, under GRH,

    Σ_γ |W(½+iγ)| ≤ Σ_γ g(γ) = Σ_j a_j T_χ(v_j) ≤ Ī_g · log q + A_g,                              (5.2)
    Ī_g = ½ Σ_j a_j = (1/2π)∫g,
    A_g = max(0, −½log π Σ_j a_j + max_{𝔞∈{0,1}} Σ_j a_j·½ψ((½+v_j+𝔞)/2) + Σ_j |a_j| Z(½+v_j) ).

*Proof.* (4.1): for `a_j > 0` use `Re L'/L ≤ Z`, for `a_j < 0` use `Re L'/L ≥ −Z`. The sum over γ is with
multiplicity on both sides. `Ī_g > 0` because g ≥ |W| ≥ 0, g ≢ 0; this is what allows `log q ≤ L` later. ∎

**Certificate for (5.1).** With τ = t²: `|W(½+it)|² = 𝒩(τ)/𝒟(τ)`, `𝒟(τ) = ∏_{j=0}^{K}((j+½)²+τ)`,
`𝒩(τ) = |Σ_k c_k k! ∏_{j=k+1}^{K}(½+j+it)|²` (a polynomial in τ with rational coefficients, degree K−2);
`g = G_n(τ)/G_d(τ)`, `G_d = ∏_j (v_j²+τ)`, `G_n = Σ_j a_j v_j ∏_{i≠j}(v_i²+τ)`. (5.1) is equivalent to

    G_n(τ) > 0   and   Q(τ) := G_n(τ)² 𝒟(τ) − 𝒩(τ) G_d(τ)² ≥ 0    for all τ ≥ 0.

Both are verified **exactly** by Sturm root counting over ℚ (`Poly.count_roots(0, ∞) == 0`, positive value at 0
and positive leading coefficient); `designA_rate.py` re-verifies the stored certificates. The `a_j` come from a
linear programme (minimise `Ī_g L + A_g` subject to (5.1) on a grid), are inflated by `1+η` (η = 2·10⁻⁵ … 2·10⁻³)
and rounded to denominators 10⁹; the LP is only a heuristic search, the certificate is the proof.

`ε_g := Ī_g/I − 1`, `I = (1/2π)∫|W(½+it)|dt`, is the "inflation"; `A_g` is the constant. Only widths `v_j > ½`
(σ_j = ½+v_j > 1) are used, so only absolutely convergent Dirichlet series appear. As σ_min ↓ 1 one gets ε_g → 0
at the price `A_g ≈ a/(σ_min − 1)`; balancing gives a total relative error ≍ (log q)^{-1/2}.

## 8. Theorem 1 (assembly) and the tables

**Theorem 1.** Assume GRH and RH. Fix a weight (§1), λ, a certified majorant g (Lemma 5) and c > 0. For L > 0 put
`x = cL²/λ` and

    F(L) = xD − 2w(λ)E₀(λx) − 2[S₂κ(f_λ)√x + C(f_λ,x)] − [S₂κ(w)√x + C(w,x)]
           − √x (Ī_g L + A_g) − R(x, e^L) − V[λ,1]·L.

If `F(L₀) > 0` and `cL₀² > max(e⁴, 100)`, then `F(L) > 0` for all `L ≥ L₀`, and for every `N ≥ e^{L₀}` and every
character χ ≠ 1 mod N there is an integer `1 ≤ a < c log²N` with `χ(a) ≠ 1`.

*Proof.* Suppose (H) with `X = c log²N`, L = log N ≥ L₀. Lemma 1, (3.1), Lemma 4, Lemma 5 and `log q_j ≤ L`
(all coefficients of log q are ≥ 0) give `F(L) ≤ 0`. Monotonicity: `F(L)/L² = (c/λ)D − Σ(terms)`, and each
subtracted term divided by L² is non-increasing in L for `X = cL² > e⁴`: `E₀(λx)/L²` (both modes; `√y log²y/y`
decreases for y > e⁴), `√x/L²`, `C(·,x)/L²`, `√x(Ī_g L + A_g)/L² = √(c/λ)(Ī_g + A_g/L)` (A_g ≥ 0),
`R/L²` (R is `α L + β +` decreasing terms with α, β ≥ 0), `V L/L²`. ∎

Leading behaviour: `F > 0` ⇔ `√(c/λ)·D > Ī_g + (A_g + o(1))/L`, so the constant attached to (weight, g) is
`c_g = λ Ī_g²/D² = c∞(w)(1+ε_g)²`, `c∞(w) = λI²/D²` (the LLS functional for h = 2:
`D = 2∫₀^λ K̃(u)u^{-1/2}du − K(½)`).

### Tables (output of `designA_main.py`; `log N₀` rounded up to 3 digits; h = 2, hence all h)

```
====================================================================================================
Weights
  riesz4: K=4 lam=87/200 D=0.1769695603 w(0)=1.0 w(lam)=0.1019046 monotone=True V[0,lam]=0.8980954 V[lam,1]=0.1019046 I=(1/2pi)int|W|=0.2408091066  c_inf(w)=lam I^2/D^2=0.80544878
     coefficients c_k: {4: '1'}
  riesz6: K=6 lam=323/1000 D=0.1242340145 w(0)=1.0 w(lam)=0.096279098 monotone=True V[0,lam]=0.9037209 V[lam,1]=0.096279098 I=(1/2pi)int|W|=0.1948521716  c_inf(w)=lam I^2/D^2=0.79456967
     coefficients c_k: {6: '1'}
  riesz10: K=10 lam=213/1000 D=0.07786663532 w(0)=1.0 w(lam)=0.091148038 monotone=True V[0,lam]=0.90885196 V[lam,1]=0.091148038 I=(1/2pi)int|W|=0.1499999886  c_inf(w)=lam I^2/D^2=0.7904224
     coefficients c_k: {10: '1'}
  opt4: K=4 lam=227/500 D=0.1773172582 w(0)=1.0 w(lam)=0.097705884 monotone=True V[0,lam]=0.90229412 V[lam,1]=0.097705884 I=(1/2pi)int|W|=0.2351637612  c_inf(w)=lam I^2/D^2=0.79853625
     coefficients c_k: {2: '47259/200000', 3: '-68693/125000', 4: '1313249/1000000'}
  opt6: K=6 lam=109/250 D=0.1491171128 w(0)=1.0 w(lam)=0.0855314 monotone=True V[0,lam]=0.9144686 V[lam,1]=0.0855314 I=(1/2pi)int|W|=0.2003968278  c_inf(w)=lam I^2/D^2=0.78743226
     coefficients c_k: {2: '286157/1000000', 3: '-320649/200000', 4: '5712813/1000000', 5: '-3750061/500000', 6: '4104397/1000000'}
  opt8: K=8 lam=433/1000 D=0.1295998903 w(0)=1.0 w(lam)=0.074927983 monotone=True V[0,lam]=0.92507202 V[lam,1]=0.074927983 I=(1/2pi)int|W|=0.1735823178  c_inf(w)=lam I^2/D^2=0.7767649
     coefficients c_k: {2: '59349/200000', 3: '-3334339/1000000', 4: '10892643/500000', 5: '-17414991/250000', 6: '15112339/125000', 7: '-105702417/1000000', 8: '36715977/1000000'}
====================================================================================================
====================================================================================================
psi lower bound mode: S (S = Schoenfeld, H = self-contained Hadamard/trapezoid)
(c, N0) table: for each c the best weight; L0 = log N0
  c=0.95  weight=riesz6     log N0=     211.0  log10 N0=  91.6361   c_g=0.8223337 eps=0.01732 A=1.81395 (1/2)sum a=0.198227221
  c=0.95  weight=riesz10    log N0=     216.0  log10 N0=  93.8076   c_g=0.8213312 eps=0.01936 A=1.44261 (1/2)sum a=0.152904674
  c=0.95  weight=riesz4     log N0=     221.0  log10 N0=  95.9791   c_g=0.8301887 eps=0.01524 A=2.18631 (1/2)sum a=0.244479445
  c=0.95  weight=opt4       log N0=     225.0  log10 N0=  97.7163   c_g=0.8211201 eps=0.01404 A=2.4365 (1/2)sum a=0.23846598
  c=0.95  weight=opt6       log N0=     281.0  log10 N0=  122.037   c_g=0.822223 eps=0.02185 A=2.31397 (1/2)sum a=0.204776002
  c=0.95  weight=opt8       log N0=     882.0  log10 N0=  383.048   c_g=0.8097199 eps=0.02099 A=2.95055 (1/2)sum a=0.177226265
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.01099', 'zeta_smooth': '0.001736', 'zeros_main': '0.9304', 'zeros_A': '0.04035', 'lower': '0.01529', 'imprim': '0.001249'}
  c=0.9  weight=riesz6     log N0=     331.0  log10 N0=  143.751   c_g=0.8027323 eps=0.005123 A=2.40521 (1/2)sum a=0.195850471
  c=0.9  weight=riesz10    log N0=     342.0  log10 N0=  148.529   c_g=0.8015377 eps=0.007007 A=1.96706 (1/2)sum a=0.151050995
  c=0.9  weight=riesz4     log N0=     359.0  log10 N0=  155.912   c_g=0.8126043 eps=0.004432 A=2.85756 (1/2)sum a=0.241876406
  c=0.9  weight=opt4       log N0=     366.0  log10 N0=  158.952   c_g=0.8130689 eps=0.009059 A=2.79145 (1/2)sum a=0.237294002
  c=0.9  weight=opt6       log N0=     438.0  log10 N0=  190.221   c_g=0.8047047 eps=0.01091 A=3.02353 (1/2)sum a=0.202582777
  c=0.9  weight=opt8       log N0=    1360.0  log10 N0=   590.64   c_g=0.8078285 eps=0.0198 A=3.18634 (1/2)sum a=0.177019156
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.008388', 'zeta_smooth': '0.001058', 'zeros_main': '0.9444', 'zeros_A': '0.03504', 'lower': '0.01012', 'imprim': '0.0008403'}
  c=0.85  weight=riesz10    log N0=     664.0  log10 N0=  288.372   c_g=0.796672 eps=0.003946 A=2.06722 (1/2)sum a=0.150591816
  c=0.85  weight=riesz6     log N0=     692.0  log10 N0=  300.532   c_g=0.8007359 eps=0.003873 A=2.54369 (1/2)sum a=0.195606785
  c=0.85  weight=riesz4     log N0=     847.0  log10 N0=  367.847   c_g=0.8107688 eps=0.003297 A=2.97335 (1/2)sum a=0.241603072
  c=0.85  weight=opt4       log N0=     854.0  log10 N0=  370.887   c_g=0.809883 eps=0.00708 A=2.99715 (1/2)sum a=0.236828643
  c=0.85  weight=opt6       log N0=     901.0  log10 N0=  391.299   c_g=0.7950801 eps=0.004844 A=3.9096 (1/2)sum a=0.201367642
  c=0.85  weight=opt8       log N0=    3000.0  log10 N0=  1302.88   c_g=0.7953545 eps=0.0119 A=7.44254 (1/2)sum a=0.175647134
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.005338', 'zeta_smooth': '0.0005208', 'zeros_main': '0.9681', 'zeros_A': '0.02001', 'lower': '0.005535', 'imprim': '0.0004418'}
  c=0.8  weight=riesz10    log N0=    6340.0  log10 N0=  2753.43   c_g=0.7919929 eps=0.000993 A=3.11834 (1/2)sum a=0.150148933
  c=0.8  weight=riesz6     log N0=   10800.0  log10 N0=  4690.38   c_g=0.7951392 eps=0.0003583 A=4.11711 (1/2)sum a=0.194921996
  c=0.8  weight=opt6       log N0=   11100.0  log10 N0=  4820.67   c_g=0.7950801 eps=0.004844 A=3.9096 (1/2)sum a=0.201367642
  c=0.8  weight=opt8       log N0=   17400.0  log10 N0=  7556.72   c_g=0.7879482 eps=0.007173 A=12.2404 (1/2)sum a=0.174827406
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.001046', 'zeta_smooth': '5.22e-5', 'zeros_main': '0.995', 'zeros_A': '0.003259', 'lower': '0.0006077', 'imprim': '4.916e-5'}
  c=0.79  weight=opt8       log N0=   83600.0  log10 N0=  36307.0   c_g=0.7827093 eps=0.003819 A=56.2834 (1/2)sum a=0.174245238
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.0001349', 'zeta_smooth': '0.0005811', 'zeros_main': '0.9954', 'zeros_A': '0.003846', 'lower': '5.692e-5', 'imprim': '3.79e-6'}
  c=0.78: no weight works
====================================================================================================
psi lower bound mode: H (S = Schoenfeld, H = self-contained Hadamard/trapezoid)
(c, N0) table: for each c the best weight; L0 = log N0
  c=0.95  weight=riesz6     log N0=     225.0  log10 N0=  97.7163   c_g=0.8208734 eps=0.01642 A=1.85277 (1/2)sum a=0.198051139
  c=0.95  weight=riesz10    log N0=     230.0  log10 N0=  99.8877   c_g=0.8124431 eps=0.01383 A=1.6327 (1/2)sum a=0.152075087
  c=0.95  weight=riesz4     log N0=     236.0  log10 N0=  102.493   c_g=0.8245213 eps=0.01177 A=2.37414 (1/2)sum a=0.243643531
  c=0.95  weight=opt4       log N0=     243.0  log10 N0=  105.534   c_g=0.8135461 eps=0.009355 A=2.76678 (1/2)sum a=0.237363631
  c=0.95  weight=opt6       log N0=     297.0  log10 N0=  128.985   c_g=0.8194523 eps=0.02013 A=2.41435 (1/2)sum a=0.204430687
  c=0.95  weight=opt8       log N0=     926.0  log10 N0=  402.157   c_g=0.8092193 eps=0.02068 A=3.08833 (1/2)sum a=0.177171475
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.01455', 'zeta_smooth': '0.001607', 'zeros_main': '0.9296', 'zeros_A': '0.03865', 'lower': '0.0143', 'imprim': '0.001171'}
  c=0.9  weight=riesz6     log N0=     355.0  log10 N0=  154.175   c_g=0.8024085 eps=0.004921 A=2.41327 (1/2)sum a=0.195810965
  c=0.9  weight=riesz10    log N0=     355.0  log10 N0=  154.175   c_g=0.7983808 eps=0.005022 A=1.96733 (1/2)sum a=0.150753235
  c=0.9  weight=riesz4     log N0=     389.0  log10 N0=  168.941   c_g=0.8121366 eps=0.004143 A=2.88354 (1/2)sum a=0.241806788
  c=0.9  weight=opt4       log N0=     393.0  log10 N0=  170.678   c_g=0.8121265 eps=0.008474 A=2.80724 (1/2)sum a=0.23715644
  c=0.9  weight=opt6       log N0=     456.0  log10 N0=  198.038   c_g=0.8021938 eps=0.00933 A=3.02512 (1/2)sum a=0.202266463
  c=0.9  weight=opt8       log N0=    1450.0  log10 N0=  629.727   c_g=0.8081083 eps=0.01998 A=3.24683 (1/2)sum a=0.177049813
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.01174', 'zeta_smooth': '0.0009766', 'zeros_main': '0.9442', 'zeros_A': '0.03278', 'lower': '0.009414', 'imprim': '0.0007835'}
  c=0.85  weight=riesz6     log N0=     783.0  log10 N0=  340.053   c_g=0.8007359 eps=0.003873 A=2.54369 (1/2)sum a=0.195606785
  c=0.85  weight=riesz10    log N0=     808.0  log10 N0=   350.91   c_g=0.797657 eps=0.004566 A=2.27331 (1/2)sum a=0.150684891
  c=0.85  weight=opt6       log N0=     960.0  log10 N0=  416.923   c_g=0.7979109 eps=0.006632 A=3.34161 (1/2)sum a=0.201725798
  c=0.85  weight=riesz4     log N0=     984.0  log10 N0=  427.346   c_g=0.8107688 eps=0.003297 A=2.97335 (1/2)sum a=0.241603072
  c=0.85  weight=opt4       log N0=    1010.0  log10 N0=  438.637   c_g=0.810386 eps=0.007392 A=3.01954 (1/2)sum a=0.23690218
  c=0.85  weight=opt8       log N0=    3230.0  log10 N0=  1402.77   c_g=0.7953545 eps=0.0119 A=7.44254 (1/2)sum a=0.175647134
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.008011', 'zeta_smooth': '0.0004231', 'zeros_main': '0.9706', 'zeros_A': '0.01612', 'lower': '0.004451', 'imprim': '0.0003761'}
  c=0.8  weight=riesz10    log N0=    9400.0  log10 N0=  4082.37   c_g=0.791985 eps=0.000988 A=3.12439 (1/2)sum a=0.150148188
  c=0.8  weight=opt6       log N0=   18100.0  log10 N0=  7860.73   c_g=0.7943535 eps=0.004385 A=5.2763 (1/2)sum a=0.201275613
  c=0.8  weight=opt8       log N0=   20600.0  log10 N0=  8946.47   c_g=0.7879701 eps=0.007187 A=12.1798 (1/2)sum a=0.174829842
  c=0.8  weight=riesz6     log N0=   22400.0  log10 N0=   9728.2   c_g=0.7957027 eps=0.0007127 A=4.26664 (1/2)sum a=0.194991052
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.002338', 'zeta_smooth': '3.51e-5', 'zeros_main': '0.995', 'zeros_A': '0.002203', 'lower': '0.0004097', 'imprim': '3.316e-5'}
  c=0.79  weight=opt8       log N0=   95800.0  log10 N0=  41605.4   c_g=0.7827585 eps=0.003851 A=55.245 (1/2)sum a=0.174250715
     terms of F at L0 (relative to main): {'main': '1.0', 'jump': '0.0007375', 'zeta_smooth': '0.0005071', 'zeros_main': '0.9954', 'zeros_A': '0.003294', 'lower': '4.967e-5', 'imprim': '3.308e-6'}
  c=0.78: no weight works
```

The majorants (a_j, v_j) of the best row for each c are in `designA_certificates.json` (and in `run_main.log`); e.g. for c = 0.9, mode S, weight (1−u)^6, λ = 323/1000:

    g(t) = Σ a_j v_j/(v_j²+t²),  (a_j, v_j) = (0.306814903, 5/8), (0.073165648, 3/4), (0.316475965, 3/2),
           (−0.488959884, 3), (0.176418986, 4), (0.005855637, 5), (0.001929688, 6);   Ī_g = 0.1958504715, A_g ≤ 2.4053.


### Corollary 2 (explicit rate), from `designA_rate.py`

For a fixed certificate (weight, λ, g) and `L ≥ 100`, `c_g ≤ c ≤ 1`: `F(L) > 0` as soon as
`√(c/λ)·D·L ≥ Ī_g L + A_g + B₁ + B₂ log²L`, where `B₂ = w(λ)√λ/π` (from `2w(λ)E₀(λx)/√x ≤ 2w(λ)√λ log²(L²)/(8π)`, mode S,
using c ≤ 1) and `B₁` = the value at `L = 100, c = c_g` of `(zeta_smooth + lower + imprim)/√x`, which is non-increasing in L and in c.
Hence `c(N) = (λ/D²)(Ī_g + (A_g+B₁)/L + B₂ log²L/L)²`:

```
S:0.95   weight=riesz6   deg Q=17  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=211.0  c_g=0.82233367
         rate: c(N) = 20.927699 * ( 0.198227221 + 2.74895/L + 0.017417*log(L)^2/L )^2,  L=log N >= 100.0;  grid violations: 0
         c_rate at L = 200,300,500,1000,3000,1e4,1e5,1e6: ['0.96214', '0.91659', '0.88009', '0.85231', '0.83306', '0.82584', '0.82275', '0.82238']
S:0.9    weight=riesz6   deg Q=19  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=331.0  c_g=0.80273228
         rate: c(N) = 20.927699 * ( 0.195850471 + 3.35121/L + 0.017417*log(L)^2/L )^2,  L=log N >= 100.0;  grid violations: 0
         c_rate at L = 200,300,500,1000,3000,1e4,1e5,1e6: ['0.96784', '0.91336', '0.87006', '0.83738', '0.81499', '0.8067', '0.8032', '0.80279']
S:0.85   weight=riesz10  deg Q=23  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=664.0  c_g=0.79667195
         rate: c(N) = 35.12989 * ( 0.150591816 + 2.83422/L + 0.01339*log(L)^2/L )^2,  L=log N >= 100.0;  grid violations: 0
         c_rate at L = 200,300,500,1000,3000,1e4,1e5,1e6: ['0.97555', '0.91617', '0.86917', '0.83384', '0.80975', '0.80088', '0.79716', '0.79673']
S:0.8    weight=riesz10  deg Q=25  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=6340.0  c_g=0.7919929
         rate: c(N) = 35.12989 * ( 0.150148933 + 3.88734/L + 0.01339*log(L)^2/L )^2,  L=log N >= 100.0;  grid violations: 0
         c_rate at L = 200,300,500,1000,3000,1e4,1e5,1e6: ['1.0328', '0.9513', '0.88765', '0.84046', '0.80877', '0.7973', '0.79259', '0.79206']
S:0.79   weight=opt8     deg Q=27  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=83600.0  c_g=0.78270925
         rate: c(N) = 25.779746 * ( 0.174245238 + 66.0844/L + 0.015694*log(L)^2/L )^2,  L=log N >= 100.0;  grid violations: 0
         c_rate at L = 200,300,500,1000,3000,1e4,1e5,1e6: ['6.6233', '4.0473', '2.4396', '1.4983', '0.99652', '0.84445', '0.78885', '0.78333']
H:0.95   weight=riesz6   deg Q=17  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=225.0  c_g=0.82087338
H:0.9    weight=riesz6   deg Q=17  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=355.0  c_g=0.80240846
H:0.85   weight=riesz6   deg Q=17  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=783.0  c_g=0.80073593
H:0.8    weight=riesz10  deg Q=25  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=9400.0  c_g=0.79198504
H:0.79   weight=opt8     deg Q=27  g>0:True  g>=|W|:True  F(L0)>0:True  log N0=95800.0  c_g=0.78275845
```


## 9. Choice of weight; what limits c∞

* `c∞(w) = λI²/D²` for `w = (1−u)^b`: 1.073 (b=1), 0.867 (2), 0.822 (3), **0.8054 (4)**, **0.7946 (6)**,
  **0.7904 (10)**, 0.7904 (20), 0.7915 (40); Γ kernel 0.7934. With λ = 1 (no truncation) no weight does better than
  ≈ 1.11: the truncation X = λx with λ < 1, i.e. LLS's "h∫₀^λ − K(½)", is essential, and so is the sharp cut-off.
* Optimising the polynomial (`designA_explore.py`, Nelder–Mead, heuristic): degree 4: 0.7985, degree 6: 0.7874,
  degree 8: 0.7768, degree 10: 0.7719, degree 14: ≈ 0.769. This is consistent with the CMQR barrier
  (0.7596 < C(1)^{-2} < 0.7615 for h = 2) being for a larger class (K̃ of both signs). The optimised weights are
  included in the scripts (`opt4/6/8`, coefficients rounded and then treated as exact), **but their |W(½+it)| is
  harder to majorise with σ_j ≥ 17/16** (ε_g ≈ 1–2% at moderate L), so they only win for c < 0.79:
  `opt8` gives c = 0.79 at log N₀ ≈ 8.4·10⁴. For c ≥ 0.8 the plain Riesz kernels b = 6, 10 are best.
* I did not find a way to make the certified limit go below ≈ 0.777 with degree ≤ 8.

## 10. The Γ(s+½) kernel in this framework (for comparison; not used)

Everything above applies verbatim to `w(u) = e^{-u}`, `W(s) = Γ(s)` (Lemma 2 only needs `M[t^{-s}] = w(t/x)` and
integration by parts at 0): `|W(½+iγ)| = (π/cosh πγ)^{1/2}` by the reflection formula, `D = 1 − 2e^{-λ}`,
`c∞ = 0.79342` at λ = 2.477. Differences, all for the worse from the formalisation point of view:
(i) Mellin inversion and (A4) need decay of Γ on Re s = 2; (ii) (5.1) becomes the transcendental inequality
`g(t)² cosh(πt) ≥ π`; (iii) the sums are infinite: the tail n ≥ X is handled by `K̃ ≥ 0`, but the imprimitivity
term becomes `e^{-λ}(1+o(1))·L` and the principal side needs `∫ψ(t)e^{-t/x}dt` type bounds; (iv) the jump
coefficient is `e^{-λ} = 0.084`, similar to ours. Its N₀ table would be close to that of `riesz6` (same c∞ up to
0.001; the referee's LP for Γ finds ε ≈ 0.3–0.9%, cost 5–6, comparable to our `ε_g`, `A_g/Ī_g`). There is no
reason to prefer it.

## 11. Answers to the referee's points (skeptic.md)

1. No zero counting / S(t,χ): the zero sum is (5.2), an exact identity plus `|L'/L(σ)| ≤ Z(σ)`, σ > 1.
2. Pointwise majorant with exact certificate: Lemma 5; simple poles only, σ_j ≥ 17/16. (Higher-order poles
   `Re(a+it)^{-k}` would be a straightforward extension using derivatives of (A1); not needed for the table.)
3. All O(1) terms are carried: pole at "−½" = Lemma 4 (iv) (`≈ (v₁+½) w(0) log q`); sharp cut-off = `2w(λ)E₀(λx)`;
   imprimitivity = `V[λ,1]·L`; Γ-factor terms = Lemma 4 (ii) and the ψ-values in `A_g`.
4. Uniformity in the conductor: (5.2) and Lemma 4 hold for every primitive χ mod q > 1 with constants independent
   of q and are increasing in log q, which is then bounded by log N. Small q̃ is not excluded and needs no
   separate argument.
5. LLS loose spots are not inherited: we never move a contour to the left of the zeros (Hadamard form), and the
   zero sum is only bounded from above.

## 12. Risk assessment / things to double-check

* **(Riskiest) Lemma 2/(A4) for weights with a corner** (`f_λ`, trapezoid: `F ≪ |s|^{-2}`): the termwise
  integration needs `Σ_ρ|1/(s−ρ) − 1/(σ₀−ρ)| ≪ log²|s|` on Re s = 2. Standard, and the same situation as the
  kernel `1/(s(s+1))` already formalised, but it is the one place where I rely on an un-numbered "standard" bound.
  It only affects the ζ side.
* **Certificates** are exact rational Sturm computations in sympy (not formally verified); the LP is not trusted.
  In Lean, `Q(τ) ≥ 0` on τ ≥ 0 for a degree ≤ 31 polynomial with 9-digit rational data is the heaviest new
  numerical lemma; an SOS/`polyrith`-style certificate or interval subdivision would be needed. Reducing the
  number of widths (e.g. to 4–5) costs little and lowers the degree.
* **Mode S** depends on Schoenfeld's Theorem 10 (cited, not re-derived). **Mode H** does not, at the cost shown
  in the tables (≈ 5–10% in log N₀).
* The numerics for `Z(σ)`, ψ are mpmath at 40 digits with a 10⁻¹² safety margin, not interval arithmetic.
  Sensitivity is tiny: all enter linearly with O(1) coefficients, and `log N₀` is rounded up to 3 digits.
* The optimised weights and the claimed limits 0.777 / 0.769 (§9) are floating-point optimisations; only the rows
  of the tables are certified.
* The rate `c(N) → c_g` for a fixed g is rigorous; the statement "total relative error ≍ (log N)^{-1/2} with
  optimally chosen g, hence c(N) → c∞(w)" is supported by the LP numerics, not proved.
* h > 2: only the worst case h = 2 is tabulated; Lemma 1 shows it implies all h. Better constants for h ≥ 3
  (λ re-optimised) are available from the same F with `D_h = ∫₀^λ w − (1/(h−1))∫_λ^1 w` but were not computed.

## 13. Script outputs

### run_sanity.log
```
(1) x=30.5: sum Lambda(n) f(n/x) = 5.96647703225   Hadamard-form RHS (800 zero pairs) = 5.96326382988   diff = 0.003213   (expected truncation error ~ 0.00344)
(1) x=200.3: sum Lambda(n) f(n/x) = 48.2619330891   Hadamard-form RHS (800 zero pairs) = 48.2586457644   diff = 0.003287   (expected truncation error ~ 0.00375)
(2) riesz4 t=0: |W| direct=0.8126984127 formula=0.8126984127 sqrt(NN/DD)=0.8126984127
(2) riesz4 t=0.7: |W| direct=0.399393564 formula=0.399393564 sqrt(NN/DD)=0.399393564
(2) riesz4 t=3.3: |W| direct=0.0178494391 formula=0.0178494391 sqrt(NN/DD)=0.0178494391
(2) riesz4 t=11: |W| direct=0.0001268586751 formula=0.0001268586751 sqrt(NN/DD)=0.0001268586751
(2) opt8 t=0: |W| direct=0.672066255 formula=0.672066255 sqrt(NN/DD)=0.672066255
(2) opt8 t=0.7: |W| direct=0.300964383 formula=0.300964383 sqrt(NN/DD)=0.300964383
(2) opt8 t=3.3: |W| direct=0.009549684404 formula=0.009549684404 sqrt(NN/DD)=0.009549684404
(2) opt8 t=11: |W| direct=0.0001252387349 formula=0.0001252387349 sqrt(NN/DD)=0.0001252387349
(3) w=0.625: sum over 800 zero pairs = 0.027815169  Re xi'/xi(1/2+w) = 0.028863118  (tail ~ 0.00119)
(3) w=1.0: sum over 800 zero pairs = 0.044459209  Re xi'/xi(1/2+w) = 0.046135928  (tail ~ 0.0019)
(4) sum_rho 1/|rho|^2 = 2+gamma-log(4pi) = 0.0461914179322  partial sum: 0.044514699
    Re xi'/xi(2) (zeta) = 0.06906623153   sum_rho 1/rho =  0.0230957089661   Z(2)-1 = -0.4300390069

[exited with code 0]
```

### run_main.log (complete, including all majorants)
See the file `run_main.log`; the tables in §8 are its content minus the majorant lines.

