# Skeptic's report: explicit c < 1 for the least character non-residue under GRH

Referee: adversarial. Scope: find reasons the target in `BRIEF.md` is a dead end, or confirm it is not.
Scripts: `skeptic_checks.py`, `skeptic_rational.py` (floating point, grid-checked LPs: evidence, not proof).

Sources read line by line:
* LLS v3 TeX (`lls.tex`, §6 = lines 1347–1540), plus arXiv v1 and v2 sources (downloaded, diffed against v3).
* CMQR = Carneiro–Milinovich–Quesada-Herrera–Ramos, arXiv:2404.08380v2 TeX source (`20250811_FOLQR_Revision_arxiv.tex`).
* Not accessible: the Math. Comp. corrigendum itself (AMS returned 403), the full text of Wakasa arXiv:1406.2803
  and Carneiro–Finder arXiv:1504.01833. Statements about those are marked "unverified".

## Verdict

**Viable with caveats. Not a dead end.** Every step of the LLS/CMQR argument is effective under GRH, the
asymptotic constants 0.794 and 0.7615 survive checking, and the one genuinely non-explicit step (the zero sum
`Σ_γ |K(iγ)|`) can be made explicit with an *absolute-constant* error by a majorant argument that needs no
bound for S(t,χ). The dead end is a specific route, not the target: **doing the zero sum by zero counting with
an explicit S(t,χ) bound gives a doubly exponential N₀** (§3).

Crude N₀ (h = 2, Γ kernel, c∞ = 0.79342; see §3 for what is and is not included):

| c    | majorant route, log N₀ | N₀            | zero-counting route (best case, constant 1/4) |
|------|------------------------|---------------|-----------------------------------------------|
| 0.95 | 200 – 400              | 10^90 – 10^170   | log log N₀ ≥ 20  (N₀ ≈ exp(10^8.7))   |
| 0.90 | 300 – 550              | 10^130 – 10^240  | log log N₀ ≥ 29  (N₀ ≈ exp(10^12.6))  |
| 0.85 | 600 – 1100             | 10^260 – 10^480  | log log N₀ ≥ 54  (N₀ ≈ exp(10^23))    |
| 0.80 | 6000 – 11000           | 10^2600 – 10^4800 | log log N₀ ≥ 455 (N₀ ≈ exp(10^197))  |

The ranges in column 2 are for the unmodelled O(1) terms set to E = 3 and E = 10; my estimate is E ≈ 4–7.
Scaling law: log N₀ ≈ (P + E) / (0.4709 · (√(c/c∞) − 1 − ε)), with P ≈ 5–9 and ε ≈ 10⁻³–10⁻².
c = 0.80 is expensive only because it sits 0.41% (in √c) above c∞ = 0.7934.

## 1. LLS Theorem 1.2 / §6

### 1.1 What the original error was
Diff of v1 against v3 (v2 is the corrected text with the Mellin-direction typos still in it; v3 fixes those):

* v1 Lemma 6.1 used an *even* kernel with `x^s + x^{-s}` and claimed for the principal character
  `Σ Λ(n)χ₀(n) n^{-1/2} K̃(x/n) = K(1/2)·√x/2 + O(...)`, proof "similar, we omit the details".
  For non-principal χ the symmetric argument (`left integral = −Ī`, hence `Re I = −Σ K(iγ) cos(γ log x)`) is
  correct: I rechecked the change of variables s → −s with ξ'/ξ(1/2−s, χ̃) = −ξ'/ξ(1/2+s, χ̃-bar).
  For the principal character it is not: −ζ'/ζ(s+1/2) has the pole at s = 1/2 with full residue
  `K(1/2)(√x + 1/√x)`, so the main term is `K(1/2)√x`, not half of it.
* Consequences in v1: Prop. 6.2 had `− K(1/2)/2`, the "limit of the method" was `((h−1)/(2h−1))²` (= 1/9 for
  h = 2), and the kernel −(Γ(s)+Γ(−s)) gave "0.42". v3: `− K(1/2)` (line 1469), limit 1/4 (line 1504), and
  0.794 with K(s) = Γ(s+1/2) (lines 1531–1539).
* This is my reconstruction from the diff; the arXiv comment only says "an error in Lemma 6.1 ... affects
  Theorems 1.2 and 1.3". Independent confirmation that v1 was wrong and v3 is at least consistent: CMQR prove
  (their Prop. 6 + Theorem 2, a duality argument) that no test function in this framework gives better than
  C(1)^{-2} > 0.7596 for h = 2. 0.42 violates that; 0.794 does not.

### 1.2 Step-by-step check of v3 Lemma 6.1 (lines 1375–1460)
Kernel hypotheses (1349–1367): holomorphic in −1/2−δ < Re s ≤ 1/2+δ except a simple pole at −1/2,
`|K(s)| ≪ 1/(1+|s|²)`, `K̃ > 0`. For K = Γ(s+1/2): K̃(u) = √u e^{-u}, K(1/2) = 1, next pole at −3/2. All hold.

| Step | Lines | Status |
|---|---|---|
| conductor term `−½ log(q̃/π)·K̃(1/x) ≪ log q/√x` | 1399–1402 | Correct. |
| Γ'/Γ term moved to Re s = 0, bounded by `∫ log(2+|t|)|K(it)|dt` | 1403–1407 | Correct (poles of ψ((1/2+s+𝔞)/2) are at s ≤ −1/2, not crossed). Explicit version needs ψ on a vertical line: Lean-unfriendly. |
| Dirichlet series side gives `K̃(n/x)` | 1408–1411 | Correct with the v3 convention `K̃(ξ) = (1/2πi)∫K(s)ξ^{-s}ds`. |
| χ̃ vs χ: terms with (n,q) > 1, `≪ log q · log x/√x` | 1412–1422 | Correct. Not o(1): it is O(log log q) when x ≍ log² q. In Miller's setting (all p | n are ≥ X) it is O(1) and small, because ω(n) ≤ log n/log X. |
| Shift to Re s = −1/2−δ/2: `I = −Σ K(iγ)x^{iγ} − r·ξ'/ξ(0,χ̃)x^{-1/2} + (left integral)` | 1429–1433 | Correct, signs checked. ξ(0,χ̃) ≠ 0. |
| Left integral `≪ x^{-1/2-δ/2}` | 1434–1435 | **Imprecise**: ξ'/ξ(1+δ/2−it) contains ½log(q̃/π), so the bound is `≪ (log q)·x^{-1/2-δ/2}`. Harmless (still ≤ log q/√x). |
| pole term: `Re ξ'/ξ(0,χ̃) ≪ log q` | 1437 | Correct. Note `−Re ξ'/ξ(0,χ̃) = Σ_γ ½/(¼+γ²) > 0`, size ≈ ½ log q̃. After dividing by √x ≍ log q this is a **constant ≈ ½√(λ/c) ≈ 0.9, not o(1)**: an explicit proof must carry it. |
| `Σ_γ|K(iγ)| = (1+o(1)) (log q̃/2π)∫|K(it)|dt` "by IK Thm 5.12" | 1439–1442 | **The soft step.** (a) IK 5.12 is an explicit formula for analytic test functions; `|K(it)|` is not one. What is actually needed is local zero density, i.e. S(T,χ) = o(log q) uniformly for bounded T (Selberg, GRH), or a majorant argument. CMQR Lemma 5 (their lines 581–615) writes this proof out with error `O_h(log q/log log q)`. (b) As an asymptotic in q̃ it is false for bounded q̃; only the upper bound `≤ (log q/2π)∫|K| + o(log q)` is true and only that is used (CMQR state it this way at eq. 20250710_11:39). (c) The lemma statement has log q, the proof log q̃; fine as an upper bound since q̃ ≤ q. |
| principal character: `K(1/2)√x + O(1)` and removal of (n,q) > 1 | 1443–1459 | Correct under RH. For the Γ kernel `Σ_γ|Γ(½+iγ)|` over ζ-zeros is ~10⁻⁹. |

### 1.3 Proposition 6.2 (lines 1464–1491)
* x = X/λ, sum over χ ∈ H̃, orthogonality (line 852): LHS = `h·Σ_{n∈H} Λ(n) n^{-1/2} K̃(n/x)`.
* n > X: dropped using `K̃ ≥ 0` (line 1480). Correct, and this is exactly why K̃ ≥ 0 is assumed. (CMQR remove
  this hypothesis by paying `ℓ·F̂₋` on n ≥ n_χ instead; that is the whole 0.794 → 0.7615 gain.)
* n ≤ X: prime powers p^k with p ≤ X, p ∤ q lie in H. Correct. Replacement of the sum by
  `√x ∫_0^λ K̃(u)u^{-1/2}du` costs `O(log² X)` under RH (sharp cut-off at X: boundary term
  `(ψ(X)−X)·K̃(λ)/√X`). They write `o(h log q)`; true, but explicitly this is ≈ `e^{-λ}√λ·log²X/(8π)` per unit
  of h, i.e. 1–3 for log q between 300 and 10⁴. It cannot be smoothed away: the cut-off at X is intrinsic.
* No use of: q prime, χ quadratic, χ primitive, ℓ ∤ q beyond the hypothesis "primes ℓ ≤ X, ℓ ∤ q lie in H".
* Numerics reproduced (`skeptic_checks.py`): `(1/2π)∫|Γ(½+it)|dt = 0.470888`, c(2.452) = 0.793504,
  optimum λ = 2.4773, c∞ = 0.793420. c∞(h) = 0.6981, 0.6566, 0.5880, 0.5488 for h = 3, 4, 10, 100:
  **h = 2 is the worst case**, and the per-character errors are divided by h − 1, so uniformity in h is fine.

**Conclusion on (1):** v3 Lemma 6.1 and Prop. 6.2 are correct as asymptotic statements once the zero-sum line is
read as an upper bound and proved as in CMQR Lemma 5. Three imprecisions (left-integral log q factor, "(1+o(1))
log q̃", citation of IK 5.12), none fatal.

## 2. CMQR (arXiv:2404.08380v2)

* **Setting matches.** Theorem 3 (their line 334): any q ∈ ℕ, any non-principal χ mod q of order ℓ,
  `n_χ = min{n : χ(n) ≠ 0, 1}`, integers not primes, `limsup n_χ/log² q ≤ C(1/(ℓ−1))^{-2}`; ℓ = 2 gives
  < 0.7615. Miller's witness count (χ(a) = 0 allowed) is only easier: least witness ≤ n_χ.
* Imprimitive χ handled by their Lemma 7 (lines 646–671), error `O(‖g‖_∞ √log q)`.
* Proof structure (lines 675–778): Guinand–Weil formula for `(χ^j)*` with
  `ĥ(t) = ½(F̂(t−Δ) + F̂(−t−Δ))`, `F̂ ∈ C_c^∞`, Δ = log n_χ/2π ≥ N so `ĥ(0) = 0` (the log q_j term vanishes
  identically; log q enters only through the zeros). I found no error.
* **Error terms: effective, none explicit.** `O_F(log q/log log q)` from Selberg's `S(T,χ)` (their eq.
  20230327_13:04, "implicit constants absolute"), `O_F(ℓ√log q)`, `O_F((log log q)²)` from RH `ψ(x)`.
  The dominant one is the S(T,χ) term: exactly the doubly-exponential trap of §3.
* Non-explicit ingredients specific to CMQR: (i) "wlog n_χ ≤ log² q" quotes LLS's asymptotic result (their
  line 677); in a proof by contradiction with cut-off X this is unnecessary. (ii) Theorem 1(i) (density of
  `F̂ ∈ C_c^∞`) is a limiting argument; the actual 0.7615 test function (their eq. `lowers`, Table 2, A = 1:
  a = 0.246, c = 0.626, twelve coefficients b_n, poles of order up to 24) has `F̂` supported on a half-line
  `t ≤ c/π` with exponential decay, not compact support. An explicit version must either truncate with a
  quantified loss or redo the explicit formula for these rational F (F is analytic in |Im x| < 1/(2a) ≈ 2.03,
  so Guinand–Weil does apply directly; then `ĥ(0) ≠ 0` and an extra, harmless, log q_j term appears).
  (iii) Theorem 2 numerics are floating point "digits stable under increased precision", not interval
  arithmetic.
* Verdict: correct, and its dual bound is the best available barrier (§5). As a base for an explicit theorem
  it is harder than LLS's Γ kernel (sign-changing F̂, 14 parameters) for a gain of 0.794 → 0.7615.

## 3. Effectivity and N₀

**Nothing is ineffective.** No Siegel-type input, no compactness. GRH replaces every zero-free-region
argument. An explicit N₀ exists in principle for every c > c∞.

### 3.1 The trap: zero counting
`N(T,χ) = (T/2π)log(qT/2πe) + S(T,χ) − S(0,χ) + O(1)` and summation by parts give

    Σ_γ |K(iγ)| ≤ (log q/2π)·‖K‖₁ + sup|S| · TV(|K|) + O(1).

Under GRH the best known is `|S(t,χ)| ≤ (1/4 + o(1)) log q/log log q` (Carneiro–Chandee–Milinovich, as quoted
by CMQR appendix, their ref. CCM2), with the o(1) of size `log log log q/log log q` and not explicit. Fully
explicit GRH bounds for S(t,χ) exist only in the Fujii/Wakasa style with a larger constant (unverified: I could
not open arXiv:1406.2803). So the error is not `O(log q)`, but it is `log q/log log q`, and the relative loss is

    2π·A·(TV/‖K‖₁)/log log q = 1.88/log log q   (A = 1/4, TV/‖K‖₁ = 1.198 for |Γ(½+it)|).

To reach c = 0.9 one needs relative loss ≤ 6.5%, i.e. log log q ≥ 29, `q ≥ exp(4·10¹²)`; for c = 0.8,
log log q ≥ 455. With a realistic explicit constant A ≈ 1 multiply log log q by 4. **This route is a dead end
for any usable N₀**, and it is the route both papers use.

### 3.2 The way out: majorants (checked to be valid for the needed weight)
`|Γ(½+it)| = √(π/cosh πt)` exactly. If `M(t) ≥ √(π/cosh πt)` on ℝ and `Σ_γ M(γ)` is given by an exact
identity, then `Σ_γ|K(iγ)| ≤ Σ_γ M(γ) = (log q̃/2π)∫M + (absolute constant)`. No S(t). Two families tested:

(a) **Band-limited M** (`M̂` supported in [−log y, log y]; Guinand–Weil applies, prime sum is finite and bounded
by `P = (1/π)Σ_{n<y} Λ(n)n^{-1/2}|M̂(log n)|` for every χ). `skeptic_checks.py` output:

      y      eps=∫M/∫|K|−1    P        Γ-term (𝔞=0 / 𝔞=1)
        2     4.72            0.00     −3.17 / −2.29
       10     0.761           1.69     −2.19 / −1.37
      100     0.133           2.98     −1.74 / −1.01
     1000     0.0318          3.98     −1.63 / −0.94
    10000     0.0087          4.84     −1.60 / −0.92

So ε ≈ 0.9/√y while P ≈ 0.5·log y. **Supports below log 2 (no primes at all) are useless** (ε = 4.7): the
"compact support avoids everything" idea fails as stated; primes up to y ≈ 10³–10⁴ must be carried, as an
absolute constant. (The sinc⁴ basis used is not optimal.)

(b) **Rational M** `= Σ c_{j,k} Re (a_j+it)^{-k}`, a_j > ½. Then
`Σ_γ Re(a+iγ)^{-k} = Re[(−1)^{k−1}/(k−1)!]·(ξ'/ξ)^{(k−1)}(½+a, χ̃)`: partial fractions at **real points
σ = ½ + a > 1**, exactly the inputs BRIEF.md says exist in Lean. Density term `½(Σ_j c_{j,1})·log q̃`; the L'/L
part is bounded for all χ by `Σ|c_{j,k}|·|(ζ'/ζ)^{(k−1)}(½+a_j)|/(k−1)!`. LP in `skeptic_rational.py`
(10 values of a ≥ 0.75, i.e. σ ≥ 1.25, k ≤ 4, minimising `I_M·log q + P`):

    log q      eps        P       effective c  (E = 3)   (E = 10)
      200    0.0091     5.09        0.951                 1.085
      300    0.0089     5.10        0.902                 0.988
      600    0.0026     6.21        0.850                 0.891
     1200    0.0011     6.79        0.823                 0.843
     6000    0.0002     8.33        0.800                 0.804
    20000    0.0001     9.20        0.796                 0.797

Poles closer to the line or higher order (a ≥ 0.51, k ≤ 10) change these by < 1%. Caveats: grid-checked
only (ε below ~10⁻⁴ is at the noise level of the grid); Γ-factor (polygamma) terms of the majorant, O(1) and
mostly negative, are not included.

### 3.3 What E must contain (normalised by √x ≈ 0.57·log q), my estimates
pole-at-(−½) term ≈ +0.9; Γ'/Γ integral of the kernel formula ≲ 1; sharp cut-off at X ≈ 0.0105·log² X
(1.3 at log q = 300, 3.1 at 6000); imprimitivity (Miller) ≲ 0.2; principal character ≲ 0.01. Total E ≈ 4–7.

## 4. Applicability to Miller

* Composite modulus: yes (LLS: any q, any subgroup H; CMQR: any q). Order h: any; h = 2 is worst. Imprimitive
  χ: yes. Integer witnesses: yes (prime powers of primes ≤ X in H; the smallest a with χ(a) ≠ 1 is prime anyway).
* No hidden assumption of q prime, χ quadratic or ℓ ∤ q found.
* **Uniformity trap.** The published statements are "as q → ∞" in the modulus. In Miller's setting the
  conductor q̃ | n can be much smaller than n (only q̃ ≥ X is forced), and X = c·log² n is defined through n.
  A proof phrased as "the theorem for q̃ ≥ N₀, plus Bach's 2 log² q̃ below N₀" leaves a hole
  (n ≥ N₀, n^{√(c/2)} < q̃ < N₀). The proof must be the single inequality
  `(1 − 2e^{-λ})√(X/λ) ≤ I_M·log q̃ + C` with C independent of q̃, then `log q̃ ≤ log n`. Every error term must
  be bounded uniformly down to small q̃; anything of the shape `log q̃/log log q̃` breaks this.
* LLS Theorem 1.1(2) (line 143) already gives ℓ ≤ (log q)² when q has no prime factor below log² q, for
  q ≥ 3000: c = 1 is published in exactly Miller's situation; c < 1 explicit would be new.

## 5. Known limits

* LLS framework (K̃ ≥ 0): nothing below ¼ for any h (lines 1493–1504). For h = 2 the Γ kernel gives 0.7934.
* CMQR framework (K̃ ≥ 0 dropped): `C(1)^{-2} ∈ (0.7596, 0.7615)` for h = 2, by duality (Prop. 6, Theorem 2):
  **no test function in this explicit-formula scheme can go below 0.7596 for quadratic characters**;
  0.6601, 0.6029, 0.5610 for ℓ = 3, 4, 5; ¼ as ℓ → ∞.
* True order: Montgomery (GRH) n_χ = Ω(log q · log log q) for some real primitive χ, so nothing below
  `log^{1+o(1)} q` is possible; CMQR's appendix shows a better S(t,χ) bound than CCM's ¼ would beat log² q.
* I found **no result or heuristic saying an explicit c < 1 is impossible**. The only structural obstacle is
  the gap c − c∞: N₀ ≈ exp(const/(√(c/c∞) − 1)).

## 6. Risks, ranked

1. **Zero-sum step done by zero counting / S(t,χ).** Doubly exponential N₀ and no clean explicit S(t,χ)
   constant to cite. If either prover's write-up contains `log q/log log q`, reject it.
2. **Pointwise majorant inequality** `M(t) ≥ √(π/cosh πt)` for all real t: the new load-bearing numeric
   lemma. Needs a rigorous certificate (interval arithmetic plus a tail argument), not a grid. My LPs are
   evidence that good M exist, nothing more.
3. **Explicit formula for the Γ(s+½) kernel itself**: needs Γ and ψ on vertical lines (BRIEF.md says avoid).
   Swapping to a rational one-sided kernel is possible (CMQR's F_n are rational) but the simplest one gives
   c∞ = 1 (Bach); beating 1 with rational kernels needs sign changes or high-order poles. c∞ may end up
   between 0.80 and 0.95 rather than 0.794, which moves the whole N₀ table.
4. **O(1) bookkeeping**: the pole-at-(−½) constant, sharp cut-off `log² X`, uniformity in q̃ (§4), sum over
   h − 1 characters with different conductors and parities.
5. **Trust in the literature**: the published LLS Theorem 1.2 was wrong for two years (0.42); the corrected
   Lemma 6.1 still has three loose statements; CMQR numerics are non-rigorous floating point. Use both only
   as guides; the explicit proof must be self-contained.
6. c = 0.80 specifically: 0.41% above c∞, needs log n ≳ 6000–11000 and majorant accuracy ε ≲ 10⁻³.
