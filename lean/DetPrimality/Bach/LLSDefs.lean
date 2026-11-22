import DetPrimality.Bach.Blueprint

/-!
# Round 8 hand-off: Lamzouri–Li–Soundararajan, Theorem 1.1(2) (fixed by the project lead)

LLS (Math. Comp. 84 (2015)), Theorem 1.1(2): under GRH, if `q ≥ 3000` has no prime factor below
`(log q)²`, then every proper subgroup of `(ℤ/q)ˣ` misses a prime `ℓ ≤ (log q)²`.  For the Miller
test this gives the constant `c = 1` (composite `n`, non-units count).

The proof compares upper and lower bounds for `Re S(X, χ)`, `S(X, χ) = ∑_{n ≤ X} Λ(n) χ(n) log(X/n)`
(Perron kernel `X^s/s²`).  The four analytic/elementary inputs are stated below as `Prop`s so that
they can be proved independently; the assembly proves `BachBoundCharComposite 1` (for `n ≥ N₀`)
from them.

Do not change these definitions without the project lead.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `∑_ρ m_ρ / |ρ|²` over the nontrivial zeros (`= 2 |Re B(χ)|` under GRH). -/
noncomputable def zeroSumSq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2

/-- `S(x, χ) = ∑_{n ≤ x} Λ(n) χ(n) log(x/n)`. -/
noncomputable def logPsi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * χ (n : ZMod N) * (Real.log (x / n) : ℂ)

/-- `∑_{n ≤ x} Λ(n) log(x/n)`. -/
noncomputable def logPsiZeta (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * Real.log (x / n)

/-- `W(x, χ) = ∑_{n ≤ x} Λ(n) χ(n) / n · (1 - n/x)`. -/
noncomputable def weightedLogSum {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ) * (1 - (n : ℂ) / (x : ℂ))

/-- `∑_{n ≤ x} Λ(n) / n · (1 - n/x)`. -/
noncomputable def weightedLogSumZeta (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n / n * (1 - (n : ℝ) / x)

/-- **LLS Lemma 1** (RH for ζ).  LLS: `κ = 2|B| = 0.04618…`. -/
def LLSZetaLower (κ : ℝ) : Prop :=
  DirichletLZerosOnLine → ∀ x : ℝ, 64 ≤ x →
    x - κ * (√x + 1) - Real.log (2 * Real.pi) * Real.log x - 1 ≤ logPsiZeta x

/-- **LLS Lemma 2** (GRH for primitive `χ`), with `2|Re B(χ)| = zeroSumSq χ` and `Ẽ_a(x) ≤ 0`. -/
def LLSChiUpper : Prop :=
  DirichletLZerosOnLine → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ x : ℝ, 3 ≤ x →
      (logPsi χ x).re
        ≤ (√x + 1 + Real.log x / 2) * zeroSumSq χ + Real.log (q / Real.pi) / 2 * Real.log x

/-- **LLS Lemma 3** (GRH for primitive `χ`): the zero sum with the hypothesis gain.
`(1 - 1/√x)² |Re B| ≤ ½ (1 - 1/x) log(q/π) - Re W(x, χ) + E_a(x)`, with `E_a(x) ≤ -27/100` for
`x ≥ 64` (`E₁(64) ≈ -0.2734`, `E₀(64) ≈ -0.897`). -/
def LLSZeroSumGain : Prop :=
  DirichletLZerosOnLine → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ x : ℝ, 64 ≤ x →
      (1 + 1 / x - 2 / √x) * (zeroSumSq χ / 2)
        ≤ (1 - 1 / x) * Real.log (q / Real.pi) / 2 - (weightedLogSum χ x).re - 27 / 100

/-- Unconditional replacement for **LLS Lemma 4** (LLS's commented lemma: `≥ log(N-1) - 2 + 4/N`). -/
def LLSWeightedLower : Prop :=
  ∀ x : ℝ, 64 ≤ x → Real.log x - 2 ≤ weightedLogSumZeta x

end DetPrimality.Bach
