import DetPrimality.Bach.LLSDefs

/-!
# Round 11 hand-off: an explicit constant `c < 1` (research/below-one/designB.md)

Kernel `K(s) = 6/(s+1)⁴`, i.e. the weight `√n · log³(x/n)` on `n < x = 3X`.  Main results
(designB Theorems A, B; referee: research/below-one/refereeB.md): under GRH, for every `n ≥ N₀` and
every `χ ≠ 1` mod `n` some `1 ≤ a < c (log n)²` has `χ a ≠ 1`, for explicit pairs `(c, N₀)` with
`c < 1`, and for every `c > 0.7772` eventually.

The analytic inputs are stated as `Prop`s with constants loosened from designB (so that they can be
certified); the lead checked numerically (scratchpad `sens.py`) that the assembly still closes with
them for the target table.  `χ₁ := (1 : DirichletCharacter ℂ 1)` is ζ.

Do not change these definitions without the project lead.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `A_j(y) = ∑_{n<y} Λ(n) √n log^j(y/n)`. -/
noncomputable def r11A (j : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌈y⌉₊, Λ n * Real.sqrt n * Real.log (y / n) ^ j

/-- `Φ_χ(y) = ∑_{n<y} Λ(n) χ(n) √n log³(y/n)`. -/
noncomputable def r11Phi {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈y⌉₊,
    (Λ n : ℂ) * χ (n : ZMod N) * ((Real.sqrt n * Real.log (y / n) ^ 3 : ℝ) : ℂ)

/-- `Z_k(χ) = ∑_ρ m_ρ / |ρ + 1/2|^k` (under GRH `|ρ + 1/2|² = 1 + γ²`). -/
noncomputable def r11Z {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ) : ℝ :=
  ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ k

/-- `T(X) = ∑_{n ≥ X} Λ(n) (1 + log n) n^{-3/2}`. -/
noncomputable def r11T (X : ℝ) : ℝ :=
  ∑' n : ℕ, if X ≤ n then Λ n * (1 + Real.log n) / (n : ℝ) ^ ((3 : ℝ) / 2) else 0

/-- Upper bounds `γ_k ≥ |g_ζ^{(k)}(-1/2)|`, `g_ζ = -ζ'/ζ` (designB values + 2%). -/
noncomputable def r11gam : ℕ → ℝ
  | 0 => 1.771
  | 1 => 0.148
  | 2 => 1.281
  | _ => 0.0515

/-- `r_j(y) = ∑_{i ≤ j} C(j,i) γ_{j-i} log^i y + 0.64 j!`. -/
noncomputable def r11r (j : ℕ) (y : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * r11gam (j - i) * Real.log y ^ i)
    + 0.64 * (j.factorial : ℝ)

/-- **designB Lemma 1** (RH): `Z₂ ≤ 0.047`, `Z₄ ≤ 0.00012` for ζ (true: 0.046136, 0.000074). -/
def R11ZetaZ : Prop :=
  DirichletLZerosOnLine →
    r11Z (1 : DirichletCharacter ℂ 1) 2 ≤ 0.047 ∧ r11Z (1 : DirichletCharacter ℂ 1) 4 ≤ 0.00012

/-- **designB Lemma 2, (3.1)** (RH): explicit formula for `A_j`, `j = 1, 2, 3`. -/
def R11ZetaExplicit : Prop :=
  DirichletLZerosOnLine → ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ y : ℝ, 1 < y →
    |r11A j y - (j.factorial : ℝ) * (2 / 3) ^ (j + 1) * y ^ ((3 : ℝ) / 2)|
      ≤ (j.factorial : ℝ) * r11Z (1 : DirichletCharacter ℂ 1) (j + 1) * y + r11r j y

/-- **designB Lemma 3, (3.2)** (GRH): upper bound for `Re Φ_χ(y)`, `χ` primitive
(`G₀..G₃` = designB values + 2%). -/
def R11ChiExplicit : Prop :=
  DirichletLZerosOnLine → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ y : ℝ, 1 < y →
      (r11Phi χ y).re ≤ 6 * y * r11Z χ 4 + (Real.log q + 1.30) * Real.log y ^ 3
        + 3 * 9.31 * Real.log y ^ 2 + 3 * 32.91 * Real.log y + 198.31

/-- **designB Lemma 4, (4.2)** (GRH): the zero sum `Z₄(χ)` with the hypothesis gain
(`κ ≥ 12.4`; designB: 12.691241). -/
def R11ZeroSumGain : Prop :=
  DirichletLZerosOnLine → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ X : ℝ, 1 ≤ X →
      (∀ n : ℕ, 1 ≤ n → (n : ℝ) < X → χ (n : ZMod q) = 1) →
        r11Z χ 4 ≤ (Real.log q - 12.4 + 4 * r11T X) / 4

/-- **designB Lemma 5** (unconditional), with Chebyshev constant `c₀` (`ψ(t) ≤ c₀ t`). -/
def R11Tail (c₀ : ℝ) : Prop :=
  ∀ X : ℝ, 1 ≤ X → r11T X ≤ c₀ * (3 * Real.log X + 7) / Real.sqrt X

/-- The target statement shape: every `χ ≠ 1` mod `n` has `χ a ≠ 1` for some `1 ≤ a < c log² n`. -/
def R11Bound (c : ℝ) (n : ℕ) : Prop :=
  ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
    ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < c * Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1

end DetPrimality.Bach
