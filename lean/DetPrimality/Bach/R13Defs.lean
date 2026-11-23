import DetPrimality.Bach.R11Defs

/-!
# Round 13 hand-off: an asymptotic record below 0.7615 (research/barrier/formal076.md)

Kernel family with exactly rational modulus on the critical line (formal076 §1, Lemma E):
`K(s) = (Z − (s−1)²)·H₀(s)²`, weights `√n · W(log(x/n))`, `W` a polynomial; design B (certified
`c* = 0.7611430`) gives: under GRH, for every `c > 0.7612`, eventually every `χ ≠ 1` mod `n` has `χ a ≠ 1` for
some `1 ≤ a < c log² n` (CMQR 2024: 0.7615).

The three analytic inputs are stated with existential constants (asymptotic statement only).

Do not change these definitions without the project lead.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `Φ_{χ,j}(y) = ∑_{n<y} Λ(n) χ(n) √n log^j(y/n)` (`r11Phi` is `j = 3`). -/
noncomputable def r13Phi {N : ℕ} (χ : DirichletCharacter ℂ N) (j : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈y⌉₊,
    (Λ n : ℂ) * χ (n : ZMod N) * ((Real.sqrt n * Real.log (y / n) ^ j : ℝ) : ℂ)

/-- The weight polynomial `W(L) = ∑_{j ≤ J} θ_j L^j / j!`. -/
noncomputable def r13W (θ : ℕ → ℝ) (J : ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), θ j * L ^ j / (j.factorial : ℝ)

/-- Its Mellin kernel `K(s) = ∑_{j ≤ J} θ_j / s^{j+1}`. -/
noncomputable def r13K (θ : ℕ → ℝ) (J : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (J + 1), (θ j : ℂ) / s ^ (j + 1)

/-- `R(L)` with `∫₀^{e^{-L}} W(log 1/t) √t dt = e^{-3L/2} R(L)`. -/
noncomputable def r13R (θ : ℕ → ℝ) (J : ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    θ j * ∑ i ∈ Finset.range (j + 1), L ^ i / (i.factorial : ℝ) * (2 / 3) ^ (j + 1 - i)

/-- `A(Y) = ∑_{n<Y} Λ(n) √n W(log(x/n))`. -/
noncomputable def r13A (θ : ℕ → ℝ) (J : ℕ) (x Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌈Y⌉₊, Λ n * Real.sqrt n * r13W θ J (Real.log (x / n))

/-- Majorant / exact modulus `G(t) = ∑_{k=1}^m e_k Re (1+it)^{-k}`. -/
noncomputable def r13G (e : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, e k * ((1 : ℂ) / (1 + (t : ℂ) * I) ^ k).re

/-- The numerical certificate (formal076 §4.1). `L₁ = 0` is design A (no sign change). -/
structure R13Cert (J m : ℕ) (θ e : ℕ → ℝ) (ℓ L₁ N₀ : ℝ) : Prop where
  low : ∀ j, j < 3 → θ j = 0
  range : 0 ≤ L₁ ∧ L₁ < ℓ
  negCell : ∀ L, 0 ≤ L → L ≤ L₁ → r13W θ J L ≤ 0
  posCell : ∀ L, L₁ ≤ L → L ≤ ℓ → 0 ≤ r13W θ J L
  modulus : ∀ t : ℝ, ‖r13K θ J (1 + (t : ℂ) * I)‖ ≤ r13G e m t
  e1pos : 0 < e 1
  num : 0 < N₀ ∧ N₀ ≤ 2 * Real.exp (-(3 * ℓ / 2)) * r13R θ J ℓ
                          - 2 * Real.exp (-(3 * L₁ / 2)) * r13R θ J L₁ + r13R θ J 0

/-- (P1) ζ side, all orders, sharp cut-off included (`i = 0`). RH. -/
def R13ZetaSmooth : Prop :=
  DirichletLZerosOnLine → ∀ i : ℕ, ∃ C : ℝ, ∀ Y : ℝ, 1 ≤ Y →
    |r11A i Y - (i.factorial : ℝ) * (2 / 3) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)| ≤ C * Y ^ ((5 : ℝ) / 4)

/-- (P2) χ explicit formula of every order `j ≥ 3`, constants uniform in `χ`. GRH. -/
def R13ChiExplicit : Prop :=
  DirichletLZerosOnLine → ∀ j : ℕ, 3 ≤ j → ∃ C : ℝ,
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ y : ℝ, 1 ≤ y →
      ‖r13Phi χ j y + (j.factorial : ℂ) *
          ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2) ^ (j + 1)‖
        ≤ C * (Real.log q + 1) * (1 + Real.log y) ^ j + C * Real.sqrt y

/-- (P3) zero sums at `3/2` of every order. GRH. -/
def R13ZeroPow : Prop :=
  DirichletLZerosOnLine →
    (∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
        ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ)).re ≤ Real.log q / 2 + C) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
          |∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ k).re| ≤ C)

end DetPrimality.Bach
