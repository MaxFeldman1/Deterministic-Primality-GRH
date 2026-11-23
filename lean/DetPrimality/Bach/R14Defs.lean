import DetPrimality.Bach.R13Defs

/-!
# Round 14 hand-off: pole at β (research/barrier/formal0760.md)

Weights `√n · (n/x)^a · W(β log(x/n))` with `a = β − 1` (β = 3, two exact sign changes: certified
`c* = 0.7607585`; the Python record of research/barrier/inside.md was 0.7607618). The three analytic inputs of
Round 13 are generalised to the shift `a`; at `a = 0` they are `R13ZetaSmooth`, `R13ChiExplicit`, `R13ZeroPow`.
The certificate structure and assembly are owned by the assembly agent (`R14Asm*.lean`), since their normalisation
is to be re-derived (formal0760 §5).

Do not change these definitions without the project lead.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `Φ^{(a)}_{χ,j}(y) = ∑_{n<y} Λ(n) χ(n) √n (n/y)^a log^j(y/n)` (`a = 0`: `r13Phi`). -/
noncomputable def r14Phi {N : ℕ} (χ : DirichletCharacter ℂ N) (a j : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈y⌉₊, (Λ n : ℂ) * χ (n : ZMod N) *
    ((Real.sqrt n * ((n : ℝ) / y) ^ a * Real.log (y / n) ^ j : ℝ) : ℂ)

/-- `A^{(a)}_i(Y) = ∑_{n<Y} Λ(n) √n (n/Y)^a log^i(Y/n)` (`a = 0`: `r11A`). -/
noncomputable def r14A (a i : ℕ) (Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌈Y⌉₊, Λ n * Real.sqrt n * ((n : ℝ) / Y) ^ a * Real.log (Y / n) ^ i

/-- (P1ₐ) ζ side with shift `a`, all orders. RH. -/
def R14ZetaSmooth (a : ℕ) : Prop :=
  DirichletLZerosOnLine → ∀ i : ℕ, ∃ C : ℝ, ∀ Y : ℝ, 1 ≤ Y →
    |r14A a i Y - (i.factorial : ℝ) * (1 / ((a : ℝ) + 3 / 2)) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)|
      ≤ C * Y ^ ((5 : ℝ) / 4)

/-- (P2ₐ) χ explicit formula with shift `a`, every order `j ≥ 3`, uniform in `χ`. GRH. -/
def R14ChiExplicit (a : ℕ) : Prop :=
  DirichletLZerosOnLine → ∀ j : ℕ, 3 ≤ j → ∃ C : ℝ,
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ y : ℝ, 1 ≤ y →
      ‖r14Phi χ a j y + (j.factorial : ℂ) *
          ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ + 1 / 2) / (ρ + 1 / 2 + a) ^ (j + 1)‖
        ≤ C * (Real.log q + 1) * (1 + Real.log y) ^ j + C * Real.sqrt y

/-- (P3ₐ) zero sums at `a + 3/2` of every order. GRH (or unconditional). -/
def R14ZeroPow (a : ℕ) : Prop :=
  DirichletLZerosOnLine →
    (∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
        ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ)).re ≤ Real.log q / 2 + C) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
          |∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ k).re| ≤ C)

end DetPrimality.Bach
