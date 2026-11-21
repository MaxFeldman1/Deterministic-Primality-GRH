import DetPrimality.Bach.Blueprint

/-!
# Round-2 hand-off statements (fixed by the project lead — do not edit)

Agents prove pieces against these `Prop`s so they can work in parallel.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- Growth of order `< 2`: `‖f s‖ ≤ exp (C (1+‖s‖)^{3/2})`. Enough for genus-1 Hadamard
and for `∑ 1/|ρ|² < ∞`. -/
def GrowthLtTwo (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖f s‖ ≤ Real.exp (C * (1 + ‖s‖) ^ ((3 : ℝ) / 2))

/-- Genus-1 Hadamard partial fraction for the completed L-function, summed over the
nontrivial zeros with multiplicity (`zeroOrd`). -/
def HadamardLogDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∃ B : ℂ, ∀ s : ℂ, completedLFunction χ s ≠ 0 →
    deriv (completedLFunction χ) s / completedLFunction χ s
      = B + ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)

end DetPrimality.Bach
