import Mathlib
import DetPrimality.GRHStatements

/-!
# Bach's Theorem 2 form, for composite moduli

Bach (1990) proves two statements under ERH:
* Theorem 2: if every positive integer `a < x` lies in a proper subgroup `G` of `(ℤ/m)ˣ`, then
  `x < 2 log² m` — here an `a` sharing a factor with `m` counts as *outside* `G`;
* Theorem 3: the same for units only (`x < 3 log² m`).

`Interfaces.BachBound` is the Theorem 3 (unit) form.  The deterministic Miller test only needs the
Theorem 2 form, and only for composite `n`: a base sharing a factor with `n` is a Miller witness
anyway.  In character language: for composite `n` and `χ ≠ 1` mod `n` some `1 ≤ a < c log² n`
has `χ a ≠ 1` (for a non-unit `a`, `χ a = 0 ≠ 1`).

The analytic proof is easier: if `χ a = 1` for all `1 ≤ a < x`, then every `a < x` is coprime to
`n`, so (i) the non-coprime correction vanishes, and (ii) the least prime factor of `n` is `≥ x`,
whence `n ≥ x²` because `n` is composite.

Do not change these definitions without the project lead.
-/

namespace DetPrimality

/-- Bach's Theorem 2 form, character version, composite moduli only. -/
def BachBoundCharComposite (c : ℝ) : Prop :=
  ∀ n : ℕ, 2 < n → ¬ n.Prime → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
    ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < c * Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1

/-- GRH implies the composite Theorem 2 form with constant `c`. -/
def GRHImpliesBachComposite (c : ℝ) : Prop :=
  DirichletLZerosOnLine → BachBoundCharComposite c

end DetPrimality
