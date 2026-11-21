import Mathlib
import DetPrimality.GRHStatements

/-!
# Shared interfaces for the GRH → Bach → deterministic algorithms chain

Every agent codes against these definitions. Do not change them without the project lead.
-/

namespace DetPrimality

/-- Bach's bound with constant `c`: every proper subgroup of `(ZMod n)ˣ` misses a unit
whose least nonnegative representative is `< c * (log n)^2`. Bach (1990): true with `c = 2`
under GRH for Dirichlet L-functions. -/
def BachBound (c : ℝ) : Prop :=
  ∀ n : ℕ, 2 < n → ∀ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ →
    ∃ a : (ZMod n)ˣ, a ∉ H ∧ (((a : ZMod n).val : ℕ) : ℝ) < c * (Real.log n) ^ 2

/-- Character form of Bach's bound: every nontrivial Dirichlet character mod `n`
is `≠ 1` at some `a` with `a < c (log n)^2`. -/
def BachBoundChar (c : ℝ) : Prop :=
  ∀ n : ℕ, 2 < n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
    ∃ a : ℕ, ((a : ℕ) : ℝ) < c * (Real.log n) ^ 2 ∧ IsUnit (a : ZMod n) ∧ χ (a : ZMod n) ≠ 1

/-- The final target of Layer 2 (open): GRH implies Bach's bound for some explicit `c`. -/
def GRHImpliesBach (c : ℝ) : Prop := DirichletLZerosOnLine → BachBound c

end DetPrimality
