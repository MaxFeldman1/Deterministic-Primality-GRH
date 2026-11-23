import Main
import DetPrimality

/-!
# Unconditional corollaries: Alpöge's GRH archive + DetPrimality

`Main` is the archive's root module (`LFunction_eq_zero_re : DirichletLZerosOnLine`), and
`DetPrimality` is this project.  Both import the same module `Statements`
(byte-identical, sha256 79ef7ca7…), so `DirichletLZerosOnLine` is literally the same constant.
Build and check with `bin/check_bridge.sh` (on the box; needs the archive's oleans).
-/

/-- Deterministic Miller test with bases below about `(ln n)²` decides primality. No hypotheses. -/
theorem millerDet_correct (n : ℕ) : DetPrimality.Miller.millerDet 1 n = true ↔ n.Prime :=
  DetPrimality.millerDet_correct_of_GRH LFunction_eq_zero_re n

/-- The bit-level Miller program is correct and uses at most `31 (log₂ n + 1)⁵` bit operations. -/
theorem millerDetBits_correct (n : ℕ) :
    ((DetPrimality.Complexity.cx_millerDetBits n).1 = true ↔ n.Prime) ∧
      (DetPrimality.Complexity.cx_millerDetBits n).2 ≤ 31 * (Nat.log2 n + 1) ^ 5 :=
  DetPrimality.Complexity.cx_millerDetBits_correct_of_GRH LFunction_eq_zero_re n

/-- Deterministic Tonelli–Shanks (non-residue search below about `(ln p)²`) finds square roots. -/
theorem sqrtModDet_correct (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, DetPrimality.TonelliShanks.sqrtModDet 1 p n = some r ∧ (r : ZMod p) ^ 2 = n :=
  DetPrimality.sqrtModDet_correct_of_GRH LFunction_eq_zero_re p hp n

theorem sqrtModDet_isSome_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    (DetPrimality.TonelliShanks.sqrtModDet 1 p n).isSome ↔ IsSquare (n : ZMod p) :=
  DetPrimality.sqrtModDet_isSome_iff_of_GRH LFunction_eq_zero_re p hp n

#print axioms millerDet_correct
#print axioms millerDetBits_correct
#print axioms sqrtModDet_correct
#print axioms sqrtModDet_isSome_iff

/-! ### Explicit constants below 1 (Rounds 11–12), unconditional -/

/-- Every `χ ≠ 1` mod `n` has `χ a ≠ 1` for some `1 ≤ a < c log² n`: table of `(c, N₀)`. -/
theorem charBound_table :
    (∀ n : ℕ, (10 : ℝ) ^ 9 ≤ n → DetPrimality.Bach.R11Bound 0.95 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 10 ≤ n → DetPrimality.Bach.R11Bound 0.9 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 11 ≤ n → DetPrimality.Bach.R11Bound 0.85 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 13 ≤ n → DetPrimality.Bach.R11Bound 0.8 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 14 ≤ n → DetPrimality.Bach.R11Bound 0.78 n) :=
  DetPrimality.charBound_table_of_GRH LFunction_eq_zero_re

theorem charBound_eventually :
    ∀ c : ℝ, 0.7772 < c → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → DetPrimality.Bach.R11Bound c n :=
  DetPrimality.charBound_eventually_of_GRH LFunction_eq_zero_re

theorem subgroupBound_eventually :
    ∀ c : ℝ, 0.6417 < c → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < c * Real.log n ^ 2 ∧
        (¬ IsUnit (a : ZMod n) ∨ ∃ u : (ZMod n)ˣ, (u : ZMod n) = a ∧ u ∉ H) :=
  DetPrimality.subgroupBound_eventually_of_GRH LFunction_eq_zero_re

/-- Deterministic Miller test with constant `7/10` for `n ≥ 10¹¹`. -/
theorem millerDet_70_correct (n : ℕ) (hn : (10 : ℝ) ^ 11 ≤ n) :
    DetPrimality.Miller.millerDet (7 / 10) n = true ↔ n.Prime :=
  DetPrimality.millerDet_correct_of_GRH_70 LFunction_eq_zero_re n hn

/-- The combined deterministic test (constant 1 below 10¹¹, 7/10 above) decides primality. -/
theorem millerDetBest_correct (n : ℕ) : DetPrimality.millerDetBest n = true ↔ n.Prime :=
  DetPrimality.millerDetBest_correct_of_GRH LFunction_eq_zero_re n

#print axioms charBound_table
#print axioms charBound_eventually
#print axioms subgroupBound_eventually
#print axioms millerDet_70_correct
#print axioms millerDetBest_correct
