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
