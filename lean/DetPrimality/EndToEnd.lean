import DetPrimality.Bach.Assembly
import DetPrimality.Bach.Constant
import DetPrimality.Bach.Constant46
import DetPrimality.Bach.Constant22
import DetPrimality.Miller.Basic
import DetPrimality.TonelliShanks.Basic

/-!
# End-to-end corollaries: GRH ⟹ correctness of the deterministic algorithms

Composes Layer 2 with Layers 3–4 (`Miller`, `TonelliShanks`).  Since round 5 the main
statements use the sorry-free chain `Bach.grh_implies_bach_c22 : GRHImpliesBach 22`
(`Bach/Constant22.lean`).  The round-4 versions with constant `46` (`Bach/Constant46.lean`) are
kept with a `_46` suffix.  The round-3 versions with constant `64` (`Bach.grh_implies_bach_c`,
`Bach/Constant.lean`) are kept with a `_64` suffix, and the round-2 versions with constant `1024`
(`Bach.grh_implies_bach_v2`, `Bach/Assembly.lean`) with a `_1024` suffix.
-/

namespace DetPrimality

/-- Bach's bound with `c = 22`, stated at the rational constant used by the algorithms. -/
theorem bachBound_22_of_GRH (hGRH : DirichletLZerosOnLine) : BachBound ((22 : ℚ) : ℝ) := by
  have h := Bach.grh_implies_bach_c22 hGRH
  norm_num
  exact h

/-- Bach's bound with `c = 46`, stated at the rational constant used by the algorithms. -/
theorem bachBound_46_of_GRH (hGRH : DirichletLZerosOnLine) : BachBound ((46 : ℚ) : ℝ) := by
  have h := Bach.grh_implies_bach_c46 hGRH
  norm_num
  exact h

/-- Bach's bound with `c = 64`, stated at the rational constant used by the algorithms. -/
theorem bachBound_64_of_GRH (hGRH : DirichletLZerosOnLine) : BachBound ((64 : ℚ) : ℝ) := by
  have h := Bach.grh_implies_bach_c hGRH
  norm_num
  exact h

/-- Bach's bound with `c = 1024`, stated at the rational constant used by the algorithms. -/
theorem bachBound_1024_of_GRH (hGRH : DirichletLZerosOnLine) : BachBound ((1024 : ℚ) : ℝ) := by
  have h := Bach.grh_implies_bach_v2 hGRH
  norm_num
  exact h

/-- **End-to-end (primality).** Under GRH for Dirichlet L-functions, the deterministic Miller
test with constant `22` (bases `2 ≤ a < min(22·(log₂ n + 1)², n)`) decides primality. -/
theorem millerDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 22 n = true ↔ n.Prime :=
  Miller.millerDet_correct 22 (by norm_num) (bachBound_22_of_GRH hGRH) n

/-- **End-to-end (square roots).** Under GRH, for an odd prime `p` and a square `n` mod `p`,
the deterministic Tonelli–Shanks procedure with constant `22` returns a square root. -/
theorem sqrtModDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 22 p n = some r ∧ (r : ZMod p) ^ 2 = n :=
  TonelliShanks.sqrtModDet_correct (bachBound_22_of_GRH hGRH) (by norm_num) p hp n

/-- Under GRH, `sqrtModDet 22 p n` returns something iff `n` is a square mod the odd prime `p`. -/
theorem sqrtModDet_isSome_iff_of_GRH (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    (TonelliShanks.sqrtModDet 22 p n).isSome ↔ IsSquare (n : ZMod p) :=
  TonelliShanks.sqrtModDet_isSome_iff (bachBound_22_of_GRH hGRH) (by norm_num) p hp n

/-! ### Round-4 versions (constant `46`), kept for reference -/

theorem millerDet_correct_of_GRH_46 (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 46 n = true ↔ n.Prime :=
  Miller.millerDet_correct 46 (by norm_num) (bachBound_46_of_GRH hGRH) n

theorem sqrtModDet_correct_of_GRH_46 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 46 p n = some r ∧ (r : ZMod p) ^ 2 = n :=
  TonelliShanks.sqrtModDet_correct (bachBound_46_of_GRH hGRH) (by norm_num) p hp n

theorem sqrtModDet_isSome_iff_of_GRH_46 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    (TonelliShanks.sqrtModDet 46 p n).isSome ↔ IsSquare (n : ZMod p) :=
  TonelliShanks.sqrtModDet_isSome_iff (bachBound_46_of_GRH hGRH) (by norm_num) p hp n

/-! ### Round-3 versions (constant `64`), kept for reference -/

theorem millerDet_correct_of_GRH_64 (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 64 n = true ↔ n.Prime :=
  Miller.millerDet_correct 64 (by norm_num) (bachBound_64_of_GRH hGRH) n

theorem sqrtModDet_correct_of_GRH_64 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 64 p n = some r ∧ (r : ZMod p) ^ 2 = n :=
  TonelliShanks.sqrtModDet_correct (bachBound_64_of_GRH hGRH) (by norm_num) p hp n

theorem sqrtModDet_isSome_iff_of_GRH_64 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    (TonelliShanks.sqrtModDet 64 p n).isSome ↔ IsSquare (n : ZMod p) :=
  TonelliShanks.sqrtModDet_isSome_iff (bachBound_64_of_GRH hGRH) (by norm_num) p hp n

/-! ### Round-2 versions (constant `1024`), kept for reference -/

theorem millerDet_correct_of_GRH_1024 (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 1024 n = true ↔ n.Prime :=
  Miller.millerDet_correct 1024 (by norm_num) (bachBound_1024_of_GRH hGRH) n

theorem sqrtModDet_correct_of_GRH_1024 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 1024 p n = some r ∧ (r : ZMod p) ^ 2 = n :=
  TonelliShanks.sqrtModDet_correct (bachBound_1024_of_GRH hGRH) (by norm_num) p hp n

theorem sqrtModDet_isSome_iff_of_GRH_1024 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    (TonelliShanks.sqrtModDet 1024 p n).isSome ↔ IsSquare (n : ZMod p) :=
  TonelliShanks.sqrtModDet_isSome_iff (bachBound_1024_of_GRH hGRH) (by norm_num) p hp n

end DetPrimality
