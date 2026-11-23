import DetPrimality.Bach.R11Defs
import DetPrimality.Bach.SharpZeroSum

/-!
# Round 11, Lemma 3 (designB (3.2)): shared definitions

* `r11Chi_F k = ∑ Λ(n) log^k n · n^{-3/2}` (`F_k` of designB §2).
-/

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `F_k = ∑_n Λ(n) log^k n · n^{-3/2}`. -/
noncomputable def r11Chi_F (k : ℕ) : ℝ :=
  ∑' n : ℕ, Λ n * Real.log n ^ k / (n : ℝ) ^ (3 / 2 : ℝ)

end DetPrimality.Bach
