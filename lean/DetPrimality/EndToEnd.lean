import DetPrimality.Bach.Assembly
import DetPrimality.Bach.Constant
import DetPrimality.Bach.Constant46
import DetPrimality.Bach.Constant22
import DetPrimality.Bach.ConstantLow
import DetPrimality.Bach.ConstantTwo
import DetPrimality.Miller.Basic
import DetPrimality.Miller.Composite
import DetPrimality.Miller.LLSMiller
import DetPrimality.TonelliShanks.LLSSqrt
import DetPrimality.Bach.R11Asm
import DetPrimality.Bach.R11ZeroSum
import DetPrimality.Bach.R11ZetaX
import DetPrimality.Bach.R11ChiMain
import DetPrimality.Bach.R12M4
import DetPrimality.Miller.R12Miller
import DetPrimality.Miller.LiarIndex
import DetPrimality.Bach.LLSZetaLower
import DetPrimality.Bach.LLSGain
import DetPrimality.TonelliShanks.Basic

/-!
# End-to-end corollaries: GRH ⟹ correctness of the deterministic algorithms

Composes Layer 2 with Layers 3–4 (`Miller`, `TonelliShanks`).  Since round 8 the Miller statement
uses constant `c = 1` (Lamzouri–Li–Soundararajan 2015, Thm 1.1(2); `Bach/LLS*.lean`,
`Miller/LLSMiller.lean`, `Miller/LLSSmall.lean`).  Round 7's
statement used Bach's Theorem 2 form for composite moduli (`CompositeInterface.lean`), proved with
`c = 73/50 = 1.46` in `Bach/ConstantTwo.lean` (`Bach.grh_implies_bach_composite_c146`); versions
with `c = 2` (Bach's constant) and the previous `c = 8` are kept with `_2` / `_8` suffixes.  The
Tonelli–Shanks statements also use `c = 1` since round 8 (`TonelliShanks/LLSSqrt.lean`); the
`c = 8` versions (`Bach.grh_implies_bach_c8`, `Bach/ConstantLow.lean`) are kept with suffix `_8`.  The round-5 versions with constant `22` (`Bach/Constant22.lean`) are
kept with a `_22` suffix.  The round-4 versions with constant `46` (`Bach/Constant46.lean`) are
kept with a `_46` suffix.  The round-3 versions with constant `64` (`Bach.grh_implies_bach_c`,
`Bach/Constant.lean`) are kept with a `_64` suffix, and the round-2 versions with constant `1024`
(`Bach.grh_implies_bach_v2`, `Bach/Assembly.lean`) with a `_1024` suffix.
-/

namespace DetPrimality

/-- Bach's bound with `c = 8`, stated at the rational constant used by the algorithms. -/
theorem bachBound_8_of_GRH (hGRH : DirichletLZerosOnLine) : BachBound ((8 : ℚ) : ℝ) := by
  have h := Bach.grh_implies_bach_c8 hGRH
  norm_num
  exact h

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

/-- Bach's Theorem 2 form (composite moduli) with `c = 73/50`, at the rational constant used by
the algorithm. -/
theorem bachBoundComposite_146_of_GRH (hGRH : DirichletLZerosOnLine) :
    BachBoundCharComposite (((73 / 50 : ℚ)) : ℝ) := by
  have h := Bach.grh_implies_bach_composite_c146 hGRH
  norm_num
  exact h

/-- Bach's Theorem 2 form (composite moduli) with Bach's constant `c = 2`. -/
theorem bachBoundComposite_2_of_GRH (hGRH : DirichletLZerosOnLine) :
    BachBoundCharComposite ((2 : ℚ) : ℝ) := by
  have h := Bach.grh_implies_bach_composite_c2 hGRH
  norm_num
  exact h

/-- Lamzouri–Li–Soundararajan (2015), Theorem 1.1(2), Miller form: under GRH every composite
`n ≥ 3000` and every `χ ≠ 1` mod `n` have some `1 ≤ a < (log n)²` with `χ a ≠ 1` (round 8). -/
theorem bachBoundComposite_one_ge_3000_of_GRH (hGRH : DirichletLZerosOnLine) :
    ∀ n : ℕ, 3000 ≤ n → ¬ n.Prime → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1 :=
  Bach.llsAsm_bachBound_one hGRH Bach.llsZL_main Bach.llsPer_chiUpper Bach.llsGain_main
    Bach.llsElem_weightedLower

/-- **End-to-end (primality).** Under GRH for Dirichlet L-functions, the deterministic Miller
test with constant `1` (bases `2 ≤ a < min(⌈0.480454 · (log₂ n + 1)²⌉, n)`, i.e. about `(ln n)²`)
decides primality.  Lamzouri–Li–Soundararajan's constant; `n < 3000` by a kernel-checked table. -/
theorem millerDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 1 n = true ↔ n.Prime :=
  Miller.llsAsm_millerDet_one_correct' hGRH Bach.llsZL_main Bach.llsPer_chiUpper
    Bach.llsGain_main n

/-- Round-7 version: constant `73/50 = 1.46` (Bach's method, composite form). -/
theorem millerDet_correct_of_GRH_146 (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet (73 / 50) n = true ↔ n.Prime :=
  Miller.millerDet_correct_of_composite (73 / 50) (by norm_num) (bachBoundComposite_146_of_GRH hGRH) n

/-- The deterministic Miller test with Bach's constant `2` is correct under GRH. -/
theorem millerDet_correct_of_GRH_2 (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 2 n = true ↔ n.Prime :=
  Miller.millerDet_correct_of_composite 2 (by norm_num) (bachBoundComposite_2_of_GRH hGRH) n

/-- Round-6 version (constant `8`, unit form `BachBound`). -/
theorem millerDet_correct_of_GRH_8 (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 8 n = true ↔ n.Prime :=
  Miller.millerDet_correct 8 (by norm_num) (bachBound_8_of_GRH hGRH) n

/-- **End-to-end (square roots).** Under GRH, for an odd prime `p` and a square `n` mod `p`,
the deterministic Tonelli–Shanks procedure with constant `1` (non-residue search below about
`(ln p)²`; Lamzouri–Li–Soundararajan Cor. 1.1) returns a square root. -/
theorem sqrtModDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 1 p n = some r ∧ (r : ZMod p) ^ 2 = n :=
  TonelliShanks.llsPrime_sqrtModDet_correct hGRH p hp n

/-- Under GRH, `sqrtModDet 1 p n` returns something iff `n` is a square mod the odd prime `p`. -/
theorem sqrtModDet_isSome_iff_of_GRH (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    (TonelliShanks.sqrtModDet 1 p n).isSome ↔ IsSquare (n : ZMod p) :=
  TonelliShanks.llsPrime_sqrtModDet_isSome_iff hGRH p hp n

/-- Round-6 version (constant `8`). -/
theorem sqrtModDet_correct_of_GRH_8 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 8 p n = some r ∧ (r : ZMod p) ^ 2 = n :=
  TonelliShanks.sqrtModDet_correct (bachBound_8_of_GRH hGRH) (by norm_num) p hp n

/-- Round-6 version (constant `8`). -/
theorem sqrtModDet_isSome_iff_of_GRH_8 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    (TonelliShanks.sqrtModDet 8 p n).isSome ↔ IsSquare (n : ZMod p) :=
  TonelliShanks.sqrtModDet_isSome_iff (bachBound_8_of_GRH hGRH) (by norm_num) p hp n

/-! ### Round-5 versions (constant `22`), kept for reference -/

theorem millerDet_correct_of_GRH_22 (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 22 n = true ↔ n.Prime :=
  Miller.millerDet_correct 22 (by norm_num) (bachBound_22_of_GRH hGRH) n

theorem sqrtModDet_correct_of_GRH_22 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 22 p n = some r ∧ (r : ZMod p) ^ 2 = n :=
  TonelliShanks.sqrtModDet_correct (bachBound_22_of_GRH hGRH) (by norm_num) p hp n

theorem sqrtModDet_isSome_iff_of_GRH_22 (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
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


/-! ### Rounds 11–12: explicit constants below 1 (research/below-one/designB.md, research/barrier/miller4.md) -/

/-- All four designB inputs, discharged under GRH. -/
theorem r11_inputs (hGRH : DirichletLZerosOnLine) :
    Bach.R11ZetaZ ∧ Bach.R11ZetaExplicit ∧ Bach.R11ChiExplicit ∧ Bach.R11ZeroSumGain :=
  ⟨Bach.r11Zs_zeta, Bach.r11Zx_main_of_zetaZ Bach.r11Zs_zeta, Bach.r11Chi_main', Bach.r11Zs_gain⟩

/-- **Explicit `c < 1` for a single character** (designB, Theorem A): under GRH, every `χ ≠ 1` mod `n`
has `χ a ≠ 1` for some `1 ≤ a < c log² n`, for these `(c, N₀)`. -/
theorem charBound_table_of_GRH (hGRH : DirichletLZerosOnLine) :
    (∀ n : ℕ, (10 : ℝ) ^ 9 ≤ n → Bach.R11Bound 0.95 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 10 ≤ n → Bach.R11Bound 0.9 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 11 ≤ n → Bach.R11Bound 0.85 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 13 ≤ n → Bach.R11Bound 0.8 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 14 ≤ n → Bach.R11Bound 0.78 n) := by
  obtain ⟨hZ, hA, hC, hG⟩ := r11_inputs hGRH
  obtain ⟨h1, h2, h3, h4⟩ := Bach.r11Asm_table hGRH hZ hA hC hG
  exact ⟨h1, h2, h3, h4, (Bach.r11Asm_table_low hGRH hZ hA hC hG).2⟩

/-- **Every `c > 0.7772` works eventually** (designB, Theorem B). -/
theorem charBound_eventually_of_GRH (hGRH : DirichletLZerosOnLine) :
    ∀ c : ℝ, 0.7772 < c → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Bach.R11Bound c n := by
  obtain ⟨hZ, hA, hC, hG⟩ := r11_inputs hGRH
  exact Bach.r11Asm_eventually hGRH hZ hA hC hG

/-- **Subgroups of index ≥ 4** (Theorem M4): explicit table. -/
theorem subgroupBound_table_of_GRH (hGRH : DirichletLZerosOnLine) :
    (∀ n : ℕ, (10 : ℝ) ^ 10 ≤ n → Bach.R12Bound 0.75 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 10 ≤ n → Bach.R12Bound 0.72 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 11 ≤ n → Bach.R12Bound 0.7 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 11 ≤ n → Bach.R12Bound 0.68 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 12 ≤ n → Bach.R12Bound 0.66 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 13 ≤ n → Bach.R12Bound 0.65 n) := by
  obtain ⟨hZ, hA, hC, hG⟩ := r11_inputs hGRH
  exact Bach.r12_subgroup_table hGRH hZ hA hC hG

/-- **Subgroups of index ≥ 4: every `c > 0.6417` works eventually.** -/
theorem subgroupBound_eventually_of_GRH (hGRH : DirichletLZerosOnLine) :
    ∀ c : ℝ, 0.6417 < c → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < c * Real.log n ^ 2 ∧
        (¬ IsUnit (a : ZMod n) ∨ ∃ u : (ZMod n)ˣ, (u : ZMod n) = a ∧ u ∉ H) := by
  obtain ⟨hZ, hA, hC, hG⟩ := r11_inputs hGRH
  exact Bach.r12_eventually hGRH hZ hA hC hG

/-- **Deterministic Miller test with constant `7/10`** (bases below about `0.7 (ln n)²`) is correct for
`n ≥ 10¹¹` under GRH (strong liars lie in a subgroup of index ≥ 4: `Miller.liar4_exists_subgroup`). -/
theorem millerDet_correct_of_GRH_70 (hGRH : DirichletLZerosOnLine) (n : ℕ) (hn : (10 : ℝ) ^ 11 ≤ n) :
    Miller.millerDet (7 / 10) n = true ↔ n.Prime := by
  obtain ⟨hZ, hA, hC, hG⟩ := r11_inputs hGRH
  exact Miller.r12_millerDet_correct hGRH hZ hA hC hG
    (fun h1 h2 h3 h4 => Miller.liar4_exists_subgroup h1 h2 h3 h4) n hn

/-- Constant `33/50 = 0.66` for `n ≥ 10¹²`. -/
theorem millerDet_correct_of_GRH_66 (hGRH : DirichletLZerosOnLine) (n : ℕ) (hn : (10 : ℝ) ^ 12 ≤ n) :
    Miller.millerDet (33 / 50) n = true ↔ n.Prime := by
  obtain ⟨hZ, hA, hC, hG⟩ := r11_inputs hGRH
  exact Miller.r12_millerDet_correct_66 hGRH hZ hA hC hG
    (fun h1 h2 h3 h4 => Miller.liar4_exists_subgroup h1 h2 h3 h4) n hn

/-- Constant `13/20 = 0.65` for `n ≥ 10¹³`. -/
theorem millerDet_correct_of_GRH_65 (hGRH : DirichletLZerosOnLine) (n : ℕ) (hn : (10 : ℝ) ^ 13 ≤ n) :
    Miller.millerDet (13 / 20) n = true ↔ n.Prime := by
  obtain ⟨hZ, hA, hC, hG⟩ := r11_inputs hGRH
  exact Miller.r12_millerDet_correct_65 hGRH hZ hA hC hG
    (fun h1 h2 h3 h4 => Miller.liar4_exists_subgroup h1 h2 h3 h4) n hn

/-- The combined test: constant `1` below `10¹¹`, `7/10` from `10¹¹` on. -/
def millerDetBest (n : ℕ) : Bool :=
  if n < 10 ^ 11 then Miller.millerDet 1 n else Miller.millerDet (7 / 10) n

theorem millerDetBest_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    millerDetBest n = true ↔ n.Prime := by
  unfold millerDetBest
  split_ifs with h
  · exact millerDet_correct_of_GRH hGRH n
  · exact millerDet_correct_of_GRH_70 hGRH n (by exact_mod_cast Nat.le_of_not_lt h)

end DetPrimality
