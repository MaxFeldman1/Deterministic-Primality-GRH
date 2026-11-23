import Mathlib
import DetPrimality.Bach.R12M4Core

/-!
# Round 12 (miller4.md), part 3: from the basic inequality to `c` (Lemma M9)

Same parametrisation as `R11AsmReal`: `k² ≤ c`, `W = √(k log n)`, `X = W⁴ ≤ c log² n`, `W ≥ W₀`,
`m = (W/W₀)^{1/3}`.  `r12_row`: if `r12Err a b d (1/k) W₀ ℓ₁ < (7.4904 - 6/k) W² - 1.5403 W + 74.0104`
for all `W ≥ W₀` (in a range `P`), then `R12Bound c n` whenever `W₀² ≤ k log n` (in that range).
-/

set_option exponentiation.threshold 5000

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- The subgroup statement: every subgroup `H ≤ (ZMod n)ˣ` of index `≥ 4` misses some
`1 ≤ a < c log² n` (either `a` is not a unit mod `n`, or it is a unit not in `H`). -/
def R12Bound (c : ℝ) (n : ℕ) : Prop :=
  ∀ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index →
    ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < c * Real.log n ^ 2 ∧
      (¬ IsUnit (a : ZMod n) ∨ ∃ u : (ZMod n)ˣ, (u : ZMod n) = a ∧ u ∉ H)

/-- The value of the error term at `(W₀, ℓ₁)`; `ik = 1/k`. -/
noncomputable def r12Err (a b d ik W₀ l₁ : ℝ) : ℝ :=
  72 * a * (l₁ ^ 1 / W₀ ^ 2) + (168 * a + 24 * d) * (l₁ ^ 0 / W₀ ^ 2)
    + 36 * b * (l₁ ^ 1 / W₀ ^ 4) + 48 * b * (l₁ ^ 0 / W₀ ^ 4)
    + ik * ((l₁ + 1.3863) ^ 3 / W₀ ^ 2)
    + 1.891 * ((l₁ + 1.3863) ^ 3 / W₀ ^ 4) + 28.078 * ((l₁ + 1.3863) ^ 2 / W₀ ^ 4)
    + 100.011 * ((l₁ + 1.3863) ^ 1 / W₀ ^ 4) + 225.055 * (l₁ ^ 0 / W₀ ^ 4)
    + 29.018 * (l₁ ^ 1 / W₀ ^ 3) + 12.912 * (l₁ ^ 0 / W₀ ^ 3)
    + 20.38 * (l₁ ^ 1 / W₀ ^ 4) + 10.413 * (l₁ ^ 2 / W₀ ^ 4) + 2.362 * (l₁ ^ 3 / W₀ ^ 4)

/-- **miller4.md Lemma M9**, real-variable form. -/
theorem r12_real {W W₀ m ik a b d L T l l₁ lam : ℝ} (hW₀ : 0 < W₀) (hm : 1 ≤ m)
    (hW : W = W₀ * m ^ 3) (hik : 0 ≤ ik) (hL : L = ik * W ^ 2) (hl0 : 0 ≤ l)
    (hl : l ≤ l₁ * m ^ 2) (hlam0 : 0 ≤ lam) (hlam : lam ≤ (l₁ + 1.3863) * m ^ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hT : T ≤ a * (3 * l + 7) / W ^ 2 + b * (1.5 * l + 2) / W ^ 4 + d / W ^ 2)
    (hP : 7.4904 * W ^ 6 - 1.5403 * W ^ 5 + 74.0104 * W ^ 4
      ≤ 6 * L * W ^ 4 + 24 * T * W ^ 4 + (L + 1.30) * lam ^ 3 + 27.93 * lam ^ 2
        + 98.73 * lam + 198.31 + 16.3849 * (1.771 * l + 0.788) * W
        + 7.6872 * (1.771 * l + 0.788) + 5.5452 * (1.771 * l ^ 2 + 0.296 * l + 2.561)
        + 4 / 3 * (1.771 * l ^ 3 + 0.444 * l ^ 2 + 3.843 * l + 3.8915)
        + 1 / 3 * (1.771 * lam ^ 3 + 0.444 * lam ^ 2 + 3.843 * lam + 3.8915)) :
    (7.4904 - 6 * ik) * W ^ 2 - 1.5403 * W + 74.0104 ≤ r12Err a b d ik W₀ l₁ := by
  have hm0 : 0 < m := by linarith
  have hW0 : 0 < W := by rw [hW]; positivity
  have hT' : T * W ^ 4 ≤ a * (3 * l + 7) * W ^ 2 + b * (1.5 * l + 2) + d * W ^ 2 := by
    calc T * W ^ 4
        ≤ (a * (3 * l + 7) / W ^ 2 + b * (1.5 * l + 2) / W ^ 4 + d / W ^ 2) * W ^ 4 :=
          mul_le_mul_of_nonneg_right hT (by positivity)
      _ = a * (3 * l + 7) * W ^ 2 + b * (1.5 * l + 2) + d * W ^ 2 := by
          field_simp
  have M := fun (i j k : ℕ) (hij : 2 * i ≤ 3 * j) (hjk : j + k = 4) =>
    r11Asm_mono hl0 hl hW₀ hm hW i j k hij hjk
  have N := fun (i j k : ℕ) (hij : 2 * i ≤ 3 * j) (hjk : j + k = 4) =>
    r11Asm_mono hlam0 hlam hW₀ hm hW i j k hij hjk
  have f1 := mul_le_mul_of_nonneg_left (M 1 2 2 (by norm_num) (by norm_num)) ha
  have f2 := mul_le_mul_of_nonneg_left (M 0 2 2 (by norm_num) (by norm_num)) ha
  have f2d := mul_le_mul_of_nonneg_left (M 0 2 2 (by norm_num) (by norm_num)) hd
  have f3 := mul_le_mul_of_nonneg_left (M 1 4 0 (by norm_num) (by norm_num)) hb
  have f4 := mul_le_mul_of_nonneg_left (M 0 4 0 (by norm_num) (by norm_num)) hb
  have f5 := mul_le_mul_of_nonneg_left (N 3 2 2 (by norm_num) (by norm_num)) hik
  have g3 := N 3 4 0 (by norm_num) (by norm_num)
  have g2 := N 2 4 0 (by norm_num) (by norm_num)
  have g1 := N 1 4 0 (by norm_num) (by norm_num)
  have g0 := M 0 4 0 (by norm_num) (by norm_num)
  have h1 := M 1 3 1 (by norm_num) (by norm_num)
  have h0 := M 0 3 1 (by norm_num) (by norm_num)
  have k1 := M 1 4 0 (by norm_num) (by norm_num)
  have k2 := M 2 4 0 (by norm_num) (by norm_num)
  have k3 := M 3 4 0 (by norm_num) (by norm_num)
  subst hL
  have hfin : ((7.4904 - 6 * ik) * W ^ 2 - 1.5403 * W + 74.0104) * W ^ 4
      ≤ r12Err a b d ik W₀ l₁ * W ^ 4 := by
    unfold r12Err
    have p1 : 0 ≤ l ^ 2 := sq_nonneg l
    have p2 : 0 ≤ l * W := mul_nonneg hl0 hW0.le
    have p3 : 0 ≤ l ^ 3 := by positivity
    have p4 : 0 ≤ lam ^ 2 := sq_nonneg lam
    have p5 : 0 ≤ lam ^ 3 := by positivity
    linarith
  exact le_of_mul_le_mul_right hfin (by positivity)

/-! ## One row of the table -/

theorem r12_row (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : 0 ≤ d)
    {c k W₀ l₁ : ℝ}
    (hT : ∀ X : ℝ, W₀ ^ 4 ≤ X → r11T X
      ≤ a * (3 * Real.log X + 7) / √X + b * (1.5 * Real.log X + 2) / X + d / √X)
    (P : ℝ → Prop) (hk0 : 0 < k) (hk1 : k ≤ 1) (hkc : k ^ 2 ≤ c)
    (hW₀ : 3 ≤ W₀) (hl₁ : Real.log (W₀ ^ 4) ≤ l₁) (h6 : 6 ≤ l₁)
    (hF : ∀ W : ℝ, W₀ ≤ W → P W → r12Err a b d (1 / k) W₀ l₁
      < (7.4904 - 6 * (1 / k)) * W ^ 2 - 1.5403 * W + 74.0104)
    (n : ℕ) (hn : W₀ ^ 2 ≤ k * Real.log n) (hP : P (√(k * Real.log n))) : R12Bound c n := by
  intro H h4
  by_contra hcon
  set L := Real.log n with hLdef
  set W := √(k * L) with hWdef
  have hW₀0 : 0 < W₀ := by linarith
  have h9 : (9 : ℝ) ≤ W₀ ^ 2 := by nlinarith
  have hkL : 9 ≤ k * L := h9.trans hn
  have hL9 : 9 ≤ L := by nlinarith
  have hWsq : W ^ 2 = k * L := Real.sq_sqrt (by linarith)
  have hWnn : 0 ≤ W := Real.sqrt_nonneg _
  have hWW₀ : W₀ ≤ W :=
    (pow_le_pow_iff_left₀ hW₀0.le hWnn two_ne_zero).mp (by rw [hWsq]; exact hn)
  have hW3 : 3 ≤ W := hW₀.trans hWW₀
  have hW0 : 0 < W := by linarith
  have hn2 : 2 < n := by
    by_contra hle
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    have hl2 := Real.log_two_lt_d9
    rcases hcases with h0 | h0 | h0 <;> rw [hLdef, h0] at hL9
    · simp at hL9; linarith
    · simp at hL9; linarith
    · push_cast at hL9; linarith
  have hW4 : W ^ 4 ≤ c * L ^ 2 := by
    have e : W ^ 4 = k ^ 2 * L ^ 2 := by
      rw [show W ^ 4 = (W ^ 2) ^ 2 by ring, hWsq]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hkc (sq_nonneg L)
  have h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < W ^ 4 →
      IsUnit (a : ZMod n) ∧ ∀ u : (ZMod n)ˣ, (u : ZMod n) = a → u ∈ H := by
    intro a ha hlt
    have hlt' : (a : ℝ) < c * L ^ 2 := lt_of_lt_of_le hlt hW4
    constructor
    · by_contra hu
      exact hcon ⟨a, ha, hlt', Or.inl hu⟩
    · intro u hu
      by_contra hmem
      exact hcon ⟨a, ha, hlt', Or.inr ⟨u, hu, hmem⟩⟩
  have core := r12_core hGRH hZ hA hC hG hn2 H h4 hW3 h
  simp only [r11Asm_r1, r11Asm_r2, r11Asm_r3] at core
  -- the scaling parameter
  have hratio : 1 ≤ W / W₀ := by rw [le_div_iff₀ hW₀0]; linarith
  set m := (W / W₀) ^ ((1 : ℝ) / 3) with hmdef
  have hm1 : 1 ≤ m := Real.one_le_rpow hratio (by norm_num)
  have hm0 : 0 < m := by linarith
  have hm3 : m ^ 3 = W / W₀ := by
    rw [hmdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hWm : W = W₀ * m ^ 3 := by rw [hm3]; field_simp
  have hlogm : 2 * Real.log m ≤ m ^ 2 - 1 := by
    have := Real.log_le_sub_one_of_pos (pow_pos hm0 2)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlW : Real.log (W ^ 4) = Real.log (W₀ ^ 4) + 12 * Real.log m := by
    rw [Real.log_pow, Real.log_pow, hWm, Real.log_mul hW₀0.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have hl : Real.log (W ^ 4) ≤ l₁ * m ^ 2 := by
    rw [hlW]
    nlinarith
  have hW41 : (81 : ℝ) ≤ W ^ 4 := by
    calc (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ W ^ 4 := pow_le_pow_left₀ (by norm_num) hW3 4
  have hl0 : 0 ≤ Real.log (W ^ 4) := Real.log_nonneg (by linarith)
  have hlamE : Real.log (4 * W ^ 4) = Real.log 4 + Real.log (W ^ 4) :=
    Real.log_mul (by norm_num) (by positivity)
  have hlam0 : 0 ≤ Real.log (4 * W ^ 4) := Real.log_nonneg (by linarith)
  have hlam : Real.log (4 * W ^ 4) ≤ (l₁ + 1.3863) * m ^ 2 := by
    rw [hlamE]
    have := r12_log4_le
    nlinarith
  have hsq : √(W ^ 4) = W ^ 2 := by
    rw [show W ^ 4 = (W ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hTW := hT (W ^ 4) (pow_le_pow_left₀ hW₀0.le hWW₀ 4)
  rw [hsq] at hTW
  have hLW : L = 1 / k * W ^ 2 := by rw [hWsq]; field_simp
  have real := r12_real hW₀0 hm1 hWm (by positivity) hLW hl0 hl hlam0 hlam ha hb hd hTW core
  exact absurd real (not_le.mpr (hF W hWW₀ hP))

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r12_row
