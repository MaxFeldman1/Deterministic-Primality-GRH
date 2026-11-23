import Mathlib
import DetPrimality.Bach.R11AsmCore

/-!
# Round 11 assembly, part 2: designB Lemma 9 (from the basic inequality to `c`)

Parametrisation: `k² ≤ c`, `W = √(k log n)` (so `X = W⁴ = k² log² n ≤ c log² n`), `W ≥ W₀`,
`m = (W/W₀)^{1/3} ≥ 1`.  Then `ℓ = log X ≤ ℓ₁ m²` whenever `ℓ₁ ≥ max (log W₀⁴) 6`, so every error
term `ℓ^i / W^j` with `2i ≤ 3j` is at most its value `ℓ₁^i / W₀^j` (`r11Asm_mono`; this is the
monotonicity of `Err_c` in designB Lemma 9).  Result (`r11Asm_row`): if the explicit number
`r11AsmErr a b d (1/k) W₀ ℓ₁` is below `(5.1046 - 4.5/k) W² - 1.1499 W + 55.4247` for all
`W ≥ W₀` (in a range `P`), then `R11Bound c n` for all `n` with `W₀² ≤ k log n` (in that range).

The tail enters through `T(X) ≤ a (3 log X + 7)/√X + b (1.5 log X + 2)/X + d/√X`.
-/

set_option exponentiation.threshold 5000

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-! ## Numerical constants -/

theorem r11Asm_log3_ge : (1.09861 : ℝ) ≤ Real.log 3 := by
  have h : Real.log ((2 : ℝ) ^ 1054) ≤ Real.log ((3 : ℝ) ^ 665) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

theorem r11Asm_log3_le : Real.log 3 ≤ (1.0987 : ℝ) := by
  have h : Real.log ((3 : ℝ) ^ 306) ≤ Real.log ((2 : ℝ) ^ 485) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  have := Real.log_two_lt_d9
  push_cast at h
  linarith

theorem r11Asm_sqrt3_le : √(3 : ℝ) ≤ 1.7320509 := by
  rw [Real.sqrt_le_iff]
  constructor <;> norm_num

theorem r11Asm_log10_ge : (2.30257 : ℝ) ≤ Real.log 10 := by
  have h : Real.log ((2 : ℝ) ^ 485) ≤ Real.log ((10 : ℝ) ^ 146) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

/-- `log x ≤ p/q` from `x^q ≤ 2.7182818283^p`. -/
theorem r11Asm_log_le {x : ℝ} (hx : 0 < x) (p q : ℕ) (hq : 0 < q)
    (h : x ^ q ≤ (2.7182818283 : ℝ) ^ p) : Real.log x ≤ (p : ℝ) / q := by
  rw [Real.log_le_iff_le_exp hx]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : Real.exp ((p : ℝ) / q) ^ q = Real.exp 1 ^ p := by
    rw [← Real.exp_nat_mul, Real.exp_one_pow]
    congr 1
    field_simp
  have h2 : (2.7182818283 : ℝ) ^ p ≤ Real.exp 1 ^ p :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le p
  exact le_of_pow_le_pow_left₀ hq.ne' (Real.exp_pos _).le (by rw [h1]; exact h.trans h2)

theorem r11Asm_log_ge_of_pow {n N : ℕ} (h : (10 : ℝ) ^ N ≤ n) :
    (N : ℝ) * 2.30257 ≤ Real.log n := by
  have h1 : Real.log ((10 : ℝ) ^ N) ≤ Real.log n := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at h1
  have := r11Asm_log10_ge
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-! ## Monotonicity of the error terms -/

theorem r11Asm_mono {u u₁ W W₀ m : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ u₁ * m ^ 2) (hW₀ : 0 < W₀)
    (hm : 1 ≤ m) (hW : W = W₀ * m ^ 3) (i j k : ℕ) (hij : 2 * i ≤ 3 * j) (hjk : j + k = 4) :
    u ^ i * W ^ k ≤ u₁ ^ i / W₀ ^ j * W ^ 4 := by
  have hm0 : 0 < m := by linarith
  have hW0 : 0 < W := by rw [hW]; positivity
  have hu₁ : 0 ≤ u₁ := by
    by_contra hneg
    push Not at hneg
    nlinarith [pow_pos hm0 2]
  have h1 : u ^ i ≤ (u₁ * m ^ 2) ^ i := pow_le_pow_left₀ hu hu1 i
  have h2 : (u₁ * m ^ 2) ^ i = u₁ ^ i * m ^ (2 * i) := by rw [mul_pow, ← pow_mul]
  have h3 : m ^ (2 * i) ≤ m ^ (3 * j) := pow_le_pow_right₀ hm hij
  have h4 : u ^ i ≤ u₁ ^ i * m ^ (3 * j) := by
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have h5 : W ^ j = W₀ ^ j * m ^ (3 * j) := by rw [hW, mul_pow, ← pow_mul]
  have h6 : W ^ 4 = W ^ j * W ^ k := by rw [← pow_add, hjk]
  have e : u₁ ^ i / W₀ ^ j * W ^ 4 = u₁ ^ i * m ^ (3 * j) * W ^ k := by
    rw [h6, h5]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right h4 (by positivity)

/-- The value of the error term at `(W₀, ℓ₁)`; `ik = 1/k`. -/
noncomputable def r11AsmErr (a b d ik W₀ l₁ : ℝ) : ℝ :=
  54 * a * (l₁ ^ 1 / W₀ ^ 2) + (126 * a + 18 * d) * (l₁ ^ 0 / W₀ ^ 2)
    + 27 * b * (l₁ ^ 1 / W₀ ^ 4) + 36 * b * (l₁ ^ 0 / W₀ ^ 4)
    + ik * ((l₁ + 1.0987) ^ 3 / W₀ ^ 2)
    + 3.071 * ((l₁ + 1.0987) ^ 3 / W₀ ^ 4) + 28.374 * ((l₁ + 1.0987) ^ 2 / W₀ ^ 4)
    + 102.573 * ((l₁ + 1.0987) ^ 1 / W₀ ^ 4) + 232.58 * (l₁ ^ 0 / W₀ ^ 4)
    + 21.664 * (l₁ ^ 1 / W₀ ^ 3) + 9.639 * (l₁ ^ 0 / W₀ ^ 3)
    + 22.463 * (l₁ ^ 1 / W₀ ^ 4) + 12.562 * (l₁ ^ 2 / W₀ ^ 4) + 3.542 * (l₁ ^ 3 / W₀ ^ 4)

/-- **designB Lemma 9**, real-variable form. -/
theorem r11Asm_real {W W₀ m ik a b d L T l l₁ lam : ℝ} (hW₀ : 0 < W₀) (hm : 1 ≤ m)
    (hW : W = W₀ * m ^ 3) (hik : 0 ≤ ik) (hL : L = ik * W ^ 2) (hl0 : 0 ≤ l)
    (hl : l ≤ l₁ * m ^ 2) (hlam0 : 0 ≤ lam) (hlam : lam ≤ (l₁ + 1.0987) * m ^ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hT : T ≤ a * (3 * l + 7) / W ^ 2 + b * (1.5 * l + 2) / W ^ 4 + d / W ^ 2)
    (hP : 5.1046 * W ^ 6 - 1.1499 * W ^ 5 + 55.4247 * W ^ 4
      ≤ 4.5 * L * W ^ 4 + 18 * T * W ^ 4 + (L + 1.30) * lam ^ 3 + 27.93 * lam ^ 2
        + 98.73 * lam + 198.31 + 12.2322 * (1.771 * l + 0.788) * W
        + 7.2417 * (1.771 * l + 0.788) + 6.5917 * (1.771 * l ^ 2 + 0.296 * l + 2.561)
        + 2 * (1.771 * l ^ 3 + 0.444 * l ^ 2 + 3.843 * l + 3.8915)
        + (1.771 * lam ^ 3 + 0.444 * lam ^ 2 + 3.843 * lam + 3.8915)) :
    (5.1046 - 4.5 * ik) * W ^ 2 - 1.1499 * W + 55.4247 ≤ r11AsmErr a b d ik W₀ l₁ := by
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
  have hfin : ((5.1046 - 4.5 * ik) * W ^ 2 - 1.1499 * W + 55.4247) * W ^ 4
      ≤ r11AsmErr a b d ik W₀ l₁ * W ^ 4 := by
    unfold r11AsmErr
    have p1 : 0 ≤ l ^ 2 := sq_nonneg l
    have p2 : 0 ≤ l * W := mul_nonneg hl0 hW0.le
    have p3 : 0 ≤ l ^ 3 := by positivity
    have p4 : 0 ≤ lam ^ 2 := sq_nonneg lam
    have p5 : 0 ≤ lam ^ 3 := by positivity
    linarith
  exact le_of_mul_le_mul_right hfin (by positivity)

/-! ## One row of the table -/

theorem r11Asm_row (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : 0 ≤ d)
    {c k W₀ l₁ : ℝ}
    (hT : ∀ X : ℝ, W₀ ^ 4 ≤ X → r11T X
      ≤ a * (3 * Real.log X + 7) / √X + b * (1.5 * Real.log X + 2) / X + d / √X)
    (P : ℝ → Prop) (hk0 : 0 < k) (hk1 : k ≤ 1) (hkc : k ^ 2 ≤ c)
    (hW₀ : 3 ≤ W₀) (hl₁ : Real.log (W₀ ^ 4) ≤ l₁) (h6 : 6 ≤ l₁)
    (hF : ∀ W : ℝ, W₀ ≤ W → P W → r11AsmErr a b d (1 / k) W₀ l₁
      < (5.1046 - 4.5 * (1 / k)) * W ^ 2 - 1.1499 * W + 55.4247)
    (n : ℕ) (hn : W₀ ^ 2 ≤ k * Real.log n) (hP : P (√(k * Real.log n))) : R11Bound c n := by
  intro χ hχ
  by_contra hcon
  push Not at hcon
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
  have h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < W ^ 4 → χ (a : ZMod n) = 1 :=
    fun a ha hlt => hcon a ha (lt_of_lt_of_le hlt hW4)
  have core := r11Asm_core hGRH hZ hA hC hG hn2 χ hχ hW3 h r11Asm_log3_ge r11Asm_sqrt3_le
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
  have hlamE : Real.log (3 * W ^ 4) = Real.log 3 + Real.log (W ^ 4) :=
    Real.log_mul (by norm_num) (by positivity)
  have hlam0 : 0 ≤ Real.log (3 * W ^ 4) := Real.log_nonneg (by linarith)
  have hlam : Real.log (3 * W ^ 4) ≤ (l₁ + 1.0987) * m ^ 2 := by
    rw [hlamE]
    have := r11Asm_log3_le
    nlinarith
  have hsq : √(W ^ 4) = W ^ 2 := by
    rw [show W ^ 4 = (W ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hTW := hT (W ^ 4) (pow_le_pow_left₀ hW₀0.le hWW₀ 4)
  rw [hsq] at hTW
  have hLW : L = 1 / k * W ^ 2 := by rw [hWsq]; field_simp
  have real := r11Asm_real hW₀0 hm1 hWm (by positivity) hLW hl0 hl hlam0 hlam ha hb hd hTW core
  exact absurd real (not_le.mpr (hF W hWW₀ hP))

end DetPrimality.Bach
