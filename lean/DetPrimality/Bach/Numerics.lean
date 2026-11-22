import Mathlib

/-!
# Numerics: `∑ Λ(n)/n² ≤ 1`

Proves `tsum_vonMangoldt_term_two_le_proof`, the statement of
`DetPrimality.Bach.tsum_vonMangoldt_term_two_le` (Blueprint §4.1).

Method: exact values of `Λ(n)` for `n ≤ 10`, elementary log bounds
(`log 2 < 0.6931471808`, `log y ≤ y - 1`), and for the tail the telescoping bound
`Λ(n)/n² ≤ log n / n² ≤ g(n-1) - g(n)` with `g(m) = (log m + 1)/m` (valid for `n ≥ 4`).
Total bound obtained: `≈ 0.806`.
-/

namespace DetPrimality.Bach.Numerics

open Real Finset

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The real summand `Λ(n)/n²`. -/
noncomputable def a (n : ℕ) : ℝ := Λ n / (n : ℝ) ^ 2

/-- The telescoping majorant `g(m) = (log m + 1)/m`. -/
noncomputable def g (x : ℝ) : ℝ := (Real.log x + 1) / x

lemma a_nonneg (n : ℕ) : 0 ≤ a n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)

lemma norm_term_eq_a (n : ℕ) :
    ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ = a n := by
  rw [LSeries.norm_term_eq]
  split_ifs with h
  · subst h; simp [a]
  · simp only [a, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    congr 1
    norm_num

lemma g_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ g x :=
  div_nonneg (by linarith [Real.log_nonneg hx]) (by linarith)

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- Key telescoping inequality: for `x ≥ 4`, `log x / x² ≤ g(x-1) - g(x)`. -/
lemma log_div_sq_le_g_sub {x : ℝ} (hx : 4 ≤ x) :
    Real.log x / x ^ 2 ≤ g (x - 1) - g x := by
  have hx1 : 0 < x - 1 := by linarith
  have hx0 : 0 < x := by linarith
  -- `log(x-1) ≥ log x - 1/(x-1)`
  have h1 : Real.log x - 1 / (x - 1) ≤ Real.log (x - 1) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < (x - 1) / x by positivity)
    rw [Real.log_div hx1.ne' hx0.ne', inv_div] at this
    have e : 1 - x / (x - 1) = -(1 / (x - 1)) := by field_simp; ring
    linarith
  -- `log x ≥ 4/3 ≥ x/(x-1)`
  have hL4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hL : x ≤ Real.log x * (x - 1) := by
    have : (4 : ℝ) / 3 ≤ Real.log x := by
      rw [log_four] at hL4; linarith [Real.log_two_gt_d9]
    nlinarith
  have step : (Real.log x - 1 / (x - 1) + 1) / (x - 1) ≤ (Real.log (x - 1) + 1) / (x - 1) :=
    div_le_div_of_nonneg_right (by linarith) hx1.le
  have main : Real.log x / x ^ 2 ≤ (Real.log x - 1 / (x - 1) + 1) / (x - 1) - (Real.log x + 1) / x := by
    have key : (Real.log x - 1 / (x - 1) + 1) / (x - 1) - (Real.log x + 1) / x
        - Real.log x / x ^ 2
        = (Real.log x * (x - 1) - x) / (x ^ 2 * (x - 1) ^ 2) := by
      field_simp
      ring
    have : 0 ≤ (Real.log x * (x - 1) - x) / (x ^ 2 * (x - 1) ^ 2) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  unfold g
  linarith

lemma a_le_g_sub {n : ℕ} (hn : 4 ≤ n) : a n ≤ g ((n : ℝ) - 1) - g n := by
  refine le_trans ?_ (log_div_sq_le_g_sub (by exact_mod_cast hn))
  exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (sq_nonneg _)

/-- Partial sums. -/
noncomputable def S (N : ℕ) : ℝ := ∑ n ∈ range N, a n

lemma S_add_g_le (k : ℕ) : S (11 + k) + g ((11 + k : ℕ) - 1 : ℝ) ≤ S 11 + g 10 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h := a_le_g_sub (n := 11 + k) (by omega)
    have e : 11 + (k + 1) = (11 + k) + 1 := by ring
    rw [e, S, sum_range_succ, ← S]
    have : (((11 + k + 1 : ℕ) : ℝ) - 1) = ((11 + k : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    linarith

lemma vM_two : Λ 2 = Real.log 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; norm_num
lemma vM_three : Λ 3 = Real.log 3 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]; norm_num
lemma vM_five : Λ 5 = Real.log 5 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]; norm_num
lemma vM_seven : Λ 7 = Real.log 7 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]; norm_num
lemma vM_four : Λ 4 = Real.log 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    vM_two]
lemma vM_eight : Λ 8 = Real.log 2 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    vM_two]
lemma vM_nine : Λ 9 = Real.log 3 := by
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    vM_three]
lemma vM_six : Λ 6 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; decide
lemma vM_ten : Λ 10 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; decide

lemma base : S 11 + g 10 ≤ 1 := by
  simp only [S, g, a, sum_range_succ, range_zero, sum_empty]
  simp only [ArithmeticFunction.vonMangoldt_apply_one, vM_two, vM_three, vM_four,
    vM_five, vM_six, vM_seven, vM_eight, vM_nine, vM_ten]
  have l2 := Real.log_two_lt_d9
  have l4 := log_four
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have l3 : Real.log 3 - Real.log 4 ≤ -1 / 4 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)]
  have l5 : Real.log 5 - Real.log 4 ≤ 1 / 4 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)]
  have l7 : Real.log 7 - Real.log 8 ≤ -1 / 8 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num)]
  have l10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  norm_num
  linarith

lemma S_le_one (N : ℕ) : S N ≤ 1 := by
  rcases le_or_gt N 11 with hN | hN
  · have : S N ≤ S 11 :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hN) (fun i _ _ => a_nonneg i)
    linarith [base, g_nonneg (show (1 : ℝ) ≤ 10 by norm_num)]
  · obtain ⟨k, rfl⟩ : ∃ k, N = 11 + k := ⟨N - 11, by omega⟩
    have hg : 0 ≤ g ((11 + k : ℕ) - 1 : ℝ) := g_nonneg (by push_cast; linarith)
    linarith [S_add_g_le k, base]

theorem tsum_vonMangoldt_term_two_le_proof :
    ∑' n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ ≤ 1 := by
  simp_rw [norm_term_eq_a]
  exact Real.tsum_le_of_sum_range_le a_nonneg S_le_one

/-! ## Sharper bound `≤ 3/4` (cut-off `K = 20`, total `≈ 0.735`) -/

lemma S_add_g_le_gen (K : ℕ) (hK : 3 ≤ K) (k : ℕ) :
    S (K + 1 + k) + g ((K + 1 + k : ℕ) - 1 : ℝ) ≤ S (K + 1) + g ((K + 1 : ℕ) - 1 : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h := a_le_g_sub (n := K + 1 + k) (by omega)
    have e : K + 1 + (k + 1) = (K + 1 + k) + 1 := by ring
    rw [e, S, sum_range_succ, ← S]
    have : (((K + 1 + k + 1 : ℕ) : ℝ) - 1) = ((K + 1 + k : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    linarith

lemma S_le_of_base (K : ℕ) (hK : 3 ≤ K) {c : ℝ} (hbase : S (K + 1) + g K ≤ c) (N : ℕ) :
    S N ≤ c := by
  have hb : S (K + 1) + g ((K + 1 : ℕ) - 1 : ℝ) ≤ c := by
    have : (((K + 1 : ℕ) : ℝ) - 1) = (K : ℝ) := by push_cast; ring
    rw [this]; exact hbase
  have hKr : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hgK : 0 ≤ g ((K + 1 : ℕ) - 1 : ℝ) := g_nonneg (by push_cast; linarith)
  rcases le_or_gt N (K + 1) with hN | hN
  · have : S N ≤ S (K + 1) :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hN) (fun i _ _ => a_nonneg i)
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, N = K + 1 + k := ⟨N - (K + 1), by omega⟩
    have hg : 0 ≤ g ((K + 1 + k : ℕ) - 1 : ℝ) := g_nonneg (by push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    linarith [S_add_g_le_gen K hK k]

lemma vM_prime' {p : ℕ} (hp : p.Prime) : Λ p = Real.log p :=
  ArithmeticFunction.vonMangoldt_apply_prime hp

lemma vM_zero_of {n : ℕ} (h : ¬ IsPrimePow n) : Λ n = 0 :=
  ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h

lemma base20 : S 21 + g 20 ≤ 3 / 4 := by
  have v11 : Λ 11 = Real.log 11 := by rw [vM_prime' (by norm_num)]; norm_num
  have v13 : Λ 13 = Real.log 13 := by rw [vM_prime' (by norm_num)]; norm_num
  have v17 : Λ 17 = Real.log 17 := by rw [vM_prime' (by norm_num)]; norm_num
  have v19 : Λ 19 = Real.log 19 := by rw [vM_prime' (by norm_num)]; norm_num
  have v16 : Λ 16 = Real.log 2 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      vM_two]
  have v12 : Λ 12 = 0 := vM_zero_of (by decide)
  have v14 : Λ 14 = 0 := vM_zero_of (by decide)
  have v15 : Λ 15 = 0 := vM_zero_of fun h => by
    have := (Nat.Coprime.isPrimePow_dvd_mul (by norm_num : Nat.Coprime 3 5) h).mp (by norm_num)
    norm_num at this
  have v18 : Λ 18 = 0 := vM_zero_of (by decide)
  have v20 : Λ 20 = 0 := vM_zero_of (by decide)
  simp only [S, g, a, sum_range_succ, range_zero, sum_empty]
  simp only [ArithmeticFunction.vonMangoldt_apply_one, vM_two, vM_three, vM_four,
    vM_five, vM_six, vM_seven, vM_eight, vM_nine, vM_ten, v11, v12, v13, v14, v15, v16, v17,
    v18, v19, v20]
  have l2 := Real.log_two_lt_d9
  have l4 := log_four
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have l16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  have hb : ∀ p q : ℝ, 0 < p → 0 < q → Real.log p - Real.log q ≤ p / q - 1 := by
    intro p q hp hq
    rw [← Real.log_div hp.ne' hq.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hp hq)
  have l3 := hb 3 4 (by norm_num) (by norm_num)
  have l5 := hb 5 4 (by norm_num) (by norm_num)
  have l7 := hb 7 8 (by norm_num) (by norm_num)
  have l11 := hb 11 8 (by norm_num) (by norm_num)
  have l13 := hb 13 16 (by norm_num) (by norm_num)
  have l17 := hb 17 16 (by norm_num) (by norm_num)
  have l19 := hb 19 16 (by norm_num) (by norm_num)
  have l10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    rw [show (20 : ℝ) = 4 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), l4]
  norm_num at l3 l5 l7 l11 l13 l17 l19 ⊢
  linarith

/-- Sharper version: `∑ Λ(n)/n² ≤ 3/4` (true value `≈ 0.5699`). -/
theorem tsum_vonMangoldt_term_two_le_three_quarters :
    ∑' n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ ≤ 3 / 4 := by
  simp_rw [norm_term_eq_a]
  exact Real.tsum_le_of_sum_range_le a_nonneg (S_le_of_base 20 (by norm_num) (by exact_mod_cast base20))

end DetPrimality.Bach.Numerics
