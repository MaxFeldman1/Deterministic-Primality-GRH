import DetPrimality.Bach.LLSZetaConst

/-!
# Numerical inputs for designB Lemma 2 (trivial-zero series, `log π`)

* `r11Zx_t n i = 1/(2i+3/2)^n`: `T_n = ∑_i 1/(2i+3/2)^n = ∑_{m ≥ 1} (2m - 1/2)^{-n}`, with
  `T₂ ≤ 0.6355`, `T₃ ≤ 0.34`, `T₄ ≤ 0.20595`, `T₂ ≥ 4/9`, `T₄ ≥ 16/81`;
* `r11Zx_u0 i = 1/(2i+3/2) - 1/(2i+4)`, `∑ ≤ 0.76`;
* `r11Zx_u1 i = 1/(2i+3/2) - 1/(2i+2)`, `∑ ≤ 0.25435`;
* `log π ≤ 1.1449`.
-/

namespace DetPrimality.Bach

theorem r11Zx_tele (a G : ℕ → ℝ) (K : ℕ) (ha : ∀ n, 0 ≤ a n)
    (hG : ∀ n, K ≤ n → 0 ≤ G n) (h : ∀ n, K ≤ n → a (n + 1) ≤ G n - G (n + 1)) :
    Summable a ∧ ∑' i, a i ≤ ∑ i ∈ Finset.range (K + 1), a i + G K :=
  ⟨summable_of_sum_range_le ha (szs_sum_range_le_of_tele a G K ha hG h),
    Real.tsum_le_of_sum_range_le ha (szs_sum_range_le_of_tele a G K ha hG h)⟩

/-- `1/(2i+3/2)^n`. -/
noncomputable def r11Zx_t (n : ℕ) (i : ℕ) : ℝ := 1 / (2 * (i : ℝ) + 3 / 2) ^ n

theorem r11Zx_t_nonneg (n i : ℕ) : 0 ≤ r11Zx_t n i := by unfold r11Zx_t; positivity

theorem r11Zx_t_tele (n : ℕ) (hn : 2 ≤ n) (K : ℕ) :
    Summable (r11Zx_t n) ∧ ∑' i, r11Zx_t n i ≤ ∑ i ∈ Finset.range (K + 1), r11Zx_t n i
      + 1 / ((2 * (K : ℝ) + 7 / 2) ^ (n - 2) * (4 * K + 5)) := by
  set c : ℝ := 1 / (2 * (K : ℝ) + 7 / 2) ^ (n - 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have key : ∀ i, K ≤ i → r11Zx_t n (i + 1)
      ≤ c / (4 * (i : ℝ) + 5) - c / (4 * ((i + 1 : ℕ) : ℝ) + 5) := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hKi : (K : ℝ) ≤ i := by exact_mod_cast hi
    have hu : (2 * ((i + 1 : ℕ) : ℝ) + 3 / 2) = 2 * (i : ℝ) + 7 / 2 := by push_cast; ring
    have hpow : (2 * (K : ℝ) + 7 / 2) ^ (n - 2) ≤ (2 * (i : ℝ) + 7 / 2) ^ (n - 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hsplit : (2 * (i : ℝ) + 7 / 2) ^ n
        = (2 * (i : ℝ) + 7 / 2) ^ (n - 2) * (2 * (i : ℝ) + 7 / 2) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have h1 : r11Zx_t n (i + 1) ≤ c * (1 / (2 * (i : ℝ) + 7 / 2) ^ 2) := by
      rw [r11Zx_t, hu, hsplit, hc, one_div_mul_one_div]
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_right hpow (by positivity))
    have h2 : 1 / (2 * (i : ℝ) + 7 / 2) ^ 2
        ≤ 1 / (4 * (i : ℝ) + 5) - 1 / (4 * ((i + 1 : ℕ) : ℝ) + 5) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (i : ℝ)]
    calc r11Zx_t n (i + 1) ≤ c * (1 / (2 * (i : ℝ) + 7 / 2) ^ 2) := h1
      _ ≤ c * (1 / (4 * (i : ℝ) + 5) - 1 / (4 * ((i + 1 : ℕ) : ℝ) + 5)) :=
          mul_le_mul_of_nonneg_left h2 hc0
      _ = _ := by ring
  have h := r11Zx_tele (r11Zx_t n) (fun i => c / (4 * (i : ℝ) + 5)) K (r11Zx_t_nonneg n)
    (fun i _ => by positivity) key
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [hc, div_div]

theorem r11Zx_t_summable {n : ℕ} (hn : 2 ≤ n) : Summable (r11Zx_t n) := (r11Zx_t_tele n hn 0).1

theorem r11Zx_T2_le : ∑' i, r11Zx_t 2 i ≤ 0.6355 := by
  refine (r11Zx_t_tele 2 le_rfl 9).2.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, r11Zx_t]
  norm_num

theorem r11Zx_T3_le : ∑' i, r11Zx_t 3 i ≤ 0.34 := by
  refine (r11Zx_t_tele 3 (by norm_num) 5).2.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, r11Zx_t]
  norm_num

theorem r11Zx_T4_le : ∑' i, r11Zx_t 4 i ≤ 0.20595 := by
  refine (r11Zx_t_tele 4 (by norm_num) 9).2.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, r11Zx_t]
  norm_num

theorem r11Zx_T_ge {n : ℕ} (hn : 2 ≤ n) : 1 / (3 / 2 : ℝ) ^ n ≤ ∑' i, r11Zx_t n i := by
  have h := (r11Zx_t_summable hn).le_tsum 0 (fun j _ => r11Zx_t_nonneg n j)
  simpa [r11Zx_t] using h

/-- `1/(2i+3/2) - 1/(2i+4)`. -/
noncomputable def r11Zx_u0 (i : ℕ) : ℝ := 1 / (2 * (i : ℝ) + 3 / 2) - 1 / (2 * (i : ℝ) + 4)

/-- `1/(2i+3/2) - 1/(2i+2)`. -/
noncomputable def r11Zx_u1 (i : ℕ) : ℝ := 1 / (2 * (i : ℝ) + 3 / 2) - 1 / (2 * (i : ℝ) + 2)

theorem r11Zx_u0_nonneg (i : ℕ) : 0 ≤ r11Zx_u0 i := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  unfold r11Zx_u0
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))

theorem r11Zx_u1_nonneg (i : ℕ) : 0 ≤ r11Zx_u1 i := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  unfold r11Zx_u1
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))

theorem r11Zx_u0_tele (K : ℕ) :
    Summable r11Zx_u0 ∧ ∑' i, r11Zx_u0 i ≤ ∑ i ∈ Finset.range (K + 1), r11Zx_u0 i
      + 5 / (8 * (K : ℝ) + 12) := by
  refine r11Zx_tele r11Zx_u0 (fun i => 5 / (8 * (i : ℝ) + 12)) K r11Zx_u0_nonneg
    (fun i _ => by positivity) (fun i _ => ?_)
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  simp only [r11Zx_u0]
  push_cast
  rw [div_sub_div _ _ (by positivity) (by positivity),
    div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (i : ℝ), mul_nonneg hi0 hi0, mul_nonneg hi0 (mul_nonneg hi0 hi0)]

theorem r11Zx_u1_tele (K : ℕ) :
    Summable r11Zx_u1 ∧ ∑' i, r11Zx_u1 i ≤ ∑ i ∈ Finset.range (K + 1), r11Zx_u1 i
      + 1 / (8 * (K : ℝ) + 11) := by
  refine r11Zx_tele r11Zx_u1 (fun i => 1 / (8 * (i : ℝ) + 11)) K r11Zx_u1_nonneg
    (fun i _ => by positivity) (fun i _ => ?_)
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  simp only [r11Zx_u1]
  push_cast
  rw [div_sub_div _ _ (by positivity) (by positivity),
    div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (i : ℝ), mul_nonneg hi0 hi0, mul_nonneg hi0 (mul_nonneg hi0 hi0)]

theorem r11Zx_U0_le : ∑' i, r11Zx_u0 i ≤ 0.76 := by
  refine (r11Zx_u0_tele 9).2.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, r11Zx_u0]
  norm_num

theorem r11Zx_U1_le : ∑' i, r11Zx_u1 i ≤ 0.25435 := by
  refine (r11Zx_u1_tele 9).2.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, r11Zx_u1]
  norm_num

theorem r11Zx_cert_pi : 3141593 ^ 4096 ≤ 2 ^ 6765 * 1000000 ^ 4096 := by decide +kernel

theorem r11Zx_log_pi_le : Real.log Real.pi ≤ 1.1449 := by
  have h1 : Real.pi ^ 4096 ≤ (2 : ℝ) ^ 6765 := by
    have h2 : Real.pi ^ 4096 ≤ (3.141593 : ℝ) ^ 4096 :=
      pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 4096
    have h3 : (3.141593 : ℝ) ^ 4096 ≤ (2 : ℝ) ^ 6765 := by
      rw [show (3.141593 : ℝ) = 3141593 / 1000000 by norm_num, div_pow,
        div_le_iff₀ (by positivity)]
      exact_mod_cast r11Zx_cert_pi
    exact h2.trans h3
  have := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith [Real.log_two_lt_d9]

end DetPrimality.Bach
