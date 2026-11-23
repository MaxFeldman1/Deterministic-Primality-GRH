theorem r12_row_75 (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) :
    ∀ n : ℕ, (10 : ℝ) ^ 10 ≤ n → R12Bound 0.75 n := by
  intro n hn
  have hL := r11Asm_log_ge_of_pow hn
  have hn0 : ((((446 : ℕ) : ℝ) / 100) ^ 2 ≤ 0.86602 * Real.log n) := by
    norm_num at hL ⊢; linarith
  refine r12_rowB hGRH hZ hA hC hG (c := 0.75) (k := 0.86602)
      (W₀ := ((446 : ℕ) : ℝ) / 100) (l₁ := ((600 : ℕ) : ℝ) / 100) (fun _ => True)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r11Asm_log4_le 446 600 (by norm_num) (by decide +kernel)) (by norm_num) ?_ n hn0 trivial
  intro W h0 _
  norm_num [r12Err] at h0 ⊢
  nlinarith [sq_nonneg (W - 4.46)]

theorem r12_row_72 (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) :
    ∀ n : ℕ, (10 : ℝ) ^ 10 ≤ n → R12Bound 0.72 n := by
  intro n hn
  have hL := r11Asm_log_ge_of_pow hn
  have hn0 : ((((442 : ℕ) : ℝ) / 100) ^ 2 ≤ 0.84852 * Real.log n) := by
    norm_num at hL ⊢; linarith
  refine r12_rowB hGRH hZ hA hC hG (c := 0.72) (k := 0.84852)
      (W₀ := ((442 : ℕ) : ℝ) / 100) (l₁ := ((600 : ℕ) : ℝ) / 100) (fun _ => True)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r11Asm_log4_le 442 600 (by norm_num) (by decide +kernel)) (by norm_num) ?_ n hn0 trivial
  intro W h0 _
  norm_num [r12Err] at h0 ⊢
  nlinarith [sq_nonneg (W - 4.42)]

theorem r12_row_70 (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) :
    ∀ n : ℕ, (10 : ℝ) ^ 11 ≤ n → R12Bound 0.7 n := by
  intro n hn
  have hL := r11Asm_log_ge_of_pow hn
  have hn0 : ((((460 : ℕ) : ℝ) / 100) ^ 2 ≤ 0.83666 * Real.log n) := by
    norm_num at hL ⊢; linarith
  refine r12_rowB hGRH hZ hA hC hG (c := 0.7) (k := 0.83666)
      (W₀ := ((460 : ℕ) : ℝ) / 100) (l₁ := ((611 : ℕ) : ℝ) / 100) (fun _ => True)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r11Asm_log4_le 460 611 (by norm_num) (by decide +kernel)) (by norm_num) ?_ n hn0 trivial
  intro W h0 _
  norm_num [r12Err] at h0 ⊢
  nlinarith [sq_nonneg (W - 4.6)]

theorem r12_row_68 (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) :
    ∀ n : ℕ, (10 : ℝ) ^ 11 ≤ n → R12Bound 0.68 n := by
  intro n hn
  have hL := r11Asm_log_ge_of_pow hn
  have hn0 : ((((457 : ℕ) : ℝ) / 100) ^ 2 ≤ 0.82462 * Real.log n) := by
    norm_num at hL ⊢; linarith
  refine r12_rowB hGRH hZ hA hC hG (c := 0.68) (k := 0.82462)
      (W₀ := ((457 : ℕ) : ℝ) / 100) (l₁ := ((608 : ℕ) : ℝ) / 100) (fun _ => True)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r11Asm_log4_le 457 608 (by norm_num) (by decide +kernel)) (by norm_num) ?_ n hn0 trivial
  intro W h0 _
  norm_num [r12Err] at h0 ⊢
  nlinarith [sq_nonneg (W - 4.57)]

theorem r12_row_66 (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) :
    ∀ n : ℕ, (10 : ℝ) ^ 12 ≤ n → R12Bound 0.66 n := by
  intro n hn
  have hL := r11Asm_log_ge_of_pow hn
  have hn0 : ((((473 : ℕ) : ℝ) / 100) ^ 2 ≤ 0.8124 * Real.log n) := by
    norm_num at hL ⊢; linarith
  refine r12_rowB hGRH hZ hA hC hG (c := 0.66) (k := 0.8124)
      (W₀ := ((473 : ℕ) : ℝ) / 100) (l₁ := ((622 : ℕ) : ℝ) / 100) (fun _ => True)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (r11Asm_log4_le 473 622 (by norm_num) (by decide +kernel)) (by norm_num) ?_ n hn0 trivial
  intro W h0 _
  norm_num [r12Err] at h0 ⊢
  nlinarith [sq_nonneg (W - 7.35)]

theorem r12_row_65 (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) :
    ∀ n : ℕ, (10 : ℝ) ^ 13 ≤ n → R12Bound 0.65 n := by
  intro n hn
  have hL := r11Asm_log_ge_of_pow hn
  have hn0 : ((((491 : ℕ) : ℝ) / 100) ^ 2 ≤ 0.80622 * Real.log n) := by
    norm_num at hL ⊢; linarith
  by_cases h0 : √(0.80622 * Real.log n) ≤ 8.63
  · refine r12_rowB hGRH hZ hA hC hG (c := 0.65) (k := 0.80622)
        (W₀ := ((491 : ℕ) : ℝ) / 100) (l₁ := ((637 : ℕ) : ℝ) / 100) (fun W => W ≤ (8.63 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (r11Asm_log4_le 491 637 (by norm_num) (by decide +kernel)) (by norm_num) ?_ n hn0 h0
    intro W h0 h1
    have h1' : W ≤ 8.63 := h1
    norm_num [r12Err] at h0 ⊢
    nlinarith [sq_nonneg (W - 8.63)]
  · have hn1 : ((((863 : ℕ) : ℝ) / 100) ^ 2 ≤ 0.80622 * Real.log n) := by
      have := (Real.lt_sqrt (by norm_num)).mp (not_le.mp h0)
      norm_num at this ⊢; linarith
    refine r12_rowB hGRH hZ hA hC hG (c := 0.65) (k := 0.80622)
        (W₀ := ((863 : ℕ) : ℝ) / 100) (l₁ := ((863 : ℕ) : ℝ) / 100) (fun _ => True)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (r11Asm_log4_le 863 863 (by norm_num) (by decide +kernel)) (by norm_num) ?_ n hn1 trivial
    intro W h0 _
    norm_num [r12Err] at h0 ⊢
    nlinarith [sq_nonneg (W - 15.96)]
