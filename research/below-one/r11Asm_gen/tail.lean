
/-- **designB Theorem A** from the tail bound with `c₀ = 2`. -/
theorem r11Asm_table_of_tail (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ)
    (hA : R11ZetaExplicit) (hC : R11ChiExplicit) (hG : R11ZeroSumGain) (hT : R11Tail 2) :
    (∀ n : ℕ, (10 : ℝ) ^ 12 ≤ n → R11Bound 0.95 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 14 ≤ n → R11Bound 0.9 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 16 ≤ n → R11Bound 0.85 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 19 ≤ n → R11Bound 0.8 n) :=
  ⟨r11Asm_rowA_95 hGRH hZ hA hC hG hT, r11Asm_rowA_90 hGRH hZ hA hC hG hT,
    r11Asm_rowA_85 hGRH hZ hA hC hG hT, r11Asm_rowA_80 hGRH hZ hA hC hG hT⟩

/-- **designB Theorem A**, sharper table, with the tail bound proved (`r11TailS_sharp`). -/
theorem r11Asm_table (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ)
    (hA : R11ZetaExplicit) (hC : R11ChiExplicit) (hG : R11ZeroSumGain) :
    (∀ n : ℕ, (10 : ℝ) ^ 9 ≤ n → R11Bound 0.95 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 10 ≤ n → R11Bound 0.9 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 11 ≤ n → R11Bound 0.85 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 13 ≤ n → R11Bound 0.8 n) :=
  ⟨r11Asm_rowB_95 hGRH hZ hA hC hG, r11Asm_rowB_90 hGRH hZ hA hC hG,
    r11Asm_rowB_85 hGRH hZ hA hC hG, r11Asm_rowB_80 hGRH hZ hA hC hG⟩

theorem r11Asm_table_low (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ)
    (hA : R11ZetaExplicit) (hC : R11ChiExplicit) (hG : R11ZeroSumGain) :
    (∀ n : ℕ, (10 : ℝ) ^ 13 ≤ n → R11Bound 0.79 n) ∧
    (∀ n : ℕ, (10 : ℝ) ^ 14 ≤ n → R11Bound 0.78 n) :=
  ⟨r11Asm_rowB_79 hGRH hZ hA hC hG, r11Asm_rowB_78 hGRH hZ hA hC hG⟩

/-- **designB Theorem B** (eventual form): every `c > 0.7772` works for all large `n`. -/
theorem r11Asm_eventually (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ)
    (hA : R11ZetaExplicit) (hC : R11ChiExplicit) (hG : R11ZeroSumGain) :
    ∀ c : ℝ, 0.7772 < c → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → R11Bound c n := by
  intro c hc
  refine ⟨⌈Real.exp (10 ^ 8 / 0.88158)⌉₊, fun n hn => ?_⟩
  have hn' : Real.exp (10 ^ 8 / 0.88158) ≤ n := Nat.ceil_le.mp hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn'
  have hL : (10 : ℝ) ^ 8 / 0.88158 ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn'
  have hnW : ((((1000000 : ℕ) : ℝ) / 100) ^ 2 ≤ 0.88158 * Real.log n) := by
    have := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 0.88158)
    norm_num at this ⊢; linarith
  refine r11Asm_rowB hGRH hZ hA hC hG (c := c) (k := 0.88158)
      (W₀ := ((1000000 : ℕ) : ℝ) / 100) (l₁ := ((3700 : ℕ) : ℝ) / 100) (fun _ => True)
      (by norm_num) (by norm_num) (by norm_num at hc ⊢; linarith) (by norm_num) (by norm_num)
      (r11Asm_log4_le 1000000 3700 (by norm_num) (by decide +kernel)) (by norm_num) ?_ n hnW
      trivial
  intro W h0 _
  norm_num [r11AsmErr] at h0 ⊢
  nlinarith [sq_nonneg (W - 10000)]

/-- The same with the hand-off hypothesis shape (`R11Tail c₀` is not needed: see `r11Tail_two`). -/
theorem r11Asm_eventually_of_tail (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ)
    (hA : R11ZetaExplicit) (hC : R11ChiExplicit) (hG : R11ZeroSumGain) (_hT : R11Tail 2) :
    ∀ c : ℝ, 0.7772 < c → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → R11Bound c n :=
  r11Asm_eventually hGRH hZ hA hC hG

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r11Asm_table_of_tail
#print axioms DetPrimality.Bach.r11Asm_table
#print axioms DetPrimality.Bach.r11Asm_table_low
#print axioms DetPrimality.Bach.r11Asm_eventually
