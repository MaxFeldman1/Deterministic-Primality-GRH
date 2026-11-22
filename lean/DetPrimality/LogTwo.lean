import Mathlib

/-!
# A rational upper bound for `(log 2)²`, for the computable loop bounds

The search bounds `Miller.millerBound` and `TonelliShanks.nonResidueBound` must dominate
`c · (ln n)²`. They work from the bit length `L` of `n` (`n < 2 ^ L`), so `ln n < L · ln 2` and
`c · (ln n)² < c · (ln 2)² · L²`. This file proves `(ln 2)² ≤ 0.480454`, against the true value
`0.4804530…`, so the bounds can use the rational `log2SqUpper` instead of `1`.
-/

namespace DetPrimality

/-- `0.480454`, a rational upper bound for `(log 2)² = 0.48045301…`. -/
def log2SqUpper : ℚ := 480454 / 1000000

theorem log_two_sq_le_log2SqUpper : Real.log 2 ^ 2 ≤ ((log2SqUpper : ℚ) : ℝ) := by
  have h1 := Real.log_two_lt_d9
  have h0 := Real.log_pos one_lt_two
  unfold log2SqUpper
  push_cast
  nlinarith

/-- If `n < 2 ^ L` and `0 ≤ c`, then `c · (ln n)² ≤ ⌈c · log2SqUpper · L²⌉₊`. -/
theorem mul_log_sq_le_ceil {c : ℚ} (hc : 0 ≤ c) {n L : ℕ} (hnL : n < 2 ^ L) :
    (c : ℝ) * Real.log n ^ 2 ≤ ((⌈c * log2SqUpper * (L : ℚ) ^ 2⌉₊ : ℕ) : ℝ) := by
  have hl2 := Real.log_pos one_lt_two
  have hlog : Real.log n ≤ L * Real.log 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, Real.log_zero]; positivity
    rw [← Real.log_pow]
    exact (Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast hnL)).le
  have h0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hsq : Real.log n ^ 2 ≤ (L : ℝ) ^ 2 * Real.log 2 ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h0 hlog 2
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hceil : ((c * log2SqUpper * (L : ℚ) ^ 2 : ℚ) : ℝ)
      ≤ ((⌈c * log2SqUpper * (L : ℚ) ^ 2⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_ceil _
  have hq := log_two_sq_le_log2SqUpper
  push_cast at hceil
  calc (c : ℝ) * Real.log n ^ 2 ≤ c * ((L : ℝ) ^ 2 * Real.log 2 ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hc'
    _ ≤ c * ((L : ℝ) ^ 2 * (log2SqUpper : ℝ)) := by gcongr
    _ = (c : ℝ) * (log2SqUpper : ℝ) * (L : ℝ) ^ 2 := by ring
    _ ≤ _ := hceil

end DetPrimality
