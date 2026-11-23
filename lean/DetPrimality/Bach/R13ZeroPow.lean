import DetPrimality.Bach.R13Defs
import DetPrimality.Bach.R11ChiDeriv
import DetPrimality.Bach.R11ZeroSumSeries

/-!
# Round 13 (P3): zero sums at `3/2` of every order

* `r13P_deriv_identity` : on the ball `B(3/2, 1/4)`, for every `m`,
  `(m+1)! (∑_ρ m_ρ/(z-ρ)^{m+2} + ∑_i 1/(z+2i+a)^{m+2}) + ∑_n χ(n)Λ(n) log^{m+1} n · n^{-z} = 0`
  (induction on `m`, generalising `r11Chi_zeroPow_eq`);
* `r13P_zeroPow_norm_le` : `‖∑_ρ m_ρ/(3/2-ρ)^{m+2}‖ ≤ 4^m ∑ 1/(i+1)² + F_{m+1}/(m+1)!`;
* `r13P_main : R13ZeroPow`.

(The GRH hypothesis of `R13ZeroPow` is not used.)
-/

open Complex DirichletCharacter Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

section Main

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- All derivative identities on the ball around `3/2`. -/
theorem r13P_deriv_identity (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) (m : ℕ) :
    ∀ z ∈ Metric.ball (3 / 2 : ℂ) (1 / 4),
      (((m + 1).factorial : ℕ) : ℂ) * ((∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / (z - ρ) ^ (m + 2))
          + ∑' i : ℕ, (1 : ℂ) / (z - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (m + 2))
        + LSeries (LSeries.logMul^[m + 1] (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ))) z = 0 := by
  set f : ℕ → ℂ := fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ) with hf
  have hZ := r11Chi_zeroHyp χ hS
  have hΓ := r11Chi_gammaHyp χ
  have hopen : IsOpen (Metric.ball (3 / 2 : ℂ) (1 / 4)) := Metric.isOpen_ball
  have hab : ∀ (j : ℕ), ∀ z ∈ Metric.ball (3 / 2 : ℂ) (1 / 4),
      HasDerivAt (LSeries (LSeries.logMul^[j] f))
        (-LSeries (LSeries.logMul (LSeries.logMul^[j] f)) z) z := by
    intro j z hz
    have hz1 : (1 : ℝ) < z.re := by linarith [(r11Chi_ball_facts hz).1]
    refine LSeries_hasDerivAt ?_
    rw [r11Chi_abscissa_iter]
    exact lt_of_le_of_lt (r11Chi_abscissa_twist χ) (by exact_mod_cast hz1)
  induction m with
  | zero =>
    intro z hz
    have d1 := r11Chi_pole_hasDerivAt_zero hZ r11Chi_mem_ball (fun w hw => r11Chi_ball_dist hw) hz
    have d2 := r11Chi_pole_hasDerivAt_zero hΓ r11Chi_mem_ball (fun w hw => r11Chi_ball_dist hw) hz
    have d3 := hab 0 z hz
    have e := r11Chi_deriv_eq_zero_of_const hopen
      (fun w hw => r11Chi_const_identity χ hχ1 hH hS hw) hz ((d1.add d2).add d3)
    simp only [Function.iterate_zero, id] at e
    simp only [zero_add, Nat.factorial_one, Nat.cast_one, one_mul, Function.iterate_succ,
      Function.iterate_zero, Function.comp_apply, id]
    linear_combination -e
  | succ m ih =>
    intro z hz
    have d1 := r11Chi_pole_hasDerivAt hZ m hz
    have d2 := r11Chi_pole_hasDerivAt hΓ m hz
    have d3 := hab (m + 1) z hz
    have e := r11Chi_deriv_eq_zero_of_const hopen (fun w hw => ih w hw) hz
      (((d1.add d2).const_mul (((m + 1).factorial : ℕ) : ℂ)).add d3)
    have hc : ((m + 1 + 1 : ℕ) : ℂ) = (m : ℂ) + 2 := by push_cast; ring
    rw [Function.iterate_succ_apply', Nat.factorial_succ (m + 1), Nat.cast_mul, hc]
    linear_combination -e

/-- `∑_ρ m_ρ/(3/2-ρ)^{m+2}` is bounded uniformly in `χ`. -/
theorem r13P_zeroPow_norm_le (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) (m : ℕ) :
    ‖∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ (m + 2)‖
      ≤ 4 ^ m * (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) + r11Chi_F (m + 1) := by
  have e := r13P_deriv_identity χ hχ1 hH hS m _ r11Chi_mem_ball
  have hΓ := r11Chi_gammaHyp χ
  have hG : ‖∑' i : ℕ, (1 : ℂ) / ((3 / 2 : ℂ) - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (m + 2)‖
      ≤ 4 ^ m * (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) :=
    tsum_of_norm_bounded (hΓ.summable.hasSum.mul_left ((4 : ℝ) ^ m))
      (fun i => r11Chi_pole_norm_le hΓ m i r11Chi_mem_ball)
  have hL := r11Chi_norm_LSeries_logMul_le χ (m + 1)
  have hfac : (((m + 1).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
  have hfac1 : (1 : ℝ) ≤ ((m + 1).factorial : ℕ) := by exact_mod_cast (m + 1).factorial_pos
  have e2 : ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ (m + 2)
      = -(∑' i : ℕ, (1 : ℂ) / ((3 / 2 : ℂ) - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (m + 2))
        - LSeries (LSeries.logMul^[m + 1] (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ))) (3 / 2)
          / (((m + 1).factorial : ℕ) : ℂ) := by
    apply mul_left_cancel₀ hfac
    rw [mul_sub, mul_div_cancel₀ _ hfac]
    linear_combination e
  rw [e2]
  have h3 : ‖LSeries (LSeries.logMul^[m + 1] (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ))) (3 / 2)
      / (((m + 1).factorial : ℕ) : ℂ)‖ ≤ r11Chi_F (m + 1) := by
    rw [norm_div, Complex.norm_natCast]
    exact (div_le_self (norm_nonneg _) hfac1).trans hL
  calc _ ≤ ‖-(∑' i : ℕ, (1 : ℂ) / ((3 / 2 : ℂ) - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (m + 2))‖
        + ‖LSeries (LSeries.logMul^[m + 1] (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ))) (3 / 2)
          / (((m + 1).factorial : ℕ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by rw [norm_neg]; exact add_le_add hG h3

/-- The real-part form of the order-`k` zero sum, `k ≥ 2`. -/
theorem r13P_abs_le (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) (m : ℕ) :
    |∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ (m + 2)).re|
      ≤ 4 ^ m * (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) + r11Chi_F (m + 1) := by
  have hs := r11Chi_summable_zeroPow χ hS (k := m + 1) (by omega)
  have e : ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ) ^ (m + 2)).re
      = (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ (m + 2)).re := by
    rw [Complex.re_tsum hs]
    refine tsum_congr fun ρ => ?_
    have key : ∀ w : ℂ, ((zeroOrd χ ρ : ℂ) / w).re = (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / w).re :=
      fun w => by rw [div_eq_mul_one_div, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    exact (key _).symm
  rw [e]
  exact (Complex.abs_re_le_norm _).trans (r13P_zeroPow_norm_le χ hχ1 hH hS m)

omit [NeZero q] in
/-- The Γ-factor term at `3/2` takes one of two values. -/
theorem r13P_gamma_le :
    (deriv (gammaFactor χ) (3 / 2) / gammaFactor χ (3 / 2)).re
      ≤ |(deriv Gammaℝ (3 / 2) / Gammaℝ (3 / 2)).re|
        + |(deriv (fun s : ℂ => Gammaℝ (s + 1)) (3 / 2) / Gammaℝ (3 / 2 + 1)).re| := by
  rcases χ.even_or_odd with he | ho
  · have hfun : gammaFactor χ = Gammaℝ := funext fun s => he.gammaFactor_def s
    rw [hfun]
    exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  · have hfun : gammaFactor χ = fun s => Gammaℝ (s + 1) := funext fun s => ho.gammaFactor_def s
    rw [hfun]
    exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))

/-- The order-one zero sum. -/
theorem r13P_one_le (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((3 / 2 : ℂ) - ρ)).re
      ≤ Real.log q / 2 + (r11Chi_F 0
        + (|(deriv Gammaℝ (3 / 2) / Gammaℝ (3 / 2)).re|
          + |(deriv (fun s : ℂ => Gammaℝ (s + 1)) (3 / 2) / Gammaℝ (3 / 2 + 1)).re|)) := by
  have h1 := r11Zs_chi_S1 χ hχ hχ1
  have h2 := r13P_gamma_le χ
  have h3 := r11Chi_norm_LSeries_logMul_le χ 0
  simp only [Function.iterate_zero, id] at h3
  rw [← r11Chi_neg_logDeriv_eq_LSeries χ (by norm_num : 1 < (3 / 2 : ℂ).re), norm_neg] at h3
  have h4 := (Complex.re_le_norm (deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2))).trans h3
  rw [h1]
  linarith

end Main

/-- **(P3)** zero sums at `3/2` of every order. -/
theorem r13P_main : R13ZeroPow := by
  intro _
  refine ⟨⟨_, fun q _ χ hχ hχ1 => r13P_one_le χ hχ hχ1⟩, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  refine ⟨4 ^ m * (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) + r11Chi_F (m + 1), fun q _ χ hχ hχ1 => ?_⟩
  have hG := growth_completedLFunction χ hχ1
  exact r13P_abs_le χ hχ1 (hadamardLogDeriv_of_growth χ hχ hχ1 hG)
    (summable_zeroOrd_div_normSq_proof χ hχ hχ1 hG) m

#print axioms r13P_main

end DetPrimality.Bach
