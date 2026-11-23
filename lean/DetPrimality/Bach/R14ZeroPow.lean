import DetPrimality.Bach.R14Defs
import DetPrimality.Bach.R13ZeroPow

/-!
# Round 14 (P3ₐ): zero sums at `a + 3/2` of every order

The argument of `R13ZeroPow.lean` on the ball `B(a + 3/2, 1/4)`:

* `r14P_zeroHyp`, `r14P_gammaHyp` : `r11Chi_PoleHyp` for the zeros and the Γ-poles on that ball;
* `r14P_const_identity`, `r14P_deriv_identity` : the Hadamard identity and all its derivatives there;
* `r14P_norm_LSeries_le` : `‖∑ χ(n)Λ(n) log^k n · n^{-s}‖ ≤ F_k` for `Re s ≥ 3/2`;
* `r14P_main : ∀ a, R14ZeroPow a`.

(The GRH hypothesis of `R14ZeroPow` is not used.)
-/

open Complex DirichletCharacter Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## The ball around `a + 3/2` -/

theorem r14P_re (a : ℕ) : ((a : ℂ) + 3 / 2).re = a + 3 / 2 := by
  rw [Complex.add_re, Complex.natCast_re]; norm_num

theorem r14P_one_lt_re (a : ℕ) : 1 < ((a : ℂ) + 3 / 2).re := by
  rw [r14P_re]
  have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  linarith

theorem r14P_ball_facts {a : ℕ} {z : ℂ} (hz : z ∈ Metric.ball ((a : ℂ) + 3 / 2) (1 / 4)) :
    5 / 4 < z.re ∧ ‖z‖ < a + 7 / 4 := by
  rw [mem_ball_iff_norm] at hz
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have h1 := Complex.abs_re_le_norm (z - ((a : ℂ) + 3 / 2))
  have h2 : (z - ((a : ℂ) + 3 / 2)).re = z.re - (a + 3 / 2) := by
    rw [Complex.sub_re, r14P_re]
  rw [h2, abs_le] at h1
  have h3 : ‖(a : ℂ) + 3 / 2‖ ≤ a + 3 / 2 := by
    have h := norm_add_le (a : ℂ) (3 / 2 : ℂ)
    have h' : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
    rw [Complex.norm_natCast, h'] at h
    exact h
  have h4 : ‖z‖ ≤ ‖z - ((a : ℂ) + 3 / 2)‖ + ‖(a : ℂ) + 3 / 2‖ := by
    have := norm_add_le (z - ((a : ℂ) + 3 / 2)) ((a : ℂ) + 3 / 2)
    rwa [sub_add_cancel] at this
  constructor <;> linarith

theorem r14P_mem_ball (a : ℕ) : ((a : ℂ) + 3 / 2) ∈ Metric.ball ((a : ℂ) + 3 / 2) (1 / 4) :=
  Metric.mem_ball_self (by norm_num)

theorem r14P_ball_dist {a : ℕ} {w : ℂ} (hw : w ∈ Metric.ball ((a : ℂ) + 3 / 2) (1 / 4)) :
    ‖((a : ℂ) + 3 / 2) - w‖ ≤ 1 := by
  rw [mem_ball_iff_norm, ← norm_neg, neg_sub] at hw
  linarith

theorem r14P_zeroHyp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ℕ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    r11Chi_PoleHyp (fun ρ : ℂ => (zeroOrd χ ρ : ℂ)) (fun ρ : ℂ => ρ)
      (fun ρ : ℂ => (4 * (a : ℝ) + 8) ^ 2 * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2))
      (Metric.ball ((a : ℂ) + 3 / 2) (1 / 4)) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have key : ∀ ρ : ℂ, (zeroOrd χ ρ : ℂ) ≠ 0 → ∀ z ∈ Metric.ball ((a : ℂ) + 3 / 2) (1 / 4),
      1 / 4 ≤ ‖z - ρ‖ ∧ 0 < ‖ρ‖ ∧ ‖ρ‖ ≤ (4 * (a : ℝ) + 8) * ‖z - ρ‖ := by
    intro ρ hc z hz
    have hm : zeroOrd χ ρ ≠ 0 := by exact_mod_cast hc
    obtain ⟨hr0, hr1⟩ := zeroOrd_strip hm
    obtain ⟨hz1, hz2⟩ := r14P_ball_facts hz
    have h1 : 1 / 4 ≤ ‖z - ρ‖ := by
      have := Complex.re_le_norm (z - ρ)
      rw [Complex.sub_re] at this
      linarith
    have h2 : ‖ρ‖ ≤ ‖z - ρ‖ + ‖z‖ := by
      have := norm_sub_le z (z - ρ)
      rw [sub_sub_cancel] at this
      linarith
    have h3 : 0 < ‖ρ‖ := norm_pos_iff.mpr (ne_zero_of_re_pos hr0)
    have h4 : (4 * (a : ℝ) + 7) * (1 / 4) ≤ (4 * (a : ℝ) + 7) * ‖z - ρ‖ :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    exact ⟨h1, h3, by linarith⟩
  refine ⟨Metric.isOpen_ball, hS.mul_left _, fun ρ => by positivity,
    fun ρ hc z hz => (key ρ hc z hz).1, fun ρ hc z hz => ?_⟩
  obtain ⟨h1, h3, h4⟩ := key ρ hc z hz
  have hx0 : 0 < ‖z - ρ‖ := by linarith
  have h5 : ‖ρ‖ ^ 2 ≤ (4 * (a : ℝ) + 8) ^ 2 * ‖z - ρ‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ h3.le h4 2
  rw [Complex.norm_natCast, div_le_iff₀ (by positivity),
    show (4 * (a : ℝ) + 8) ^ 2 * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) * ‖z - ρ‖ ^ 2
      = (zeroOrd χ ρ : ℝ) * ((4 * (a : ℝ) + 8) ^ 2 * ‖z - ρ‖ ^ 2) / ‖ρ‖ ^ 2 by ring,
    le_div_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _)

theorem r14P_gammaHyp {N : ℕ} (χ : DirichletCharacter ℂ N) (a : ℕ) :
    r11Chi_PoleHyp (fun _ : ℕ => (1 : ℂ)) (fun i : ℕ => -((2 * i + gammaShift χ : ℕ) : ℂ))
      (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) (Metric.ball ((a : ℂ) + 3 / 2) (1 / 4)) := by
  have key : ∀ (i : ℕ), ∀ z ∈ Metric.ball ((a : ℂ) + 3 / 2) (1 / 4),
      (i : ℝ) + 1 ≤ ‖z - -((2 * i + gammaShift χ : ℕ) : ℂ)‖ := by
    intro i z hz
    obtain ⟨hz1, -⟩ := r14P_ball_facts hz
    have := Complex.re_le_norm (z - -((2 * i + gammaShift χ : ℕ) : ℂ))
    rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re] at this
    have h0 : (0 : ℝ) ≤ gammaShift χ := Nat.cast_nonneg _
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hre : ((2 * i + gammaShift χ : ℕ) : ℝ) = 2 * i + gammaShift χ := by push_cast; ring
    rw [hre] at this
    linarith
  refine ⟨Metric.isOpen_ball, (r11Chi_gammaHyp χ).summable, fun i => by positivity,
    fun i _ z hz => ?_, fun i _ z hz => ?_⟩
  · have := key i z hz
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    linarith
  · have hk := key i z hz
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    rw [norm_one]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hk 2)

/-! ## The Dirichlet series for `Re s ≥ 3/2` -/

/-- `‖∑ χ(n) Λ(n) log^k n · n^{-s}‖ ≤ F_k` for `Re s ≥ 3/2`. -/
theorem r14P_norm_LSeries_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ) {s : ℂ}
    (hs : 3 / 2 ≤ s.re) :
    ‖LSeries (LSeries.logMul^[k] (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ))) s‖
      ≤ r11Chi_F k := by
  have hF := r11Chi_deriv_summable_F k
  have hle : ∀ n : ℕ, ‖LSeries.term (LSeries.logMul^[k]
      (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ))) s n‖
      ≤ Λ n * Real.log n ^ k / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · subst hn
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num), div_zero]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have h1 : ‖χ (n : ZMod N) * (Λ n : ℂ)‖ ≤ Λ n := by
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
      have hlog := pow_nonneg (Real.log_natCast_nonneg n) k
      rw [r11Chi_iter_apply, norm_mul, norm_pow, ← Complex.natCast_log, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_natCast_nonneg n)]
      refine div_le_div₀ (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog) ?_
        (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le hn1 hs)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h1 hlog
  have hsum : Summable fun n : ℕ => ‖LSeries.term (LSeries.logMul^[k]
      (fun n : ℕ => χ (n : ZMod N) * (Λ n : ℂ))) s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hF
  unfold r11Chi_F LSeries
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hle hF)

/-! ## The identity on the ball and its derivatives -/

section Main

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- On the ball around `a + 3/2`, `T(z) + Γ₀(z) + ∑ χΛ n^{-z}` is constant. -/
theorem r14P_const_identity (a : ℕ) (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) {z : ℂ}
    (hz : z ∈ Metric.ball ((a : ℂ) + 3 / 2) (1 / 4)) :
    (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (z - ρ) - 1 / ((a : ℂ) + 3 / 2 - ρ)))
      + (∑' i : ℕ, (1 : ℂ) * (1 / (z - -((2 * i + gammaShift χ : ℕ) : ℂ))
          - 1 / ((a : ℂ) + 3 / 2 - -((2 * i + gammaShift χ : ℕ) : ℂ))))
      + LSeries (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)) z
      = LSeries (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)) ((a : ℂ) + 3 / 2) := by
  have hz1 : 1 < z.re := by linarith [(r14P_ball_facts hz).1]
  have h32 : 1 < ((a : ℂ) + 3 / 2).re := r14P_one_lt_re a
  have h2 : 1 < (2 : ℂ).re := by norm_num
  have hsum : ∀ {s : ℂ}, 1 < s.re →
      Summable fun ρ : ℂ => (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ)) := by
    intro s hs
    exact ((summable_hadamard_terms χ hS hs).sub (summable_hadamard_terms χ hS h2)).congr
      (fun ρ => by ring)
  have hT : ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (z - ρ) - 1 / ((a : ℂ) + 3 / 2 - ρ))
      = Zfun χ z - Zfun χ ((a : ℂ) + 3 / 2) := by
    unfold Zfun
    rw [← (hsum hz1).tsum_sub (hsum h32)]
    exact tsum_congr fun ρ => by ring
  have hG : ∑' i : ℕ, (1 : ℂ) * (1 / (z - -((2 * i + gammaShift χ : ℕ) : ℂ))
      - 1 / ((a : ℂ) + 3 / 2 - -((2 * i + gammaShift χ : ℕ) : ℂ)))
      = Gfun χ ((a : ℂ) + 3 / 2) - Gfun χ z := by
    have h := (hasSum_Gfun_sub χ (s := (a : ℂ) + 3 / 2) (by linarith)).sub
      (hasSum_Gfun_sub χ (s := z) (by linarith))
    have e : ∑' i : ℕ, (1 : ℂ) * (1 / (z - -((2 * i + gammaShift χ : ℕ) : ℂ))
        - 1 / ((a : ℂ) + 3 / 2 - -((2 * i + gammaShift χ : ℕ) : ℂ)))
        = (Gfun χ ((a : ℂ) + 3 / 2) - Gfun χ 2) - (Gfun χ z - Gfun χ 2) := by
      rw [← h.tsum_eq]
      refine tsum_congr fun i => ?_
      simp only [sub_neg_eq_add, one_mul]
      ring
    rw [e]; ring
  have eZz := Zfun_eq χ hχ1 hH hS hz1
  have eZ32 := Zfun_eq χ hχ1 hH hS h32
  have eLz := r11Chi_neg_logDeriv_eq_LSeries χ hz1
  have eL32 := r11Chi_neg_logDeriv_eq_LSeries χ h32
  linear_combination hT + hG + eZz - eZ32 - eLz + eL32

/-- All derivative identities on the ball around `a + 3/2`. -/
theorem r14P_deriv_identity (a : ℕ) (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) (m : ℕ) :
    ∀ z ∈ Metric.ball ((a : ℂ) + 3 / 2) (1 / 4),
      (((m + 1).factorial : ℕ) : ℂ) * ((∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / (z - ρ) ^ (m + 2))
          + ∑' i : ℕ, (1 : ℂ) / (z - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (m + 2))
        + LSeries (LSeries.logMul^[m + 1] (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ))) z = 0 := by
  set f : ℕ → ℂ := fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ) with hf
  have hZ := r14P_zeroHyp χ a hS
  have hΓ := r14P_gammaHyp χ a
  have hopen : IsOpen (Metric.ball ((a : ℂ) + 3 / 2) (1 / 4)) := Metric.isOpen_ball
  have hab : ∀ (j : ℕ), ∀ z ∈ Metric.ball ((a : ℂ) + 3 / 2) (1 / 4),
      HasDerivAt (LSeries (LSeries.logMul^[j] f))
        (-LSeries (LSeries.logMul (LSeries.logMul^[j] f)) z) z := by
    intro j z hz
    have hz1 : (1 : ℝ) < z.re := by linarith [(r14P_ball_facts hz).1]
    refine LSeries_hasDerivAt ?_
    rw [r11Chi_abscissa_iter]
    exact lt_of_le_of_lt (r11Chi_abscissa_twist χ) (by exact_mod_cast hz1)
  induction m with
  | zero =>
    intro z hz
    have d1 := r11Chi_pole_hasDerivAt_zero hZ (r14P_mem_ball a)
      (fun w hw => r14P_ball_dist hw) hz
    have d2 := r11Chi_pole_hasDerivAt_zero hΓ (r14P_mem_ball a)
      (fun w hw => r14P_ball_dist hw) hz
    have d3 := hab 0 z hz
    have e := r11Chi_deriv_eq_zero_of_const hopen
      (fun w hw => r14P_const_identity χ a hχ1 hH hS hw) hz ((d1.add d2).add d3)
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

/-- `∑_ρ m_ρ/(a+3/2-ρ)^{m+2}` is bounded uniformly in `χ` (and in `a`). -/
theorem r14P_zeroPow_norm_le (a : ℕ) (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) (m : ℕ) :
    ‖∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ (m + 2)‖
      ≤ 4 ^ m * (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) + r11Chi_F (m + 1) := by
  have e := r14P_deriv_identity χ a hχ1 hH hS m _ (r14P_mem_ball a)
  have hΓ := r14P_gammaHyp χ a
  have hG : ‖∑' i : ℕ, (1 : ℂ)
      / ((a : ℂ) + 3 / 2 - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (m + 2)‖
      ≤ 4 ^ m * (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) :=
    tsum_of_norm_bounded (hΓ.summable.hasSum.mul_left ((4 : ℝ) ^ m))
      (fun i => r11Chi_pole_norm_le hΓ m i (r14P_mem_ball a))
  have hL := r14P_norm_LSeries_le χ (m + 1) (s := (a : ℂ) + 3 / 2)
    (by rw [r14P_re]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)])
  have hfac : (((m + 1).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
  have hfac1 : (1 : ℝ) ≤ ((m + 1).factorial : ℕ) := by exact_mod_cast (m + 1).factorial_pos
  have e2 : ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ (m + 2)
      = -(∑' i : ℕ, (1 : ℂ)
          / ((a : ℂ) + 3 / 2 - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (m + 2))
        - LSeries (LSeries.logMul^[m + 1] (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)))
            ((a : ℂ) + 3 / 2) / (((m + 1).factorial : ℕ) : ℂ) := by
    apply mul_left_cancel₀ hfac
    rw [mul_sub, mul_div_cancel₀ _ hfac]
    linear_combination e
  rw [e2]
  have h3 : ‖LSeries (LSeries.logMul^[m + 1] (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)))
      ((a : ℂ) + 3 / 2) / (((m + 1).factorial : ℕ) : ℂ)‖ ≤ r11Chi_F (m + 1) := by
    rw [norm_div, Complex.norm_natCast]
    exact (div_le_self (norm_nonneg _) hfac1).trans hL
  calc _ ≤ ‖-(∑' i : ℕ, (1 : ℂ)
          / ((a : ℂ) + 3 / 2 - -((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (m + 2))‖
        + ‖LSeries (LSeries.logMul^[m + 1] (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)))
          ((a : ℂ) + 3 / 2) / (((m + 1).factorial : ℕ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by rw [norm_neg]; exact add_le_add hG h3

/-- The real-part form of the order-`k` zero sum, `k ≥ 2`. -/
theorem r14P_abs_le (a : ℕ) (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) (m : ℕ) :
    |∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ (m + 2)).re|
      ≤ 4 ^ m * (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) + r11Chi_F (m + 1) := by
  have hZ := r14P_zeroHyp χ a hS
  have hs : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ (m + 2) :=
    Summable.of_norm_bounded (hZ.summable.mul_left ((4 : ℝ) ^ m))
      (fun ρ => r11Chi_pole_norm_le hZ m ρ (r14P_mem_ball a))
  have e : ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ (m + 2)).re
      = (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((a : ℂ) + 3 / 2 - ρ) ^ (m + 2)).re := by
    rw [Complex.re_tsum hs]
    refine tsum_congr fun ρ => ?_
    have key : ∀ w : ℂ, ((zeroOrd χ ρ : ℂ) / w).re = (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / w).re :=
      fun w => by rw [div_eq_mul_one_div, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    exact (key _).symm
  rw [e]
  exact (Complex.abs_re_le_norm _).trans (r14P_zeroPow_norm_le χ a hχ1 hH hS m)

omit [NeZero q] in
/-- The Γ-factor term at `s` takes one of two values. -/
theorem r14P_gamma_le (s : ℂ) :
    (deriv (gammaFactor χ) s / gammaFactor χ s).re
      ≤ |(deriv Gammaℝ s / Gammaℝ s).re|
        + |(deriv (fun s : ℂ => Gammaℝ (s + 1)) s / Gammaℝ (s + 1)).re| := by
  rcases χ.even_or_odd with he | ho
  · have hfun : gammaFactor χ = Gammaℝ := funext fun s => he.gammaFactor_def s
    rw [hfun]
    exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  · have hfun : gammaFactor χ = fun s => Gammaℝ (s + 1) := funext fun s => ho.gammaFactor_def s
    rw [hfun]
    exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))

/-- The order-one zero sum at `a + 3/2`. -/
theorem r14P_one_le (a : ℕ) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * ((1 : ℂ) / ((a : ℂ) + 3 / 2 - ρ)).re
      ≤ Real.log q / 2 + (r11Chi_F 0
        + (|(deriv Gammaℝ ((a : ℂ) + 3 / 2) / Gammaℝ ((a : ℂ) + 3 / 2)).re|
          + |(deriv (fun s : ℂ => Gammaℝ (s + 1)) ((a : ℂ) + 3 / 2)
              / Gammaℝ ((a : ℂ) + 3 / 2 + 1)).re|)) := by
  have h1 := re_logDeriv_eq_tsum_of_growth χ hχ hχ1 (growth_completedLFunction χ hχ1)
    (s := (a : ℂ) + 3 / 2) (r14P_one_lt_re a)
  rw [add_re] at h1
  have h2 := r14P_gamma_le χ ((a : ℂ) + 3 / 2)
  have h3 := r14P_norm_LSeries_le χ 0 (s := (a : ℂ) + 3 / 2)
    (by rw [r14P_re]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)])
  simp only [Function.iterate_zero, id] at h3
  rw [← r11Chi_neg_logDeriv_eq_LSeries χ (r14P_one_lt_re a), norm_neg] at h3
  have h4 := (Complex.re_le_norm (deriv (LFunction χ) ((a : ℂ) + 3 / 2)
    / LFunction χ ((a : ℂ) + 3 / 2))).trans h3
  linarith

end Main

/-- **(P3ₐ)** zero sums at `a + 3/2` of every order, for every shift `a`. -/
theorem r14P_main (a : ℕ) : R14ZeroPow a := by
  intro _
  refine ⟨⟨_, fun q _ χ hχ hχ1 => r14P_one_le χ a hχ hχ1⟩, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  refine ⟨4 ^ m * (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) + r11Chi_F (m + 1), fun q _ χ hχ hχ1 => ?_⟩
  have hG := growth_completedLFunction χ hχ1
  exact r14P_abs_le χ a hχ1 (hadamardLogDeriv_of_growth χ hχ hχ1 hG)
    (summable_zeroOrd_div_normSq_proof χ hχ hχ1 hG) m

#print axioms r14P_main

end DetPrimality.Bach
