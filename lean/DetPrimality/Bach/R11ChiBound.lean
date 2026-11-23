import DetPrimality.Bach.R11ChiFormula
import DetPrimality.Bach.R11ChiDeriv

/-!
# designB Lemma 3, (3.2): real parts and constants

`r11Chi_main_of_F` : `R11ChiExplicit`'s conclusion from upper bounds
`F₁ ≤ 5.31`, `F₂ ≤ 17.5`, `F₃ ≤ 102.3` for `F_k = ∑ Λ(n) log^k n n^{-3/2}`.

The coefficients of `log^i y` (`i ≤ 2`) are `∑_ρ m_ρ/(ρ+1/2)^j + ∑_k 1/s_k^j`; under GRH the
real part of the zero sum equals that of `∑_ρ m_ρ/(3/2-ρ)^j`, which `R11ChiDeriv` evaluates
by the Dirichlet series at `3/2`; the Γ-sums telescope against `∑_k 1/s_k^j` (`2 - s_k = -s_{k+1}`).
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Telescoping Γ-sums -/

theorem r11Chi_two_sub_r (a k : ℕ) : 2 - r11Chi_r a k = -r11Chi_r a (k + 1) := by
  rw [r11Chi_r_succ]; ring

theorem r11Chi_tele_even (a : ℕ) {j : ℕ} (hj : Even j) (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / r11Chi_r a k ^ j - 1 / (2 - r11Chi_r a k) ^ j)
      = 1 / r11Chi_r a 0 ^ j - 1 / r11Chi_r a K ^ j := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, r11Chi_two_sub_r, hj.neg_pow]
    ring

theorem r11Chi_tsum_even_le {a : ℕ} (ha : a = 0 ∨ a = 1) {j : ℕ} (hj : Even j) (hj2 : 2 ≤ j) :
    ∑' k : ℕ, 1 / r11Chi_r a k ^ j - ∑' k : ℕ, 1 / (2 - r11Chi_r a k) ^ j ≤ 2 ^ j := by
  have hs1 := r11Chi_summable_inv_r_pow a hj2
  have hs2 := r11Chi_summable_inv_two_sub_r_pow a hj2
  rw [← hs1.tsum_sub hs2]
  refine (hs1.sub hs2).tsum_le_of_sum_range_le fun K => ?_
  rw [r11Chi_tele_even a hj K]
  have h1 : 0 ≤ 1 / r11Chi_r a K ^ j := by
    have := hj.pow_nonneg (r11Chi_r a K)
    positivity
  have h2 : 1 / r11Chi_r a 0 ^ j = 2 ^ j := by
    rcases ha with rfl | rfl
    · have : r11Chi_r 0 0 = 1 / 2 := by unfold r11Chi_r; norm_num
      rw [this, one_div_pow, one_div_one_div]
    · have : r11Chi_r 1 0 = -(1 / 2) := by unfold r11Chi_r; norm_num
      rw [this, hj.neg_pow, one_div_pow, one_div_one_div]
  linarith

theorem r11Chi_tsum_three_le {a : ℕ} (ha : a = 0 ∨ a = 1) :
    ∑' k : ℕ, 1 / r11Chi_r a k ^ 3 - ∑' k : ℕ, 1 / (2 - r11Chi_r a k) ^ 3 ≤ 8 - 8 / 27 := by
  have hs1 := r11Chi_summable_inv_r_pow a (j := 3) (by norm_num)
  have hs2 := r11Chi_summable_inv_two_sub_r_pow a (j := 3) (by norm_num)
  rw [← hs1.tsum_sub hs2]
  refine (hs1.sub hs2).tsum_le_of_sum_range_le fun K => ?_
  rcases K with _ | K
  · simp; norm_num
  · rw [Finset.sum_range_succ']
    have hneg : ∀ k : ℕ, 1 / r11Chi_r a (k + 1) ^ 3 - 1 / (2 - r11Chi_r a (k + 1)) ^ 3 ≤ 0 := by
      intro k
      have h := r11Chi_r_neg a (k := k + 1) (by omega)
      have h1 : 1 / r11Chi_r a (k + 1) ^ 3 ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos zero_le_one
          ((Odd.pow_nonpos_iff (by decide)).mpr (by linarith))
      have h2 : 0 ≤ 1 / (2 - r11Chi_r a (k + 1)) ^ 3 := by
        have : 0 < 2 - r11Chi_r a (k + 1) := by linarith
        positivity
      linarith
    have h0 : 1 / r11Chi_r a 0 ^ 3 - 1 / (2 - r11Chi_r a 0) ^ 3 ≤ 8 - 8 / 27 := by
      rcases ha with rfl | rfl <;> · unfold r11Chi_r; norm_num
    have := Finset.sum_nonpos (s := Finset.range K) (fun k _ => hneg k)
    linarith

theorem r11Chi_tele_inv (a K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / r11Chi_r a k + 1 / (2 - r11Chi_r a k))
      = 1 / r11Chi_r a 0 - 1 / r11Chi_r a K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, r11Chi_two_sub_r, one_div_neg_eq_neg_one_div]
    ring

theorem r11Chi_U_le (a : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    ∑' k : ℕ, (1 / r11Chi_r a k + 1 / (2 - r11Chi_r a k))
      ≤ 1 / r11Chi_r a 0 - 1 / r11Chi_r a K := by
  have hs := r11Chi_summable_inv_add a
  have h := hs.neg.sum_le_tsum (Finset.range K) (fun k hk => ?_)
  · rw [Finset.sum_neg_distrib, tsum_neg, r11Chi_tele_inv] at h
    linarith
  · rw [Finset.mem_range, not_lt] at hk
    have hr := r11Chi_r_neg a (k := k) (by omega)
    have h1 : 1 / (2 - r11Chi_r a k) ≤ 1 / (-r11Chi_r a k) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    rw [one_div_neg_eq_neg_one_div] at h1
    linarith

/-! ## The coefficient of `log³ y` -/

theorem r11Chi_cert_digamma :
    ∑ k ∈ Finset.range 64, (1 / ((k : ℚ) + 1) - 1 / ((k : ℚ) + 3 / 4)) ≤ -504 / 1000 := by
  decide +kernel

theorem r11Chi_cube_coef_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    2 * (Gfun χ (3 / 2)).re
      + ∑' k : ℕ, (1 / r11Chi_r (gammaShift χ) k + 1 / (2 - r11Chi_r (gammaShift χ) k))
      ≤ -0.2075 := by
  have hU := r11Chi_U_le (gammaShift χ) (K := 1000) (by norm_num)
  rcases gammaShift_cases χ with ha | ha
  · rw [ha] at hU ⊢
    have hU' : 1 / r11Chi_r 0 0 - 1 / r11Chi_r 0 1000 ≤ 2.0006 := by
      unfold r11Chi_r; norm_num
    have hG := Gfun_eq χ (s := (3 / 2 : ℂ)) (by norm_num)
    rw [ha, Nat.cast_zero, add_zero,
      show (3 / 2 : ℂ) / 2 = ((3 / 4 : ℚ) : ℂ) by push_cast; norm_num] at hG
    have hd := szs_digamma_re_le (3 / 4) 1 (by norm_num) (by norm_num) 64
    rw [Rat.cast_one, digamma_one] at hd
    have hc := (Rat.cast_le (K := ℝ)).mpr r11Chi_cert_digamma
    have hhalf : ∀ z : ℂ, (z / 2).re = z.re / 2 := fun z => by
      rw [show z / 2 = ((1 / 2 : ℝ) : ℂ) * z by push_cast; ring, Complex.re_ofReal_mul]; ring
    have hGre : (Gfun χ (3 / 2)).re
        = -Real.log Real.pi / 2 + (digamma ((3 / 4 : ℚ) : ℂ)).re / 2 := by
      rw [hG, Complex.add_re, hhalf, hhalf, Complex.neg_re, Complex.ofReal_re]
    rw [Complex.neg_re, Complex.ofReal_re] at hd
    have hγ := szs_gamma_gt
    have hπ := szs_log_pi_gt
    push_cast at hc
    rw [hGre]
    linarith
  · rw [ha] at hU ⊢
    have hU' : 1 / r11Chi_r 1 0 - 1 / r11Chi_r 1 1000 ≤ -1.999 := by
      unfold r11Chi_r; norm_num
    have hG : (Gfun χ (3 / 2)).re ≤ -0.6853 := re_logDeriv_gammaFactor_three_halves_le_sharp χ
    linarith

/-! ## The coefficients of `log^i y`, `i ≤ 2` -/

theorem r11Chi_coef_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    ∑' i : ℕ, 1 / r11Chi_r (gammaShift χ) i ^ (k + 1)
        + (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ (k + 1)).re
      ≤ (∑' i : ℕ, 1 / r11Chi_r (gammaShift χ) i ^ (k + 1)
          - ∑' i : ℕ, 1 / (2 - r11Chi_r (gammaShift χ) i) ^ (k + 1))
        + r11Chi_F k / (k.factorial : ℝ) := by
  rw [r11Chi_zeroPow_eq χ hχ1 hH hS hk1 hk3]
  have e : ∑' i : ℕ, 1 / ((3 / 2 : ℂ) + ((2 * i + gammaShift χ : ℕ) : ℂ)) ^ (k + 1)
      = ((∑' i : ℕ, 1 / (2 - r11Chi_r (gammaShift χ) i) ^ (k + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun i => ?_
    unfold r11Chi_r
    push_cast
    rw [show (2 : ℂ) - (1 / 2 - (2 * (i : ℂ) + (gammaShift χ : ℂ)))
      = 3 / 2 + (2 * (i : ℂ) + (gammaShift χ : ℂ)) by ring]
  have hfac : (1 : ℂ) / (k.factorial : ℂ) = ((1 / (k.factorial : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  set X : ℂ := LSeries (LSeries.logMul^[k] (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ))) (3 / 2)
    with hX
  have h1 : ‖X‖ ≤ r11Chi_F k := r11Chi_norm_LSeries_logMul_le χ k
  rw [e, hfac, Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  have h2 := Complex.abs_re_le_norm X
  have h3 := neg_abs_le X.re
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h4 : -(1 / (k.factorial : ℝ) * X.re) ≤ r11Chi_F k / (k.factorial : ℝ) := by
    have h5 := mul_le_mul_of_nonneg_left (show -X.re ≤ r11Chi_F k by linarith)
      (show (0 : ℝ) ≤ 1 / (k.factorial : ℝ) by positivity)
    calc -(1 / (k.factorial : ℝ) * X.re) = 1 / (k.factorial : ℝ) * -X.re := by ring
      _ ≤ 1 / (k.factorial : ℝ) * r11Chi_F k := h5
      _ = r11Chi_F k / (k.factorial : ℝ) := by ring
  linarith

/-! ## Geometry of the zeros on the critical line -/

theorem r11Chi_zero_geom (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) :
    (ρ + 1 / 2).re = 1 ∧ (3 / 2 : ℂ) - ρ = (starRingEnd ℂ) (ρ + 1 / 2) := by
  have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h
  have e0 : (ρ + 1 / 2).re = ρ.re + 1 / 2 := by simp
  have e1 : (ρ + 1 / 2).re = 1 := by rw [e0, hρ]; norm_num
  have e2 : (ρ + 1 / 2).im = ρ.im := by simp
  have e32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by norm_num
  refine ⟨e1, ?_⟩
  apply Complex.ext
  · rw [Complex.conj_re, e1, e32, Complex.sub_re, Complex.ofReal_re, hρ]; norm_num
  · rw [Complex.conj_im, e2, e32, Complex.sub_im, Complex.ofReal_im]; ring

theorem r11Chi_summable_Z4 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 4 := by
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) (hS.mul_left 4)
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  · have hre := (zeroOrd_strip h0).1
    have hρ : 0 < ‖ρ‖ := norm_pos_iff.mpr (ne_zero_of_re_pos hre)
    have h1 := r11Chi_norm_add_half_ge hre
    have h2 : 1 / 2 ≤ ‖ρ + 1 / 2‖ := by
      have := Complex.re_le_norm (ρ + 1 / 2)
      have e1 : (ρ + 1 / 2).re = ρ.re + 1 / 2 := by simp
      rw [e1] at this; linarith
    have h3 : ‖ρ‖ ^ 2 ≤ 4 * ‖ρ + 1 / 2‖ ^ 4 := by
      have ha : ‖ρ‖ ^ 2 ≤ ‖ρ + 1 / 2‖ ^ 2 := pow_le_pow_left₀ hρ.le h1 2
      have hb : (1 / 4 : ℝ) ≤ ‖ρ + 1 / 2‖ ^ 2 := by nlinarith
      nlinarith
    have hm : (0 : ℝ) ≤ zeroOrd χ ρ := Nat.cast_nonneg _
    rw [show 4 * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) = (zeroOrd χ ρ : ℝ) * 4 / ‖ρ‖ ^ 2 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h3 hm]

theorem r11Chi_summable_re_inv (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re := by
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hS
  · by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    · rw [(szs_zero_facts32 hGRH χ h0).1]; positivity
  · by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    · obtain ⟨h1, h2, -⟩ := szs_zero_facts32 hGRH χ h0
      rw [h1, h2, mul_one_div]
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      linarith

/-! ## Termwise real parts -/

theorem r11Chi_gamma_term_le (a k : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    ((-1 : ℂ) * r11Chi_perron 3 (fun s => 1 / (s - ((r11Chi_r a k : ℝ) : ℂ))
        - 1 / (2 - ((r11Chi_r a k : ℝ) : ℂ))) y).re
      ≤ 1 / r11Chi_r a k ^ 4 + Real.log y * (1 / r11Chi_r a k ^ 3)
        + Real.log y ^ 2 / 2 * (1 / r11Chi_r a k ^ 2)
        + Real.log y ^ 3 / 6 * (1 / r11Chi_r a k + 1 / (2 - r11Chi_r a k)) := by
  set r := r11Chi_r a k with hr
  have hy0 : 0 < y := by linarith
  have hr0 : r ≠ 0 := r11Chi_r_ne a k
  have hr2 : r < 2 := by
    have := r11Chi_r_le a k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [r11Chi_perron_pole3 (w := (r : ℂ)) (by rw [Complex.ofReal_re]; exact hr2)
    (by exact_mod_cast hr0) hy]
  have e : (-1 : ℂ) * ((y : ℂ) ^ (r : ℂ) / (r : ℂ) ^ 4 - 1 / (r : ℂ) ^ 4
        - (Real.log y : ℂ) * (1 / (r : ℂ) ^ 3)
        - ((Real.log y ^ 2 / 2 : ℝ) : ℂ) * (1 / (r : ℂ) ^ 2)
        - ((Real.log y ^ 3 / 6 : ℝ) : ℂ) * (1 / (r : ℂ) + 1 / (2 - (r : ℂ))))
      = ((-(y ^ r / r ^ 4) + 1 / r ^ 4 + Real.log y * (1 / r ^ 3)
          + Real.log y ^ 2 / 2 * (1 / r ^ 2)
          + Real.log y ^ 3 / 6 * (1 / r + 1 / (2 - r)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hy0.le]
    push_cast
    ring
  rw [e, Complex.ofReal_re]
  have : 0 ≤ y ^ r / r ^ 4 := div_nonneg (Real.rpow_nonneg hy0.le _) (by positivity)
  linarith

theorem r11Chi_gamma_re_le (a : ℕ) {y : ℝ} (hy : 1 ≤ y) {P : ℂ}
    (h : HasSum (fun k : ℕ => (-1 : ℂ) * r11Chi_perron 3 (fun s =>
        1 / (s - ((r11Chi_r a k : ℝ) : ℂ)) - 1 / (2 - ((r11Chi_r a k : ℝ) : ℂ))) y) P) :
    P.re ≤ ∑' k : ℕ, 1 / r11Chi_r a k ^ 4 + Real.log y * ∑' k : ℕ, 1 / r11Chi_r a k ^ 3
      + Real.log y ^ 2 / 2 * ∑' k : ℕ, 1 / r11Chi_r a k ^ 2
      + Real.log y ^ 3 / 6 * ∑' k : ℕ, (1 / r11Chi_r a k + 1 / (2 - r11Chi_r a k)) := by
  have hg := (((r11Chi_summable_inv_r_pow a (j := 4) (by norm_num)).hasSum.add
    ((r11Chi_summable_inv_r_pow a (j := 3) (by norm_num)).hasSum.mul_left (Real.log y))).add
    ((r11Chi_summable_inv_r_pow a (j := 2) (by norm_num)).hasSum.mul_left
      (Real.log y ^ 2 / 2))).add
    ((r11Chi_summable_inv_add a).hasSum.mul_left (Real.log y ^ 3 / 6))
  exact hasSum_le (fun k => r11Chi_gamma_term_le a k hy) (Complex.hasSum_re h) hg

theorem r11Chi_zero_term_le (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (ρ : ℂ) {y : ℝ} (hy : 1 ≤ y) :
    ((-(zeroOrd χ ρ : ℂ)) * r11Chi_perron 3 (fun s =>
        1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2))) y).re
      ≤ y * ((zeroOrd χ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 4)
        + ((zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 4).re
        + Real.log y * ((zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 3).re
        + Real.log y ^ 2 / 2 * ((zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 2).re
        + Real.log y ^ 3 / 3 * ((zeroOrd χ ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re) := by
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  obtain ⟨hre, hconj⟩ := r11Chi_zero_geom hGRH χ h0
  have hy0 : 0 < y := by linarith
  have hmc : (zeroOrd χ ρ : ℂ) = (((zeroOrd χ ρ : ℝ)) : ℂ) := by push_cast; rfl
  have hm0 : (0 : ℝ) ≤ (zeroOrd χ ρ : ℝ) := Nat.cast_nonneg _
  generalize (zeroOrd χ ρ : ℝ) = m at hmc hm0 ⊢
  rw [hmc]
  have h2w : (2 : ℂ) - (ρ + 1 / 2) = (3 / 2 : ℂ) - ρ := by ring
  generalize hw : ρ + 1 / 2 = w at hre hconj h2w ⊢
  generalize hv : (3 / 2 : ℂ) - ρ = v at hconj h2w ⊢
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  rw [r11Chi_perron_pole3 (by rw [hre]; norm_num) hw0 hy, h2w]
  have hc : ∀ j : ℕ, (1 / w ^ j).re = (1 / v ^ j).re := by
    intro j
    have : (1 : ℂ) / v ^ j = (starRingEnd ℂ) (1 / w ^ j) := by
      rw [hconj]; simp [map_pow]
    rw [this, Complex.conj_re]
  have hc1 : (1 / w).re = (1 / v).re := by simpa using hc 1
  have hdiv : ∀ j : ℕ, ((m : ℂ) / v ^ j).re = m * (1 / v ^ j).re := by
    intro j; rw [div_eq_mul_one_div, Complex.re_ofReal_mul]
  have hA : -(m * ((y : ℂ) ^ w / w ^ 4).re) ≤ y * (m / ‖w‖ ^ 4) := by
    have hn : ‖(y : ℂ) ^ w / w ^ 4‖ = y / ‖w‖ ^ 4 := by
      rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hy0, hre, Real.rpow_one]
    have h1 := Complex.abs_re_le_norm ((y : ℂ) ^ w / w ^ 4)
    rw [hn] at h1
    have h2 := neg_abs_le (((y : ℂ) ^ w / w ^ 4).re)
    calc -(m * ((y : ℂ) ^ w / w ^ 4).re) = m * (-((y : ℂ) ^ w / w ^ 4).re) := by ring
      _ ≤ m * (y / ‖w‖ ^ 4) := mul_le_mul_of_nonneg_left (by linarith) hm0
      _ = y * (m / ‖w‖ ^ 4) := by ring
  have hexp : (-(m : ℂ) * ((y : ℂ) ^ w / w ^ 4 - 1 / w ^ 4 - (Real.log y : ℂ) * (1 / w ^ 3)
        - ((Real.log y ^ 2 / 2 : ℝ) : ℂ) * (1 / w ^ 2)
        - ((Real.log y ^ 3 / 6 : ℝ) : ℂ) * (1 / w + 1 / v))).re
      = -(m * ((y : ℂ) ^ w / w ^ 4).re) + m * (1 / w ^ 4).re
        + Real.log y * (m * (1 / w ^ 3).re) + Real.log y ^ 2 / 2 * (m * (1 / w ^ 2).re)
        + Real.log y ^ 3 / 6 * (m * ((1 / w).re + (1 / v).re)) := by
    rw [← Complex.ofReal_neg, Complex.re_ofReal_mul]
    simp only [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul]
    ring
  rw [hexp, hdiv, hdiv, hdiv, hc 4, hc 3, hc 2, hc1,
    show Real.log y ^ 3 / 6 * (m * ((1 / v).re + (1 / v).re))
      = Real.log y ^ 3 / 3 * (m * (1 / v).re) by ring]
  linarith

theorem r11Chi_zero_re_le (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {y : ℝ} (hy : 1 ≤ y) {P : ℂ}
    (h : HasSum (fun ρ : ℂ => (-(zeroOrd χ ρ : ℂ)) * r11Chi_perron 3 (fun s =>
        1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2))) y) P) :
    P.re ≤ y * r11Z χ 4
      + (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 4).re
      + Real.log y * (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 3).re
      + Real.log y ^ 2 / 2 * (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 2).re
      + Real.log y ^ 3 / 3 * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re := by
  have h4 := Complex.hasSum_re (r11Chi_summable_zeroPow χ hS (k := 3) (by norm_num)).hasSum
  have h3 := Complex.hasSum_re (r11Chi_summable_zeroPow χ hS (k := 2) (by norm_num)).hasSum
  have h2 := Complex.hasSum_re (r11Chi_summable_zeroPow χ hS (k := 1) (by norm_num)).hasSum
  have hg := (((((r11Chi_summable_Z4 χ hS).hasSum.mul_left y).add h4).add
    (h3.mul_left (Real.log y))).add (h2.mul_left (Real.log y ^ 2 / 2))).add
    ((r11Chi_summable_re_inv hGRH χ hS).hasSum.mul_left (Real.log y ^ 3 / 3))
  exact hasSum_le (fun ρ => r11Chi_zero_term_le hGRH χ ρ hy) (Complex.hasSum_re h) hg

/-! ## Assembly -/

/-- designB (3.2) from upper bounds for `F₁, F₂, F₃`. -/
theorem r11Chi_main_of_F (hF1 : r11Chi_F 1 ≤ 5.31) (hF2 : r11Chi_F 2 ≤ 17.5)
    (hF3 : r11Chi_F 3 ≤ 102.3) : R11ChiExplicit := by
  intro hGRH q _ χ hχ hχ1 y hy
  have hy1 : 1 ≤ y := hy.le
  have hG := growth_completedLFunction χ hχ1
  have hH := hadamardLogDeriv_of_growth χ hχ hχ1 hG
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 hG
  obtain ⟨hA, hB, hΦ⟩ := r11Chi_Phi_formula χ hχ1 hH hS hy1
  have hL0 : 0 < Real.log y := Real.log_pos hy
  have hPA := r11Chi_gamma_re_le (gammaShift χ) hy1 hA
  have hPB := r11Chi_zero_re_le hGRH χ hS hy1 hB
  have hRL := re_logDeriv_eq_tsum_proof χ hχ hχ1 hS hH (s := 3 / 2) (by norm_num)
  have hK1 := r11Chi_cube_coef_le χ
  have hLL := norm_logDeriv_LFunction_three_halves_le_sharp χ
  have hDre := Complex.re_le_norm (deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2))
  have ha := gammaShift_cases χ
  have hK2 := r11Chi_coef_le χ hχ1 hH hS (k := 1) le_rfl (by norm_num)
  have hK3 := r11Chi_coef_le χ hχ1 hH hS (k := 2) (by norm_num) (by norm_num)
  have hK4 := r11Chi_coef_le χ hχ1 hH hS (k := 3) (by norm_num) le_rfl
  have hT2 := r11Chi_tsum_even_le ha (j := 2) (by decide) le_rfl
  have hT3 := r11Chi_tsum_three_le ha
  have hT4 := r11Chi_tsum_even_le ha (j := 4) (by decide) (by norm_num)
  have h6 : ∀ z : ℂ, (6 * z).re = 6 * z.re := fun z => by simp
  have hre := congrArg Complex.re hΦ
  rw [Complex.add_re, Complex.add_re, h6, h6,
    show (Real.log y : ℂ) ^ 3 = ((Real.log y ^ 3 : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_mul_ofReal, Complex.neg_re] at hre
  rw [Complex.add_re] at hRL
  have hGdef : (deriv (gammaFactor χ) (3 / 2) / gammaFactor χ (3 / 2)).re
      = (Gfun χ (3 / 2)).re := rfl
  rw [hGdef] at hRL
  simp only [Nat.reduceAdd] at hK2 hK3 hK4
  rw [hre]
  set L := Real.log y with hL
  generalize (deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)).re = D at *
  generalize (Gfun χ (3 / 2)).re = Gr at *
  generalize ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re = S1 at *
  generalize r11Z χ 4 = Z4 at *
  generalize (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 4).re = H4 at *
  generalize (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 3).re = H3 at *
  generalize (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) / ((3 / 2 : ℂ) - ρ) ^ 2).re = H2 at *
  generalize ∑' k : ℕ, 1 / r11Chi_r (gammaShift χ) k ^ 4 = G4 at *
  generalize ∑' k : ℕ, 1 / r11Chi_r (gammaShift χ) k ^ 3 = G3 at *
  generalize ∑' k : ℕ, 1 / r11Chi_r (gammaShift χ) k ^ 2 = G2 at *
  generalize ∑' k : ℕ, 1 / (2 - r11Chi_r (gammaShift χ) k) ^ 4 = E4 at *
  generalize ∑' k : ℕ, 1 / (2 - r11Chi_r (gammaShift χ) k) ^ 3 = E3 at *
  generalize ∑' k : ℕ, 1 / (2 - r11Chi_r (gammaShift χ) k) ^ 2 = E2 at *
  generalize ∑' k : ℕ, (1 / r11Chi_r (gammaShift χ) k + 1 / (2 - r11Chi_r (gammaShift χ) k))
    = U at *
  norm_num [Nat.factorial] at hK2 hK3 hK4 hT2 hT4
  have hc2 : G2 + H2 ≤ 9.31 := by linarith
  have hc3 : G3 + H3 ≤ 16.455 := by linarith
  have hc4 : G4 + H4 ≤ 198.31 / 6 := by linarith
  have hc1 : U + 2 * S1 - D ≤ Real.log q + 1.30 := by linarith
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have hL3 : 0 ≤ L ^ 3 := by positivity
  have p1 := mul_le_mul_of_nonneg_left hc1 hL3
  have p2 := mul_le_mul_of_nonneg_left hc2 hL2
  have p3 := mul_le_mul_of_nonneg_left hc3 hL0.le
  nlinarith [p1, p2, p3, hc4, hPA, hPB]

end DetPrimality.Bach
