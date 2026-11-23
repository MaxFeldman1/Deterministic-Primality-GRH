import DetPrimality.Bach.R11ChiPerron
import DetPrimality.Bach.LLSPerronMain

/-!
# designB Lemma 3: the explicit formula for `Φ_χ(y)` (Perron side)

* `r11Chi_r a k = 1/2 - (2k + a)` : the (shifted) trivial zeros `s_k`;
* `r11Chi_coeff χ n = χ(n) Λ(n) √n`, `r11Chi_term_shift`, `r11Chi_Phi_eq_perron` :
  `Φ_χ(y) = 6 · P₃[L(f, ·)](y)`;
* `r11Chi_decomp` : on `Re s > 3/2`,
  `L(f,s) = -L'/L(s - 1/2) = -L'/L(3/2) - ∑_k (1/(s-s_k) - 1/(2-s_k))
     - ∑_ρ m_ρ (1/(s-(ρ+1/2)) - 1/(2-(ρ+1/2)))`  (Hadamard, re-centred at `3/2`);
* `r11Chi_perron_pole3` : closed form of `P₃[1/(s-w) - 1/(2-w)]`;
* `r11Chi_Phi_formula` : `Φ_χ(y) = -L'/L(3/2) log³ y - 6 ∑_k Q(s_k) - 6 ∑_ρ m_ρ Q(ρ+1/2)`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## The trivial zeros `s_k = 1/2 - (2k + a)` -/

/-- `s_k = 1/2 - (2k + a)`. -/
noncomputable def r11Chi_r (a k : ℕ) : ℝ := 1 / 2 - (2 * k + a)

theorem r11Chi_r_succ (a k : ℕ) : r11Chi_r a (k + 1) = r11Chi_r a k - 2 := by
  unfold r11Chi_r; push_cast; ring

theorem r11Chi_r_le (a k : ℕ) : r11Chi_r a k ≤ 1 / 2 - k := by
  unfold r11Chi_r
  have h1 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  linarith

theorem r11Chi_r_cases (a k : ℕ) : r11Chi_r a k = 1 / 2 ∨ r11Chi_r a k ≤ -(1 / 2) := by
  unfold r11Chi_r
  rcases Nat.eq_zero_or_pos (2 * k + a) with h | h
  · left
    have : ((2 * k + a : ℕ) : ℝ) = 0 := by rw [h]; simp
    push_cast at this
    linarith
  · right
    have : (1 : ℝ) ≤ ((2 * k + a : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith

theorem r11Chi_r_ne (a k : ℕ) : r11Chi_r a k ≠ 0 := by
  rcases r11Chi_r_cases a k with h | h <;> intro h0 <;> rw [h0] at h <;> norm_num at h

theorem r11Chi_half_le_abs_r (a k : ℕ) : 1 / 2 ≤ |r11Chi_r a k| := by
  rcases r11Chi_r_cases a k with h | h
  · rw [h]; norm_num
  · rw [abs_of_nonpos (by linarith)]; linarith

theorem r11Chi_abs_r_ge (a k : ℕ) : ((k : ℝ) + 1) / 4 ≤ |r11Chi_r a k| := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := r11Chi_half_le_abs_r a 0
    norm_num
    linarith
  · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h2 := r11Chi_r_le a k
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem r11Chi_r_neg (a : ℕ) {k : ℕ} (hk : 1 ≤ k) : r11Chi_r a k ≤ -(3 / 2) := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  unfold r11Chi_r
  linarith

theorem r11Chi_two_sub_r_ge (a k : ℕ) : (k : ℝ) + 1 ≤ 2 - r11Chi_r a k := by
  have := r11Chi_r_le a k
  have h1 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem r11Chi_summable_inv_sq : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 :=
  llsPer_hasSum_inv_succ_sq.summable

theorem r11Chi_summable_inv_r_pow (a : ℕ) {j : ℕ} (hj : 2 ≤ j) :
    Summable fun k : ℕ => 1 / r11Chi_r a k ^ j := by
  set c : ℝ := (1 / 2) ^ (j - 2) with hc
  have hc0 : 0 < c := by positivity
  refine Summable.of_norm_bounded (r11Chi_summable_inv_sq.mul_left (16 / c)) fun k => ?_
  have h1 := r11Chi_half_le_abs_r a k
  have h2 := r11Chi_abs_r_ge a k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpow : |r11Chi_r a k| ^ j = |r11Chi_r a k| ^ 2 * |r11Chi_r a k| ^ (j - 2) := by
    rw [← pow_add]; congr 1; omega
  have h3 : c ≤ |r11Chi_r a k| ^ (j - 2) := pow_le_pow_left₀ (by norm_num) h1 _
  have h4 : ((k : ℝ) + 1) ^ 2 ≤ 16 * |r11Chi_r a k| ^ 2 := by nlinarith
  have h5 : ((k : ℝ) + 1) ^ 2 * c ≤ 16 * |r11Chi_r a k| ^ j := by
    rw [hpow]
    have := mul_le_mul h4 h3 hc0.le (by positivity)
    linarith
  rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs,
    show 16 / c * (1 / ((k : ℝ) + 1) ^ 2) = 16 / (c * ((k : ℝ) + 1) ^ 2) by field_simp,
    div_le_div_iff₀ (pow_pos (abs_pos.mpr (r11Chi_r_ne a k)) j) (by positivity)]
  linarith

theorem r11Chi_summable_inv_two_sub_r_pow (a : ℕ) {j : ℕ} (hj : 2 ≤ j) :
    Summable fun k : ℕ => 1 / (2 - r11Chi_r a k) ^ j := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) r11Chi_summable_inv_sq
  · have := r11Chi_two_sub_r_ge a k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : 0 < 2 - r11Chi_r a k := by linarith
    positivity
  · have h := r11Chi_two_sub_r_ge a k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    apply one_div_le_one_div_of_le (by positivity)
    calc ((k : ℝ) + 1) ^ 2 ≤ (2 - r11Chi_r a k) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
      _ ≤ (2 - r11Chi_r a k) ^ j := pow_le_pow_right₀ (by linarith) hj

theorem r11Chi_summable_inv_add (a : ℕ) :
    Summable fun k : ℕ => 1 / r11Chi_r a k + 1 / (2 - r11Chi_r a k) := by
  refine Summable.of_norm_bounded (r11Chi_summable_inv_sq.mul_left 8) fun k => ?_
  have h1 := r11Chi_abs_r_ge a k
  have h2 := r11Chi_two_sub_r_ge a k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr := r11Chi_r_ne a k
  have h2r : 2 - r11Chi_r a k ≠ 0 := by linarith
  have e : 1 / r11Chi_r a k + 1 / (2 - r11Chi_r a k)
      = 2 / (r11Chi_r a k * (2 - r11Chi_r a k)) := by
    field_simp
    ring
  have hpos : 0 < |r11Chi_r a k| := abs_pos.mpr hr
  rw [e, norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by linarith : (0 : ℝ) < 2 - r11Chi_r a k), abs_of_pos (by norm_num : (0 : ℝ) < 2),
    show 8 * (1 / ((k : ℝ) + 1) ^ 2) = 2 / (((k : ℝ) + 1) ^ 2 / 4) by field_simp; ring,
    div_le_div_iff₀ (mul_pos hpos (by linarith)) (by positivity)]
  have : ((k : ℝ) + 1) / 4 * ((k : ℝ) + 1) ≤ |r11Chi_r a k| * (2 - r11Chi_r a k) :=
    mul_le_mul h1 h2 (by positivity) hpos.le
  nlinarith

/-! ## The Dirichlet series `∑ Λ(n) χ(n) √n · n^{-s}` -/

/-- `f(n) = χ(n) Λ(n) √n`. -/
noncomputable def r11Chi_coeff {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  χ (n : ZMod N) * (Λ n : ℂ) * ((Real.sqrt n : ℝ) : ℂ)

theorem r11Chi_term_shift {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) :
    LSeries.term (r11Chi_coeff χ) s n
      = LSeries.term (fun n => χ (n : ZMod N) * (Λ n : ℂ)) (s - 1 / 2) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, r11Chi_coeff]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hsq : ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rfl
    have h1 : (n : ℂ) ^ s ≠ 0 := by rw [cpow_def_of_ne_zero hn0]; exact exp_ne_zero _
    have h2 : (n : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by rw [cpow_def_of_ne_zero hn0]; exact exp_ne_zero _
    rw [cpow_sub _ _ hn0, hsq]
    field_simp

theorem r11Chi_LSeries_shift {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) :
    LSeries (r11Chi_coeff χ) s = LSeries (fun n => χ (n : ZMod N) * (Λ n : ℂ)) (s - 1 / 2) := by
  unfold LSeries
  exact tsum_congr fun n => r11Chi_term_shift χ s n

theorem r11Chi_summable_coeff {N : ℕ} (χ : DirichletCharacter ℂ N) :
    LSeriesSummable (r11Chi_coeff χ) 2 := by
  have h := LSeriesSummable_twist_vonMangoldt χ (s := 2 - 1 / 2) (by norm_num)
  exact h.congr fun n => (r11Chi_term_shift χ 2 n).symm

/-- `Φ_χ(y) = 6 · P₃[L(f,·)](y)`. -/
theorem r11Chi_Phi_eq_perron {N : ℕ} (χ : DirichletCharacter ℂ N) {y : ℝ} (hy : 0 < y) :
    r11Phi χ y = 6 * r11Chi_perron 3 (LSeries (r11Chi_coeff χ)) y := by
  rw [r11Chi_perron_LSeries (by norm_num) (r11Chi_summable_coeff χ) hy, Finset.mul_sum]
  unfold r11Phi
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [r11Chi_coeff, Nat.factorial]
  push_cast
  ring

/-! ## The Hadamard decomposition, re-centred at `3/2` -/

theorem r11Chi_decomp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries (r11Chi_coeff χ) s
      = -(deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2))
        + ∑' k : ℕ, (-1 : ℂ) * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
            - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)))
        + ∑' ρ : ℂ, (-(zeroOrd χ ρ : ℂ)) * (1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2))) := by
  set z : ℂ := s - 1 / 2 with hz
  have hzre : 1 < z.re := by
    rw [hz, Complex.sub_re]
    norm_num
    linarith
  have h32 : (1 : ℝ) < (3 / 2 : ℂ).re := by norm_num
  have hLS : LSeries (r11Chi_coeff χ) s = -(deriv (LFunction χ) z / LFunction χ z) := by
    have h1 : LSeries (fun n => χ (n : ZMod q) * (Λ n : ℂ)) z = _ :=
      LSeries_twist_vonMangoldt_eq χ hzre
    rw [r11Chi_LSeries_shift, h1, deriv_LFunction_eq_deriv_LSeries χ hzre,
      LFunction_eq_LSeries χ hzre, neg_div]
  have hdz := neg_logDeriv_decomp χ hχ1 hH hS hzre
  have hd32 := neg_logDeriv_decomp χ hχ1 hH hS h32
  have hG1 := hasSum_Gfun_sub χ (s := z) (by linarith)
  have hG2 := hasSum_Gfun_sub χ (s := (3 / 2 : ℂ)) (by norm_num)
  have hA : ∑' k : ℕ, (-1 : ℂ) * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
      - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))) = Gfun χ z - Gfun χ (3 / 2) := by
    have h := (hG2.sub hG1).tsum_eq
    rw [show Gfun χ z - Gfun χ (3 / 2)
        = -(Gfun χ (3 / 2) - Gfun χ 2 - (Gfun χ z - Gfun χ 2)) by ring, ← h, ← tsum_neg]
    refine tsum_congr fun k => ?_
    simp only [r11Chi_r, hz]
    push_cast
    rw [show s - (1 / 2 - (2 * (k : ℂ) + (gammaShift χ : ℂ)))
        = s - 1 / 2 + (2 * (k : ℂ) + (gammaShift χ : ℂ)) by ring,
      show (2 : ℂ) - (1 / 2 - (2 * (k : ℂ) + (gammaShift χ : ℂ)))
        = 3 / 2 + (2 * (k : ℂ) + (gammaShift χ : ℂ)) by ring]
    ring
  have hsm : ∀ {u : ℂ}, 1 < u.re →
      Summable fun ρ : ℂ => (zeroOrd χ ρ : ℂ) * (1 / (u - ρ) - 1 / (2 - ρ)) := by
    intro u hu
    have h := (summable_hadamard_terms χ hS hu).sub
      (summable_hadamard_terms χ hS (s := 2) (by norm_num))
    refine h.congr fun ρ => ?_
    ring
  have hB : ∑' ρ : ℂ, (-(zeroOrd χ ρ : ℂ)) * (1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2)))
      = -((∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (z - ρ) - 1 / (2 - ρ)))
        - ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (3 / 2 - ρ) - 1 / (2 - ρ))) := by
    rw [← (hsm hzre).tsum_sub (hsm h32), ← tsum_neg]
    refine tsum_congr fun ρ => ?_
    rw [hz, show s - (ρ + 1 / 2) = s - 1 / 2 - ρ by ring,
      show (2 : ℂ) - (ρ + 1 / 2) = 3 / 2 - ρ by ring]
    ring
  rw [hLS, hA, hB]
  linear_combination hdz - hd32

/-! ## Closed form of one regularised pole -/

theorem r11Chi_perron_pole3 {w : ℂ} (hw : w.re < 2) (hw0 : w ≠ 0) {y : ℝ} (hy : 1 ≤ y) :
    r11Chi_perron 3 (fun s => 1 / (s - w) - 1 / (2 - w)) y
      = (y : ℂ) ^ w / w ^ 4 - 1 / w ^ 4 - (Real.log y : ℂ) * (1 / w ^ 3)
        - ((Real.log y ^ 2 / 2 : ℝ) : ℂ) * (1 / w ^ 2)
        - ((Real.log y ^ 3 / 6 : ℝ) : ℂ) * (1 / w + 1 / (2 - w)) := by
  have hy0 : 0 < y := by linarith
  have h2w : (2 : ℂ) - w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.sub_re] at this
    norm_num at this
    linarith
  rw [r11Chi_perron_sub (r11Chi_vi_inv_sub (by norm_num) hw) (r11Chi_vi_const (by norm_num) _)
      hy0, r11Chi_perron_inv_sub (by norm_num) hw hw0 hy, r11Chi_perron_const,
    r11Chi_perron_one (by norm_num) hy]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast
  field_simp
  ring

/-! ## The explicit formula -/

theorem r11Chi_summable_gamma_weight (a : ℕ) :
    Summable fun k : ℕ => ‖(-1 : ℂ)‖ / (1 + ‖((r11Chi_r a k : ℝ) : ℂ)‖) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (r11Chi_summable_inv_sq.mul_left 16)
  have h := r11Chi_abs_r_ge a k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [norm_neg, norm_one, Complex.norm_real, Real.norm_eq_abs,
    show 16 * (1 / ((k : ℝ) + 1) ^ 2) = 1 / (((k : ℝ) + 1) / 4) ^ 2 by field_simp; ring]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg (r11Chi_r a k)]) 2

theorem r11Chi_norm_add_half_ge {ρ : ℂ} (h : 0 < ρ.re) : ‖ρ‖ ≤ ‖ρ + 1 / 2‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  have e1 : (ρ + 1 / 2).re = ρ.re + 1 / 2 := by simp
  have e2 : (ρ + 1 / 2).im = ρ.im := by simp
  rw [e1, e2]
  nlinarith

theorem r11Chi_summable_zero_weight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    Summable fun ρ : ℂ => ‖(-(zeroOrd χ ρ : ℂ))‖ / (1 + ‖ρ + 1 / 2‖) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) hS
  rw [norm_neg, Complex.norm_natCast]
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  · have hre := (zeroOrd_strip h0).1
    have hρ : 0 < ‖ρ‖ := norm_pos_iff.mpr (ne_zero_of_re_pos hre)
    have h1 := r11Chi_norm_add_half_ge hre
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    exact pow_le_pow_left₀ hρ.le (by linarith) 2

/-- **The explicit formula** (designB Lemma 3, before taking real parts). -/
theorem r11Chi_Phi_formula {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {y : ℝ} (hy : 1 ≤ y) :
    HasSum (fun k : ℕ => (-1 : ℂ) * r11Chi_perron 3 (fun s =>
        1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
          - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))) y)
      (r11Chi_perron 3 (fun s => ∑' k : ℕ, (-1 : ℂ) * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
          - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)))) y) ∧
    HasSum (fun ρ : ℂ => (-(zeroOrd χ ρ : ℂ)) * r11Chi_perron 3 (fun s =>
        1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2))) y)
      (r11Chi_perron 3 (fun s => ∑' ρ : ℂ, (-(zeroOrd χ ρ : ℂ))
        * (1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2)))) y) ∧
    r11Phi χ y = -(deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)) * (Real.log y : ℂ) ^ 3
      + 6 * r11Chi_perron 3 (fun s => ∑' k : ℕ, (-1 : ℂ)
          * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
            - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)))) y
      + 6 * r11Chi_perron 3 (fun s => ∑' ρ : ℂ, (-(zeroOrd χ ρ : ℂ))
          * (1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2)))) y := by
  have hy0 : 0 < y := by linarith
  have hwk : ∀ k : ℕ, (-1 : ℂ) ≠ 0 → (((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)).re ≤ 3 / 2 := by
    intro k _
    rw [Complex.ofReal_re]
    have := r11Chi_r_le (gammaShift χ) k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hwρ : ∀ ρ : ℂ, (-(zeroOrd χ ρ : ℂ)) ≠ 0 → (ρ + 1 / 2).re ≤ 3 / 2 := by
    intro ρ h
    have h0 : zeroOrd χ ρ ≠ 0 := by
      intro h0; apply h; simp [h0]
    have := (zeroOrd_strip h0).2
    have e1 : (ρ + 1 / 2).re = ρ.re + 1 / 2 := by simp
    rw [e1]; linarith
  have hsk := r11Chi_summable_gamma_weight (gammaShift χ)
  have hsρ := r11Chi_summable_zero_weight χ hS
  refine ⟨r11Chi_perron_hasSum_poles (le_refl 3) _ _ hwk hsk hy0,
    r11Chi_perron_hasSum_poles (le_refl 3) _ _ hwρ hsρ hy0, ?_⟩
  have hviA := r11Chi_vi_poles (le_refl 3) _ _ hwk hsk
  have hviB := r11Chi_vi_poles (le_refl 3) _ _ hwρ hsρ
  set c0 : ℂ := -(deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)) with hc0
  have hvic : VerticalIntegrable (fun s : ℂ => c0 / s ^ (3 + 1)) 2 := r11Chi_vi_const (by norm_num) c0
  have hviCA : VerticalIntegrable (fun s : ℂ => (c0 + ∑' k : ℕ, (-1 : ℂ)
      * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
        - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ)))) / s ^ (3 + 1)) 2 := by
    have h := Integrable.add hvic hviA
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, add_div]
  rw [r11Chi_Phi_eq_perron χ hy0,
    r11Chi_perron_congr_line (g := fun s => (c0 + ∑' k : ℕ, (-1 : ℂ)
      * (1 / (s - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))
        - 1 / (2 - ((r11Chi_r (gammaShift χ) k : ℝ) : ℂ))))
      + ∑' ρ : ℂ, (-(zeroOrd χ ρ : ℂ)) * (1 / (s - (ρ + 1 / 2)) - 1 / (2 - (ρ + 1 / 2))))
      (fun t => r11Chi_decomp χ hχ1 hH hS (by rw [line_re]; norm_num)),
    r11Chi_perron_add hviCA hviB hy0, r11Chi_perron_add hvic hviA hy0, r11Chi_perron_const,
    r11Chi_perron_one (by norm_num) hy]
  simp only [Nat.factorial]
  push_cast
  ring

end DetPrimality.Bach
