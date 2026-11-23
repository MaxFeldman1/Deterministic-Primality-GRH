import DetPrimality.Bach.R11ZetaXSums
import DetPrimality.Bach.R11ZetaXNum

/-!
# designB Lemma 2: the explicit formula for `A_j(y)` (`r11Zx_formula`)

Under RH, for `j ∈ {1,2,3}` and `x ≥ 1`:

`A_j(x) = j! [ (2/3)^{j+1} x^{3/2} - ∑_ρ m_ρ x^{ρ+1/2}/(ρ+1/2)^{j+1} - ∑_{m ≥ 1} x^{1/2-2m}/(1/2-2m)^{j+1}
            + ∑_{i<j} (log^i x/i!) H_{j-i} + (log^j x/j!) H_0 ]`,

where `H_n = g^{(n)}(-1/2)/n!` (`g = -ζ'/ζ`) is given by its partial-fraction expansion:
`H_n = -(2/3)^{n+1} + ∑_{m ≥ 1} (1/2-2m)^{-n-1} + ∑_ρ m_ρ (ρ+1/2)^{-n-1}` (`n ≥ 1`), and `H_0` the
re-centred value.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-! ## Facts about the zeros under RH -/

theorem r11Zx_zfacts (hGRH : DirichletLZerosOnLine) {ρ : ℂ} (h : zeroOrd χ₁ ρ ≠ 0) :
    (ρ + 1 / 2).re = 1 ∧ 1 ≤ ‖ρ + 1 / 2‖ ∧ 0 < ‖ρ‖ ∧ ‖ρ‖ ^ 2 ≤ ‖ρ + 1 / 2‖ ^ 2
      ∧ ‖ρ‖ ^ 2 ≤ ‖2 - ρ‖ ^ 2 ∧ ‖ρ + 1 / 2‖ ^ 2 = 1 + ρ.im ^ 2 := by
  have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ₁ h
  have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hhalfi : ((1 / 2 : ℂ)).im = 0 := by norm_num
  have hre : (ρ + 1 / 2).re = 1 := by rw [Complex.add_re, hρ, hhalf]; norm_num
  have hρ0 : ρ ≠ 0 := by
    intro h0; rw [h0] at hρ; norm_num at hρ
  have ha2 : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hρ]; ring
  have hb2 : ‖ρ + 1 / 2‖ ^ 2 = 1 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, Complex.add_im, hhalfi]; ring
  have hc2 : ‖2 - ρ‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hρ]
    norm_num
    ring
  refine ⟨hre, ?_, norm_pos_iff.mpr hρ0, ?_, ?_, hb2⟩
  · have := Complex.re_le_norm (ρ + 1 / 2)
    rwa [hre] at this
  · rw [ha2, hb2]; linarith
  · rw [ha2, hc2]; linarith

theorem r11Zx_re_inv (hGRH : DirichletLZerosOnLine) {ρ : ℂ} (h : zeroOrd χ₁ ρ ≠ 0) :
    (1 / (ρ + 1 / 2)).re = 1 / ‖ρ + 1 / 2‖ ^ 2 := by
  obtain ⟨hre, -, -, -, -, -⟩ := r11Zx_zfacts hGRH h
  rw [one_div, Complex.inv_re, hre, Complex.sq_norm]

theorem r11Zx_re_inv_conj (hGRH : DirichletLZerosOnLine) {ρ : ℂ} (h : zeroOrd χ₁ ρ ≠ 0) :
    (1 / (3 / 2 - ρ)).re = 1 / ‖ρ + 1 / 2‖ ^ 2 := by
  obtain ⟨hre, -, -, -, -, hb2⟩ := r11Zx_zfacts hGRH h
  have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ₁ h
  have h32 : ((3 / 2 : ℂ)).re = 3 / 2 := by norm_num
  have h32i : ((3 / 2 : ℂ)).im = 0 := by norm_num
  rw [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, h32, h32i, hρ,
    hb2]
  congr 1 <;> ring

theorem r11Zx_re_inv_sq (hGRH : DirichletLZerosOnLine) {ρ : ℂ} (h : zeroOrd χ₁ ρ ≠ 0) :
    (1 / (ρ + 1 / 2) ^ 2).re = 2 / ‖ρ + 1 / 2‖ ^ 4 - 1 / ‖ρ + 1 / 2‖ ^ 2 := by
  obtain ⟨hre, h1, -, -, -, hb2⟩ := r11Zx_zfacts hGRH h
  have hN : Complex.normSq (ρ + 1 / 2) = 1 + ρ.im ^ 2 := by rw [← Complex.sq_norm, hb2]
  have hhalfi : ((1 / 2 : ℂ)).im = 0 := by norm_num
  have him : (ρ + 1 / 2).im = ρ.im := by rw [Complex.add_im, hhalfi, add_zero]
  have h4 : ‖ρ + 1 / 2‖ ^ 4 = (1 + ρ.im ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hb2]
  have hpos : (0 : ℝ) < 1 + ρ.im ^ 2 := by positivity
  rw [one_div, ← inv_pow, sq, Complex.mul_re, Complex.inv_re, Complex.inv_im, hre, him, hN, h4,
    hb2]
  field_simp
  ring

theorem r11Zx_norm_cpow (hGRH : DirichletLZerosOnLine) {ρ : ℂ} (h : zeroOrd χ₁ ρ ≠ 0) {x : ℝ}
    (hx : 0 < x) : ‖(x : ℂ) ^ ρ‖ = √x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, re_eq_half_of_zeroOrd_ne_zero hGRH χ₁ h,
    Real.sqrt_eq_rpow]

/-! ## Summability -/

theorem r11Zx_Zterm_le (hGRH : DirichletLZerosOnLine) {n : ℕ} (hn : 2 ≤ n) (ρ : ℂ) :
    (zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ n ≤ (zeroOrd χ₁ ρ : ℝ) / ‖ρ‖ ^ 2 := by
  by_cases h0 : zeroOrd χ₁ ρ = 0
  · simp [h0]
  · obtain ⟨-, h1, hpos, h2, -, -⟩ := r11Zx_zfacts hGRH h0
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      (h2.trans (pow_le_pow_right₀ h1 hn))

theorem r11Zx_summable_Z (hGRH : DirichletLZerosOnLine) {n : ℕ} (hn : 2 ≤ n) :
    Summable fun ρ : ℂ => (zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ n :=
  Summable.of_nonneg_of_le (fun ρ => by positivity) (r11Zx_Zterm_le hGRH hn) llsZeta_summable

/-- `m_ρ (1/(ρ+1/2) + 1/(2-ρ))`. -/
noncomputable def r11Zx_aZ (ρ : ℂ) : ℂ := (zeroOrd χ₁ ρ : ℂ) * (1 / (ρ + 1 / 2) + 1 / (2 - ρ))

/-- `m_ρ / (ρ+1/2)^{n+1}`. -/
noncomputable def r11Zx_cZ (n : ℕ) (ρ : ℂ) : ℂ := (zeroOrd χ₁ ρ : ℂ) * (1 / (ρ + 1 / 2) ^ (n + 1))

/-- `m_ρ x^{ρ+1/2} / (ρ+1/2)^{j+1}`. -/
noncomputable def r11Zx_bZ (j : ℕ) (x : ℝ) (ρ : ℂ) : ℂ :=
  (zeroOrd χ₁ ρ : ℂ) * ((√x : ℂ) * (x : ℂ) ^ ρ / (ρ + 1 / 2) ^ (j + 1))

theorem r11Zx_norm_cZ (n : ℕ) (ρ : ℂ) :
    ‖r11Zx_cZ n ρ‖ = (zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ (n + 1) := by
  rw [r11Zx_cZ, norm_mul, Complex.norm_natCast, norm_div, norm_one, norm_pow]
  ring

theorem r11Zx_summable_cZ (hGRH : DirichletLZerosOnLine) {n : ℕ} (hn : 1 ≤ n) :
    Summable (r11Zx_cZ n) :=
  Summable.of_norm_bounded (r11Zx_summable_Z hGRH (n := n + 1) (by omega))
    (fun ρ => (r11Zx_norm_cZ n ρ).le)

theorem r11Zx_norm_bZ_le (hGRH : DirichletLZerosOnLine) (j : ℕ) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖r11Zx_bZ j x ρ‖ ≤ x * ((zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ (j + 1)) := by
  by_cases h0 : zeroOrd χ₁ ρ = 0
  · simp [r11Zx_bZ, h0]
  · rw [r11Zx_bZ, norm_mul, Complex.norm_natCast, norm_div, norm_mul, norm_pow,
      r11Zx_norm_cpow hGRH h0 hx, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x),
      Real.mul_self_sqrt hx.le]
    apply le_of_eq
    ring

theorem r11Zx_summable_bZ (hGRH : DirichletLZerosOnLine) {j : ℕ} (hj : 1 ≤ j) {x : ℝ}
    (hx : 0 < x) : Summable (r11Zx_bZ j x) :=
  Summable.of_norm_bounded ((r11Zx_summable_Z hGRH (n := j + 1) (by omega)).mul_left x)
    (r11Zx_norm_bZ_le hGRH j hx)

theorem r11Zx_norm_aZ_le (hGRH : DirichletLZerosOnLine) (ρ : ℂ) :
    ‖r11Zx_aZ ρ‖ ≤ 5 / 2 * ((zeroOrd χ₁ ρ : ℝ) / ‖ρ‖ ^ 2) := by
  by_cases h0 : zeroOrd χ₁ ρ = 0
  · simp [r11Zx_aZ, h0]
  · obtain ⟨hre, h1, hpos, h2, h3, -⟩ := r11Zx_zfacts hGRH h0
    have hz : ρ + 1 / 2 ≠ 0 := norm_pos_iff.mp (by linarith)
    have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ₁ h0
    have hw : 2 - ρ ≠ 0 := ne_zero_of_re_pos (by rw [Complex.sub_re, hρ]; norm_num)
    have hid : 1 / (ρ + 1 / 2) + 1 / (2 - ρ) = (5 / 2) / ((ρ + 1 / 2) * (2 - ρ)) := by
      rw [div_add_div _ _ hz hw, div_eq_div_iff (mul_ne_zero hz hw) (mul_ne_zero hz hw)]
      ring
    have hle1 : ‖ρ‖ ≤ ‖ρ + 1 / 2‖ := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
      two_ne_zero).mp h2
    have hle2 : ‖ρ‖ ≤ ‖2 - ρ‖ := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
      two_ne_zero).mp h3
    have h52 : ‖(5 / 2 : ℂ)‖ = 5 / 2 := by
      rw [show (5 / 2 : ℂ) = ((5 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
      norm_num
    rw [r11Zx_aZ, hid, norm_mul, Complex.norm_natCast, norm_div, norm_mul, h52]
    have hden : ‖ρ‖ ^ 2 ≤ ‖ρ + 1 / 2‖ * ‖2 - ρ‖ := by
      rw [sq]; exact mul_le_mul hle1 hle2 hpos.le (by positivity)
    have := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 5 / 2 by norm_num) (by positivity) hden
    calc (zeroOrd χ₁ ρ : ℝ) * (5 / 2 / (‖ρ + 1 / 2‖ * ‖2 - ρ‖))
        ≤ (zeroOrd χ₁ ρ : ℝ) * (5 / 2 / ‖ρ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = _ := by ring

theorem r11Zx_summable_aZ (hGRH : DirichletLZerosOnLine) : Summable r11Zx_aZ :=
  Summable.of_norm_bounded (llsZeta_summable.mul_left (5 / 2)) (r11Zx_norm_aZ_le hGRH)

/-! ## The trivial zeros -/

/-- `1/(2 + 2(i+1)) + 1/(1/2 - 2(i+1))`. -/
noncomputable def r11Zx_aG (i : ℕ) : ℂ :=
  1 / (2 + ((2 * (i + 1) : ℕ) : ℂ)) + 1 / (-((2 * (i + 1) : ℕ) : ℂ) + 1 / 2)

/-- `1/(1/2 - 2(i+1))^{n+1}`. -/
noncomputable def r11Zx_cG (n i : ℕ) : ℂ := 1 / (-((2 * (i + 1) : ℕ) : ℂ) + 1 / 2) ^ (n + 1)

/-- `x^{1/2 - 2(i+1)} / (1/2 - 2(i+1))^{j+1}`. -/
noncomputable def r11Zx_bG (j : ℕ) (x : ℝ) (i : ℕ) : ℂ :=
  (√x : ℂ) * (x : ℂ) ^ (-((2 * (i + 1) : ℕ) : ℂ)) / (-((2 * (i + 1) : ℕ) : ℂ) + 1 / 2) ^ (j + 1)

theorem r11Zx_triv_eq (i : ℕ) :
    (-((2 * (i + 1) : ℕ) : ℂ) + 1 / 2) = ((-(2 * (i : ℝ) + 3 / 2) : ℝ) : ℂ) := by
  push_cast; ring

theorem r11Zx_aG_eq (i : ℕ) : r11Zx_aG i = ((-r11Zx_u0 i : ℝ) : ℂ) := by
  rw [r11Zx_aG, r11Zx_triv_eq, r11Zx_u0,
    show (2 + ((2 * (i + 1) : ℕ) : ℂ)) = ((2 * (i : ℝ) + 4 : ℝ) : ℂ) by push_cast; ring]
  push_cast
  rw [div_neg]
  ring

theorem r11Zx_cG_eq (n i : ℕ) :
    r11Zx_cG n i = (((-1) ^ (n + 1) * r11Zx_t (n + 1) i : ℝ) : ℂ) := by
  rw [r11Zx_cG, r11Zx_triv_eq, r11Zx_t]
  push_cast
  rw [neg_pow, one_div, mul_inv, ← inv_pow, inv_neg_one, one_div]

theorem r11Zx_summable_cG {n : ℕ} (hn : 1 ≤ n) : Summable (r11Zx_cG n) := by
  have h : Summable fun i : ℕ => (((-1) ^ (n + 1) * r11Zx_t (n + 1) i : ℝ) : ℂ) :=
    Complex.summable_ofReal.mpr ((r11Zx_t_summable (n := n + 1) (by omega)).mul_left _)
  exact h.congr fun i => (r11Zx_cG_eq n i).symm

theorem r11Zx_summable_aG : Summable r11Zx_aG := by
  have h : Summable fun i : ℕ => ((-r11Zx_u0 i : ℝ) : ℂ) :=
    Complex.summable_ofReal.mpr (r11Zx_u0_tele 0).1.neg
  exact h.congr fun i => (r11Zx_aG_eq i).symm

theorem r11Zx_norm_bG_le (j : ℕ) {x : ℝ} (hx : 1 ≤ x) (i : ℕ) :
    ‖r11Zx_bG j x i‖ ≤ r11Zx_t (j + 1) i := by
  have hx0 : 0 < x := by linarith
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hre : (-((2 * (i + 1) : ℕ) : ℂ)).re = -(2 * (i : ℝ) + 2) := by
    push_cast; simp; ring
  have hn : ‖(-((2 * (i + 1) : ℕ) : ℂ) + 1 / 2)‖ = 2 * (i : ℝ) + 3 / 2 := by
    rw [r11Zx_triv_eq, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  rw [r11Zx_bG, norm_div, norm_mul, norm_pow, hn, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x), r11Zx_t]
  have h1 : √x * x ^ (-(2 * (i : ℝ) + 2)) ≤ 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  exact div_le_div_of_nonneg_right h1 (by positivity)

theorem r11Zx_summable_bG {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : 1 ≤ x) :
    Summable (r11Zx_bG j x) :=
  Summable.of_norm_bounded (r11Zx_t_summable (n := j + 1) (by omega)) (r11Zx_norm_bG_le j hx)

/-! ## The constants `H_n` -/

/-- `H_n = g^{(n)}(-1/2)/n!` for `n ≥ 1` (`g = -ζ'/ζ`). -/
noncomputable def r11Zx_Hn (n : ℕ) : ℂ :=
  -(1 / (1 + 1 / 2 : ℂ) ^ (n + 1)) + ∑' i, r11Zx_cG n i + ∑' ρ, r11Zx_cZ n ρ

/-- `H_0 = g(-1/2)`. -/
noncomputable def r11Zx_H0 : ℂ :=
  llsZL_c1 + 1 / 2 - 1 / (1 + 1 / 2 : ℂ) + ∑' i, r11Zx_aG i + ∑' ρ, r11Zx_aZ ρ

/-! ## Multiplying by `√x` -/

theorem r11Zx_sqrt_R {j : ℕ} (hj : j = 1 ∨ j = 2 ∨ j = 3) {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (√x : ℂ) * r11Zx_R (j + 1) w x = (√x : ℂ) * (x : ℂ) ^ w / (w + 1 / 2) ^ (j + 1)
      - ∑ l ∈ Finset.range j, ((Real.log x : ℂ) ^ l / (l.factorial : ℂ))
          * (1 / (w + 1 / 2) ^ (j - l + 1))
      - ((Real.log x : ℂ) ^ j / (j.factorial : ℂ)) * (1 / (w + 1 / 2)) := by
  have hsx : ((√x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  unfold r11Zx_R
  rw [mul_sub, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ hsx, one_mul]
  rcases hj with rfl | rfl | rfl <;> simp [Finset.sum_range_succ] <;> ring

theorem r11Zx_sqrt_one (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (√x : ℂ) * r11Zx_one (j + 1) x = (Real.log x : ℂ) ^ j / (j.factorial : ℂ) := by
  have hsx : ((√x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  unfold r11Zx_one
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp

/-- **designB Lemma 2** (the identity). -/
theorem r11Zx_formula (hGRH : DirichletLZerosOnLine) {j : ℕ} (hj : j = 1 ∨ j = 2 ∨ j = 3) {x : ℝ}
    (hx : 1 ≤ x) :
    ((r11A j x : ℝ) : ℂ) = (j.factorial : ℂ) * ((√x : ℂ) * (x : ℂ) / (1 + 1 / 2 : ℂ) ^ (j + 1)
      - ∑' ρ, r11Zx_bZ j x ρ - ∑' i, r11Zx_bG j x i
      + ∑ l ∈ Finset.range j, ((Real.log x : ℂ) ^ l / (l.factorial : ℂ)) * r11Zx_Hn (j - l)
      + ((Real.log x : ℂ) ^ j / (j.factorial : ℂ)) * r11Zx_H0) := by
  have hx0 : 0 < x := by linarith
  have hj1 : 1 ≤ j := by rcases hj with rfl | rfl | rfl <;> norm_num
  have hk : j + 1 = 2 ∨ j + 1 = 3 ∨ j + 1 = 4 := by rcases hj with rfl | rfl | rfl <;> simp
  have hsx : ((√x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hx0).ne'
  have hfac : ((j.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  set Q := r11Zx_Q (j + 1) (fun s => -(deriv (LFunction χ₁) s / LFunction χ₁ s)) x with hQ
  set cf : ℕ → ℂ := fun l => (Real.log x : ℂ) ^ l / (l.factorial : ℂ) with hcf
  -- Perron
  have hA : ((r11A j x : ℝ) : ℂ) = (j.factorial : ℂ) * ((√x : ℂ) * Q) := by
    rw [hQ, r11Zx_perron hk hx, r11A]
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp
  -- the Γ-part
  have hG := r11Zx_hasSum_Q_gamma hk χ₁ hx
  rw [llsZL_gammaShift] at hG
  simp only [add_zero, r11Zx_Q_gterm hk _ hx] at hG
  have hG0 := hG.summable.tsum_eq_zero_add
  have hGs : Summable fun i : ℕ => (1 / (2 + ((2 * (i + 1) : ℕ) : ℂ)) * r11Zx_one (j + 1) x
      - r11Zx_R (j + 1) (-((2 * (i + 1) : ℕ) : ℂ)) x) :=
    (summable_nat_add_iff 1).mpr hG.summable
  have hPG : ∀ i : ℕ, (√x : ℂ) * (1 / (2 + ((2 * (i + 1) : ℕ) : ℂ)) * r11Zx_one (j + 1) x
      - r11Zx_R (j + 1) (-((2 * (i + 1) : ℕ) : ℂ)) x)
      = -r11Zx_bG j x i + ∑ l ∈ Finset.range j, cf l * r11Zx_cG (j - l) i
        + cf j * r11Zx_aG i := by
    intro i
    rw [mul_sub, mul_left_comm, r11Zx_sqrt_one j hx0, r11Zx_sqrt_R hj hx0]
    simp only [r11Zx_bG, r11Zx_cG, r11Zx_aG, hcf]
    ring
  have hGsum : HasSum (fun i : ℕ => -r11Zx_bG j x i
      + ∑ l ∈ Finset.range j, cf l * r11Zx_cG (j - l) i + cf j * r11Zx_aG i)
      (-∑' i, r11Zx_bG j x i + ∑ l ∈ Finset.range j, cf l * ∑' i, r11Zx_cG (j - l) i
        + cf j * ∑' i, r11Zx_aG i) :=
    ((r11Zx_summable_bG hj1 hx).hasSum.neg.add (hasSum_sum fun l hl =>
      ((r11Zx_summable_cG (n := j - l) (by have := Finset.mem_range.mp hl; omega)).hasSum.mul_left
        (cf l)))).add (r11Zx_summable_aG.hasSum.mul_left (cf j))
  have hGtot : (√x : ℂ) * ∑' i : ℕ, (1 / (2 + ((2 * (i + 1) : ℕ) : ℂ)) * r11Zx_one (j + 1) x
      - r11Zx_R (j + 1) (-((2 * (i + 1) : ℕ) : ℂ)) x)
      = -∑' i, r11Zx_bG j x i + ∑ l ∈ Finset.range j, cf l * ∑' i, r11Zx_cG (j - l) i
        + cf j * ∑' i, r11Zx_aG i := by
    rw [← tsum_mul_left, ← hGsum.tsum_eq]
    exact tsum_congr hPG
  -- the zeros
  have hPZ : ∀ ρ : ℂ, (√x : ℂ) * ((zeroOrd χ₁ ρ : ℂ)
      * (r11Zx_R (j + 1) ρ x - 1 / (2 - ρ) * r11Zx_one (j + 1) x))
      = r11Zx_bZ j x ρ - ∑ l ∈ Finset.range j, cf l * r11Zx_cZ (j - l) ρ
        - cf j * r11Zx_aZ ρ := by
    intro ρ
    rw [mul_left_comm, mul_sub, mul_left_comm (√x : ℂ) (1 / (2 - ρ)), r11Zx_sqrt_one j hx0,
      r11Zx_sqrt_R hj hx0]
    simp only [r11Zx_bZ, r11Zx_cZ, r11Zx_aZ, hcf]
    rw [mul_sub, mul_sub, mul_sub, Finset.mul_sum]
    have e : ∀ l ∈ Finset.range j, (zeroOrd χ₁ ρ : ℂ) * ((Real.log x : ℂ) ^ l / (l.factorial : ℂ)
        * (1 / (ρ + 1 / 2) ^ (j - l + 1)))
        = (Real.log x : ℂ) ^ l / (l.factorial : ℂ)
          * ((zeroOrd χ₁ ρ : ℂ) * (1 / (ρ + 1 / 2) ^ (j - l + 1))) := fun l _ => by ring
    rw [Finset.sum_congr rfl e]
    ring
  have hZsum : HasSum (fun ρ : ℂ => r11Zx_bZ j x ρ
      - ∑ l ∈ Finset.range j, cf l * r11Zx_cZ (j - l) ρ - cf j * r11Zx_aZ ρ)
      (∑' ρ, r11Zx_bZ j x ρ - ∑ l ∈ Finset.range j, cf l * ∑' ρ, r11Zx_cZ (j - l) ρ
        - cf j * ∑' ρ, r11Zx_aZ ρ) :=
    ((r11Zx_summable_bZ hGRH hj1 hx0).hasSum.sub (hasSum_sum fun l hl =>
      ((r11Zx_summable_cZ hGRH (n := j - l)
        (by have := Finset.mem_range.mp hl; omega)).hasSum.mul_left (cf l)))).sub
      ((r11Zx_summable_aZ hGRH).hasSum.mul_left (cf j))
  have hZtot : (√x : ℂ) * ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ)
      * (r11Zx_R (j + 1) ρ x - 1 / (2 - ρ) * r11Zx_one (j + 1) x)
      = ∑' ρ, r11Zx_bZ j x ρ - ∑ l ∈ Finset.range j, cf l * ∑' ρ, r11Zx_cZ (j - l) ρ
        - cf j * ∑' ρ, r11Zx_aZ ρ := by
    rw [← tsum_mul_left, ← hZsum.tsum_eq]
    exact tsum_congr hPZ
  -- assembly
  have hE := r11Zx_explicit hk hx
  rw [← hQ, hG0] at hE
  simp only [Nat.mul_zero, Nat.cast_zero, neg_zero, add_zero] at hE
  have hR1 := r11Zx_sqrt_R hj hx0 1
  rw [Complex.cpow_one] at hR1
  have hone := r11Zx_sqrt_one j hx0
  have hQx : (√x : ℂ) * Q = (√x : ℂ) * (x : ℂ) / (1 + 1 / 2 : ℂ) ^ (j + 1)
      - ∑' ρ, r11Zx_bZ j x ρ - ∑' i, r11Zx_bG j x i
      + ∑ l ∈ Finset.range j, cf l * r11Zx_Hn (j - l) + cf j * r11Zx_H0 := by
    have hH : ∑ l ∈ Finset.range j, cf l * r11Zx_Hn (j - l)
        = -∑ l ∈ Finset.range j, cf l * (1 / (1 + 1 / 2 : ℂ) ^ (j - l + 1))
          + ∑ l ∈ Finset.range j, cf l * ∑' i, r11Zx_cG (j - l) i
          + ∑ l ∈ Finset.range j, cf l * ∑' ρ, r11Zx_cZ (j - l) ρ := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [r11Zx_Hn]; ring
    have hQ1 : (√x : ℂ) * Q = llsZL_c1 * ((√x : ℂ) * r11Zx_one (j + 1) x)
        + (√x : ℂ) * r11Zx_R (j + 1) 1 x + 1 / 2 * ((√x : ℂ) * r11Zx_one (j + 1) x)
        + (√x : ℂ) * ∑' i : ℕ, (1 / (2 + ((2 * (i + 1) : ℕ) : ℂ)) * r11Zx_one (j + 1) x
            - r11Zx_R (j + 1) (-((2 * (i + 1) : ℕ) : ℂ)) x)
        - (√x : ℂ) * ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ)
            * (r11Zx_R (j + 1) ρ x - 1 / (2 - ρ) * r11Zx_one (j + 1) x) := by
      rw [hE]; ring
    rw [hQ1, hGtot, hZtot, hR1, hone, hH, r11Zx_H0]
    simp only [hcf]
    ring
  rw [hA, hQx]

end DetPrimality.Bach
