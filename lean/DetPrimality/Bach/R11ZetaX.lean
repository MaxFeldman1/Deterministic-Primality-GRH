import DetPrimality.Bach.R11ZetaXFormula

/-!
# designB Lemma 2, (3.1): `r11Zx_main_of_zetaZ : R11ZetaZ → R11ZetaExplicit`

Real parts of the identity `r11Zx_formula` and certified bounds for the constants
`H_n = g^{(n)}(-1/2)/n!`, `g = -ζ'/ζ`:

* `Re H_0 = -1/6 - U₀ + Z₂ - (log π + γ)/2`, with `Z₂ = 8/3 + Re G(3/2) + Re ζ'/ζ(3/2)` (Hadamard at `3/2`);
* `Re H_1 = -4/9 + T₂ + 2 Z₄ - Z₂`;
* `|Re H_2 + 8/27 + T₃| ≤ Z₃`, `|Re H_3 + 16/81 - T₄| ≤ Z₄`.

The bounds `Z₂ ≤ 0.047`, `Z₄ ≤ 0.00012` (designB Lemma 1, `R11ZetaZ`) are used as a hypothesis; the
lower bound `Z₂ ≥ 0.0435` is proved here from `∑ Λ(n) n^{-3/2} ≤ 1.5075`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-! ## Hadamard: real parts -/

/-- `∑_ρ m_ρ Re 1/(s-ρ) = Re (1/s + 1/(s-1) + G(s) + ζ'/ζ(s))` for `Re s > 1`. -/
theorem r11Zx_sum_re {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun ρ : ℂ => (zeroOrd χ₁ ρ : ℝ) * (1 / (s - ρ)).re)
      (1 / s + 1 / (s - 1) + Gfun χ₁ s + deriv (LFunction χ₁) s / LFunction χ₁ s).re := by
  have hS := llsZeta_summable
  have hBs : ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
      = 1 / s + 1 / (s - 1) + Gfun χ₁ s - (llsZeta_B : ℂ)
        + deriv (LFunction χ₁) s / LFunction χ₁ s := by
    linear_combination llsZL_decomp hs
  have hsum := summable_hadamard_terms χ₁ hS hs
  have h1 := Complex.hasSum_re hsum.hasSum
  rw [hBs] at h1
  have h2 := llsZeta_summable_re_inv.hasSum
  have hB : ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℝ) * (1 / ρ).re = -llsZeta_B := by
    rw [llsZeta_B_eq_neg_tsum, neg_neg]
  rw [hB] at h2
  have h3 := h1.sub h2
  have e1 : (fun ρ : ℂ => ((zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re
      - (zeroOrd χ₁ ρ : ℝ) * (1 / ρ).re) = fun ρ : ℂ => (zeroOrd χ₁ ρ : ℝ) * (1 / (s - ρ)).re := by
    funext ρ
    rw [natCast_mul_re', Complex.add_re]
    ring
  have e2 : (1 / s + 1 / (s - 1) + Gfun χ₁ s + deriv (LFunction χ₁) s / LFunction χ₁ s).re
      = (1 / s + 1 / (s - 1) + Gfun χ₁ s - (llsZeta_B : ℂ)
        + deriv (LFunction χ₁) s / LFunction χ₁ s).re - -llsZeta_B := by
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    ring
  rw [e1] at h3
  rw [e2]
  exact h3

theorem r11Zx_Z2_eq (hGRH : DirichletLZerosOnLine) :
    r11Z χ₁ 2 = (1 / (3 / 2 : ℂ) + 1 / ((3 / 2 : ℂ) - 1) + Gfun χ₁ (3 / 2)
      + deriv (LFunction χ₁) (3 / 2) / LFunction χ₁ (3 / 2)).re := by
  have h := (r11Zx_sum_re (s := 3 / 2) (by norm_num)).tsum_eq
  rw [← h, r11Z]
  refine tsum_congr fun ρ => ?_
  by_cases h0 : zeroOrd χ₁ ρ = 0
  · simp [h0]
  · rw [r11Zx_re_inv_conj hGRH h0]
    ring

theorem r11Zx_Gfun_two_re :
    (Gfun χ₁ 2).re = -(Real.log Real.pi) / 2 - Real.eulerMascheroniConstant / 2 := by
  rcases llsPer_Gfun_two_re χ₁ with ⟨_, hG⟩ | ⟨hsh, _⟩
  · exact hG
  · rw [llsZL_gammaShift] at hsh
    exact absurd hsh (by norm_num)

theorem r11Zx_Gfun_three_halves_re :
    (Gfun χ₁ (3 / 2)).re = -(Real.log Real.pi) / 2 - Real.eulerMascheroniConstant / 2
      - ∑' i, r11Zx_u1 i := by
  have h := hasSum_Gfun_sub χ₁ (s := 3 / 2) (by norm_num)
  rw [llsZL_gammaShift] at h
  have h2 : HasSum (fun k : ℕ => ((-r11Zx_u1 k : ℝ) : ℂ)) (Gfun χ₁ (3 / 2) - Gfun χ₁ 2) := by
    convert h using 1
    funext k
    rw [r11Zx_u1]
    push_cast
    ring
  have h3 := h2.tsum_eq
  rw [← Complex.ofReal_tsum, tsum_neg] at h3
  have h4 : Gfun χ₁ (3 / 2) = Gfun χ₁ 2 + ((-∑' i, r11Zx_u1 i : ℝ) : ℂ) := by
    rw [h3]; ring
  rw [h4, Complex.add_re, Complex.ofReal_re, r11Zx_Gfun_two_re]
  ring

theorem r11Zx_Z2_ge (hGRH : DirichletLZerosOnLine) : 0.0435 ≤ r11Z χ₁ 2 := by
  rw [r11Zx_Z2_eq hGRH]
  have hL := norm_logDeriv_LFunction_three_halves_le_sharp χ₁
  have hre := Complex.abs_re_le_norm (deriv (LFunction χ₁) (3 / 2) / LFunction χ₁ (3 / 2))
  have hG := r11Zx_Gfun_three_halves_re
  have h1 : (1 / (3 / 2 : ℂ)).re = 2 / 3 := by
    rw [show (1 : ℂ) / (3 / 2) = ((2 / 3 : ℝ) : ℂ) by push_cast; norm_num, Complex.ofReal_re]
  have h2 : (1 / ((3 / 2 : ℂ) - 1)).re = 2 := by
    rw [show (1 : ℂ) / ((3 / 2) - 1) = ((2 : ℝ) : ℂ) by push_cast; norm_num, Complex.ofReal_re]
  rw [Complex.add_re, Complex.add_re, Complex.add_re, h1, h2, hG]
  have h3 := r11Zx_U1_le
  have h4 := r11Zx_log_pi_le
  have h5 := llsZeta_gamma_lt
  have h6 := (abs_le.mp (hre.trans hL)).1
  linarith

/-- `Z₃ ≤ (t Z₂ + Z₄/t)/2` with `t = 1/20`. -/
theorem r11Zx_Z3_le (hGRH : DirichletLZerosOnLine) (h2 : r11Z χ₁ 2 ≤ 0.047)
    (h4 : r11Z χ₁ 4 ≤ 0.00012) : r11Z χ₁ 3 ≤ 0.003 := by
  have hs2 := r11Zx_summable_Z hGRH (n := 2) le_rfl
  have hs3 := r11Zx_summable_Z hGRH (n := 3) (by norm_num)
  have hs4 := r11Zx_summable_Z hGRH (n := 4) (by norm_num)
  have hsum := ((hs2.hasSum.mul_left (1 / 20)).add (hs4.hasSum.mul_left 20)).div_const 2
  have hle : ∀ ρ : ℂ, (zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 3
      ≤ (1 / 20 * ((zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 2)
        + 20 * ((zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ 4)) / 2 := by
    intro ρ
    by_cases h0 : zeroOrd χ₁ ρ = 0
    · simp [h0]
    · obtain ⟨-, h1, -, -, -, -⟩ := r11Zx_zfacts hGRH h0
      set a := ‖ρ + 1 / 2‖ with ha
      have ha0 : 0 < a := by linarith
      have key : 1 / a ^ 3 ≤ (1 / 20 * (1 / a ^ 2) + 20 * (1 / a ^ 4)) / 2 := by
        rw [show (1 / 20 * (1 / a ^ 2) + 20 * (1 / a ^ 4)) / 2
            = (a ^ 2 + 400) / (40 * a ^ 4) by field_simp; ring,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (pow_nonneg ha0.le 3) (sq_nonneg (a - 20))]
      have hm : (0 : ℝ) ≤ (zeroOrd χ₁ ρ : ℝ) := Nat.cast_nonneg _
      calc (zeroOrd χ₁ ρ : ℝ) / a ^ 3 = (zeroOrd χ₁ ρ : ℝ) * (1 / a ^ 3) := by ring
        _ ≤ (zeroOrd χ₁ ρ : ℝ) * ((1 / 20 * (1 / a ^ 2) + 20 * (1 / a ^ 4)) / 2) :=
            mul_le_mul_of_nonneg_left key hm
        _ = _ := by ring
  have h := hs3.tsum_le_tsum hle hsum.summable
  rw [hsum.tsum_eq] at h
  unfold r11Z at h2 h4 ⊢
  linarith

/-! ## Real parts of the constants -/

theorem r11Zx_pole_re (n : ℕ) : (1 / (1 + 1 / 2 : ℂ) ^ (n + 1)).re = (2 / 3 : ℝ) ^ (n + 1) := by
  have h : (1 / (1 + 1 / 2 : ℂ) ^ (n + 1)) = (((2 / 3 : ℝ) ^ (n + 1) : ℝ) : ℂ) := by
    push_cast
    rw [show (1 + 1 / 2 : ℂ) = (2 / 3)⁻¹ by norm_num, inv_pow, one_div, inv_inv]
  rw [h, Complex.ofReal_re]

theorem r11Zx_cG_re (n : ℕ) :
    (∑' i, r11Zx_cG n i).re = (-1) ^ (n + 1) * ∑' i, r11Zx_t (n + 1) i := by
  simp only [r11Zx_cG_eq]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re, tsum_mul_left]

theorem r11Zx_aG_re : (∑' i, r11Zx_aG i).re = -∑' i, r11Zx_u0 i := by
  simp only [r11Zx_aG_eq]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re, tsum_neg]

theorem r11Zx_Hn_re (n : ℕ) : (r11Zx_Hn n).re = -(2 / 3 : ℝ) ^ (n + 1)
    + (-1) ^ (n + 1) * ∑' i, r11Zx_t (n + 1) i + (∑' ρ, r11Zx_cZ n ρ).re := by
  rw [r11Zx_Hn, Complex.add_re, Complex.add_re, Complex.neg_re, r11Zx_pole_re, r11Zx_cG_re]

theorem r11Zx_cZ_abs (hGRH : DirichletLZerosOnLine) {n : ℕ} (hn : 1 ≤ n) :
    |(∑' ρ, r11Zx_cZ n ρ).re| ≤ r11Z χ₁ (n + 1) := by
  have hs := r11Zx_summable_Z hGRH (n := n + 1) (by omega)
  have hn' : Summable fun ρ => ‖r11Zx_cZ n ρ‖ := hs.congr fun ρ => (r11Zx_norm_cZ n ρ).symm
  calc |(∑' ρ, r11Zx_cZ n ρ).re| ≤ ‖∑' ρ, r11Zx_cZ n ρ‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' ρ, ‖r11Zx_cZ n ρ‖ := norm_tsum_le_tsum_norm hn'
    _ = r11Z χ₁ (n + 1) := by
        rw [r11Z]; exact tsum_congr fun ρ => r11Zx_norm_cZ n ρ

theorem r11Zx_cZ1_re (hGRH : DirichletLZerosOnLine) :
    (∑' ρ, r11Zx_cZ 1 ρ).re = 2 * r11Z χ₁ 4 - r11Z χ₁ 2 := by
  have h4 := r11Zx_summable_Z hGRH (n := 4) (by norm_num)
  have h2 := r11Zx_summable_Z hGRH (n := 2) le_rfl
  rw [Complex.re_tsum (r11Zx_summable_cZ hGRH le_rfl), r11Z, r11Z, ← tsum_mul_left,
    ← (h4.mul_left 2).tsum_sub h2]
  refine tsum_congr fun ρ => ?_
  by_cases h0 : zeroOrd χ₁ ρ = 0
  · simp [r11Zx_cZ, h0]
  · rw [r11Zx_cZ, natCast_mul_re', show (1 + 1 : ℕ) = 2 from rfl, r11Zx_re_inv_sq hGRH h0]
    ring

theorem r11Zx_H0_re (hGRH : DirichletLZerosOnLine) :
    r11Zx_H0.re = -1 / 6 - ∑' i, r11Zx_u0 i + r11Z χ₁ 2 - Real.log Real.pi / 2
      - Real.eulerMascheroniConstant / 2 := by
  have hs2 := r11Zx_sum_re (s := 2) (by norm_num)
  have hZ2 := (r11Zx_summable_Z hGRH (n := 2) le_rfl).hasSum
  have haZ : (∑' ρ, r11Zx_aZ ρ).re = r11Z χ₁ 2
      + (1 / 2 + 1 / (2 - 1) + Gfun χ₁ 2 + deriv (LFunction χ₁) 2 / LFunction χ₁ 2).re := by
    have h := hZ2.add hs2
    rw [Complex.re_tsum (r11Zx_summable_aZ hGRH), r11Z, ← h.tsum_eq]
    refine tsum_congr fun ρ => ?_
    by_cases h0 : zeroOrd χ₁ ρ = 0
    · simp [r11Zx_aZ, h0]
    · rw [r11Zx_aZ, natCast_mul_re', Complex.add_re, r11Zx_re_inv hGRH h0]
      ring
  have hc1 : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hc2 : (1 / (1 + 1 / 2 : ℂ)).re = 2 / 3 := by
    have := r11Zx_pole_re 0
    simpa using this
  have hc4 : (1 / ((2 : ℂ) - 1)).re = 1 := by norm_num
  have hc5 : ((3 / 2 : ℂ)).re = 3 / 2 := by norm_num
  have hG2 := r11Zx_Gfun_two_re
  rw [r11Zx_H0]
  simp only [Complex.add_re, Complex.sub_re]
  rw [haZ, r11Zx_aG_re, llsZL_c1]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]
  linarith

theorem r11Zx_bZ_abs (hGRH : DirichletLZerosOnLine) {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : 0 < x) :
    |(∑' ρ, r11Zx_bZ j x ρ).re| ≤ x * r11Z χ₁ (j + 1) := by
  have hs := r11Zx_summable_Z hGRH (n := j + 1) (by omega)
  have hb := r11Zx_summable_bZ hGRH hj hx
  calc |(∑' ρ, r11Zx_bZ j x ρ).re| ≤ ‖∑' ρ, r11Zx_bZ j x ρ‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' ρ, ‖r11Zx_bZ j x ρ‖ := norm_tsum_le_tsum_norm hb.norm
    _ ≤ ∑' ρ : ℂ, x * ((zeroOrd χ₁ ρ : ℝ) / ‖ρ + 1 / 2‖ ^ (j + 1)) :=
        hb.norm.tsum_le_tsum (r11Zx_norm_bZ_le hGRH j hx) (hs.mul_left x)
    _ = x * r11Z χ₁ (j + 1) := by rw [tsum_mul_left, r11Z]

theorem r11Zx_bG_abs {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : 1 ≤ x) :
    |(∑' i, r11Zx_bG j x i).re| ≤ ∑' i, r11Zx_t (j + 1) i := by
  have hb := r11Zx_summable_bG hj hx
  calc |(∑' i, r11Zx_bG j x i).re| ≤ ‖∑' i, r11Zx_bG j x i‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' i, ‖r11Zx_bG j x i‖ := norm_tsum_le_tsum_norm hb.norm
    _ ≤ ∑' i, r11Zx_t (j + 1) i :=
        hb.norm.tsum_le_tsum (r11Zx_norm_bG_le j hx) (r11Zx_t_summable (by omega))

theorem r11Zx_cf_re (L : ℝ) (l : ℕ) (H : ℂ) :
    (((L : ℂ) ^ l / (l.factorial : ℂ)) * H).re = L ^ l / (l.factorial : ℝ) * H.re := by
  rw [show ((L : ℂ) ^ l / (l.factorial : ℂ)) = ((L ^ l / (l.factorial : ℝ) : ℝ) : ℂ) by
    push_cast; rfl, Complex.re_ofReal_mul]

theorem r11Zx_main_re (a : ℝ) (n : ℕ) :
    ((a : ℂ) / (1 + 1 / 2 : ℂ) ^ (n + 1)).re = a * (2 / 3 : ℝ) ^ (n + 1) := by
  rw [div_eq_mul_one_div, Complex.re_ofReal_mul, r11Zx_pole_re]

/-- Real form of designB Lemma 2. -/
theorem r11Zx_formula_re (hGRH : DirichletLZerosOnLine) {j : ℕ} (hj : j = 1 ∨ j = 2 ∨ j = 3)
    {x : ℝ} (hx : 1 ≤ x) :
    r11A j x = (j.factorial : ℝ) * (√x * x * (2 / 3 : ℝ) ^ (j + 1)
      - (∑' ρ, r11Zx_bZ j x ρ).re - (∑' i, r11Zx_bG j x i).re
      + ∑ l ∈ Finset.range j, Real.log x ^ l / (l.factorial : ℝ) * (r11Zx_Hn (j - l)).re
      + Real.log x ^ j / (j.factorial : ℝ) * r11Zx_H0.re) := by
  have h := congrArg Complex.re (r11Zx_formula hGRH hj hx)
  rw [Complex.ofReal_re, natCast_mul_re', Complex.add_re, Complex.add_re, Complex.sub_re,
    Complex.sub_re, Complex.re_sum, r11Zx_cf_re, ← Complex.ofReal_mul, r11Zx_main_re] at h
  simp only [r11Zx_cf_re] at h
  exact h

/-! ## The main theorem -/

/-- **designB Lemma 2, (3.1)**, given designB Lemma 1 (`R11ZetaZ`). -/
theorem r11Zx_main_of_zetaZ (hZ : R11ZetaZ) : R11ZetaExplicit := by
  intro hGRH j hj1 hj3 y hy
  obtain ⟨hZ2, hZ4⟩ := hZ hGRH
  have hy0 : 0 < y := by linarith
  have hj : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  have hL : 0 ≤ Real.log y := Real.log_nonneg hy.le
  have hZ2lo := r11Zx_Z2_ge hGRH
  have hZ4nn : 0 ≤ r11Z χ₁ 4 := tsum_nonneg fun ρ => by positivity
  have hZ3 := r11Zx_Z3_le hGRH hZ2 hZ4
  have hU0 := r11Zx_U0_le
  have hU0nn : 0 ≤ ∑' i, r11Zx_u0 i := tsum_nonneg r11Zx_u0_nonneg
  have hpi := r11Zx_log_pi_le
  have hpi' := szs_log_pi_gt
  have hγ := llsZeta_gamma_lt
  have hγ' := szs_gamma_gt
  have hT2 := r11Zx_T2_le
  have hT3 := r11Zx_T3_le
  have hT4 := r11Zx_T4_le
  have hT2' := r11Zx_T_ge (n := 2) le_rfl
  have hT4' := r11Zx_T_ge (n := 4) (by norm_num)
  have hT3nn : 0 ≤ ∑' i, r11Zx_t 3 i := tsum_nonneg (r11Zx_t_nonneg 3)
  -- the constants
  have hH0 : |r11Zx_H0.re| ≤ 1.771 := by
    rw [r11Zx_H0_re hGRH, abs_le]
    constructor <;> linarith
  have hH1 : |(r11Zx_Hn 1).re| ≤ 0.148 := by
    rw [r11Zx_Hn_re, r11Zx_cZ1_re hGRH, abs_le]
    norm_num at hT2' ⊢
    constructor <;> linarith
  have hH2 : |(r11Zx_Hn 2).re| ≤ 1.281 / 2 := by
    have hc := abs_le.mp ((r11Zx_cZ_abs hGRH (n := 2) (by norm_num)).trans hZ3)
    rw [r11Zx_Hn_re, abs_le]
    norm_num at hc ⊢
    constructor <;> linarith
  have hH3 : |(r11Zx_Hn 3).re| ≤ 0.0515 / 6 := by
    have hc := abs_le.mp ((r11Zx_cZ_abs hGRH (n := 3) (by norm_num)).trans hZ4)
    rw [r11Zx_Hn_re, abs_le]
    norm_num at hc hT4' ⊢
    constructor <;> linarith
  obtain ⟨h0l, h0u⟩ := abs_le.mp hH0
  obtain ⟨h1l, h1u⟩ := abs_le.mp hH1
  obtain ⟨h2l, h2u⟩ := abs_le.mp hH2
  obtain ⟨h3l, h3u⟩ := abs_le.mp hH3
  have hre := r11Zx_formula_re hGRH hj hy.le
  have hj1' : 1 ≤ j := hj1
  obtain ⟨hZl, hZu⟩ := abs_le.mp (r11Zx_bZ_abs hGRH hj1' hy0)
  have hGb := r11Zx_bG_abs hj1' hy.le
  have hL2 : 0 ≤ Real.log y ^ 2 := pow_nonneg hL 2
  have hL3 : 0 ≤ Real.log y ^ 3 := pow_nonneg hL 3
  rw [rpow_three_halves hy0, hre, r11r, abs_le]
  rcases hj with rfl | rfl | rfl
  · obtain ⟨hGl, hGu⟩ := abs_le.mp (hGb.trans (hT2.trans (by norm_num : (0.6355 : ℝ) ≤ 0.64)))
    have e1 := mul_le_mul_of_nonneg_left h0u hL
    have e2 := mul_le_mul_of_nonneg_left h0l hL
    norm_num [Finset.sum_range_succ, Nat.factorial, Nat.choose, r11gam] at hZl hZu hGl hGu ⊢
    constructor <;> linarith
  · obtain ⟨hGl, hGu⟩ := abs_le.mp (hGb.trans (hT3.trans (by norm_num : (0.34 : ℝ) ≤ 0.64)))
    have e1 := mul_le_mul_of_nonneg_left h0u hL2
    have e2 := mul_le_mul_of_nonneg_left h0l hL2
    have e3 := mul_le_mul_of_nonneg_left h1u hL
    have e4 := mul_le_mul_of_nonneg_left h1l hL
    norm_num [Finset.sum_range_succ, Nat.factorial, Nat.choose, r11gam] at hZl hZu hGl hGu ⊢
    constructor <;> linarith
  · obtain ⟨hGl, hGu⟩ := abs_le.mp (hGb.trans (hT4.trans (by norm_num : (0.20595 : ℝ) ≤ 0.64)))
    have e1 := mul_le_mul_of_nonneg_left h0u hL3
    have e2 := mul_le_mul_of_nonneg_left h0l hL3
    have e3 := mul_le_mul_of_nonneg_left h1u hL2
    have e4 := mul_le_mul_of_nonneg_left h1l hL2
    have e5 := mul_le_mul_of_nonneg_left h2u hL
    have e6 := mul_le_mul_of_nonneg_left h2l hL
    norm_num [Finset.sum_range_succ, Nat.factorial, Nat.choose, r11gam] at hZl hZu hGl hGu ⊢
    constructor <;> linarith

#print axioms r11Zx_formula
#print axioms r11Zx_main_of_zetaZ

end DetPrimality.Bach
