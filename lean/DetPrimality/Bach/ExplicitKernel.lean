import DetPrimality.Bach.ExplicitPerron

/-!
# Per-zero kernel integral (fully proved)

`kernel_zero_bound`: for `Re ρ < 1`,
`∫ |y| |K(2+iy)| / |2+iy-ρ| dy ≤ CJ (1+|Im ρ|)^{-3/4}`, `K(s) = 1/(s(s+1))`.
-/

open Complex MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

/-- `1/(ab) ≤ 2 g^{-3/4} b^{-5/4}` when `1 ≤ b ≤ a` and `g ≤ a + b`. -/
theorem inv_mul_le_aux {a b g : ℝ} (hb : 1 ≤ b) (hba : b ≤ a) (hg : 1 ≤ g) (habg : g ≤ a + b) :
    1 / (a * b) ≤ 2 * g ^ (-(3 / 4 : ℝ)) * b ^ (-(5 / 4 : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  have hg0 : 0 < g := by linarith
  have ha' : g / 2 ≤ a := by linarith
  have h1 : a ^ (-(3 / 4 : ℝ)) ≤ (g / 2) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) ha' (by norm_num)
  have h2 : a ^ (-(1 / 4 : ℝ)) ≤ b ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hb0 hba (by norm_num)
  have h3 : (g / 2) ^ (-(3 / 4 : ℝ)) ≤ 2 * g ^ (-(3 / 4 : ℝ)) := by
    rw [Real.div_rpow hg0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
      neg_neg, mul_comm]
    have h4 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 / 4 : ℝ) ≤ 1)
      simpa using this
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hsplit : 1 / (a * b) = a ^ (-(3 / 4 : ℝ)) * a ^ (-(1 / 4 : ℝ)) * b ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add ha0, show (-(3 / 4 : ℝ)) + -(1 / 4) = -1 by norm_num,
      Real.rpow_neg_one, Real.rpow_neg_one]
    field_simp
  have hb5 : b ^ (-(1 / 4 : ℝ)) * b ^ (-(1 : ℝ)) = b ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add hb0]; norm_num
  rw [hsplit]
  calc a ^ (-(3 / 4 : ℝ)) * a ^ (-(1 / 4 : ℝ)) * b ^ (-(1 : ℝ))
      ≤ (2 * g ^ (-(3 / 4 : ℝ))) * b ^ (-(1 / 4 : ℝ)) * b ^ (-(1 : ℝ)) := by
        gcongr
        exact h1.trans h3
    _ = 2 * g ^ (-(3 / 4 : ℝ)) * b ^ (-(5 / 4 : ℝ)) := by rw [mul_assoc, hb5]

theorem inv_mul_le_sym {a b g : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hg : 1 ≤ g) (habg : g ≤ a + b) :
    1 / (a * b) ≤ 2 * g ^ (-(3 / 4 : ℝ)) * (a ^ (-(5 / 4 : ℝ)) + b ^ (-(5 / 4 : ℝ))) := by
  have hA : 0 ≤ a ^ (-(5 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hB : 0 ≤ b ^ (-(5 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hG : 0 ≤ g ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  rcases le_total b a with h | h
  · have := inv_mul_le_aux hb h hg habg
    nlinarith
  · have := inv_mul_le_aux ha h hg (by linarith)
    rw [mul_comm a b]
    nlinarith

theorem kernel_zero_bound : ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ ρ : ℂ, ρ.re < 1 →
    Integrable (fun y : ℝ => |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
      / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖) ∧
    ∫ y : ℝ, |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
      / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ ≤ CJ * (1 + |ρ.im|) ^ (-(3 / 4 : ℝ)) := by
  set P : ℝ → ℝ := fun y => (1 + ‖y‖) ^ (-(5 / 4 : ℝ)) with hPdef
  have hP : Integrable P := integrable_one_add_norm (by simp; norm_num)
  have hPnn : 0 ≤ ∫ y, P y := integral_nonneg fun y => Real.rpow_nonneg (by positivity) _
  refine ⟨16 * ∫ y, P y, by positivity, fun ρ hρ => ?_⟩
  set γ := ρ.im with hγ
  set g : ℝ := 1 + |γ| with hg
  have hg1 : 1 ≤ g := by rw [hg]; linarith [abs_nonneg γ]
  set f : ℝ → ℝ := fun y => |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
      / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ with hfdef
  have hsρ : ∀ y : ℝ, (((2 : ℝ) : ℂ) + y * I) - ρ ≠ 0 := fun y =>
    ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith)
  have hcont : Continuous f := by
    refine Continuous.div (continuous_abs.mul (Continuous.norm (continuous_const.div
      (by fun_prop) (fun y => mul_ne_zero (ne_zero_of_re_pos (by rw [line_re]; norm_num))
        (ne_zero_of_re_pos (by rw [Complex.add_re, line_re]; simp; norm_num))))))
      (Continuous.norm (by fun_prop)) (fun y => norm_ne_zero_iff.mpr (hsρ y))
  set B : ℝ → ℝ := fun y => (8 * g ^ (-(3 / 4 : ℝ))) * (P y + P (y - γ)) with hBdef
  have hBint : Integrable B := ((hP.add (hP.comp_sub_right γ)).const_mul _)
  have hfB : ∀ y, f y ≤ B y := by
    intro y
    have hK := norm_kernel_le (c := 2) two_pos y
    have hsρn : 0 < ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ := norm_pos_iff.mpr (hsρ y)
    have hre := Complex.re_le_norm ((((2 : ℝ) : ℂ) + y * I) - ρ)
    have him := Complex.abs_im_le_norm ((((2 : ℝ) : ℂ) + y * I) - ρ)
    rw [Complex.sub_re, line_re] at hre
    have himv : ((((2 : ℝ) : ℂ) + y * I) - ρ).im = y - γ := by simp [hγ]
    rw [himv] at him
    set a : ℝ := 1 + |y| with ha
    set b : ℝ := 1 + |y - γ| with hb
    have ha1 : 1 ≤ a := by rw [ha]; linarith [abs_nonneg y]
    have hb1 : 1 ≤ b := by rw [hb]; linarith [abs_nonneg (y - γ)]
    have habg : g ≤ a + b := by
      have : |γ| ≤ |y| + |y - γ| := by
        calc |γ| = |y - (y - γ)| := by ring_nf
          _ ≤ |y| + |y - γ| := abs_sub _ _
      rw [hg, ha, hb]; linarith
    have hA : |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ ≤ 2 / a := by
      calc _ ≤ |y| * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) := mul_le_mul_of_nonneg_left hK (abs_nonneg y)
        _ ≤ 2 / a := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by linarith), ha]
          nlinarith [sq_abs y, abs_nonneg y]
    have hBb : 1 / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ ≤ 2 / b := by
      rw [div_le_div_iff₀ hsρn (by linarith), hb]
      linarith
    have hkey := inv_mul_le_sym ha1 hb1 hg1 habg
    have hfab : f y ≤ 4 / (a * b) := by
      simp only [hfdef]
      rw [div_eq_mul_one_div]
      calc _ ≤ (2 / a) * (2 / b) :=
            mul_le_mul hA hBb (by positivity) (by positivity)
        _ = 4 / (a * b) := by ring
    have hPa : P y = a ^ (-(5 / 4 : ℝ)) := by simp [hPdef, ha, Real.norm_eq_abs]
    have hPb : P (y - γ) = b ^ (-(5 / 4 : ℝ)) := by simp [hPdef, hb, Real.norm_eq_abs]
    simp only [hBdef, hPa, hPb]
    calc f y ≤ 4 / (a * b) := hfab
      _ = 4 * (1 / (a * b)) := by ring
      _ ≤ 4 * (2 * g ^ (-(3 / 4 : ℝ)) * (a ^ (-(5 / 4 : ℝ)) + b ^ (-(5 / 4 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hkey (by norm_num)
      _ = 8 * g ^ (-(3 / 4 : ℝ)) * (a ^ (-(5 / 4 : ℝ)) + b ^ (-(5 / 4 : ℝ))) := by ring
  have hfnn : ∀ y, 0 ≤ f y := fun y => by simp only [hfdef]; positivity
  have hfint : Integrable f := hBint.mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (hfnn y)]; exact hfB y)
  refine ⟨hfint, ?_⟩
  calc ∫ y, f y ≤ ∫ y, B y := integral_mono hfint hBint hfB
    _ = 8 * g ^ (-(3 / 4 : ℝ)) * ((∫ y, P y) + ∫ y, P (y - γ)) := by
        simp only [hBdef]
        rw [integral_const_mul, integral_add hP (hP.comp_sub_right γ)]
    _ = (16 * ∫ y, P y) * g ^ (-(3 / 4 : ℝ)) := by
        rw [integral_sub_right_eq_self (fun y => P y) γ]
        ring

end DetPrimality.Bach
