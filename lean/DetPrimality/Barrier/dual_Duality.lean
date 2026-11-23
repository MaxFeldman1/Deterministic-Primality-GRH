import Mathlib

/-!
# Weak duality for the CMQR extremal problem (EP1) ≤ (EP2)

Carneiro–Milinovich–Quesada-Herrera–Ramos (arXiv:2404.08380), Proposition 6, at `A = 1`, with
Mathlib's Fourier transform `𝓕 F t = ∫ F(x) e^{-2πixt} dx`.

* `dual_fourier_flip`: the multiplication formula `∫ 𝓕f · g = ∫ f · 𝓕g` for integrable `f, g`.
* `dual_weak_duality`: if `g = e^{π t}` on `t < 0`, `|g| ≤ e^{π t}` on `t > 0`, `g ∈ L¹` and
  `|𝓕 g| ≤ c` everywhere, then the (EP1) numerator of every `F ∈ 𝒜` is `≤ c ‖F‖₁`.
* `dualPiece`, `dualG`: the dual functions used here, finite combinations of one-sided
  exponentials `e^{π t} 1_{t < a}`, and their Fourier transforms in closed form.
-/

open MeasureTheory Set
open scoped FourierTransform Real

namespace DetPrimality.Barrier

/-- The multiplication formula for the Fourier transform on `ℝ`. -/
theorem dual_fourier_flip {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner hf hg
  simp only [smul_eq_mul, flip_innerₗ] at this
  exact this

theorem dual_fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

theorem dual_fourier_norm_le (f : ℝ → ℂ) (t : ℝ) : ‖𝓕 f t‖ ≤ ∫ x, ‖f x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- **CMQR Proposition 6 (weak duality), `A = 1`.**  `F ∈ L¹(ℝ)` with real-valued `𝓕 F`; `g` a
dual function.  The integrability hypothesis `hint` says that the (EP1) functional is not `-∞`. -/
theorem dual_weak_duality {F : ℝ → ℂ} (hF : Integrable F) (hreal : ∀ t, (𝓕 F t).im = 0)
    {g : ℝ → ℝ} (hg : Integrable g) (hneg : ∀ t, t < 0 → g t = Real.exp (π * t))
    (hpos : ∀ t, 0 < t → |g t| ≤ Real.exp (π * t)) {c : ℝ}
    (hc : ∀ x, ‖𝓕 (fun t => (g t : ℂ)) x‖ ≤ c)
    (hint : IntegrableOn (fun t => (𝓕 F t).re * Real.exp (π * t)) (Ioi 0)) :
    (∫ t in Iio 0, (𝓕 F t).re * Real.exp (π * t))
        - ∫ t in Ioi 0, |(𝓕 F t).re| * Real.exp (π * t)
      ≤ c * ∫ x, ‖F x‖ := by
  set φ : ℝ → ℝ := fun t => (𝓕 F t).re with hφ
  have hφc : Continuous φ := Complex.continuous_re.comp (dual_fourier_continuous hF)
  have hbd : ∀ t, ‖φ t‖ ≤ ∫ x, ‖F x‖ := fun t =>
    (Complex.abs_re_le_norm _).trans (dual_fourier_norm_le F t)
  have hφg : Integrable (fun t => φ t * g t) :=
    hg.bdd_mul hφc.aestronglyMeasurable (ae_of_all _ hbd)
  have key : ∫ t, φ t * g t = (∫ x, F x * 𝓕 (fun t => (g t : ℂ)) x).re := by
    have hgC : Integrable (fun t => (g t : ℂ)) := hg.ofReal
    rw [← dual_fourier_flip hF hgC]
    have : ∀ t, 𝓕 F t * (g t : ℂ) = ((φ t * g t : ℝ) : ℂ) := by
      intro t; apply Complex.ext <;> simp [hφ, hreal t]
    simp_rw [this]
    rw [show (∫ ξ, ((φ ξ * g ξ : ℝ) : ℂ)) = ((∫ ξ, φ ξ * g ξ : ℝ) : ℂ) from integral_ofReal,
      Complex.ofReal_re]
  have up : ∫ t, φ t * g t ≤ c * ∫ x, ‖F x‖ := by
    rw [key]
    calc (∫ x, F x * 𝓕 (fun t => (g t : ℂ)) x).re
        ≤ ‖∫ x, F x * 𝓕 (fun t => (g t : ℂ)) x‖ := Complex.re_le_norm _
      _ ≤ ∫ x, ‖F x * 𝓕 (fun t => (g t : ℂ)) x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, c * ‖F x‖ :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hF.norm.const_mul c)
            (ae_of_all _ fun x => by
              show ‖F x * 𝓕 (fun t => (g t : ℂ)) x‖ ≤ c * ‖F x‖
              rw [norm_mul, mul_comm]
              exact mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _))
      _ = c * ∫ x, ‖F x‖ := integral_const_mul _ _
  have split : ∫ t, φ t * g t = (∫ t in Iio 0, φ t * g t) + ∫ t in Ioi 0, φ t * g t := by
    rw [← integral_add_compl measurableSet_Iio hφg, compl_Iio, integral_Ici_eq_integral_Ioi]
  have e1 : ∫ t in Iio 0, φ t * g t = ∫ t in Iio 0, φ t * Real.exp (π * t) :=
    setIntegral_congr_fun measurableSet_Iio fun t ht => by
      simp only [hneg t ht]
  have habs : IntegrableOn (fun t => |φ t| * Real.exp (π * t)) (Ioi 0) := by
    have h := hint.abs
    refine h.congr (ae_of_all _ fun t => ?_)
    simp only [hφ, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e2 : -(∫ t in Ioi 0, |φ t| * Real.exp (π * t)) ≤ ∫ t in Ioi 0, φ t * g t := by
    rw [← integral_neg]
    refine setIntegral_mono_on habs.neg hφg.integrableOn measurableSet_Ioi fun t ht => ?_
    have h1 : |φ t * g t| ≤ |φ t| * Real.exp (π * t) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hpos t ht) (abs_nonneg _)
    linarith [neg_abs_le (φ t * g t)]
  linarith

/-! ## One-sided exponentials -/

/-- `e^{π t} 1_{t < a}`. -/
noncomputable def dualPiece (a t : ℝ) : ℝ := if t < a then Real.exp (π * t) else 0

theorem dualPiece_eq_indicator (a : ℝ) :
    dualPiece a = (Iio a).indicator fun t => Real.exp (π * t) := by
  ext t; simp [dualPiece, indicator]

theorem dualPiece_integrable (a : ℝ) : Integrable (dualPiece a) := by
  rw [dualPiece_eq_indicator, integrable_indicator_iff measurableSet_Iio]
  exact (integrableOn_exp_mul_Iic Real.pi_pos a).mono_set Iio_subset_Iic_self

/-- The frequency variable `w = π (1 - 2 i x)`. -/
noncomputable def dualW (x : ℝ) : ℂ := π - 2 * π * x * Complex.I

theorem dualW_re (x : ℝ) : (dualW x).re = π := by simp [dualW]

theorem dualW_ne (x : ℝ) : dualW x ≠ 0 := fun h => by
  have := dualW_re x; rw [h] at this; exact Real.pi_pos.ne this

theorem dual_integrand_piece (a x v : ℝ) :
    Complex.exp (↑(-2 * π * v * x) * Complex.I) • ((dualPiece a v : ℝ) : ℂ)
      = (Iio a).indicator (fun v : ℝ => Complex.exp (dualW x * v)) v := by
  by_cases h : v < a
  · simp only [dualPiece, h, if_true, indicator, mem_Iio, smul_eq_mul]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; simp only [dualW]; push_cast; ring
  · simp [dualPiece, h, indicator]

theorem dualPiece_fourier (a x : ℝ) :
    𝓕 (fun t => (dualPiece a t : ℂ)) x = Complex.exp (dualW x * a) / dualW x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [dual_integrand_piece]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio]
  exact integral_exp_mul_complex_Iic (by rw [dualW_re]; exact Real.pi_pos) a

/-! ## Finite combinations: `l` is a list of `(v, d)`; node `v/(2π)`, coefficient `d` -/

/-- `g(t) = ∑ d · e^{π t} 1_{t < v/(2π)}`. -/
noncomputable def dualG (l : List (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (l.map fun p => p.2 * dualPiece (p.1 / (2 * π)) t).sum

/-- The step function `∑ d · 1_{u < v}`. -/
noncomputable def dualStep (l : List (ℝ × ℝ)) (u : ℝ) : ℝ :=
  (l.map fun p => if u < p.1 then p.2 else 0).sum

/-- The exponential sum `N(y) = ∑ d e^{v/2} e^{i y v}`. -/
noncomputable def dualN (l : List (ℝ × ℝ)) (y : ℝ) : ℂ :=
  (l.map fun p => ((p.2 * Real.exp (p.1 / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * ((y * p.1 : ℝ) : ℂ))).sum

theorem dualG_eq (l : List (ℝ × ℝ)) (t : ℝ) :
    dualG l t = Real.exp (π * t) * dualStep l (2 * π * t) := by
  induction l with
  | nil => simp [dualG, dualStep]
  | cons p l ih =>
    simp only [dualG, dualStep, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    congr 1
    have : t < p.1 / (2 * π) ↔ 2 * π * t < p.1 := by
      rw [lt_div_iff₀ (by positivity), mul_comm]
    by_cases h : t < p.1 / (2 * π)
    · rw [dualPiece, if_pos h, if_pos (this.mp h)]; ring
    · rw [dualPiece, if_neg h, if_neg (mt this.mpr h)]; ring

theorem dualG_integrable (l : List (ℝ × ℝ)) : Integrable (dualG l) := by
  induction l with
  | nil =>
    have : dualG [] = fun _ => 0 := by ext t; simp [dualG]
    rw [this]; exact integrable_zero _ _ _
  | cons p l ih =>
    have : dualG (p :: l) = fun t => p.2 * dualPiece (p.1 / (2 * π)) t + dualG l t := by
      ext t; simp [dualG]
    rw [this]
    exact ((dualPiece_integrable _).const_mul _).add ih

theorem dual_integrable_exp_smul {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable fun v : ℝ => Complex.exp (↑(-2 * π * v * x) * Complex.I) • f v := by
  simp_rw [smul_eq_mul]
  exact hf.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun v => by rw [Complex.norm_exp_ofReal_mul_I])

theorem dualG_fourier (l : List (ℝ × ℝ)) (x : ℝ) :
    𝓕 (fun t => (dualG l t : ℂ)) x
      = (l.map fun p => (p.2 : ℂ) * Complex.exp (dualW x * (p.1 / (2 * π) : ℝ))).sum / dualW x := by
  induction l with
  | nil => simp [dualG, Real.fourier_real_eq_integral_exp_smul]
  | cons p l ih =>
    have e : ∀ t, ((dualG (p :: l) t : ℝ) : ℂ)
        = (p.2 : ℂ) * (dualPiece (p.1 / (2 * π)) t : ℂ) + (dualG l t : ℂ) := by
      intro t; simp [dualG]
    have i1 : Integrable fun v : ℝ => Complex.exp (↑(-2 * π * v * x) * Complex.I)
        • ((p.2 : ℂ) * (dualPiece (p.1 / (2 * π)) v : ℂ)) :=
      dual_integrable_exp_smul (((dualPiece_integrable _).ofReal).const_mul _) x
    have i2 : Integrable fun v : ℝ => Complex.exp (↑(-2 * π * v * x) * Complex.I)
        • ((dualG l v : ℝ) : ℂ) :=
      dual_integrable_exp_smul (dualG_integrable l).ofReal x
    rw [Real.fourier_real_eq_integral_exp_smul] at ih ⊢
    simp_rw [e, smul_add]
    rw [integral_add i1 i2, ih, List.map_cons, List.sum_cons, add_div]
    congr 1
    have := dualPiece_fourier (p.1 / (2 * π)) x
    rw [Real.fourier_real_eq_integral_exp_smul] at this
    simp_rw [smul_eq_mul] at this ⊢
    simp_rw [mul_left_comm _ (p.2 : ℂ)]
    rw [integral_const_mul, this, mul_div_assoc]

theorem dualG_fourier_norm (l : List (ℝ × ℝ)) (x : ℝ) :
    ‖𝓕 (fun t => (dualG l t : ℂ)) x‖ = ‖dualN l (-x)‖ / (2 * π * Real.sqrt (1 / 4 + x ^ 2)) := by
  rw [dualG_fourier, norm_div]
  congr 1
  · congr 1
    unfold dualN
    congr 1
    refine List.map_congr_left fun p _ => ?_
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [dualW]
    field_simp
    ring_nf
  · have h : ‖dualW x‖ ^ 2 = (2 * π * Real.sqrt (1 / 4 + x ^ 2)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, mul_pow, Real.sq_sqrt (by positivity)]
      simp [dualW]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h

end DetPrimality.Barrier
