import DetPrimality.Barrier.dual_Coeff
import DetPrimality.Barrier.dual_Data

/-!
# The limit of the CMQR framework: `C(1) ≤ 1.14654`

Carneiro–Milinovich–Quesada-Herrera–Ramos (arXiv:2404.08380), extremal problem (EP1) at `A = 1`
(the case of the least quadratic non-residue / index 2):

  `C(1) = sup_{0 ≠ F ∈ 𝒜} (2π/‖F‖₁) ( ∫_{-∞}^0 F̂(t) e^{πt} dt - ∫_0^∞ |F̂(t)| e^{πt} dt )`,

`𝒜 = {F ∈ L¹(ℝ), F̂ real-valued}`, `F̂ = 𝓕 F` (Mathlib's convention `∫ F(x) e^{-2πixt} dx`, which
is CMQR's).  Their Theorem 3 gives `limsup n_χ / log² q ≤ C(1)⁻²` under GRH.

`cmqr_EP1_le`: for every `F ∈ 𝒜` the (EP1) numerator is `≤ 1.14654 ‖F‖₁ / 2π`, i.e.
`C(1) ≤ 1.14654`, so the method cannot give a constant below `C(1)⁻² ≥ 0.76071`.

The proof is weak duality (`dual_weak_duality`, CMQR Prop. 6) with the explicit dual function
`ψ(t) = s(2πt) e^{πt}`, `s` the step function with 26 steps encoded by `dualVD`, and the bound
`2π ‖𝓕 g‖_∞ ≤ 1.14654` checked in the kernel (`dual_cert`, 5476 cells).
-/

open MeasureTheory Set
open scoped FourierTransform Real

namespace DetPrimality.Barrier

theorem dualData_coeff : dualCoeffOK dualVD dualVA ((1 : ℚ) / 100000000) = true := by
  decide +kernel

/-- The dual function `g = 1_{t<0} e^{πt} - 1_{t>0} ψ`. -/
noncomputable def dualFn : ℝ → ℝ := dualG (dualL dualVD)

theorem dualFn_integrable : Integrable dualFn := dualG_integrable _

theorem dualFn_neg {t : ℝ} (ht : t < 0) : dualFn t = Real.exp (π * t) := by
  have h := (dualCoeffOK_sound dualData_coeff).2.1 (2 * π * t)
    (by have := Real.pi_pos; nlinarith)
  rw [dualFn, dualG_eq, h, mul_one]

theorem dualFn_pos (t : ℝ) : |dualFn t| ≤ Real.exp (π * t) := by
  have h := (dualCoeffOK_sound dualData_coeff).1 (2 * π * t)
  rw [dualFn, dualG_eq, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le h

/-- `sup_y |N(y)| / √(1/4 + y²) ≤ 1.14654` for the exponential sum of the dual function. -/
theorem dualN_bound (y : ℝ) :
    ‖dualN (dualL dualVD) y‖ ≤ 1.14654 * Real.sqrt (1 / 4 + y ^ 2) := by
  have h1 := (dualCoeffOK_sound dualData_coeff).2.2 y
  have h2 := dual_cert dualData_par dualData_rots dualData_run y
  have hcp : ((dualPar.cp : ℚ) : ℝ) = 1.1465399 := by simp [dualPar]; norm_num
  rw [hcp] at h2
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 4 + y ^ 2) := by
    have := Real.abs_le_sqrt (x := 1 / 2) (y := 1 / 4 + y ^ 2) (by nlinarith [sq_nonneg y])
    rwa [abs_of_pos (by norm_num)] at this
  have h3 : ‖dualN (dualL dualVD) y‖ ≤ ‖dualNq dualVA y‖ + ((1 / 100000000 : ℚ) : ℝ) := by
    have := norm_le_norm_add_norm_sub' (dualN (dualL dualVD) y) (dualNq dualVA y)
    linarith
  push_cast at h3
  linarith

/-- `2π ‖𝓕 g‖_∞ ≤ 1.14654`: the value of (EP2) at `A = 1` is at most `1.14654`. -/
theorem dualFn_fourier_bound (x : ℝ) :
    ‖𝓕 (fun t => (dualFn t : ℂ)) x‖ ≤ 1.14654 / (2 * π) := by
  have hpi := Real.pi_pos
  have hs : 0 < Real.sqrt (1 / 4 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h := dualN_bound (-x)
  rw [neg_sq] at h
  unfold dualFn
  rw [dualG_fourier_norm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ 2 * π)]

/-- **The framework limit `C(1) ≤ 1.14654`** (CMQR (EP1), `A = 1`).  For `F ∈ L¹(ℝ)` with
real-valued Fourier transform, such that the (EP1) functional is not `-∞` (`hint`). -/
theorem cmqr_EP1_le {F : ℝ → ℂ} (hF : Integrable F) (hreal : ∀ t, (𝓕 F t).im = 0)
    (hint : IntegrableOn (fun t => (𝓕 F t).re * Real.exp (π * t)) (Ioi 0)) :
    2 * π * ((∫ t in Iic 0, (𝓕 F t).re * Real.exp (π * t))
        - ∫ t in Ioi 0, |(𝓕 F t).re| * Real.exp (π * t))
      ≤ 1.14654 * ∫ x, ‖F x‖ := by
  have hpi := Real.pi_pos
  have h := dual_weak_duality hF hreal dualFn_integrable (fun t ht => dualFn_neg ht)
    (fun t _ => dualFn_pos t) dualFn_fourier_bound hint
  rw [integral_Iic_eq_integral_Iio]
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * π)
  refine h2.trans (le_of_eq ?_)
  field_simp

/-- The same in normalised form: `J(F) ≤ 1.14654` for `F ≠ 0`. -/
theorem cmqr_C_one_le {F : ℝ → ℂ} (hF : Integrable F) (hreal : ∀ t, (𝓕 F t).im = 0)
    (hint : IntegrableOn (fun t => (𝓕 F t).re * Real.exp (π * t)) (Ioi 0))
    (h0 : 0 < ∫ x, ‖F x‖) :
    2 * π / (∫ x, ‖F x‖) * ((∫ t in Iic 0, (𝓕 F t).re * Real.exp (π * t))
        - ∫ t in Ioi 0, |(𝓕 F t).re| * Real.exp (π * t))
      ≤ 1.14654 := by
  have h := cmqr_EP1_le hF hreal hint
  rw [div_mul_eq_mul_div, div_le_iff₀ h0]
  exact h

/-- `C(1)⁻² ≥ 0.76071`: no test function in (EP1) proves `limsup n_χ / log² q ≤ c` with
`c < 0.76071`. -/
theorem cmqr_barrier : (0.76071 : ℝ) ≤ ((1.14654 : ℝ) ^ 2)⁻¹ := by norm_num

end DetPrimality.Barrier
