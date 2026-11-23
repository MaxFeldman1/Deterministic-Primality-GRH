import Mathlib

/-!
# The Nehari barrier for one-sided kernels (research/below-one/designB.md §1.1)

For `φ : ℝ → ℂ` continuous and integrable with integrable Fourier transform and `φ 0 = 0`
(in particular for `φ` supported on `(-∞, 0]`), with `K(s) = ∫ φ(v) e^{sv} dv`:

  `‖K(1/2)‖ ≤ (1/2π) ∫ ‖K(it)‖ dt`.

Proof: Fourier inversion + Fubini give `∫_{v ≤ 0} φ(v) e^{v/2} dv = ∫ 𝓕φ(w) / a(w) dw` with
`a(w) = 1/2 + 2πiw`, and inversion at `0` gives `∫ 𝓕φ = φ(0) = 0`; hence
`K(1/2) = ∫ 𝓕φ(w) (1/a(w) - 1) dw`, and `1/a - 1 = conj a / a` is unimodular.
(The `- 1` is the `δ₀` of the design note.)  Equality holds for `K(s) = 1/(s+1/2)²`.

Consequently the reduced functional `c = (I / K(1/2))²`, `I = (1/2π)∫‖K(it)‖dt`, is `≥ 1`.
-/

open MeasureTheory Real Complex Set
open scoped FourierTransform

noncomputable section

/-- `a(w) = 1/2 + 2πiw`. -/
def neh_a (w : ℝ) : ℂ := 1 / 2 + 2 * π * w * I

lemma neh_a_re (w : ℝ) : (neh_a w).re = 1 / 2 := by simp [neh_a]

lemma neh_a_ne (w : ℝ) : neh_a w ≠ 0 := fun h => by
  have := neh_a_re w
  rw [h] at this
  norm_num at this

lemma neh_a_norm (w : ℝ) : (1 / 2 : ℝ) ≤ ‖neh_a w‖ :=
  calc (1 / 2 : ℝ) = (neh_a w).re := (neh_a_re w).symm
    _ ≤ |(neh_a w).re| := le_abs_self _
    _ ≤ ‖neh_a w‖ := Complex.abs_re_le_norm _

/-- The symbol `1/a - 1 = conj a / a` has modulus one. -/
lemma neh_unimodular (w : ℝ) : ‖1 / neh_a w - 1‖ = 1 := by
  have h1 : (1 : ℂ) - neh_a w = (starRingEnd ℂ) (neh_a w) := by
    apply Complex.ext <;> simp [neh_a]
    norm_num
  have h : 1 / neh_a w - 1 = (starRingEnd ℂ) (neh_a w) / neh_a w := by
    rw [← h1]
    field_simp [neh_a_ne w]
  rw [h, norm_div, RCLike.norm_conj, div_self (norm_ne_zero_iff.mpr (neh_a_ne w))]

/-- Fourier inversion, written out. -/
lemma neh_inversion {φ : ℝ → ℂ} (hc : Continuous φ) (hφ : Integrable φ)
    (hF : Integrable (𝓕 φ)) (v : ℝ) :
    φ v = ∫ w : ℝ, cexp (↑(2 * π * w * v) * I) * 𝓕 φ w := by
  have h := congrFun (hc.fourierInv_fourier_eq hφ hF) v
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [smul_eq_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- A continuous function vanishing on `(0, ∞)` vanishes at `0`. -/
lemma neh_zero {φ : ℝ → ℂ} (hc : Continuous φ) (hs : ∀ v, 0 < v → φ v = 0) : φ 0 = 0 := by
  have h1 : Filter.Tendsto φ (nhdsWithin 0 (Ioi 0)) (nhds (φ 0)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto φ (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hs v hv).symm
  exact tendsto_nhds_unique h1 h2

/-- **Nehari inequality, general form.** Only `φ 0 = 0` is needed. -/
theorem neh_nehari_of_zero {φ : ℝ → ℂ} (hc : Continuous φ) (hφ : Integrable φ)
    (hF : Integrable (𝓕 φ)) (h0 : φ 0 = 0) :
    ‖∫ v in Iic (0 : ℝ), φ v * cexp ((1 / 2 : ℂ) * v)‖ ≤ ∫ w, ‖𝓕 φ w‖ := by
  have hpt : ∀ v : ℝ, φ v * cexp ((1 / 2 : ℂ) * v) = ∫ w, cexp (neh_a w * v) * 𝓕 φ w := by
    intro v
    rw [neh_inversion hc hφ hF v, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [neh_a]
    rw [mul_right_comm, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hint : Integrable (Function.uncurry fun (v w : ℝ) => cexp (neh_a w * v) * 𝓕 φ w)
      ((volume.restrict (Iic (0 : ℝ))).prod volume) := by
    have hg : Integrable (fun z : ℝ × ℝ => cexp ((1 / 2 : ℂ) * z.1) * 𝓕 φ z.2)
        ((volume.restrict (Iic (0 : ℝ))).prod volume) :=
      Integrable.mul_prod (integrableOn_exp_mul_complex_Iic (by norm_num) 0) hF
    refine hg.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine AEStronglyMeasurable.mul ?_ hF.aestronglyMeasurable.comp_snd
      exact Continuous.aestronglyMeasurable (by unfold neh_a; fun_prop)
    · simp only [Function.uncurry, norm_mul, Complex.norm_exp]
      apply le_of_eq
      congr 2
      simp [neh_a]
  have hK : ∫ v in Iic (0 : ℝ), φ v * cexp ((1 / 2 : ℂ) * v) = ∫ w, 1 / neh_a w * 𝓕 φ w := by
    simp_rw [hpt]
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [integral_mul_const, integral_exp_mul_complex_Iic (by rw [neh_a_re]; norm_num) 0]
    simp
  have hz : ∫ w, 𝓕 φ w = 0 := by
    have := neh_inversion hc hφ hF 0
    rw [h0] at this
    simpa using this.symm
  have hi : Integrable (fun w => 1 / neh_a w * 𝓕 φ w) := by
    refine (hF.const_mul 2).mono ((Measurable.aestronglyMeasurable
      (by unfold neh_a; fun_prop)).mul hF.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_mul, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have ha := neh_a_norm w
    gcongr
    rw [norm_div, norm_one, h2, div_le_iff₀ (by linarith)]
    linarith
  have hsub : ∫ w, 1 / neh_a w * 𝓕 φ w = ∫ w, (1 / neh_a w - 1) * 𝓕 φ w := by
    simp_rw [sub_mul, one_mul]
    rw [integral_sub hi hF, hz, sub_zero]
  rw [hK, hsub]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [norm_mul, neh_unimodular, one_mul]

/-- The two-sided Laplace transform `K(s) = ∫ φ(v) e^{sv} dv`. -/
def neh_K (φ : ℝ → ℂ) (s : ℂ) : ℂ := ∫ v : ℝ, φ v * cexp (s * v)

/-- On the imaginary axis `K` is the Fourier transform: `K(it) = 𝓕φ(-t/2π)`. -/
lemma neh_K_line (φ : ℝ → ℂ) (t : ℝ) : neh_K φ (t * I) = 𝓕 φ (-t / (2 * π)) := by
  rw [neh_K, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have h : (-2 * π * v * (-t / (2 * π)) : ℝ) = t * v := by field_simp
  simp only [h, smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- **Nehari inequality** for kernels supported on `(-∞, 0]`, Mathlib normalisation of `𝓕`. -/
theorem neh_nehari {φ : ℝ → ℂ} (hc : Continuous φ) (hφ : Integrable φ)
    (hs : ∀ v, 0 < v → φ v = 0) (hF : Integrable (𝓕 φ)) :
    ‖neh_K φ (1 / 2)‖ ≤ ∫ w, ‖𝓕 φ w‖ := by
  have e : neh_K φ (1 / 2) = ∫ v in Iic (0 : ℝ), φ v * cexp ((1 / 2 : ℂ) * v) := by
    rw [neh_K]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hs v (by simpa using hv)]
    simp
  rw [e]
  exact neh_nehari_of_zero hc hφ hF (neh_zero hc hs)

/-- **Nehari inequality, Laplace form**: `‖K(1/2)‖ ≤ (1/2π) ∫ ‖K(it)‖ dt`. -/
theorem neh_nehari_line {φ : ℝ → ℂ} (hc : Continuous φ) (hφ : Integrable φ)
    (hs : ∀ v, 0 < v → φ v = 0) (hL : Integrable fun t : ℝ => neh_K φ (t * I)) :
    ‖neh_K φ (1 / 2)‖ ≤ 1 / (2 * π) * ∫ t : ℝ, ‖neh_K φ (t * I)‖ := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hF : Integrable (𝓕 φ) := by
    have h := hL.comp_mul_left' (R := -(2 * π)) (by linarith)
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only
    have := neh_K_line φ (-(2 * π) * w)
    rw [this]
    field_simp
  have e : ∫ t : ℝ, ‖neh_K φ (t * I)‖ = (2 * π) * ∫ w, ‖𝓕 φ w‖ := by
    have := Measure.integral_comp_mul_left (fun w => ‖𝓕 φ w‖) (-(2 * π))⁻¹
    simp only [inv_inv, abs_neg, smul_eq_mul] at this
    rw [abs_of_pos hpi] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [neh_K_line]
    congr 2
    field_simp
  rw [e, ← mul_assoc, one_div_mul_cancel hpi.ne', one_mul]
  exact neh_nehari hc hφ hs hF

/-- **Nehari barrier**: the reduced functional `c = (I / |K(1/2)|)²` of a one-sided kernel
is at least `1`. -/
theorem neh_barrier {φ : ℝ → ℂ} (hc : Continuous φ) (hφ : Integrable φ)
    (hs : ∀ v, 0 < v → φ v = 0) (hL : Integrable fun t : ℝ => neh_K φ (t * I))
    (hK : neh_K φ (1 / 2) ≠ 0) :
    1 ≤ ((1 / (2 * π) * ∫ t : ℝ, ‖neh_K φ (t * I)‖) / ‖neh_K φ (1 / 2)‖) ^ 2 := by
  have h := neh_nehari_line hc hφ hs hL
  have hpos : 0 < ‖neh_K φ (1 / 2)‖ := norm_pos_iff.mpr hK
  have h1 : 1 ≤ (1 / (2 * π) * ∫ t : ℝ, ‖neh_K φ (t * I)‖) / ‖neh_K φ (1 / 2)‖ := by
    rw [le_div_iff₀ hpos, one_mul]
    exact h
  exact one_le_pow₀ h1

/-- Real-valued version: `∫ φ(v) e^{v/2} dv ≤ (1/2π) ∫ |K(it)| dt`. -/
theorem neh_nehari_real {φ : ℝ → ℝ} (hc : Continuous φ) (hφ : Integrable φ)
    (hs : ∀ v, 0 < v → φ v = 0)
    (hL : Integrable fun t : ℝ => neh_K (fun v => (φ v : ℂ)) (t * I)) :
    ∫ v : ℝ, φ v * rexp (v / 2) ≤
      1 / (2 * π) * ∫ t : ℝ, ‖neh_K (fun v => (φ v : ℂ)) (t * I)‖ := by
  have h := neh_nehari_line (φ := fun v => (φ v : ℂ)) (Complex.continuous_ofReal.comp hc)
    hφ.ofReal (fun v hv => by simp [hs v hv]) hL
  have e : neh_K (fun v => (φ v : ℂ)) (1 / 2) = ((∫ v : ℝ, φ v * rexp (v / 2) : ℝ) : ℂ) := by
    rw [neh_K, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only
    push_cast
    congr 2
    ring
  rw [e, Complex.norm_real] at h
  exact (le_abs_self _).trans h

/-- **Nehari barrier, real form with the scale `λ`**: for a real one-sided kernel with
`K(1/2) > 0`, the functional `c = λ (I / K(1/2))²` satisfies `c ≥ λ`; in particular `c ≥ 1`
at `λ = 1` (all of the support counted). -/
theorem neh_barrier_real {φ : ℝ → ℝ} (hc : Continuous φ) (hφ : Integrable φ)
    (hs : ∀ v, 0 < v → φ v = 0)
    (hL : Integrable fun t : ℝ => neh_K (fun v => (φ v : ℂ)) (t * I))
    (hK : 0 < ∫ v : ℝ, φ v * rexp (v / 2)) {lam : ℝ} (hlam : 0 ≤ lam) :
    lam ≤ lam * ((1 / (2 * π) * ∫ t : ℝ, ‖neh_K (fun v => (φ v : ℂ)) (t * I)‖) /
      ∫ v : ℝ, φ v * rexp (v / 2)) ^ 2 := by
  have h := neh_nehari_real hc hφ hs hL
  have h1 : 1 ≤ (1 / (2 * π) * ∫ t : ℝ, ‖neh_K (fun v => (φ v : ℂ)) (t * I)‖) /
      ∫ v : ℝ, φ v * rexp (v / 2) := by
    rw [le_div_iff₀ hK, one_mul]
    exact h
  exact le_mul_of_one_le_right hlam (one_le_pow₀ h1)

end

#print axioms neh_nehari_of_zero
#print axioms neh_nehari
#print axioms neh_nehari_line
#print axioms neh_barrier
#print axioms neh_nehari_real
#print axioms neh_barrier_real
