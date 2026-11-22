import DetPrimality.Bach.ExplicitWeight
import DetPrimality.Bach.ExplicitKernel

/-!
# The zero part of the explicit formula (blueprint §3, Step 4a)

`zero_part`: with `Z(s) = ∑_ρ m_ρ (1/(s-ρ) - 1/(2-ρ))`,
* `Z(s)/(s(s+1))` is integrable on `Re s = 2`  (proved: `vi_Zfun`), and
* `I[Z](x) = ∑_ρ m_ρ · zeroTerm ρ x`  (proved from two lemmas below by Fubini).

Inputs: `kernel_zero_bound` (`ExplicitKernel.lean`) and `summable_zeroOrd_weight`
(`ExplicitWeight.lean`).
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `Z(s) = ∑_ρ m_ρ (1/(s-ρ) - 1/(2-ρ))`. -/
noncomputable def Zfun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))

theorem Zfun_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {s : ℂ} (hs : 1 < s.re) :
    Zfun χ s = -(deriv (LFunction χ) 2 / LFunction χ 2) + (Gfun χ s - Gfun χ 2)
      + deriv (LFunction χ) s / LFunction χ s := by
  have h := neg_logDeriv_decomp χ hχ1 hH hS hs
  unfold Zfun
  linear_combination h

theorem continuous_logDeriv_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) :
    Continuous fun y : ℝ => deriv (LFunction χ) (((2 : ℝ) : ℂ) + y * I)
      / LFunction χ (((2 : ℝ) : ℂ) + y * I) := by
  have hd : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ1
  have hd' : Differentiable ℂ (deriv (LFunction χ)) := fun z =>
    ((hd.differentiableOn.deriv isOpen_univ) z (mem_univ z)).differentiableAt
      (isOpen_univ.mem_nhds (mem_univ z))
  exact Continuous.div (hd'.continuous.comp (by fun_prop)) (hd.continuous.comp (by fun_prop))
    (fun y => LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by rw [line_re]; norm_num))

theorem integrable_inv_four_add_sq : Integrable fun y : ℝ => 1 / ((2 : ℝ) ^ 2 + y ^ 2) := by
  refine integrable_inv_one_add_sq.mono'
    ((continuous_const.div (by fun_prop) (fun y => by positivity)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity), one_div]
  exact inv_anti₀ (by positivity) (by nlinarith)

/-- **`Z(s)/(s(s+1))` is integrable on `Re s = 2`.** -/
theorem vi_Zfun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    VerticalIntegrable (fun s => Zfun χ s / (s * (s + 1))) 2 := by
  unfold VerticalIntegrable
  have hre : ∀ y : ℝ, 1 < (((2 : ℝ) : ℂ) + y * I).re := fun y => by rw [line_re]; norm_num
  have e : (fun y : ℝ => Zfun χ (((2 : ℝ) : ℂ) + y * I)) = fun y : ℝ =>
      -(deriv (LFunction χ) 2 / LFunction χ 2) + (Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2)
        + deriv (LFunction χ) (((2 : ℝ) : ℂ) + y * I) / LFunction χ (((2 : ℝ) : ℂ) + y * I) :=
    funext fun y => Zfun_eq χ hχ1 hH hS (hre y)
  have hZc : Continuous fun y : ℝ => Zfun χ (((2 : ℝ) : ℂ) + y * I) := by
    rw [e]
    exact (continuous_const.add ((continuous_Gfun_line χ).sub continuous_const)).add
      (continuous_logDeriv_line χ hχ1)
  have hcont : Continuous fun y : ℝ => Zfun χ (((2 : ℝ) : ℂ) + y * I)
      / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1)) :=
    Continuous.div hZc (by fun_prop)
      (fun y => mul_ne_zero (ne_zero_of_re_pos (by simp))
        (ne_zero_of_re_pos (by simp; norm_num)))
  set W := ∑' k, wk k with hW
  refine ((integrable_phiG.const_mul W).add (integrable_inv_four_add_sq.const_mul (2 * CL))).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hZ : ‖Zfun χ (((2 : ℝ) : ℂ) + y * I)‖ ≤ 2 * CL + √|y| * W := by
    rw [Zfun_eq χ hχ1 hH hS (hre y)]
    have h1 := norm_logDeriv_LFunction_le χ (s := 2) (by norm_num)
    have h2 := norm_logDeriv_LFunction_le χ (s := ((2 : ℝ) : ℂ) + y * I)
      (by rw [line_re])
    have h3 := norm_Gfun_sub_le χ y
    calc _ ≤ ‖-(deriv (LFunction χ) 2 / LFunction χ 2)‖
          + ‖Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2‖
          + ‖deriv (LFunction χ) (((2 : ℝ) : ℂ) + y * I)
              / LFunction χ (((2 : ℝ) : ℂ) + y * I)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2 * CL + √|y| * W := by rw [norm_neg]; linarith
  have hK := norm_kernel_le (c := 2) two_pos y
  show ‖Zfun χ (((2 : ℝ) : ℂ) + y * I)
      / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
      ≤ W * phiG y + 2 * CL * (1 / ((2 : ℝ) ^ 2 + y ^ 2))
  rw [div_eq_mul_one_div, norm_mul]
  unfold phiG
  calc _ ≤ (2 * CL + √|y| * W) * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) :=
        mul_le_mul hZ hK (norm_nonneg _) (by
          have := CL_nonneg
          have : 0 ≤ W := tsum_nonneg wk_nonneg
          positivity)
    _ = W * (√|y| / ((2 : ℝ) ^ 2 + y ^ 2)) + 2 * CL * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) := by ring

/-! ### Fubini -/

theorem vi_zero_term {ρ : ℂ} (hρ : ρ.re < 2) (c : ℂ) :
    VerticalIntegrable (fun s : ℂ => c * (1 / (s - ρ) - 1 / (2 - ρ)) / (s * (s + 1))) 2 := by
  have h := (Integrable.sub (verticalIntegrable_inv_sub hρ)
    (verticalIntegrable_const_kernel (1 / (2 - ρ)))).const_mul c
  unfold VerticalIntegrable
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  ring

theorem perronI_const_mul_fun (c : ℂ) (g : ℂ → ℂ) (x : ℝ) :
    perronI (fun s => c * g s) x = c * perronI g x := by
  unfold perronI
  rw [← mellinInv_const_mul]
  congr 1
  funext s
  ring

theorem norm_two_sub_ge {ρ : ℂ} (hρ : ρ.re < 1) : (1 + |ρ.im|) / 2 ≤ ‖2 - ρ‖ := by
  have h1 := Complex.re_le_norm (2 - ρ)
  have h2 := Complex.abs_im_le_norm (2 - ρ)
  simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, zero_sub,
    abs_neg] at h1 h2
  linarith

theorem perronI_Zfun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {x : ℝ} (hx : 1 ≤ x) :
    perronI (Zfun χ) x = ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * zeroTerm ρ x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨CJ, hCJ0, hJ⟩ := kernel_zero_bound
  have hWs := summable_zeroOrd_weight χ hχ1 hH hS
  set Sρ : Set ℂ := Function.support (fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) with hSρ
  have : Countable Sρ := hS.countable_support.to_subtype
  have hmem : ∀ ρ : ℂ, zeroOrd χ ρ ≠ 0 → ρ ∈ Sρ := by
    intro ρ h
    have hρ : ρ ≠ 0 := ne_zero_of_re_pos (zeroOrd_strip h).1
    rw [hSρ, Function.mem_support]
    exact div_ne_zero (by exact_mod_cast h) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hρ))
  have hstrip : ∀ ρ : Sρ, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    intro ρ
    apply zeroOrd_strip (χ := χ)
    intro h0
    have h2 : (ρ : ℂ) ∈ Function.support (fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) := ρ.2
    rw [Function.mem_support] at h2
    exact h2 (by simp [h0])
  set c : ℝ → ℂ := fun y => ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) with hc
  set F : Sρ → ℝ → ℂ := fun ρ y => c y • ((zeroOrd χ (ρ : ℂ) : ℂ)
      * (1 / ((((2 : ℝ) : ℂ) + y * I) - ρ) - 1 / (2 - (ρ : ℂ)))
      / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))) with hF
  have hsupp : ∀ s : ℂ, Function.support (fun ρ : ℂ => (zeroOrd χ ρ : ℂ)
      * (1 / (s - ρ) - 1 / (2 - ρ))) ⊆ Sρ := by
    intro s ρ hρ
    apply hmem
    intro h0
    apply hρ
    simp [h0]
  have hpt : ∀ y : ℝ, c y • (fun s => Zfun χ s / (s * (s + 1))) (((2 : ℝ) : ℂ) + y * I)
      = ∑' ρ : Sρ, F ρ y := by
    intro y
    simp only [hF, Zfun]
    rw [← tsum_subtype_eq_of_support_subset (hsupp _), smul_eq_mul, ← tsum_div_const,
      ← tsum_mul_left]
    rfl
  have hFint : ∀ ρ : Sρ, Integrable (F ρ) := fun ρ =>
    integrable_mellinInv_integrand (vi_zero_term (by linarith [(hstrip ρ).2])
      (zeroOrd χ (ρ : ℂ) : ℂ)) (inv_pos.mpr hx0)
  have hFnorm : ∀ ρ : Sρ, ∫ y, ‖F ρ y‖
      ≤ (2 * x ^ 2 * CJ) * ((zeroOrd χ (ρ : ℂ) : ℝ) * (1 + |(ρ : ℂ).im|) ^ (-(7 / 4 : ℝ))) := by
    intro ρ
    obtain ⟨hJi, hJb⟩ := hJ ρ (hstrip ρ).2
    set m : ℝ := (zeroOrd χ (ρ : ℂ) : ℝ) with hm
    set g : ℝ := 1 + |(ρ : ℂ).im| with hg
    have hgpos : 0 < g := by positivity
    have h2ρ : g / 2 ≤ ‖2 - (ρ : ℂ)‖ := norm_two_sub_ge (hstrip ρ).2
    have h2ρpos : 0 < ‖2 - (ρ : ℂ)‖ := lt_of_lt_of_le (by positivity) h2ρ
    have hpt' : ∀ y : ℝ, ‖F ρ y‖ = (x ^ 2 * m / ‖2 - (ρ : ℂ)‖) * (|y|
        * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
        / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖) := by
      intro y
      have hsρ : (((2 : ℝ) : ℂ) + y * I) - ρ ≠ 0 :=
        ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith [(hstrip ρ).2])
      have h2 : 2 - (ρ : ℂ) ≠ 0 := norm_pos_iff.mp h2ρpos
      simp only [hF, hc]
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hx0)]
      have hre : (-(((2 : ℝ) : ℂ) + y * I)).re = -2 := by simp
      rw [hre, Real.rpow_neg (inv_nonneg.mpr hx0.le), Real.inv_rpow hx0.le, inv_inv,
        Real.rpow_two]
      have hid : (zeroOrd χ (ρ : ℂ) : ℂ) * (1 / ((((2 : ℝ) : ℂ) + y * I) - ρ) - 1 / (2 - (ρ : ℂ)))
          / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))
          = (zeroOrd χ (ρ : ℂ) : ℂ) * (-(y * I)) / (((((2 : ℝ) : ℂ) + y * I) - ρ) * (2 - ρ))
            * (1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))) := by
        field_simp
        push_cast
        ring
      rw [hid, norm_mul, norm_div, norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs, ← hm]
      field_simp
    rw [integral_congr_ae (Eventually.of_forall hpt'), integral_const_mul]
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have hint0 : 0 ≤ ∫ y : ℝ, |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I)
        * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ :=
      integral_nonneg fun y => by positivity
    have hcoef : x ^ 2 * m / ‖2 - (ρ : ℂ)‖ ≤ x ^ 2 * m * (2 / g) := by
      rw [div_le_iff₀ h2ρpos]
      calc x ^ 2 * m = x ^ 2 * m * (2 / g) * (g / 2) := by field_simp
        _ ≤ x ^ 2 * m * (2 / g) * ‖2 - (ρ : ℂ)‖ :=
          mul_le_mul_of_nonneg_left h2ρ (by positivity)
    have hgexp : (1 / g) * g ^ (-(3 / 4 : ℝ)) = g ^ (-(7 / 4 : ℝ)) := by
      rw [show (-(7 / 4 : ℝ)) = -1 + -(3 / 4) by norm_num, Real.rpow_add hgpos, Real.rpow_neg_one,
        one_div]
    calc x ^ 2 * m / ‖2 - (ρ : ℂ)‖ * ∫ y : ℝ, |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I)
          * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖
        ≤ x ^ 2 * m * (2 / g) * (CJ * g ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul hcoef hJb hint0 (by positivity)
      _ = 2 * x ^ 2 * CJ * (m * ((1 / g) * g ^ (-(3 / 4 : ℝ)))) := by ring
      _ = 2 * x ^ 2 * CJ * (m * g ^ (-(7 / 4 : ℝ))) := by rw [hgexp]
  have hFsum : Summable fun ρ : Sρ => ∫ y, ‖F ρ y‖ :=
    Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun y => norm_nonneg _) hFnorm
      ((hWs.subtype Sρ).mul_left _)
  have hsum := hasSum_integral_of_summable_integral_norm hFint hFsum
  rw [integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)] at hsum
  have h2 := hsum.const_smul (1 / (2 * Real.pi))
  have e1 : ∀ ρ : Sρ, (1 / (2 * Real.pi)) • ∫ y, F ρ y = (zeroOrd χ (ρ : ℂ) : ℂ) * zeroTerm ρ x := by
    intro ρ
    have : (1 / (2 * Real.pi)) • ∫ y, F ρ y
        = perronI (fun s => (zeroOrd χ (ρ : ℂ) : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) x := rfl
    rw [this, perronI_const_mul_fun, perronI_zeroTerm (hstrip ρ) hx]
  simp only [e1] at h2
  have e2 : (1 / (2 * Real.pi)) • ∫ y : ℝ, c y • (fun s => Zfun χ s / (s * (s + 1)))
      (((2 : ℝ) : ℂ) + y * I) = perronI (Zfun χ) x := rfl
  rw [e2] at h2
  rw [← h2.tsum_eq]
  refine tsum_subtype_eq_of_support_subset
    (f := fun ρ : ℂ => (zeroOrd χ ρ : ℂ) * zeroTerm ρ x) (s := Sρ) ?_
  intro ρ hρ
  apply hmem
  intro h0
  apply hρ
  simp [h0]

/-- **Step 4a: the zero part.** -/
theorem zero_part {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) {x : ℝ} (hx : 1 ≤ x) :
    VerticalIntegrable (fun s => (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ)))
      / (s * (s + 1))) 2 ∧
    perronI (fun s => ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) x
      = ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * zeroTerm ρ x :=
  ⟨vi_Zfun χ hχ1 hH hS, perronI_Zfun χ hχ1 hH hS hx⟩

end DetPrimality.Bach
