import DetPrimality.Bach.LLSPerronGamma

/-!
# The zero part for the kernel `x^s/s²` (LLS Lemmas 1 and 2)

* `llsPer_perronL_zeroSum` (generic Fubini, reusable for `ζ`): for any multiplicity function
  `m : ℂ → ℕ` supported in the critical strip with `∑ m_ρ (1+|Im ρ|)^{-7/4} < ∞`,
  `L[∑_ρ m_ρ (1/(s-ρ) - 1/(2-ρ))](x) = ∑_ρ m_ρ · llsPer_zeroTerm ρ x`  (`x ≥ 1`);
* `llsPer_vi_Zfun` : `Z(s)/s²` is integrable on `Re s = 2` (`χ ≠ 1`);
* `llsPer_perronL_Zfun` : the specialisation to `Zfun χ`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

theorem llsPer_inv_sq_le {s : ℂ} (h2 : 2 ≤ ‖s‖) (hs1 : s + 1 ≠ 0) :
    ‖1 / s ^ 2‖ ≤ 3 / 2 * ‖1 / (s * (s + 1))‖ := by
  have hpos : 0 < ‖s‖ := by linarith
  have hs1n : 0 < ‖s + 1‖ := norm_pos_iff.mpr hs1
  have h1 : ‖s + 1‖ ≤ ‖s‖ + 1 := (norm_add_le _ _).trans (by simp)
  have h3 : ‖s + 1‖ ≤ 3 / 2 * ‖s‖ := by linarith
  rw [norm_div, norm_one, norm_pow, norm_div, norm_one, norm_mul, ← mul_div_assoc, mul_one,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h3 hpos.le]

theorem llsPer_vi_zero_term {ρ : ℂ} (hρ : ρ.re < 2) (c : ℂ) :
    VerticalIntegrable (fun s : ℂ => c * (1 / (s - ρ) - 1 / (2 - ρ)) / s ^ 2) 2 := by
  have h := (Integrable.sub (llsPer_vi_inv_sub hρ) (llsPer_vi_const (1 / (2 - ρ)))).const_mul c
  unfold VerticalIntegrable
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  ring

/-- **Termwise integration over the zeros** (generic in the multiplicity function). -/
theorem llsPer_perronL_zeroSum {m : ℂ → ℕ} (hstrip : ∀ ρ, m ρ ≠ 0 → 0 < ρ.re ∧ ρ.re < 1)
    (hWs : Summable fun ρ : ℂ => (m ρ : ℝ) * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) {x : ℝ}
    (hx : 1 ≤ x) :
    llsPer_perronL (fun s => ∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) x
      = ∑' ρ : ℂ, (m ρ : ℂ) * llsPer_zeroTerm ρ x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨CJ, hCJ0, hJ⟩ := kernel_zero_bound
  set Sρ : Set ℂ := Function.support
    (fun ρ : ℂ => (m ρ : ℝ) * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) with hSρ
  have : Countable Sρ := hWs.countable_support.to_subtype
  have hmem : ∀ ρ : ℂ, m ρ ≠ 0 → ρ ∈ Sρ := by
    intro ρ h
    rw [hSρ, Function.mem_support]
    exact mul_ne_zero (by exact_mod_cast h) (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hstrip' : ∀ ρ : Sρ, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    intro ρ
    apply hstrip
    intro h0
    have h2 : (ρ : ℂ) ∈ Function.support
      (fun ρ : ℂ => (m ρ : ℝ) * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) := ρ.2
    rw [Function.mem_support] at h2
    exact h2 (by simp [h0])
  set c : ℝ → ℂ := fun y => ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) with hc
  set F : Sρ → ℝ → ℂ := fun ρ y => c y • ((m (ρ : ℂ) : ℂ)
      * (1 / ((((2 : ℝ) : ℂ) + y * I) - ρ) - 1 / (2 - (ρ : ℂ)))
      / (((2 : ℝ) : ℂ) + y * I) ^ 2) with hF
  have hsupp : ∀ s : ℂ, Function.support (fun ρ : ℂ => (m ρ : ℂ)
      * (1 / (s - ρ) - 1 / (2 - ρ))) ⊆ Sρ := by
    intro s ρ hρ
    apply hmem
    intro h0
    apply hρ
    simp [h0]
  have hpt : ∀ y : ℝ, c y • (fun s => (∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ)))
      / s ^ 2) (((2 : ℝ) : ℂ) + y * I) = ∑' ρ : Sρ, F ρ y := by
    intro y
    simp only [hF]
    rw [← tsum_subtype_eq_of_support_subset (hsupp _), smul_eq_mul, ← tsum_div_const,
      ← tsum_mul_left]
    rfl
  have hFint : ∀ ρ : Sρ, Integrable (F ρ) := fun ρ =>
    integrable_mellinInv_integrand (llsPer_vi_zero_term (by linarith [(hstrip' ρ).2])
      (m (ρ : ℂ) : ℂ)) (inv_pos.mpr hx0)
  have hFnorm : ∀ ρ : Sρ, ∫ y, ‖F ρ y‖
      ≤ (3 * x ^ 2 * CJ) * ((m (ρ : ℂ) : ℝ) * (1 + |(ρ : ℂ).im|) ^ (-(7 / 4 : ℝ))) := by
    intro ρ
    obtain ⟨hJi, hJb⟩ := hJ ρ (hstrip' ρ).2
    set mm : ℝ := (m (ρ : ℂ) : ℝ) with hmm
    set g : ℝ := 1 + |(ρ : ℂ).im| with hg
    have hgpos : 0 < g := by positivity
    have h2ρ : g / 2 ≤ ‖2 - (ρ : ℂ)‖ := norm_two_sub_ge (hstrip' ρ).2
    have h2ρpos : 0 < ‖2 - (ρ : ℂ)‖ := lt_of_lt_of_le (by positivity) h2ρ
    have hm0 : 0 ≤ mm := Nat.cast_nonneg _
    have hpt' : ∀ y : ℝ, ‖F ρ y‖ ≤ (3 / 2 * x ^ 2 * mm / ‖2 - (ρ : ℂ)‖) * (|y|
        * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
        / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖) := by
      intro y
      have hsρ : (((2 : ℝ) : ℂ) + y * I) - ρ ≠ 0 :=
        ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith [(hstrip' ρ).2])
      have hsρn : 0 < ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ := norm_pos_iff.mpr hsρ
      have h2 : 2 - (ρ : ℂ) ≠ 0 := norm_pos_iff.mp h2ρpos
      have hs0 := llsPer_line_ne y
      have hs1 : ((2 : ℝ) : ℂ) + y * I + 1 ≠ 0 :=
        ne_zero_of_re_pos (by rw [Complex.add_re, line_re, Complex.one_re]; norm_num)
      have hK := llsPer_inv_sq_le (llsPer_two_le_norm_line y) hs1
      simp only [hF, hc]
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hx0)]
      have hre : (-(((2 : ℝ) : ℂ) + y * I)).re = -2 := by simp
      rw [hre, Real.rpow_neg (inv_nonneg.mpr hx0.le), Real.inv_rpow hx0.le, inv_inv,
        Real.rpow_two]
      have hid : (m (ρ : ℂ) : ℂ) * (1 / ((((2 : ℝ) : ℂ) + y * I) - ρ) - 1 / (2 - (ρ : ℂ)))
          / (((2 : ℝ) : ℂ) + y * I) ^ 2
          = (m (ρ : ℂ) : ℂ) * (-(y * I)) / (((((2 : ℝ) : ℂ) + y * I) - ρ) * (2 - ρ))
            * (1 / (((2 : ℝ) : ℂ) + y * I) ^ 2) := by
        field_simp
        push_cast
        ring
      rw [hid, norm_mul, norm_div, norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs, ← hmm]
      calc x ^ 2 * (mm * |y| / (‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ * ‖2 - (ρ : ℂ)‖)
            * ‖1 / (((2 : ℝ) : ℂ) + y * I) ^ 2‖)
          ≤ x ^ 2 * (mm * |y| / (‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ * ‖2 - (ρ : ℂ)‖)
            * (3 / 2 * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK (by positivity))
              (by positivity)
        _ = _ := by field_simp
    have hint0 : 0 ≤ ∫ y : ℝ, |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I)
        * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ :=
      integral_nonneg fun y => by positivity
    have hcoef : 3 / 2 * x ^ 2 * mm / ‖2 - (ρ : ℂ)‖ ≤ 3 / 2 * x ^ 2 * mm * (2 / g) := by
      rw [div_le_iff₀ h2ρpos]
      calc 3 / 2 * x ^ 2 * mm = 3 / 2 * x ^ 2 * mm * (2 / g) * (g / 2) := by field_simp
        _ ≤ 3 / 2 * x ^ 2 * mm * (2 / g) * ‖2 - (ρ : ℂ)‖ :=
          mul_le_mul_of_nonneg_left h2ρ (by positivity)
    have hgexp : (1 / g) * g ^ (-(3 / 4 : ℝ)) = g ^ (-(7 / 4 : ℝ)) := by
      rw [show (-(7 / 4 : ℝ)) = -1 + -(3 / 4) by norm_num, Real.rpow_add hgpos,
        Real.rpow_neg_one, one_div]
    calc ∫ y, ‖F ρ y‖
        ≤ ∫ y : ℝ, (3 / 2 * x ^ 2 * mm / ‖2 - (ρ : ℂ)‖) * (|y|
          * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
          / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖) :=
          integral_mono (hFint ρ).norm (hJi.const_mul _) hpt'
      _ = (3 / 2 * x ^ 2 * mm / ‖2 - (ρ : ℂ)‖) * ∫ y : ℝ, |y|
          * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
          / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ := integral_const_mul _ _
      _ ≤ 3 / 2 * x ^ 2 * mm * (2 / g) * (CJ * g ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul hcoef hJb hint0 (by positivity)
      _ = 3 * x ^ 2 * CJ * (mm * ((1 / g) * g ^ (-(3 / 4 : ℝ)))) := by ring
      _ = 3 * x ^ 2 * CJ * (mm * g ^ (-(7 / 4 : ℝ))) := by rw [hgexp]
  have hFsum : Summable fun ρ : Sρ => ∫ y, ‖F ρ y‖ :=
    Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun y => norm_nonneg _) hFnorm
      ((hWs.subtype Sρ).mul_left _)
  have hsum := hasSum_integral_of_summable_integral_norm hFint hFsum
  rw [integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)] at hsum
  have h2 := hsum.const_smul (1 / (2 * Real.pi))
  have e1 : ∀ ρ : Sρ, (1 / (2 * Real.pi)) • ∫ y, F ρ y
      = (m (ρ : ℂ) : ℂ) * llsPer_zeroTerm ρ x := by
    intro ρ
    have : (1 / (2 * Real.pi)) • ∫ y, F ρ y
        = llsPer_perronL (fun s => (m (ρ : ℂ) : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) x := rfl
    rw [this, llsPer_perronL_const_mul,
      llsPer_perronL_zeroTerm (by linarith [(hstrip' ρ).2])
        (ne_zero_of_re_pos (hstrip' ρ).1) hx]
  simp only [e1] at h2
  have e2 : (1 / (2 * Real.pi)) • ∫ y : ℝ, c y • (fun s =>
      (∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) / s ^ 2)
      (((2 : ℝ) : ℂ) + y * I)
      = llsPer_perronL (fun s => ∑' ρ : ℂ, (m ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))) x := rfl
  rw [e2] at h2
  rw [← h2.tsum_eq]
  refine tsum_subtype_eq_of_support_subset
    (f := fun ρ : ℂ => (m ρ : ℂ) * llsPer_zeroTerm ρ x) (s := Sρ) ?_
  intro ρ hρ
  apply hmem
  intro h0
  apply hρ
  simp [h0]

/-! ### Dirichlet characters -/

/-- **`Z(s)/s²` is integrable on `Re s = 2`.** -/
theorem llsPer_vi_Zfun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    VerticalIntegrable (fun s => Zfun χ s / s ^ 2) 2 := by
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
      / (((2 : ℝ) : ℂ) + y * I) ^ 2 :=
    Continuous.div hZc (by fun_prop) (fun y => pow_ne_zero 2 (llsPer_line_ne y))
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
  show ‖Zfun χ (((2 : ℝ) : ℂ) + y * I) / (((2 : ℝ) : ℂ) + y * I) ^ 2‖
      ≤ W * phiG y + 2 * CL * (1 / ((2 : ℝ) ^ 2 + y ^ 2))
  rw [div_eq_mul_one_div, norm_mul, llsPer_norm_kernel]
  unfold phiG
  calc _ ≤ (2 * CL + √|y| * W) * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) :=
        mul_le_mul_of_nonneg_right hZ (by positivity)
    _ = W * (√|y| / ((2 : ℝ) ^ 2 + y ^ 2)) + 2 * CL * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) := by ring

theorem llsPer_perronL_Zfun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {x : ℝ} (hx : 1 ≤ x) :
    llsPer_perronL (Zfun χ) x = ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * llsPer_zeroTerm ρ x :=
  llsPer_perronL_zeroSum (m := zeroOrd χ) (fun _ h => zeroOrd_strip h)
    (summable_zeroOrd_weight χ hχ1 hH hS) hx

end DetPrimality.Bach
