import DetPrimality.Bach.LLSPerronZeros
import DetPrimality.Bach.Growth
import DetPrimality.Bach.HadamardL

/-!
# LLS Lemma 2: `llsPer_chiUpper : LLSChiUpper`

* `llsPer_explicit` : the explicit formula for the kernel `x^s/s²` (`χ ≠ 1`, unconditional given
  the Hadamard partial fraction):
  `S(x,χ) = -L'/L(2,χ) log x + L[G - G(2)](x) - ∑_ρ m_ρ · llsPer_zeroTerm ρ x`;
* `llsPer_chiUpper` : under GRH, for primitive `χ ≠ 1` and `x ≥ 3`,
  `Re S(x,χ) ≤ (√x + 1 + log x / 2) ∑_ρ 1/|ρ|² + ½ log(q/π) log x`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

/-- Explicit formula for `S(x,χ) = ∑_{n ≤ x} Λ(n) χ(n) log(x/n)`. -/
theorem llsPer_explicit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {x : ℝ} (hx : 1 ≤ x) :
    logPsi χ x = -(deriv (LFunction χ) 2 / LFunction χ 2) * (Real.log x : ℂ)
      + llsPer_perronL (fun s => Gfun χ s - Gfun χ 2) x
      - ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * llsPer_zeroTerm ρ x := by
  have hx0 : 0 < x := by linarith
  have hZi := llsPer_vi_Zfun χ hχ1 hH hS
  have hGi := llsPer_vi_gamma χ
  set c0 : ℂ := -(deriv (LFunction χ) 2 / LFunction χ 2) with hc0
  have hAi : VerticalIntegrable (fun s => (c0 + (Gfun χ s - Gfun χ 2)) / s ^ 2) 2 := by
    have h := Integrable.add (llsPer_vi_const c0) hGi
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have h1 : logPsi χ x
      = llsPer_perronL (fun s => (c0 + (Gfun χ s - Gfun χ 2)) - Zfun χ s) x := by
    rw [llsPer_logPsi_eq_perronL χ hx]
    apply llsPer_perronL_congr_line
    intro y
    exact neg_logDeriv_decomp χ hχ1 hH hS (by simp)
  rw [llsPer_perronL_sub hAi hZi hx0, llsPer_perronL_add (llsPer_vi_const c0) hGi hx0,
    llsPer_perronL_const, llsPer_perronL_one hx, llsPer_perronL_Zfun χ hχ1 hH hS hx] at h1
  exact h1

/-- **LLS Lemma 2.** -/
theorem llsPer_chiUpper : LLSChiUpper := by
  intro hGRH q _ χ hχ hχ1 x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hG := growth_completedLFunction χ hχ1
  have hH := hadamardLogDeriv_of_growth χ hχ hχ1 hG
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 hG
  have hE := llsPer_explicit χ hχ1 hH hS hx1
  have hGam := llsPer_gamma_bound χ hx
  set L := Real.log x with hL
  have hhalf : ∀ ρ, zeroOrd χ ρ ≠ 0 → ρ.re = 1 / 2 := fun ρ h =>
    re_eq_half_of_zeroOrd_ne_zero hGRH χ h
  set a : ℂ → ℂ := fun ρ => (zeroOrd χ ρ : ℂ) * ((x : ℂ) ^ ρ / ρ ^ 2 - 1 / ρ ^ 2) with ha
  set b : ℂ → ℂ := fun ρ => (zeroOrd χ ρ : ℂ) * (1 / (2 - ρ) + 1 / ρ) with hb
  have hbs : Summable b := summable_hadamard_terms χ hS (s := 2) (by norm_num)
  have hanorm : ∀ ρ, ‖a ρ‖ ≤ (√x + 1) * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [ha, h0]
    · have hre := hhalf ρ h0
      have hρ : ρ ≠ 0 := by
        intro h; rw [h] at hre; norm_num at hre
      have hxρ : ‖(x : ℂ) ^ ρ‖ = √x := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre, Real.sqrt_eq_rpow]
      simp only [ha]
      rw [norm_mul, Complex.norm_natCast, ← sub_div, norm_div, norm_pow]
      have h1 : ‖(x : ℂ) ^ ρ - 1‖ ≤ √x + 1 :=
        (norm_sub_le _ _).trans (by rw [hxρ, norm_one])
      have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
      calc (zeroOrd χ ρ : ℝ) * (‖(x : ℂ) ^ ρ - 1‖ / ‖ρ‖ ^ 2)
          ≤ (zeroOrd χ ρ : ℝ) * ((√x + 1) / ‖ρ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (by positivity))
              (Nat.cast_nonneg _)
        _ = (√x + 1) * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) := by ring
  have has : Summable a := Summable.of_norm_bounded (hS.mul_left (√x + 1)) hanorm
  have hsplit : ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * llsPer_zeroTerm ρ x
      = ∑' ρ, a ρ - (L : ℂ) * ∑' ρ, b ρ := by
    rw [← tsum_mul_left, ← has.tsum_sub (hbs.mul_left _)]
    refine tsum_congr fun ρ => ?_
    simp only [ha, hb, llsPer_zeroTerm]
    ring
  -- real parts
  have hm : ∀ ρ, zeroOrd χ ρ ≠ 0 → |ρ.re| ≤ 1 := by
    intro ρ h
    obtain ⟨h1, h2⟩ := zeroOrd_strip h
    rw [abs_le]; constructor <;> linarith
  have hd := summable_re_inv hS hm
  have hreb : (∑' ρ, b ρ).re = ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re
      + ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ρ).re := (re_partialFraction hS hd 2).2
  have hRL := re_logDeriv_eq_tsum_proof χ hχ hχ1 hS hH (s := 2) (by norm_num)
  have hGdef : (deriv (gammaFactor χ) 2 / gammaFactor χ 2).re = (Gfun χ 2).re := rfl
  rw [Complex.add_re, hGdef] at hRL
  have hZhalf : ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ρ).re = zeroSumSq χ / 2 := by
    unfold zeroSumSq
    rw [← tsum_div_const]
    refine tsum_congr fun ρ => ?_
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    · rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, hhalf ρ h0]
      ring
  have hRa : -((√x + 1) * zeroSumSq χ) ≤ (∑' ρ, a ρ).re := by
    have h1 : ‖∑' ρ, a ρ‖ ≤ ∑' ρ, ‖a ρ‖ := norm_tsum_le_tsum_norm has.norm
    have h2 : ∑' ρ, ‖a ρ‖ ≤ ∑' ρ : ℂ, (√x + 1) * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :=
      has.norm.tsum_le_tsum hanorm (hS.mul_left _)
    rw [tsum_mul_left] at h2
    have h3 := Complex.abs_re_le_norm (∑' ρ, a ρ)
    have h4 := neg_abs_le (∑' ρ, a ρ).re
    unfold zeroSumSq
    linarith
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hlogq : Real.log (q / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div hq Real.pi_ne_zero
  have hEre := congrArg Complex.re hE
  rw [hsplit] at hEre
  simp only [Complex.add_re, Complex.sub_re, Complex.re_mul_ofReal, Complex.re_ofReal_mul,
    Complex.neg_re] at hEre
  rw [hEre, hreb, hZhalf, hlogq]
  have h1 : ((deriv (LFunction χ) 2 / LFunction χ 2).re + (Gfun χ 2).re) * L
      = (-(Real.log q) / 2 + ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re) * L := by
    rw [hRL]
  generalize (deriv (LFunction χ) 2 / LFunction χ 2).re = D at *
  generalize ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re = S2 at *
  generalize (∑' ρ, a ρ).re = A at *
  generalize zeroSumSq χ = Z at *
  generalize (Gfun χ 2).re = Gr at *
  generalize (llsPer_perronL (fun s => Gfun χ s - Gfun χ 2) x).re = P at *
  nlinarith

#print axioms llsPer_chiUpper
#print axioms llsPer_logPsi_eq_perronL
#print axioms llsPer_perronL_zeroSum
#print axioms llsPer_gamma_bound

end DetPrimality.Bach
