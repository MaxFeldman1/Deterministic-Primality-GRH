import DetPrimality.Bach.LLSPerronMain
import DetPrimality.Bach.LLSZetaConst

/-!
# LLS Lemma 1: `llsZL_main : LLSZetaLower (1 / 20)`

Explicit formula for `∑_{n ≤ x} Λ(n) log(x/n)` (kernel `x^s/s²`, the Riemann zeta function):

`∑_{n ≤ x} Λ(n) log(x/n) = x - 1 - log x + log²x/2 + (G(2) - B) log x + L[G - G(2)](x)
    - ∑_ρ m_ρ (x^ρ - 1)/ρ²`  (`llsZL_explicit'`),

and `G(2) - B - 1 = -log(2π)`, `L[G - G(2)](x) ≥ -log²x/2`, `|∑_ρ m_ρ (x^ρ-1)/ρ²| ≤ (√x+1) ∑ m_ρ/|ρ|²`
under RH.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-! ### The trivial character mod 1 -/

theorem llsZL_logPsi_one (x : ℝ) : logPsi χ₁ x = (logPsiZeta x : ℂ) := by
  unfold logPsi logPsiZeta
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MulChar.one_apply (isUnit_of_subsingleton _), mul_one, Complex.ofReal_mul]

theorem llsZL_gammaShift : gammaShift χ₁ = 0 := by
  unfold gammaShift
  rw [if_pos]
  show χ₁ (-1) = 1
  exact MulChar.one_apply (isUnit_of_subsingleton _)

/-- `-ζ'/ζ(s) = 1/s + 1/(s-1) + G(s) - B - ∑_ρ m_ρ (1/(s-ρ) + 1/ρ)` for `Re s > 1`. -/
theorem llsZL_decomp {s : ℂ} (hs : 1 < s.re) :
    -(deriv (LFunction χ₁) s / LFunction χ₁ s)
      = 1 / s + 1 / (s - 1) + Gfun χ₁ s - (llsZeta_B : ℂ)
        - ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  rw [LFunction_modOne_eq, Gfun_eq χ₁ (by linarith), llsZL_gammaShift]
  simp only [Nat.cast_zero, add_zero]
  exact llsZeta_neg_logDeriv_zeta_B hs

/-- `Z(s) = ∑_ρ m_ρ (1/(s-ρ) - 1/(2-ρ))`. -/
noncomputable def llsZL_Z (s : ℂ) : ℂ :=
  ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ))

/-- `-ζ'/ζ(2) - 3/2`. -/
noncomputable def llsZL_c1 : ℂ := -(deriv (LFunction χ₁) 2 / LFunction χ₁ 2) - 3 / 2

theorem llsZL_line_decomp {s : ℂ} (hs : 1 < s.re) :
    -(deriv (LFunction χ₁) s / LFunction χ₁ s)
      = (llsZL_c1 + 1 / s + 1 / (s - 1) + (Gfun χ₁ s - Gfun χ₁ 2)) - llsZL_Z s := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hS := llsZeta_summable
  have hsub : llsZL_Z s = (∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
      - ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (1 / (2 - ρ) + 1 / ρ) := by
    unfold llsZL_Z
    rw [← (summable_hadamard_terms χ₁ hS hs).tsum_sub (summable_hadamard_terms χ₁ hS h2)]
    congr 1; funext ρ; ring
  have hs' := llsZL_decomp hs
  have h2' := llsZL_decomp h2
  rw [show (1 : ℂ) / (2 - 1) = 1 by norm_num] at h2'
  rw [hsub, llsZL_c1]
  linear_combination hs' - h2'

/-! ### `∑ m_ρ (1+|Im ρ|)^{-7/4} < ∞` for the zeros of `ζ` -/

theorem llsZL_summable_weight_of_bound {m : ℂ → ℕ}
    (hstrip : ∀ ρ, m ρ ≠ 0 → 0 < ρ.re ∧ ρ.re < 1) {A0 : ℝ}
    (hb : ∀ (T : ℝ) (F : Finset ℂ),
      ∑ ρ ∈ F, (m ρ : ℝ) * fW ρ T ≤ A0 + √|T| * ∑' k, wk k) :
    Summable fun ρ : ℂ => (m ρ : ℝ) * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ)) := by
  set W : ℝ := ∑' k, wk k with hW
  have hW0 : 0 ≤ W := tsum_nonneg wk_nonneg
  set P5 : ℝ → ℝ := fun T => (1 + ‖T‖) ^ (-(5 / 4 : ℝ)) with hP5
  have hP5i : Integrable P5 := integrable_one_add_norm (by simp; norm_num)
  have hRi : Integrable fun T => A0 * wT T + W * P5 T :=
    (integrable_wT.const_mul A0).add (hP5i.const_mul W)
  set Atot : ℝ := ∫ T, (A0 * wT T + W * P5 T) with hAtot
  have hsq : ∀ T : ℝ, √|T| * wT T ≤ P5 T := by
    intro T
    have hu : 0 < 1 + ‖T‖ := by positivity
    have h1 : √|T| ≤ (1 + ‖T‖) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs]
      exact Real.sqrt_le_sqrt (by linarith)
    calc √|T| * wT T ≤ (1 + ‖T‖) ^ (1 / 2 : ℝ) * wT T :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu.le _)
      _ = P5 T := by
          rw [wT, hP5, ← Real.rpow_add hu]
          norm_num
  have hfin : ∀ F : Finset ℂ,
      ∑ ρ ∈ F, (m ρ : ℝ) * (1 / 10 * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) ≤ Atot := by
    intro F
    have hint : ∀ ρ ∈ F, Integrable fun T => (m ρ : ℝ) * (fW ρ T * wT T) := by
      intro ρ _
      by_cases h0 : m ρ = 0
      · simp [h0]
      · exact (integrable_fW_wT (hstrip ρ h0).2).const_mul _
    calc ∑ ρ ∈ F, (m ρ : ℝ) * (1 / 10 * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ)))
        ≤ ∑ ρ ∈ F, ∫ T, (m ρ : ℝ) * (fW ρ T * wT T) := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          rw [integral_const_mul]
          by_cases h0 : m ρ = 0
          · simp [h0]
          · exact mul_le_mul_of_nonneg_left (integral_fW_wT_ge (hstrip ρ h0))
              (Nat.cast_nonneg _)
      _ = ∫ T, ∑ ρ ∈ F, (m ρ : ℝ) * (fW ρ T * wT T) :=
          (integral_finsetSum F hint).symm
      _ ≤ Atot := by
          refine integral_mono (integrable_finsetSum F hint) hRi fun T => ?_
          have hw0 : 0 ≤ wT T := Real.rpow_nonneg (by positivity) _
          have h1 := hb T F
          calc ∑ ρ ∈ F, (m ρ : ℝ) * (fW ρ T * wT T)
              = (∑ ρ ∈ F, (m ρ : ℝ) * fW ρ T) * wT T := by
                rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => by ring
            _ ≤ (A0 + √|T| * W) * wT T := mul_le_mul_of_nonneg_right (by linarith) hw0
            _ = A0 * wT T + W * (√|T| * wT T) := by ring
            _ ≤ A0 * wT T + W * P5 T := by
                have := mul_le_mul_of_nonneg_left (hsq T) hW0
                linarith
  have hnn : 0 ≤ fun ρ : ℂ => (m ρ : ℝ) * (1 / 10 * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) :=
    fun ρ => mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
  have hsum := summable_of_sum_le hnn hfin
  have h10 := hsum.mul_left 10
  refine h10.congr fun ρ => ?_
  ring

theorem llsZL_sum_fW_le (T : ℝ) (F : Finset ℂ) :
    ∑ ρ ∈ F, (zeroOrd χ₁ ρ : ℝ) * fW ρ T
      ≤ (CL + ‖Gfun χ₁ 2‖ + |llsZeta_B| + 3 / 2) + √|T| * ∑' k, wk k := by
  have hS := llsZeta_summable
  set s : ℂ := ((2 : ℝ) : ℂ) + T * I with hsdef
  have hsre : s.re = 2 := line_re 2 T
  have hs : 1 < s.re := by rw [hsre]; norm_num
  have hBs : ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
      = 1 / s + 1 / (s - 1) + Gfun χ₁ s - (llsZeta_B : ℂ)
        + deriv (LFunction χ₁) s / LFunction χ₁ s := by
    linear_combination llsZL_decomp hs
  have hsum := summable_hadamard_terms χ₁ hS hs
  have hu_eq : ∀ ρ : ℂ, ((zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re
      = (zeroOrd χ₁ ρ : ℝ) * fW ρ T + (zeroOrd χ₁ ρ : ℝ) * (1 / ρ).re := by
    intro ρ
    rw [natCast_mul_re', Complex.add_re, hsdef, re_inv_line_sub, fW]
    ring
  have hnn1 : ∀ ρ : ℂ, 0 ≤ (zeroOrd χ₁ ρ : ℝ) * fW ρ T := by
    intro ρ
    by_cases h0 : zeroOrd χ₁ ρ = 0
    · simp [h0]
    · have := (zeroOrd_strip h0).2
      exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) (sq_nonneg _))
  have hnn2 : ∀ ρ : ℂ, 0 ≤ (zeroOrd χ₁ ρ : ℝ) * (1 / ρ).re := by
    intro ρ
    by_cases h0 : zeroOrd χ₁ ρ = 0
    · simp [h0]
    · have := (zeroOrd_strip h0).1
      rw [one_div, Complex.inv_re]
      exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg this.le (Complex.normSq_nonneg _))
  have hsumu := (Complex.hasSum_re hsum.hasSum).summable
  have hGs : ‖Gfun χ₁ s‖ ≤ ‖Gfun χ₁ 2‖ + √|T| * ∑' k, wk k := by
    calc ‖Gfun χ₁ s‖ = ‖Gfun χ₁ 2 + (Gfun χ₁ s - Gfun χ₁ 2)‖ := by ring_nf
      _ ≤ ‖Gfun χ₁ 2‖ + ‖Gfun χ₁ s - Gfun χ₁ 2‖ := norm_add_le _ _
      _ ≤ ‖Gfun χ₁ 2‖ + √|T| * ∑' k, wk k := by linarith [norm_Gfun_sub_le χ₁ T]
  have hLs := norm_logDeriv_LFunction_le χ₁ (s := s) (by rw [hsre])
  have h2s : 2 ≤ ‖s‖ := llsPer_two_le_norm_line T
  have h1s : ‖1 / s‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le two_pos h2s
  have h1s1 : ‖1 / (s - 1)‖ ≤ 1 := by
    have h : 1 ≤ ‖s - 1‖ := by
      have := Complex.re_le_norm (s - 1)
      rw [Complex.sub_re, hsre, Complex.one_re] at this
      linarith
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr h
  have hBn : ‖(llsZeta_B : ℂ)‖ = |llsZeta_B| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  calc ∑ ρ ∈ F, (zeroOrd χ₁ ρ : ℝ) * fW ρ T
      ≤ ∑ ρ ∈ F, ((zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re :=
        Finset.sum_le_sum fun ρ _ => by rw [hu_eq]; linarith [hnn2 ρ]
    _ ≤ ∑' ρ : ℂ, ((zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re :=
        hsumu.sum_le_tsum F (fun ρ _ => by rw [hu_eq]; linarith [hnn1 ρ, hnn2 ρ])
    _ = (∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re :=
        (Complex.re_tsum hsum).symm
    _ ≤ ‖1 / s + 1 / (s - 1) + Gfun χ₁ s - (llsZeta_B : ℂ)
          + deriv (LFunction χ₁) s / LFunction χ₁ s‖ := by
        rw [hBs]; exact Complex.re_le_norm _
    _ ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ + ‖Gfun χ₁ s‖ + ‖(llsZeta_B : ℂ)‖
          + ‖deriv (LFunction χ₁) s / LFunction χ₁ s‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by rw [hBn]; linarith

theorem llsZL_summable_weight :
    Summable fun ρ : ℂ => (zeroOrd χ₁ ρ : ℝ) * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ)) :=
  llsZL_summable_weight_of_bound (fun _ h => zeroOrd_strip h) llsZL_sum_fW_le

/-! ### Integrability on `Re s = 2` -/

theorem llsZL_vi_logDeriv :
    VerticalIntegrable (fun s => -(deriv (LFunction χ₁) s / LFunction χ₁ s) / s ^ 2) 2 := by
  unfold VerticalIntegrable
  have hline : ∀ y : ℝ, ((2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h
    rw [line_re] at this
    norm_num at this
  have hd : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hd' : DifferentiableOn ℂ (deriv riemannZeta) {(1 : ℂ)}ᶜ :=
    hd.deriv isOpen_compl_singleton
  have hlc : Continuous fun y : ℝ => ((2 : ℝ) : ℂ) + y * I := by fun_prop
  have hcont : Continuous fun y : ℝ =>
      -(deriv (LFunction χ₁) (((2 : ℝ) : ℂ) + y * I) / LFunction χ₁ (((2 : ℝ) : ℂ) + y * I))
        / (((2 : ℝ) : ℂ) + y * I) ^ 2 := by
    rw [LFunction_modOne_eq]
    refine Continuous.div (Continuous.neg (Continuous.div
      (hd'.continuousOn.comp_continuous hlc hline)
      (hd.continuousOn.comp_continuous hlc hline)
      (fun y => riemannZeta_ne_zero_of_one_le_re (by rw [line_re]; norm_num)))) (by fun_prop)
      (fun y => pow_ne_zero 2 (llsPer_line_ne y))
  refine integrable_of_le_div_sq hcont (c := 2) (M := CL) two_pos fun y => ?_
  beta_reduce
  rw [div_eq_mul_one_div, norm_mul, norm_neg, llsPer_norm_kernel]
  have h1 := norm_logDeriv_LFunction_le χ₁ (s := ((2 : ℝ) : ℂ) + y * I) (by rw [line_re])
  calc _ ≤ CL * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = CL / ((2 : ℝ) ^ 2 + y ^ 2) := by ring

/-! ### The explicit formula -/

theorem llsZL_explicit {x : ℝ} (hx : 1 ≤ x) :
    logPsi χ₁ x = llsZL_c1 * (Real.log x : ℂ) + (Real.log x : ℂ) ^ 2 / 2
      + ((x : ℂ) - (Real.log x : ℂ) - 1)
      + llsPer_perronL (fun s => Gfun χ₁ s - Gfun χ₁ 2) x
      - ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * llsPer_zeroTerm ρ x := by
  have hx0 : 0 < x := by linarith
  have hc := llsPer_vi_const llsZL_c1
  have h1i := llsPer_vi_inv_self
  have h2i : VerticalIntegrable (fun s : ℂ => 1 / (s - 1) / s ^ 2) 2 :=
    llsPer_vi_inv_sub (w := 1) (by norm_num)
  have hGi := llsPer_vi_gamma χ₁
  have hA1 : VerticalIntegrable (fun s : ℂ => (llsZL_c1 + 1 / s) / s ^ 2) 2 := by
    refine (Integrable.add hc h1i).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have hA2 : VerticalIntegrable (fun s : ℂ => (llsZL_c1 + 1 / s + 1 / (s - 1)) / s ^ 2) 2 := by
    refine (Integrable.add hA1 h2i).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have hA3 : VerticalIntegrable (fun s : ℂ =>
      (llsZL_c1 + 1 / s + 1 / (s - 1) + (Gfun χ₁ s - Gfun χ₁ 2)) / s ^ 2) 2 := by
    refine (Integrable.add hA2 hGi).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have hZi : VerticalIntegrable (fun s => llsZL_Z s / s ^ 2) 2 := by
    refine (Integrable.sub hA3 llsZL_vi_logDeriv).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [llsZL_line_decomp (s := ((2 : ℝ) : ℂ) + y * I) (by rw [line_re]; norm_num)]
    ring
  have hZ : llsPer_perronL llsZL_Z x = ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * llsPer_zeroTerm ρ x :=
    llsPer_perronL_zeroSum (m := zeroOrd χ₁) (fun _ h => zeroOrd_strip h)
      llsZL_summable_weight hx
  have h1 : logPsi χ₁ x = llsPer_perronL (fun s =>
      (llsZL_c1 + 1 / s + 1 / (s - 1) + (Gfun χ₁ s - Gfun χ₁ 2)) - llsZL_Z s) x := by
    rw [llsPer_logPsi_eq_perronL χ₁ hx]
    apply llsPer_perronL_congr_line
    intro y
    exact llsZL_line_decomp (by rw [line_re]; norm_num)
  rw [llsPer_perronL_sub hA3 hZi hx0, llsPer_perronL_add hA2 hGi hx0,
    llsPer_perronL_add hA1 h2i hx0, llsPer_perronL_add hc h1i hx0, llsPer_perronL_const,
    llsPer_perronL_one hx, llsPer_perronL_inv_self hx, llsPer_perronL_inv_sub_one hx, hZ] at h1
  exact h1

/-- The Γ-part: `Re L[G - G(2)](x) ≥ -log²x/2`
(exactly: `= -log²x/2 + ∑_{k ≥ 1} (1 - x^{-2k})/(4k²)`). -/
theorem llsZL_gamma_lower {x : ℝ} (hx : 1 ≤ x) :
    -(Real.log x ^ 2 / 2) ≤ (llsPer_perronL (fun s => Gfun χ₁ s - Gfun χ₁ 2) x).re := by
  have hx0 : 0 < x := by linarith
  have hR := llsPer_hasSum_lterm χ₁ hx
  rw [llsZL_gammaShift] at hR
  simp only [add_zero] at hR
  rw [← hR.tsum_eq, hR.summable.tsum_eq_zero_add]
  have htail : Summable fun j : ℕ => llsPer_lterm (2 * (j + 1)) x :=
    (summable_nat_add_iff (f := fun k : ℕ => llsPer_lterm (2 * k) x) 1).mpr hR.summable
  set L := Real.log x with hLdef
  have hcs : HasSum (fun j : ℕ => -(L / 2) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))))
      (-(L / 2) * 1) := hasSum_telescope.mul_left _
  have hle : ∀ j : ℕ, -(L / 2) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
      ≤ llsPer_lterm (2 * (j + 1)) x := by
    intro j
    rw [llsPer_lterm, if_neg (by omega), ← hLdef]
    have hp : x ^ (-((2 * (j + 1) : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr (Nat.cast_nonneg _))
    have hm : (0 : ℝ) < ((2 * (j + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * (j + 1))
    have h0 : 0 ≤ 1 / ((2 * (j + 1) : ℕ) : ℝ) ^ 2
        - x ^ (-((2 * (j + 1) : ℕ) : ℝ)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 := by
      rw [← sub_div]
      exact div_nonneg (by linarith) (by positivity)
    have e : L / (2 + ((2 * (j + 1) : ℕ) : ℝ)) - L / ((2 * (j + 1) : ℕ) : ℝ)
        = -(L / 2) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      field_simp
      ring
    linarith
  have hT := hcs.summable.tsum_le_tsum hle htail
  rw [hcs.tsum_eq] at hT
  have h0 : llsPer_lterm (2 * 0) x = L / 2 - L ^ 2 / 2 := by
    rw [llsPer_lterm, if_pos rfl]
  rw [h0]
  linarith

/-- **LLS Lemma 1.** -/
theorem llsZL_main : LLSZetaLower (1 / 20) := by
  intro hGRH x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hS := llsZeta_summable
  have hE := llsZL_explicit hx1
  have hP := llsZL_gamma_lower hx1
  set L := Real.log x with hL
  have hhalf : ∀ ρ, zeroOrd χ₁ ρ ≠ 0 → ρ.re = 1 / 2 := fun ρ h =>
    re_eq_half_of_zeroOrd_ne_zero hGRH χ₁ h
  set a : ℂ → ℂ := fun ρ => (zeroOrd χ₁ ρ : ℂ) * ((x : ℂ) ^ ρ / ρ ^ 2 - 1 / ρ ^ 2) with ha
  have hbs : Summable fun ρ : ℂ => (zeroOrd χ₁ ρ : ℂ) * (1 / (2 - ρ) + 1 / ρ) :=
    summable_hadamard_terms χ₁ hS (s := 2) (by norm_num)
  have hanorm : ∀ ρ, ‖a ρ‖ ≤ (√x + 1) * ((zeroOrd χ₁ ρ : ℝ) / ‖ρ‖ ^ 2) := by
    intro ρ
    by_cases h0 : zeroOrd χ₁ ρ = 0
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
      calc (zeroOrd χ₁ ρ : ℝ) * (‖(x : ℂ) ^ ρ - 1‖ / ‖ρ‖ ^ 2)
          ≤ (zeroOrd χ₁ ρ : ℝ) * ((√x + 1) / ‖ρ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (by positivity))
              (Nat.cast_nonneg _)
        _ = (√x + 1) * ((zeroOrd χ₁ ρ : ℝ) / ‖ρ‖ ^ 2) := by ring
  have has : Summable a := Summable.of_norm_bounded (hS.mul_left (√x + 1)) hanorm
  have hsplit : ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * llsPer_zeroTerm ρ x
      = ∑' ρ, a ρ - (L : ℂ) * ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (1 / (2 - ρ) + 1 / ρ) := by
    rw [← tsum_mul_left, ← has.tsum_sub (hbs.mul_left _)]
    refine tsum_congr fun ρ => ?_
    simp only [ha, llsPer_zeroTerm]
    ring
  have hb2 : ∑' ρ : ℂ, (zeroOrd χ₁ ρ : ℂ) * (1 / (2 - ρ) + 1 / ρ)
      = 3 / 2 + Gfun χ₁ 2 - (llsZeta_B : ℂ) + deriv (LFunction χ₁) 2 / LFunction χ₁ 2 := by
    have h := llsZL_decomp (s := 2) (by norm_num)
    rw [show (1 : ℂ) / (2 - 1) = 1 by norm_num] at h
    linear_combination h
  have hRa : (∑' ρ, a ρ).re ≤ (√x + 1) * zeroSumSq χ₁ := by
    have h1 : ‖∑' ρ, a ρ‖ ≤ ∑' ρ, ‖a ρ‖ := norm_tsum_le_tsum_norm has.norm
    have h2 : ∑' ρ, ‖a ρ‖ ≤ ∑' ρ : ℂ, (√x + 1) * ((zeroOrd χ₁ ρ : ℝ) / ‖ρ‖ ^ 2) :=
      has.norm.tsum_le_tsum hanorm (hS.mul_left _)
    rw [tsum_mul_left] at h2
    have h3 := Complex.re_le_norm (∑' ρ, a ρ)
    unfold zeroSumSq
    linarith
  rw [hsplit, hb2, llsZL_logPsi_one, llsZL_c1] at hE
  have hC : ((logPsiZeta x : ℝ) : ℂ)
      = ((x - 1 - L + L ^ 2 / 2 - L * llsZeta_B : ℝ) : ℂ)
        + llsPer_perronL (fun s => Gfun χ₁ s - Gfun χ₁ 2) x - ∑' ρ, a ρ
        + (L : ℂ) * Gfun χ₁ 2 := by
    rw [hE]; push_cast; ring
  have hRe := congrArg Complex.re hC
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul] at hRe
  rcases llsPer_Gfun_two_re χ₁ with ⟨_, hG⟩ | ⟨hsh, _⟩
  swap
  · rw [llsZL_gammaShift] at hsh; exact absurd hsh (by norm_num)
  rw [hG, llsZeta_B] at hRe
  have hZ := llsZeta_zeroSumSq_le hGRH
  have hsq : (0 : ℝ) ≤ √x + 1 := by positivity
  have hZ' : (√x + 1) * zeroSumSq χ₁ ≤ (√x + 1) * (1 / 20) :=
    mul_le_mul_of_nonneg_left (hZ.trans (by norm_num)) hsq
  have hlog : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  rw [hlog, hRe]
  generalize (llsPer_perronL (fun s => Gfun χ₁ s - Gfun χ₁ 2) x).re = P at *
  generalize (∑' ρ, a ρ).re = A at *
  generalize zeroSumSq χ₁ = Z at *
  nlinarith

#print axioms llsZL_main

end DetPrimality.Bach
