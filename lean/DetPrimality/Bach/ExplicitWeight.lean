import DetPrimality.Bach.ExplicitGamma

/-!
# Zero-density input: `∑_ρ m_ρ (1+|Im ρ|)^{-7/4} < ∞` from `HadamardLogDeriv` (blueprint §3)
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `C_L = ∑ Λ(n)/n²`. -/
noncomputable def CL : ℝ := ∑' n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖

/-- `|L'/L(s)| ≤ ∑ Λ(n)/n²` for `Re s ≥ 2`. -/
theorem norm_logDeriv_LFunction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 2 ≤ s.re) : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ CL := by
  have hs1 : 1 < s.re := by linarith
  have hsum : Summable fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
  have h1 := (LSeriesSummable_twist_vonMangoldt χ hs1).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs1, ← deriv_LFunction_eq_deriv_LSeries χ hs1,
    ← LFunction_eq_LSeries χ hs1, neg_div] at h1
  rw [← norm_neg]
  refine HasSum.norm_le_of_bounded h1 hsum.hasSum fun n => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with hn
  · exact le_refl _
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have h2 : (2 : ℂ).re = 2 := by norm_num
    rw [h2]
    refine div_le_div₀ (norm_nonneg _) ?_ (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hn1 hs)
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem CL_nonneg : 0 ≤ CL := tsum_nonneg fun _ => norm_nonneg _

theorem norm_Gfun_sub_le {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) :
    ‖Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2‖ ≤ √|y| * ∑' k, wk k := by
  have hre : 0 < (((2 : ℝ) : ℂ) + y * I).re := by simp
  exact (hasSum_Gfun_sub χ hre).norm_le_of_bounded (summable_wk.hasSum.mul_left √|y|)
    (fun k => norm_gterm_le (by omega) y)

theorem re_inv_line_sub (ρ : ℂ) (T : ℝ) :
    (1 / ((((2 : ℝ) : ℂ) + T * I) - ρ)).re
      = (2 - ρ.re) / ‖(((2 : ℝ) : ℂ) + T * I) - ρ‖ ^ 2 := by
  rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, Complex.sub_re, line_re]

theorem norm_sq_line_sub (ρ : ℂ) (T : ℝ) :
    ‖(((2 : ℝ) : ℂ) + T * I) - ρ‖ ^ 2 = (2 - ρ.re) ^ 2 + (T - ρ.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- `f_ρ(T) = Re 1/(2+iT-ρ) = (2-β)/|2+iT-ρ|²`. -/
noncomputable def fW (ρ : ℂ) (T : ℝ) : ℝ := (2 - ρ.re) / ‖(((2 : ℝ) : ℂ) + T * I) - ρ‖ ^ 2

theorem natCast_mul_re' (n : ℕ) (w : ℂ) : ((n : ℂ) * w).re = (n : ℝ) * w.re := by simp

/-- Positivity/Hadamard bound: `∑_{ρ ∈ F} m_ρ (2-β)/|2+iT-ρ|² ≤ C_L + |G(2)| + |B| + W√|T|`. -/
theorem sum_fW_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) (B : ℂ)
    (hB : ∀ s : ℂ, completedLFunction χ s ≠ 0 →
      deriv (completedLFunction χ) s / completedLFunction χ s
        = B + ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) (T : ℝ) (F : Finset ℂ) :
    ∑ ρ ∈ F, (zeroOrd χ ρ : ℝ) * fW ρ T
      ≤ CL + ‖Gfun χ 2‖ + ‖B‖ + √|T| * ∑' k, wk k := by
  have hs : 1 < ((((2 : ℝ) : ℂ) + T * I)).re := by rw [line_re]; norm_num
  obtain ⟨hc, hd⟩ := logDeriv_completed_eq χ hχ1 hs
  have hBs := hB _ hc
  have hsum := summable_hadamard_terms χ hS hs
  have hu_eq : ∀ ρ : ℂ, ((zeroOrd χ ρ : ℂ) * (1 / ((((2 : ℝ) : ℂ) + T * I) - ρ) + 1 / ρ)).re
      = (zeroOrd χ ρ : ℝ) * fW ρ T + (zeroOrd χ ρ : ℝ) * (1 / ρ).re := by
    intro ρ
    rw [natCast_mul_re', Complex.add_re, re_inv_line_sub, fW]
    ring
  have hnn1 : ∀ ρ : ℂ, 0 ≤ (zeroOrd χ ρ : ℝ) * fW ρ T := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    · have := (zeroOrd_strip h0).2
      exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) (sq_nonneg _))
  have hnn2 : ∀ ρ : ℂ, 0 ≤ (zeroOrd χ ρ : ℝ) * (1 / ρ).re := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    · have := (zeroOrd_strip h0).1
      rw [one_div, Complex.inv_re]
      exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg this.le (Complex.normSq_nonneg _))
  have hsumu := (Complex.hasSum_re hsum.hasSum).summable
  have hGs : ‖Gfun χ ((((2 : ℝ) : ℂ) + T * I))‖ ≤ ‖Gfun χ 2‖ + √|T| * ∑' k, wk k := by
    calc ‖Gfun χ ((((2 : ℝ) : ℂ) + T * I))‖
        = ‖Gfun χ 2 + (Gfun χ ((((2 : ℝ) : ℂ) + T * I)) - Gfun χ 2)‖ := by ring_nf
      _ ≤ ‖Gfun χ 2‖ + ‖Gfun χ ((((2 : ℝ) : ℂ) + T * I)) - Gfun χ 2‖ := norm_add_le _ _
      _ ≤ ‖Gfun χ 2‖ + √|T| * ∑' k, wk k := by linarith [norm_Gfun_sub_le χ T]
  have hLs := norm_logDeriv_LFunction_le χ (s := ((2 : ℝ) : ℂ) + T * I) (by rw [line_re])
  calc ∑ ρ ∈ F, (zeroOrd χ ρ : ℝ) * fW ρ T
      ≤ ∑ ρ ∈ F, ((zeroOrd χ ρ : ℂ) * (1 / ((((2 : ℝ) : ℂ) + T * I) - ρ) + 1 / ρ)).re :=
        Finset.sum_le_sum fun ρ _ => by rw [hu_eq]; linarith [hnn2 ρ]
    _ ≤ ∑' ρ : ℂ, ((zeroOrd χ ρ : ℂ) * (1 / ((((2 : ℝ) : ℂ) + T * I) - ρ) + 1 / ρ)).re :=
        hsumu.sum_le_tsum F (fun ρ _ => by rw [hu_eq]; linarith [hnn1 ρ, hnn2 ρ])
    _ = (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / ((((2 : ℝ) : ℂ) + T * I) - ρ) + 1 / ρ)).re :=
        (Complex.re_tsum hsum).symm
    _ = (deriv (completedLFunction χ) ((((2 : ℝ) : ℂ) + T * I))
          / completedLFunction χ ((((2 : ℝ) : ℂ) + T * I)) - B).re := by rw [hBs]; ring_nf
    _ ≤ ‖deriv (completedLFunction χ) ((((2 : ℝ) : ℂ) + T * I))
          / completedLFunction χ ((((2 : ℝ) : ℂ) + T * I)) - B‖ := Complex.re_le_norm _
    _ ≤ CL + ‖Gfun χ 2‖ + ‖B‖ + √|T| * ∑' k, wk k := by
        rw [hd]
        calc _ ≤ ‖deriv (LFunction χ) ((((2 : ℝ) : ℂ) + T * I))
                / LFunction χ ((((2 : ℝ) : ℂ) + T * I))‖
              + ‖Gfun χ ((((2 : ℝ) : ℂ) + T * I))‖ + ‖B‖ :=
              (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
          _ ≤ _ := by linarith

/-- The weight `w(T) = (1+|T|)^{-7/4}`. -/
noncomputable def wT (T : ℝ) : ℝ := (1 + ‖T‖) ^ (-(7 / 4 : ℝ))

theorem integrable_wT : Integrable wT := integrable_one_add_norm (by simp; norm_num)

theorem continuous_fW {ρ : ℂ} (hρ : ρ.re < 1) : Continuous (fW ρ) := by
  have hne : ∀ T : ℝ, (((2 : ℝ) : ℂ) + T * I) - ρ ≠ 0 := fun T =>
    ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith)
  exact continuous_const.div ((by fun_prop : Continuous fun T : ℝ =>
    (((2 : ℝ) : ℂ) + T * I) - ρ).norm.pow 2)
    (fun T => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne T)))

theorem fW_nonneg {ρ : ℂ} (hρ : ρ.re < 1) (T : ℝ) : 0 ≤ fW ρ T :=
  div_nonneg (by linarith) (sq_nonneg _)

theorem fW_le_one {ρ : ℂ} (hρ : ρ.re < 1) (T : ℝ) : fW ρ T ≤ 1 := by
  unfold fW
  rw [norm_sq_line_sub, div_le_one (by nlinarith [sq_nonneg (T - ρ.im)])]
  nlinarith [sq_nonneg (T - ρ.im)]

theorem integrable_fW_wT {ρ : ℂ} (hρ : ρ.re < 1) : Integrable fun T => fW ρ T * wT T := by
  have hwc : Continuous wT :=
    (continuous_const.add continuous_norm).rpow_const (fun T => Or.inl (by positivity : (1 : ℝ) + ‖T‖ ≠ 0))
  refine integrable_wT.mono' ((continuous_fW hρ).mul hwc).aestronglyMeasurable
    (Eventually.of_forall fun T => ?_)
  have hw0 : 0 ≤ wT T := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_of_nonneg (mul_nonneg (fW_nonneg hρ T) hw0)]
  exact mul_le_of_le_one_left hw0 (fW_le_one hρ T)

theorem integral_fW_wT_ge {ρ : ℂ} (hρ : 0 < ρ.re ∧ ρ.re < 1) :
    1 / 10 * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ)) ≤ ∫ T, fW ρ T * wT T := by
  set γ := ρ.im with hγ
  set g : ℝ := 1 + |γ| with hg
  have hg0 : 0 < g := by positivity
  set c : ℝ := 1 / 20 * g ^ (-(7 / 4 : ℝ)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hlow : ∀ T, (Icc (γ - 1) (γ + 1)).indicator (fun _ => c) T ≤ fW ρ T * wT T := by
    intro T
    by_cases hT : T ∈ Icc (γ - 1) (γ + 1)
    · rw [indicator_of_mem hT]
      have hTγ : |T - γ| ≤ 1 := abs_le.mpr ⟨by linarith [hT.1], by linarith [hT.2]⟩
      have hf : 1 / 5 ≤ fW ρ T := by
        unfold fW
        rw [norm_sq_line_sub, ← hγ, le_div_iff₀ (by nlinarith [sq_nonneg (T - γ)])]
        nlinarith [sq_abs (T - γ), abs_nonneg (T - γ)]
      have hT1 : 1 + ‖T‖ ≤ 2 * g := by
        rw [Real.norm_eq_abs, hg]
        have : |T| ≤ |γ| + 1 := by
          calc |T| = |(T - γ) + γ| := by ring_nf
            _ ≤ |T - γ| + |γ| := abs_add_le _ _
            _ ≤ |γ| + 1 := by linarith
        linarith [abs_nonneg γ]
      have hw : 1 / 4 * g ^ (-(7 / 4 : ℝ)) ≤ wT T := by
        unfold wT
        calc 1 / 4 * g ^ (-(7 / 4 : ℝ)) ≤ (2 : ℝ) ^ (-(7 / 4 : ℝ)) * g ^ (-(7 / 4 : ℝ)) := by
              gcongr
              rw [Real.rpow_neg (by norm_num), ← one_div]
              apply one_div_le_one_div_of_le (by positivity)
              have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
                (by norm_num : (7 / 4 : ℝ) ≤ 2)
              exact this.trans_eq (by rw [Real.rpow_two]; norm_num)
          _ = (2 * g) ^ (-(7 / 4 : ℝ)) := (Real.mul_rpow (by norm_num) hg0.le).symm
          _ ≤ (1 + ‖T‖) ^ (-(7 / 4 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hT1 (by norm_num)
      calc c = 1 / 5 * (1 / 4 * g ^ (-(7 / 4 : ℝ))) := by rw [hc]; ring
        _ ≤ fW ρ T * wT T := mul_le_mul hf hw (by positivity) (fW_nonneg hρ.2 T)
    · rw [indicator_of_notMem hT]
      exact mul_nonneg (fW_nonneg hρ.2 T) (Real.rpow_nonneg (by positivity) _)
  have hind : Integrable ((Icc (γ - 1) (γ + 1)).indicator (fun _ => c)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  calc 1 / 10 * g ^ (-(7 / 4 : ℝ)) = ∫ T, (Icc (γ - 1) (γ + 1)).indicator (fun _ => c) T := by
        rw [integral_indicator_const c measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
          smul_eq_mul, hc]
        ring
    _ ≤ ∫ T, fW ρ T * wT T := integral_mono hind (integrable_fW_wT hρ.2) hlow

/-- **`∑_ρ m_ρ (1+|Im ρ|)^{-7/4} < ∞`** (from `HadamardLogDeriv` and `∑ m_ρ/|ρ|² < ∞`). -/
theorem summable_zeroOrd_weight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ)) := by
  obtain ⟨B, hB⟩ := hH
  set W : ℝ := ∑' k, wk k with hW
  have hW0 : 0 ≤ W := tsum_nonneg wk_nonneg
  set A0 : ℝ := CL + ‖Gfun χ 2‖ + ‖B‖ with hA0
  have hA00 : 0 ≤ A0 := by have := CL_nonneg; positivity
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
      ∑ ρ ∈ F, (zeroOrd χ ρ : ℝ) * (1 / 10 * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) ≤ Atot := by
    intro F
    have hint : ∀ ρ ∈ F, Integrable fun T => (zeroOrd χ ρ : ℝ) * (fW ρ T * wT T) := by
      intro ρ _
      by_cases h0 : zeroOrd χ ρ = 0
      · simp [h0]
      · exact (integrable_fW_wT (zeroOrd_strip h0).2).const_mul _
    calc ∑ ρ ∈ F, (zeroOrd χ ρ : ℝ) * (1 / 10 * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ)))
        ≤ ∑ ρ ∈ F, ∫ T, (zeroOrd χ ρ : ℝ) * (fW ρ T * wT T) := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          rw [integral_const_mul]
          by_cases h0 : zeroOrd χ ρ = 0
          · simp [h0]
          · exact mul_le_mul_of_nonneg_left (integral_fW_wT_ge (zeroOrd_strip h0))
              (Nat.cast_nonneg _)
      _ = ∫ T, ∑ ρ ∈ F, (zeroOrd χ ρ : ℝ) * (fW ρ T * wT T) :=
          (integral_finsetSum F hint).symm
      _ ≤ Atot := by
          refine integral_mono (integrable_finsetSum F hint) hRi fun T => ?_
          have hw0 : 0 ≤ wT T := Real.rpow_nonneg (by positivity) _
          have h1 := sum_fW_le χ hχ1 B hB hS T F
          calc ∑ ρ ∈ F, (zeroOrd χ ρ : ℝ) * (fW ρ T * wT T)
              = (∑ ρ ∈ F, (zeroOrd χ ρ : ℝ) * fW ρ T) * wT T := by
                rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => by ring
            _ ≤ (A0 + √|T| * W) * wT T := mul_le_mul_of_nonneg_right (by linarith) hw0
            _ = A0 * wT T + W * (√|T| * wT T) := by ring
            _ ≤ A0 * wT T + W * P5 T := by
                have := mul_le_mul_of_nonneg_left (hsq T) hW0
                linarith
  have hnn : 0 ≤ fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * (1 / 10 * (1 + |ρ.im|) ^ (-(7 / 4 : ℝ))) :=
    fun ρ => mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
  have hsum := summable_of_sum_le hnn hfin
  have h10 := hsum.mul_left 10
  refine h10.congr fun ρ => ?_
  ring

end DetPrimality.Bach
