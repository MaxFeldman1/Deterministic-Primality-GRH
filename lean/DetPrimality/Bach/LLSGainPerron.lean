import DetPrimality.Bach.LLSDefs
import DetPrimality.Bach.ExplicitMain
import DetPrimality.Bach.HadamardL
import DetPrimality.Bach.Growth

/-!
# LLS Lemma 3, analytic part: Perron for `W(x, χ) = ∑_{n ≤ x} Λ(n)χ(n)/n (1 - n/x)`

We apply the existing kernel `1/(s(s+1))` (`perronI`) to the shifted function
`s ↦ -L'/L(s + 1, χ)`:

* `llsGain_weightedLogSum_eq_perronI` : `W(x, χ) = I[-L'/L(· + 1)](x)`;
* `llsGain_decomp` : `-L'/L(s+1) = -L'/L(3) + (G(s+1) - G(3)) - ∑_ρ m_ρ (1/(s-(ρ-1)) - 1/(2-(ρ-1)))`;
* `llsGain_hasSum_perronI_gamma`, `llsGain_vi_gamma` : the Γ-part, termwise;
* `llsGain_perronI_Z` : the zero part, termwise;
* `llsGain_formula` : the resulting explicit formula.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Step 1: `W(x) = I[-L'/L(· + 1)](x)` -/

theorem llsGain_term_shift {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => χ (n : ZMod N) * (Λ n : ℂ) / (n : ℂ)) s n
      = LSeries.term (fun n => χ (n : ZMod N) * (Λ n : ℂ)) (s + 1) n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, cpow_add _ _ hnc, cpow_one]
    field_simp

theorem llsGain_line_re (y : ℝ) : (((2 : ℝ) : ℂ) + y * I + 1).re = 3 := by
  have : (((2 : ℝ) : ℂ) + y * I + 1).re = 2 + 1 := by simp
  rw [this]; norm_num

theorem llsGain_weightedLogSum_eq_perronI {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 1 ≤ x) :
    weightedLogSum χ x
      = perronI (fun s => -(deriv (LFunction χ) (s + 1) / LFunction χ (s + 1))) x := by
  have hx0 : 0 < x := by linarith
  let f0 : ℕ → ℂ := fun n => χ (n : ZMod N) * (Λ n : ℂ)
  let f : ℕ → ℂ := fun n => χ (n : ZMod N) * (Λ n : ℂ) / (n : ℂ)
  have hterm : ∀ (s : ℂ) (n : ℕ), LSeries.term f s n = LSeries.term f0 (s + 1) n :=
    llsGain_term_shift χ
  set K : ℂ → ℂ := fun s => 1 / (s * (s + 1)) with hK
  set F : ℕ → ℝ → ℂ := fun n y => if n = 0 then 0 else
    f n * ((((n : ℝ) / x : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) • K (((2 : ℝ) : ℂ) + y * I))
    with hFdef
  have hpos : ∀ n : ℕ, n ≠ 0 → 0 < (n : ℝ) / x := fun n hn =>
    div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hx0
  -- the Dirichlet series on the line
  have hLS : ∀ y : ℝ, -(deriv (LFunction χ) (((2 : ℝ) : ℂ) + y * I + 1)
      / LFunction χ (((2 : ℝ) : ℂ) + y * I + 1)) = LSeries f (((2 : ℝ) : ℂ) + y * I) := by
    intro y
    have hs : 1 < (((2 : ℝ) : ℂ) + y * I + 1).re := by rw [llsGain_line_re]; norm_num
    have h1 : LSeries f0 (((2 : ℝ) : ℂ) + y * I + 1) = _ := LSeries_twist_vonMangoldt_eq χ hs
    have h2 : LSeries f (((2 : ℝ) : ℂ) + y * I) = LSeries f0 (((2 : ℝ) : ℂ) + y * I + 1) :=
      tsum_congr fun n => hterm _ n
    rw [h2, h1, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs, neg_div]
  -- pointwise expansion of the integrand
  have hpt : ∀ y : ℝ, ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
      (fun s => -(deriv (LFunction χ) (s + 1) / LFunction χ (s + 1)) / (s * (s + 1)))
        (((2 : ℝ) : ℂ) + y * I) = ∑' n : ℕ, F n y := by
    intro y
    set s : ℂ := ((2 : ℝ) : ℂ) + y * I with hs
    simp only
    rw [hLS y, LSeries, smul_eq_mul, ← tsum_div_const, ← tsum_mul_left]
    congr 1
    funext n
    simp only [hFdef]
    split_ifs with hn
    · simp [hn]
    · rw [LSeries.term_of_ne_zero hn, smul_eq_mul, hK]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hcp : (((n : ℝ) / x : ℝ) : ℂ) ^ (-s)
          = ((x⁻¹ : ℝ) : ℂ) ^ (-s) * ((n : ℂ) ^ s)⁻¹ := by
        rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hn0 (inv_nonneg.mpr hx0.le),
          cpow_neg, ofReal_natCast]
        ring
      rw [hcp]
      ring
  -- integrability and the norm series
  have hKint := verticalIntegrable_kernel (c := 2) two_pos
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    by_cases hn : n = 0
    · have : F n = fun _ => 0 := by funext y; simp [hFdef, hn]
      rw [this]; exact integrable_zero _ _ _
    · have h := (integrable_mellinInv_integrand hKint (hpos n hn)).const_mul (f n)
      refine h.congr (Eventually.of_forall fun y => ?_)
      simp [hFdef, hn, hK]
  set C : ℝ := ∫ y : ℝ, ‖K (((2 : ℝ) : ℂ) + y * I)‖ with hC
  have hFnorm : ∀ n, ∫ y, ‖F n y‖ = ‖LSeries.term f 2 n‖ * (x ^ 2 * C) := by
    intro n
    by_cases hn : n = 0
    · simp [hFdef, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hpt' : ∀ y : ℝ, ‖F n y‖ = (‖f n‖ * ((n : ℝ) / x) ^ (-(2 : ℝ)))
          * ‖K (((2 : ℝ) : ℂ) + y * I)‖ := by
        intro y
        simp only [hFdef, hn, if_false, norm_mul, norm_smul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos n hn)]
        have : (-(((2 : ℝ) : ℂ) + y * I)).re = -2 := by simp
        rw [this]
        ring
      rw [integral_congr_ae (Eventually.of_forall hpt'), integral_const_mul, ← hC,
        LSeries.norm_term_eq, if_neg hn]
      have h2 : (2 : ℂ).re = 2 := by simp
      rw [h2, Real.rpow_neg (div_nonneg hnpos.le hx0.le), Real.div_rpow hnpos.le hx0.le,
        Real.rpow_two, Real.rpow_two]
      field_simp
  have hsum2 : Summable fun n => ‖LSeries.term f 2 n‖ := by
    have h := (LSeriesSummable_twist_vonMangoldt χ (s := 3) (by norm_num)).norm
    refine h.congr fun n => ?_
    rw [hterm 2 n, show (2 : ℂ) + 1 = 3 by norm_num]
    rfl
  have hsum : Summable fun n => ∫ y, ‖F n y‖ := by
    have h := hsum2.mul_right (x ^ 2 * C)
    refine h.congr fun n => (hFnorm n).symm
  -- interchange
  have hint := integral_tsum_of_summable_integral_norm hFint hsum
  have hFn : ∀ n, ∫ y, F n y = if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ) * (if (n : ℝ) / x ≤ 1 then ((1 - (n : ℝ) / x : ℝ) : ℂ) else 0)) := by
    intro n
    by_cases hn : n = 0
    · simp [hFdef, hn]
    · simp only [hFdef, hn, if_false]
      rw [integral_const_mul, kernel_integral (hpos n hn)]
  unfold perronI mellinInv
  rw [integral_congr_ae (Eventually.of_forall hpt), ← hint]
  simp_rw [hFn]
  rw [Complex.real_smul, ← tsum_mul_left]
  have hzero : ∀ n ∉ Finset.range (⌊x⌋₊ + 1), (((1 / (2 * Real.pi) : ℝ) : ℂ) * (if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ) * (if (n : ℝ) / x ≤ 1 then ((1 - (n : ℝ) / x : ℝ) : ℂ) else 0))))
      = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hxn : x < n := Nat.lt_of_floor_lt hn
    have h1 : 1 < (n : ℝ) / x := by rw [lt_div_iff₀ hx0]; linarith
    split_ifs with h0 h2
    · simp
    · exact absurd h2 (not_le.mpr h1)
    · simp
  rw [tsum_eq_sum hzero]
  unfold weightedLogSum
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnx : (n : ℝ) ≤ x :=
    (Nat.le_floor_iff hx0.le).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  by_cases h0 : n = 0
  · simp [h0]
  · have hle : (n : ℝ) / x ≤ 1 := by rw [div_le_one hx0]; exact hnx
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast h0
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    rw [if_neg h0, if_pos hle]
    show _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * (χ (n : ZMod N) * (Λ n : ℂ) / (n : ℂ)
      * ((2 * Real.pi : ℂ) * ((1 - (n : ℝ) / x : ℝ) : ℂ)))
    push_cast
    field_simp

/-! ## Step 2: decomposition of `-L'/L(s+1)` -/

/-- `Z(s) = ∑_ρ m_ρ (1/(s-(ρ-1)) - 1/(2-(ρ-1)))`. -/
noncomputable def llsGain_Z {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - (ρ - 1)) - 1 / (2 - (ρ - 1)))

theorem llsGain_decomp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {s : ℂ} (hs : 0 < s.re) :
    -(deriv (LFunction χ) (s + 1) / LFunction χ (s + 1))
      = -(deriv (LFunction χ) 3 / LFunction χ 3) + (Gfun χ (s + 1) - Gfun χ 3)
        - llsGain_Z χ s := by
  obtain ⟨B, hB⟩ := hH
  have hs1 : 1 < (s + 1).re := by simp; linarith
  have h3 : (1 : ℝ) < (3 : ℂ).re := by norm_num
  obtain ⟨hcs, hds⟩ := logDeriv_completed_eq χ hχ1 hs1
  obtain ⟨hc3, hd3⟩ := logDeriv_completed_eq χ hχ1 h3
  have hBs := hB (s + 1) hcs
  have hB3 := hB 3 hc3
  have hsub : llsGain_Z χ s
      = (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s + 1 - ρ) + 1 / ρ))
        - ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (3 - ρ) + 1 / ρ) := by
    rw [← (summable_hadamard_terms χ hS hs1).tsum_sub (summable_hadamard_terms χ hS h3)]
    unfold llsGain_Z
    congr 1; funext ρ
    rw [show s - (ρ - 1) = s + 1 - ρ by ring, show 2 - (ρ - 1) = 3 - ρ by ring]
    ring
  rw [hsub]
  linear_combination hds - hd3 - hBs + hB3

/-! ## Step 3: the Γ-part -/

theorem llsGain_hasSum_Gfun_shift {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ => 1 / (2 + ((2 * k + gammaShift χ + 1 : ℕ) : ℂ))
        - 1 / (s + ((2 * k + gammaShift χ + 1 : ℕ) : ℂ))) (Gfun χ (s + 1) - Gfun χ 3) := by
  have h1 := hasSum_Gfun_sub χ (s := s + 1) (by simp; linarith)
  have h3 := hasSum_Gfun_sub χ (s := 3) (by norm_num)
  have h := h1.sub h3
  have hfun : (fun k : ℕ => 1 / (2 + ((2 * k + gammaShift χ + 1 : ℕ) : ℂ))
        - 1 / (s + ((2 * k + gammaShift χ + 1 : ℕ) : ℂ)))
      = fun k : ℕ => (1 / (2 + ((2 * k + gammaShift χ : ℕ) : ℂ))
          - 1 / (s + 1 + ((2 * k + gammaShift χ : ℕ) : ℂ)))
        - (1 / (2 + ((2 * k + gammaShift χ : ℕ) : ℂ))
          - 1 / (3 + ((2 * k + gammaShift χ : ℕ) : ℂ))) := by
    funext k
    have e1 : (2 : ℂ) + ((2 * k + gammaShift χ + 1 : ℕ) : ℂ)
        = 3 + ((2 * k + gammaShift χ : ℕ) : ℂ) := by push_cast; ring
    have e2 : s + ((2 * k + gammaShift χ + 1 : ℕ) : ℂ)
        = s + 1 + ((2 * k + gammaShift χ : ℕ) : ℂ) := by push_cast; ring
    rw [e1, e2]
    ring
  rw [hfun, show Gfun χ (s + 1) - Gfun χ 3
      = (Gfun χ (s + 1) - Gfun χ 2) - (Gfun χ 3 - Gfun χ 2) by ring]
  exact h

theorem llsGain_hasSum_perronI_gamma {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun k : ℕ => perronI (fun s => 1 / (2 + ((2 * k + gammaShift χ + 1 : ℕ) : ℂ))
        - 1 / (s + ((2 * k + gammaShift χ + 1 : ℕ) : ℂ))) x)
      (perronI (fun s => Gfun χ (s + 1) - Gfun χ 3) x) := by
  have hx0 : 0 < x := by linarith
  set m : ℕ → ℕ := fun k => 2 * k + gammaShift χ + 1 with hm
  have hmk : ∀ k, 2 * k ≤ m k := fun k => by simp only [hm]; omega
  set T : ℕ → ℝ → ℂ := fun k y => ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
    ((1 / (2 + ((m k : ℕ) : ℂ)) - 1 / ((((2 : ℝ) : ℂ) + y * I) + ((m k : ℕ) : ℂ)))
      / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))) with hT
  have hTint : ∀ k, Integrable (T k) := fun k =>
    integrable_mellinInv_integrand (vi_gterm (m k)) (inv_pos.mpr hx0)
  have hTle : ∀ k y, ‖T k y‖ ≤ (x ^ 2 * wk k) * phiG y := by
    intro k y
    simp only [hT]
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hx0)]
    have hre : (-(((2 : ℝ) : ℂ) + y * I)).re = -2 := by simp
    rw [hre, Real.rpow_neg (inv_nonneg.mpr hx0.le), Real.inv_rpow hx0.le, inv_inv,
      Real.rpow_two, div_eq_mul_one_div _ ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1)),
      norm_mul]
    have hg := norm_gterm_le (hmk k) y
    have hK := norm_kernel_le (c := 2) two_pos y
    unfold phiG
    calc x ^ 2 * (‖1 / (2 + ((m k : ℕ) : ℂ)) - 1 / ((((2 : ℝ) : ℂ) + y * I) + ((m k : ℕ) : ℂ))‖
          * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖)
        ≤ x ^ 2 * ((√|y| * wk k) * (1 / ((2 : ℝ) ^ 2 + y ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hg hK (norm_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (wk_nonneg k))) (by positivity)
      _ = x ^ 2 * wk k * (√|y| / ((2 : ℝ) ^ 2 + y ^ 2)) := by ring
  have hTsum : Summable fun k => ∫ y, ‖T k y‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => ?_) ((summable_wk.mul_left (x ^ 2)).mul_right (∫ y, phiG y))
    calc ∫ y, ‖T k y‖ ≤ ∫ y, (x ^ 2 * wk k) * phiG y :=
          integral_mono (hTint k).norm (integrable_phiG.const_mul _) (hTle k)
      _ = x ^ 2 * wk k * ∫ y, phiG y := integral_const_mul _ _
  have hsumI := hasSum_integral_of_summable_integral_norm hTint hTsum
  have hpt : ∀ y : ℝ, ∑' k, T k y = ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
      ((Gfun χ (((2 : ℝ) : ℂ) + y * I + 1) - Gfun χ 3)
        / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))) := by
    intro y
    have hre : 0 < (((2 : ℝ) : ℂ) + y * I).re := by simp
    have h := ((llsGain_hasSum_Gfun_shift χ hre).div_const
      ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))).mul_left
      (((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)))
    exact h.tsum_eq
  rw [integral_congr_ae (Eventually.of_forall hpt)] at hsumI
  have h2 := hsumI.const_smul (1 / (2 * Real.pi))
  exact h2

theorem llsGain_continuous_Gfun_line {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Continuous fun y : ℝ => Gfun χ (((2 : ℝ) : ℂ) + y * I + 1) := by
  have hre : ∀ y : ℝ, 0 < (((2 : ℝ) : ℂ) + y * I + 1).re := fun y => by
    rw [llsGain_line_re]; norm_num
  have e : (fun y : ℝ => Gfun χ (((2 : ℝ) : ℂ) + y * I + 1)) = fun y : ℝ =>
      -(Real.log Real.pi : ℂ) / 2
        + digamma ((((2 : ℝ) : ℂ) + y * I + 1 + gammaShift χ) / 2) / 2 :=
    funext fun y => Gfun_eq χ (hre y)
  rw [e]
  have hd : Continuous fun y : ℝ =>
      digamma ((((2 : ℝ) : ℂ) + y * I + 1 + gammaShift χ) / 2) := by
    refine differentiableOn_digamma.continuousOn.comp_continuous (by fun_prop) (fun y => ?_)
    show 0 < ((((2 : ℝ) : ℂ) + y * I + 1 + gammaShift χ) / 2).re
    simp
    positivity
  fun_prop

theorem llsGain_vi_gamma {N : ℕ} (χ : DirichletCharacter ℂ N) :
    VerticalIntegrable (fun s => (Gfun χ (s + 1) - Gfun χ 3) / (s * (s + 1))) 2 := by
  unfold VerticalIntegrable
  have hcont : Continuous fun y : ℝ => (Gfun χ (((2 : ℝ) : ℂ) + y * I + 1) - Gfun χ 3)
      / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1)) := by
    refine Continuous.div ((llsGain_continuous_Gfun_line χ).sub continuous_const) (by fun_prop)
      (fun y => mul_ne_zero (ne_zero_of_re_pos (by simp))
        (ne_zero_of_re_pos (by rw [llsGain_line_re]; norm_num)))
  refine (integrable_phiG.const_mul (∑' k, wk k)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hre : 0 < (((2 : ℝ) : ℂ) + y * I).re := by simp
  have hG := llsGain_hasSum_Gfun_shift χ hre
  have hbd : ‖Gfun χ (((2 : ℝ) : ℂ) + y * I + 1) - Gfun χ 3‖ ≤ √|y| * ∑' k, wk k :=
    hG.norm_le_of_bounded (summable_wk.hasSum.mul_left √|y|)
      (fun k => norm_gterm_le (by omega) y)
  have hK := norm_kernel_le (c := 2) two_pos y
  show ‖(Gfun χ (((2 : ℝ) : ℂ) + y * I + 1) - Gfun χ 3)
      / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ ≤ (∑' k, wk k) * phiG y
  rw [div_eq_mul_one_div, norm_mul]
  unfold phiG
  calc ‖Gfun χ (((2 : ℝ) : ℂ) + y * I + 1) - Gfun χ 3‖
        * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
      ≤ (√|y| * ∑' k, wk k) * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) :=
        mul_le_mul hbd hK (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg wk_nonneg))
    _ = (∑' k, wk k) * (√|y| / ((2 : ℝ) ^ 2 + y ^ 2)) := by ring

/-! ## Step 4: the zero part -/

theorem llsGain_vi_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ1 : χ ≠ 1) :
    VerticalIntegrable
      (fun s => -(deriv (LFunction χ) (s + 1) / LFunction χ (s + 1)) / (s * (s + 1))) 2 := by
  unfold VerticalIntegrable
  have hd : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ1
  have hd' : Differentiable ℂ (deriv (LFunction χ)) := fun z =>
    ((hd.differentiableOn.deriv isOpen_univ) z (mem_univ z)).differentiableAt
      (isOpen_univ.mem_nhds (mem_univ z))
  have hcont : Continuous fun y : ℝ =>
      -(deriv (LFunction χ) (((2 : ℝ) : ℂ) + y * I + 1) / LFunction χ (((2 : ℝ) : ℂ) + y * I + 1))
        / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1)) := by
    refine Continuous.div (Continuous.neg (Continuous.div (hd'.continuous.comp (by fun_prop))
      (hd.continuous.comp (by fun_prop))
      (fun y => LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
        (by rw [llsGain_line_re]; norm_num)))) (by fun_prop)
      (fun y => mul_ne_zero (ne_zero_of_re_pos (by simp))
        (ne_zero_of_re_pos (by rw [llsGain_line_re]; norm_num)))
  refine integrable_of_le_div_sq hcont (c := 2) (M := CL) two_pos fun y => ?_
  beta_reduce
  rw [div_eq_mul_one_div, norm_mul, norm_neg]
  have h1 := norm_logDeriv_LFunction_le χ (s := ((2 : ℝ) : ℂ) + y * I + 1)
    (by rw [llsGain_line_re]; norm_num)
  have hK := norm_kernel_le (c := 2) two_pos y
  calc _ ≤ CL * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) := mul_le_mul h1 hK (norm_nonneg _) CL_nonneg
    _ = CL / ((2 : ℝ) ^ 2 + y ^ 2) := by ring

/-- Norm bound for one zero term (general `w` with `Re w < 1`). -/
theorem llsGain_zterm_bound {CJ : ℝ}
    (hJ : ∀ ρ : ℂ, ρ.re < 1 →
      Integrable (fun y : ℝ => |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
        / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖) ∧
      ∫ y : ℝ, |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
        / ‖(((2 : ℝ) : ℂ) + y * I) - ρ‖ ≤ CJ * (1 + |ρ.im|) ^ (-(3 / 4 : ℝ)))
    {w : ℂ} (hw : w.re < 1) (n : ℕ) {x : ℝ} (hx0 : 0 < x) :
    ∫ y : ℝ, ‖((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) • ((n : ℂ)
        * (1 / ((((2 : ℝ) : ℂ) + y * I) - w) - 1 / (2 - w))
        / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1)))‖
      ≤ (2 * x ^ 2 * CJ) * ((n : ℝ) * (1 + |w.im|) ^ (-(7 / 4 : ℝ))) := by
  obtain ⟨hJi, hJb⟩ := hJ w hw
  set m : ℝ := (n : ℝ) with hm
  set g : ℝ := 1 + |w.im| with hg
  have hgpos : 0 < g := by positivity
  have h2ρ : g / 2 ≤ ‖2 - w‖ := norm_two_sub_ge hw
  have h2ρpos : 0 < ‖2 - w‖ := lt_of_lt_of_le (by positivity) h2ρ
  have hpt' : ∀ y : ℝ, ‖((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) • ((n : ℂ)
        * (1 / ((((2 : ℝ) : ℂ) + y * I) - w) - 1 / (2 - w))
        / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1)))‖
      = (x ^ 2 * m / ‖2 - w‖) * (|y|
      * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
      / ‖(((2 : ℝ) : ℂ) + y * I) - w‖) := by
    intro y
    have hsρ : (((2 : ℝ) : ℂ) + y * I) - w ≠ 0 :=
      ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith)
    have h2 : 2 - w ≠ 0 := norm_pos_iff.mp h2ρpos
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hx0)]
    have hre : (-(((2 : ℝ) : ℂ) + y * I)).re = -2 := by simp
    rw [hre, Real.rpow_neg (inv_nonneg.mpr hx0.le), Real.inv_rpow hx0.le, inv_inv,
      Real.rpow_two]
    have hid : (n : ℂ) * (1 / ((((2 : ℝ) : ℂ) + y * I) - w) - 1 / (2 - w))
        / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))
        = (n : ℂ) * (-(y * I)) / (((((2 : ℝ) : ℂ) + y * I) - w) * (2 - w))
          * (1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))) := by
      field_simp
      push_cast
      ring
    have hsn : 0 < ‖(((2 : ℝ) : ℂ) + y * I) - w‖ := norm_pos_iff.mpr hsρ
    rw [hid, norm_mul, norm_div, norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs, ← hm]
    field_simp
  rw [integral_congr_ae (Eventually.of_forall hpt'), integral_const_mul]
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hint0 : 0 ≤ ∫ y : ℝ, |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I)
      * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ / ‖(((2 : ℝ) : ℂ) + y * I) - w‖ :=
    integral_nonneg fun y => by positivity
  have hcoef : x ^ 2 * m / ‖2 - w‖ ≤ x ^ 2 * m * (2 / g) := by
    rw [div_le_iff₀ h2ρpos]
    calc x ^ 2 * m = x ^ 2 * m * (2 / g) * (g / 2) := by field_simp
      _ ≤ x ^ 2 * m * (2 / g) * ‖2 - w‖ :=
        mul_le_mul_of_nonneg_left h2ρ (by positivity)
  have hgexp : (1 / g) * g ^ (-(3 / 4 : ℝ)) = g ^ (-(7 / 4 : ℝ)) := by
    rw [show (-(7 / 4 : ℝ)) = -1 + -(3 / 4) by norm_num, Real.rpow_add hgpos, Real.rpow_neg_one,
      one_div]
  calc x ^ 2 * m / ‖2 - w‖ * ∫ y : ℝ, |y| * ‖1 / ((((2 : ℝ) : ℂ) + y * I)
        * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ / ‖(((2 : ℝ) : ℂ) + y * I) - w‖
      ≤ x ^ 2 * m * (2 / g) * (CJ * g ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul hcoef hJb hint0 (by positivity)
    _ = 2 * x ^ 2 * CJ * (m * ((1 / g) * g ^ (-(3 / 4 : ℝ)))) := by ring
    _ = 2 * x ^ 2 * CJ * (m * g ^ (-(7 / 4 : ℝ))) := by rw [hgexp]

theorem llsGain_perronI_Z {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {x : ℝ} (hx : 1 ≤ x) :
    perronI (llsGain_Z χ) x = ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ)
      * perronI (fun s => 1 / (s - (ρ - 1)) - 1 / (2 - (ρ - 1))) x := by
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
  have hw1 : ∀ ρ : Sρ, ((ρ : ℂ) - 1).re < 1 := fun ρ => by
    have := (hstrip ρ).2
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  set c : ℝ → ℂ := fun y => ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) with hc
  set F : Sρ → ℝ → ℂ := fun ρ y => c y • ((zeroOrd χ (ρ : ℂ) : ℂ)
      * (1 / ((((2 : ℝ) : ℂ) + y * I) - ((ρ : ℂ) - 1)) - 1 / (2 - ((ρ : ℂ) - 1)))
      / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))) with hF
  have hsupp : ∀ s : ℂ, Function.support (fun ρ : ℂ => (zeroOrd χ ρ : ℂ)
      * (1 / (s - (ρ - 1)) - 1 / (2 - (ρ - 1)))) ⊆ Sρ := by
    intro s ρ hρ
    apply hmem
    intro h0
    apply hρ
    simp [h0]
  have hpt : ∀ y : ℝ, c y • (fun s => llsGain_Z χ s / (s * (s + 1))) (((2 : ℝ) : ℂ) + y * I)
      = ∑' ρ : Sρ, F ρ y := by
    intro y
    simp only [hF, llsGain_Z]
    rw [← tsum_subtype_eq_of_support_subset (hsupp _), smul_eq_mul, ← tsum_div_const,
      ← tsum_mul_left]
    rfl
  have hFint : ∀ ρ : Sρ, Integrable (F ρ) := fun ρ =>
    integrable_mellinInv_integrand (vi_zero_term (by linarith [hw1 ρ])
      (zeroOrd χ (ρ : ℂ) : ℂ)) (inv_pos.mpr hx0)
  have hFnorm : ∀ ρ : Sρ, ∫ y, ‖F ρ y‖
      ≤ (2 * x ^ 2 * CJ) * ((zeroOrd χ (ρ : ℂ) : ℝ) * (1 + |(ρ : ℂ).im|) ^ (-(7 / 4 : ℝ))) := by
    intro ρ
    have h := llsGain_zterm_bound hJ (hw1 ρ) (zeroOrd χ (ρ : ℂ)) hx0
    have him : ((ρ : ℂ) - 1).im = (ρ : ℂ).im := by simp
    rw [him] at h
    exact h
  have hFsum : Summable fun ρ : Sρ => ∫ y, ‖F ρ y‖ :=
    Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun y => norm_nonneg _) hFnorm
      ((hWs.subtype Sρ).mul_left _)
  have hsum := hasSum_integral_of_summable_integral_norm hFint hFsum
  rw [integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)] at hsum
  have h2 := hsum.const_smul (1 / (2 * Real.pi))
  have e1 : ∀ ρ : Sρ, (1 / (2 * Real.pi)) • ∫ y, F ρ y = (zeroOrd χ (ρ : ℂ) : ℂ)
      * perronI (fun s => 1 / (s - ((ρ : ℂ) - 1)) - 1 / (2 - ((ρ : ℂ) - 1))) x := by
    intro ρ
    have : (1 / (2 * Real.pi)) • ∫ y, F ρ y
        = perronI (fun s => (zeroOrd χ (ρ : ℂ) : ℂ)
          * (1 / (s - ((ρ : ℂ) - 1)) - 1 / (2 - ((ρ : ℂ) - 1)))) x := rfl
    rw [this, perronI_const_mul_fun]
  simp only [e1] at h2
  have e2 : (1 / (2 * Real.pi)) • ∫ y : ℝ, c y • (fun s => llsGain_Z χ s / (s * (s + 1)))
      (((2 : ℝ) : ℂ) + y * I) = perronI (llsGain_Z χ) x := rfl
  rw [e2] at h2
  rw [← h2.tsum_eq]
  refine tsum_subtype_eq_of_support_subset
    (f := fun ρ : ℂ => (zeroOrd χ ρ : ℂ)
      * perronI (fun s => 1 / (s - (ρ - 1)) - 1 / (2 - (ρ - 1))) x) (s := Sρ) ?_
  intro ρ hρ
  apply hmem
  intro h0
  apply hρ
  simp [h0]

/-! ## Step 5: the explicit formula -/

theorem llsGain_formula {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (hH : HadamardLogDeriv χ) (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2)
    {x : ℝ} (hx : 1 ≤ x) :
    weightedLogSum χ x
      = -(deriv (LFunction χ) 3 / LFunction χ 3) * (1 - 1 / (x : ℂ))
        + perronI (fun s => Gfun χ (s + 1) - Gfun χ 3) x
        - ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ)
            * perronI (fun s => 1 / (s - (ρ - 1)) - 1 / (2 - (ρ - 1))) x := by
  have hx0 : 0 < x := by linarith
  have hDi := llsGain_vi_gamma χ
  have hgi := llsGain_vi_logDeriv χ hχ1
  have hAi : VerticalIntegrable (fun s => (-(deriv (LFunction χ) 3 / LFunction χ 3)
      + (Gfun χ (s + 1) - Gfun χ 3)) / (s * (s + 1))) 2 := by
    have h := Integrable.add
      (verticalIntegrable_const_kernel (-(deriv (LFunction χ) 3 / LFunction χ 3))) hDi
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have hZi : VerticalIntegrable (fun s => llsGain_Z χ s / (s * (s + 1))) 2 := by
    have h := Integrable.sub hAi hgi
    unfold VerticalIntegrable
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    have hd := llsGain_decomp χ hχ1 hH hS (s := ((2 : ℝ) : ℂ) + y * I) (by simp)
    linear_combination (-(1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1)))) * hd
  have h1 : weightedLogSum χ x = perronI (fun s => (-(deriv (LFunction χ) 3 / LFunction χ 3)
      + (Gfun χ (s + 1) - Gfun χ 3)) - llsGain_Z χ s) x := by
    rw [llsGain_weightedLogSum_eq_perronI χ hx]
    apply perronI_congr_line
    intro y
    exact llsGain_decomp χ hχ1 hH hS (by simp)
  rw [perronI_sub hAi hZi hx0,
    perronI_add (verticalIntegrable_const_kernel _) hDi hx0,
    perronI_const, perronI_one hx, llsGain_perronI_Z χ hχ1 hH hS hx] at h1
  exact h1

end DetPrimality.Bach
