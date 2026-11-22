import DetPrimality.Bach.LLSPerron
import DetPrimality.Bach.ExplicitZeros

/-!
# The Γ-part for the kernel `x^s/s²` (LLS Lemmas 1 and 2)

* `llsPer_lterm m x` : the (real) value of `L[1/(2+m) - 1/(s+m)](x)`:
  `log x / 2 - (log x)²/2` for `m = 0`, and
  `log x/(2+m) - log x/m + 1/m² - x^{-m}/m²` for `m ≥ 1`  (`llsPer_perronL_gterm`);
* `llsPer_hasSum_perronL_gamma` : `L[G - G(2)](x) = ∑_k L[1/(2+m_k) - 1/(s+m_k)](x)`,
  `m_k = 2k + a`;  `llsPer_hasSum_lterm` the same with real values;
* `llsPer_vi_gamma` : `(G(s) - G(2))/s²` is integrable on `Re s = 2`;
* `llsPer_Gfun_two_re` : `Re G(2)` in the two parities;
* `llsPer_gamma_bound` : `Re G(2) · log x + Re L[G - G(2)](x) ≤ -(log π / 2) log x` for `x ≥ 3`
  (this is `Ẽ_a(x) ≤ 0` of LLS Lemma 2).
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

/-- Value of `L[1/(2+m) - 1/(s+m)](x)` (real). -/
noncomputable def llsPer_lterm (m : ℕ) (x : ℝ) : ℝ :=
  if m = 0 then Real.log x / 2 - Real.log x ^ 2 / 2
  else Real.log x / (2 + m) - Real.log x / m + 1 / (m : ℝ) ^ 2 - x ^ (-(m : ℝ)) / (m : ℝ) ^ 2

theorem llsPer_vi_gterm (m : ℕ) :
    VerticalIntegrable (fun s : ℂ => (1 / (2 + (m : ℂ)) - 1 / (s + m)) / s ^ 2) 2 := by
  have hw : (-(m : ℂ)).re < 2 := by
    simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h := Integrable.sub (llsPer_vi_const (1 / (2 + (m : ℂ)))) (llsPer_vi_inv_sub hw)
  unfold VerticalIntegrable
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply, sub_neg_eq_add, sub_div]

theorem llsPer_perronL_gterm (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    llsPer_perronL (fun s => 1 / (2 + (m : ℂ)) - 1 / (s + m)) x = (llsPer_lterm m x : ℂ) := by
  have hx0 : 0 < x := by linarith
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero, add_zero]
    rw [llsPer_perronL_sub (llsPer_vi_const _) llsPer_vi_inv_self hx0, llsPer_perronL_const,
      llsPer_perronL_one hx, llsPer_perronL_inv_self hx, llsPer_lterm, if_pos rfl]
    push_cast
    ring
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hw : (-(m : ℂ)).re < 2 := by simp; linarith
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hw0 : -(m : ℂ) ≠ 0 := neg_ne_zero.mpr hm0
    have hm2 : (2 : ℂ) + m ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have e : (fun s : ℂ => 1 / (2 + (m : ℂ)) - 1 / (s + m))
        = fun s => 1 / (2 + (m : ℂ)) - 1 / (s - -(m : ℂ)) := by
      funext s; rw [sub_neg_eq_add]
    have hc : (x : ℂ) ^ (-(m : ℂ)) = ((x ^ (-(m : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]; push_cast; rfl
    rw [e, llsPer_perronL_sub (llsPer_vi_const _) (llsPer_vi_inv_sub hw) hx0,
      llsPer_perronL_const, llsPer_perronL_one hx, llsPer_perronL_inv_sub hw hw0 hx, hc,
      llsPer_lterm, if_neg hm.ne']
    push_cast
    field_simp
    ring

/-! ### Interchange of `∑_k` and `∫` -/

theorem llsPer_hasSum_perronL_gamma {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 1 ≤ x) :
    HasSum (fun k : ℕ => llsPer_perronL (fun s => 1 / (2 + ((2 * k + gammaShift χ : ℕ) : ℂ))
        - 1 / (s + ((2 * k + gammaShift χ : ℕ) : ℂ))) x)
      (llsPer_perronL (fun s => Gfun χ s - Gfun χ 2) x) := by
  have hx0 : 0 < x := by linarith
  set m : ℕ → ℕ := fun k => 2 * k + gammaShift χ with hm
  have hmk : ∀ k, 2 * k ≤ m k := fun k => by simp [hm]
  set T : ℕ → ℝ → ℂ := fun k y => ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
    ((1 / (2 + ((m k : ℕ) : ℂ)) - 1 / ((((2 : ℝ) : ℂ) + y * I) + ((m k : ℕ) : ℂ)))
      / (((2 : ℝ) : ℂ) + y * I) ^ 2) with hT
  have hTint : ∀ k, Integrable (T k) := fun k =>
    integrable_mellinInv_integrand (llsPer_vi_gterm (m k)) (inv_pos.mpr hx0)
  have hTle : ∀ k y, ‖T k y‖ ≤ (x ^ 2 * wk k) * phiG y := by
    intro k y
    simp only [hT]
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hx0)]
    have hre : (-(((2 : ℝ) : ℂ) + y * I)).re = -2 := by simp
    rw [hre, Real.rpow_neg (inv_nonneg.mpr hx0.le), Real.inv_rpow hx0.le, inv_inv,
      Real.rpow_two, div_eq_mul_one_div _ ((((2 : ℝ) : ℂ) + y * I) ^ 2), norm_mul,
      llsPer_norm_kernel]
    have hg := norm_gterm_le (hmk k) y
    unfold phiG
    calc x ^ 2 * (‖1 / (2 + ((m k : ℕ) : ℂ)) - 1 / ((((2 : ℝ) : ℂ) + y * I) + ((m k : ℕ) : ℂ))‖
          * (1 / ((2 : ℝ) ^ 2 + y ^ 2)))
        ≤ x ^ 2 * ((√|y| * wk k) * (1 / ((2 : ℝ) ^ 2 + y ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg (by positivity))
            (by positivity)
      _ = x ^ 2 * wk k * (√|y| / ((2 : ℝ) ^ 2 + y ^ 2)) := by ring
  have hTsum : Summable fun k => ∫ y, ‖T k y‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => ?_) ((summable_wk.mul_left (x ^ 2)).mul_right (∫ y, phiG y))
    calc ∫ y, ‖T k y‖ ≤ ∫ y, (x ^ 2 * wk k) * phiG y :=
          integral_mono (hTint k).norm (integrable_phiG.const_mul _) (hTle k)
      _ = x ^ 2 * wk k * ∫ y, phiG y := integral_const_mul _ _
  have hsumI := hasSum_integral_of_summable_integral_norm hTint hTsum
  have hpt : ∀ y : ℝ, ∑' k, T k y = ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
      ((Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2) / (((2 : ℝ) : ℂ) + y * I) ^ 2) := by
    intro y
    have hre : 0 < (((2 : ℝ) : ℂ) + y * I).re := by simp
    have h := ((hasSum_Gfun_sub χ hre).div_const
      ((((2 : ℝ) : ℂ) + y * I) ^ 2)).mul_left
      (((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)))
    exact h.tsum_eq
  rw [integral_congr_ae (Eventually.of_forall hpt)] at hsumI
  have h2 := hsumI.const_smul (1 / (2 * Real.pi))
  exact h2

/-- The Γ-part as a real series. -/
theorem llsPer_hasSum_lterm {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun k : ℕ => llsPer_lterm (2 * k + gammaShift χ) x)
      (llsPer_perronL (fun s => Gfun χ s - Gfun χ 2) x).re := by
  have hS := llsPer_hasSum_perronL_gamma χ hx
  simp only [llsPer_perronL_gterm _ hx] at hS
  have hR := Complex.hasSum_re hS
  simpa only [Complex.ofReal_re] using hR

/-! ### Integrability of the Γ-part -/

theorem llsPer_vi_gamma {N : ℕ} (χ : DirichletCharacter ℂ N) :
    VerticalIntegrable (fun s => (Gfun χ s - Gfun χ 2) / s ^ 2) 2 := by
  unfold VerticalIntegrable
  have hcont : Continuous fun y : ℝ => (Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2)
      / (((2 : ℝ) : ℂ) + y * I) ^ 2 := by
    refine Continuous.div ((continuous_Gfun_line χ).sub continuous_const) (by fun_prop)
      (fun y => pow_ne_zero 2 (llsPer_line_ne y))
  refine (integrable_phiG.const_mul (∑' k, wk k)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hbd := norm_Gfun_sub_le χ y
  show ‖(Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2) / (((2 : ℝ) : ℂ) + y * I) ^ 2‖
    ≤ (∑' k, wk k) * phiG y
  rw [div_eq_mul_one_div, norm_mul, llsPer_norm_kernel]
  unfold phiG
  calc ‖Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2‖ * (1 / ((2 : ℝ) ^ 2 + y ^ 2))
      ≤ (√|y| * ∑' k, wk k) * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) :=
        mul_le_mul_of_nonneg_right hbd (by positivity)
    _ = (∑' k, wk k) * (√|y| / ((2 : ℝ) ^ 2 + y ^ 2)) := by ring

/-! ### `Re G(2)` -/

theorem llsPer_Gfun_two_re {N : ℕ} (χ : DirichletCharacter ℂ N) :
    (gammaShift χ = 0 ∧ (Gfun χ 2).re
        = -(Real.log Real.pi) / 2 - Real.eulerMascheroniConstant / 2) ∨
    (gammaShift χ = 1 ∧ (Gfun χ 2).re
        = -(Real.log Real.pi) / 2 - Real.log 2 - Real.eulerMascheroniConstant / 2 + 1) := by
  have h2 : (0 : ℝ) < (2 : ℂ).re := by norm_num
  rcases gammaShift_cases χ with h | h
  · left
    refine ⟨h, ?_⟩
    rw [Gfun_eq χ h2, h]
    simp only [Nat.cast_zero, add_zero]
    rw [show (2 : ℂ) / 2 = 1 by norm_num, digamma_one]
    have e : (-(Real.log Real.pi : ℂ) / 2 + -(Real.eulerMascheroniConstant : ℂ) / 2)
        = ((-(Real.log Real.pi) / 2 - Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re]
  · right
    refine ⟨h, ?_⟩
    have hhalf : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -m := fun m h => by
      have h1 := congrArg Complex.re h
      have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      norm_num at h1
      linarith
    have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; norm_num
    rw [Gfun_eq χ h2, h]
    simp only [Nat.cast_one]
    rw [show ((2 : ℂ) + 1) / 2 = 1 / 2 + 1 by norm_num, digamma_apply_add_one _ hhalf,
      digamma_one_half, hlog]
    have e : (-(Real.log Real.pi : ℂ) / 2
        + (-2 * (Real.log 2 : ℂ) - (Real.eulerMascheroniConstant : ℂ) + (1 / 2 : ℂ)⁻¹) / 2)
        = ((-(Real.log Real.pi) / 2 - Real.log 2 - Real.eulerMascheroniConstant / 2 + 1 : ℝ) : ℂ)
        := by
      push_cast; ring
    rw [e, Complex.ofReal_re]

/-! ### Series values -/

theorem llsPer_hasSum_inv_succ_sq :
    HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := hasSum_zeta_two
  have hs : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    have h1 : Summable (fun j : ℕ => (1 : ℝ) / (((j + 1 : ℕ) : ℝ)) ^ 2) :=
      (summable_nat_add_iff 1).mpr h.summable
    refine h1.congr fun j => ?_
    rw [Nat.cast_add, Nat.cast_one]
  have e : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2
      = 1 / ((0 : ℕ) : ℝ) ^ 2 + ∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2 :=
    h.summable.tsum_eq_zero_add
  rw [h.tsum_eq] at e
  have e0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ 2 = 0 := by norm_num
  rw [e0, zero_add] at e
  have e2 : ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 6 := by
    rw [e]
    exact tsum_congr fun j => by rw [Nat.cast_add, Nat.cast_one]
  rw [← e2]
  exact hs.hasSum

theorem llsPer_hasSum_inv_odd_sq :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 8) := by
  have h := hasSum_zeta_two
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have he : Summable fun k => f (2 * k) :=
    h.summable.comp_injective (fun a b hab => by
      have : 2 * a = 2 * b := hab
      omega)
  have ho : Summable fun k => f (2 * k + 1) :=
    h.summable.comp_injective (fun a b hab => by
      have : 2 * a + 1 = 2 * b + 1 := hab
      omega)
  have e := tsum_even_add_odd he ho
  have e1 : ∑' k, f (2 * k) = 1 / 4 * ∑' k, f k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by simp only [hf]; push_cast; ring
  rw [e1, h.tsum_eq] at e
  have e3 : ∑' k, f (2 * k + 1) = Real.pi ^ 2 / 8 := by linarith
  have e2 : ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 8 := by
    rw [← e3]
    exact tsum_congr fun k => by simp only [hf]; push_cast; ring
  have hs : Summable fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2 :=
    ho.congr fun k => by simp only [hf]; push_cast; ring
  rw [← e2]
  exact hs.hasSum

theorem llsPer_hasSum_odd_telescope :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 3)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by
    have : 1 / (2 * (k : ℝ) + 3) ≤ 1 / (2 * (k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith)]
  have hps : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 3))
      = 1 - 1 / (2 * (n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring
  rw [show (fun n : ℕ => ∑ k ∈ Finset.range n, (1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 3)))
      = fun n : ℕ => 1 - 1 / (2 * (n : ℝ) + 1) from funext hps]
  have h0 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ) + 1)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact one_div_le_one_div_of_le (by positivity)
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  rw [sub_zero] at h
  exact h

/-! ### The bound `Ẽ_a(x) ≤ 0` -/

theorem llsPer_lterm_le {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) :
    llsPer_lterm m x ≤ Real.log x / (2 + m) - Real.log x / m + 1 / (m : ℝ) ^ 2 := by
  rw [llsPer_lterm, if_neg (by omega)]
  have : 0 ≤ x ^ (-(m : ℝ)) / (m : ℝ) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hx.le _) (by positivity)
  linarith

theorem llsPer_lterm_one (x : ℝ) :
    llsPer_lterm 1 x = Real.log x / 3 - Real.log x + 1 - 1 / x := by
  rw [llsPer_lterm, if_neg one_ne_zero]
  have : x ^ (-((1 : ℕ) : ℝ)) = 1 / x := by
    rw [Nat.cast_one, Real.rpow_neg_one, one_div]
  rw [this]
  push_cast
  ring

/-- **`Ẽ_a(x) ≤ 0`** (LLS Lemma 2): for `x ≥ 3`,
`Re G(2) · log x + Re L[G - G(2)](x) ≤ -(log π / 2) · log x`. -/
theorem llsPer_gamma_bound {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 3 ≤ x) :
    (Gfun χ 2).re * Real.log x + (llsPer_perronL (fun s => Gfun χ s - Gfun χ 2) x).re
      ≤ -(Real.log Real.pi / 2) * Real.log x := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hR := llsPer_hasSum_lterm χ hx1
  rw [← hR.tsum_eq, hR.summable.tsum_eq_zero_add]
  have htail : Summable fun j : ℕ => llsPer_lterm (2 * (j + 1) + gammaShift χ) x :=
    (summable_nat_add_iff (f := fun k : ℕ => llsPer_lterm (2 * k + gammaShift χ) x) 1).mpr
      hR.summable
  have hL3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl3 := Real.log_three_gt_d9
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hpi2 : Real.pi ^ 2 < 9.8697 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hL4 : 4 ≤ x → 2 * Real.log 2 ≤ Real.log x := fun h => by
    have := Real.log_le_log (by norm_num) h
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this
    push_cast at this
    linarith
  set L := Real.log x with hLdef
  have hL1 : 1.0986 ≤ L := by linarith
  rcases llsPer_Gfun_two_re χ with ⟨ha, hG⟩ | ⟨ha, hG⟩
  · -- even characters
    simp only [ha, add_zero, mul_zero] at htail ⊢
    have hcs : HasSum (fun j : ℕ => -(L / 2) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
        + 1 / 4 * (1 / ((j : ℝ) + 1) ^ 2)) (-(L / 2) * 1 + 1 / 4 * (Real.pi ^ 2 / 6)) :=
      (hasSum_telescope.mul_left _).add (llsPer_hasSum_inv_succ_sq.mul_left _)
    have hle : ∀ j : ℕ, llsPer_lterm (2 * (j + 1)) x
        ≤ -(L / 2) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
          + 1 / 4 * (1 / ((j : ℝ) + 1) ^ 2) := by
      intro j
      have h := llsPer_lterm_le (m := 2 * (j + 1)) (by omega) hx0
      rw [← hLdef] at h
      refine h.trans (le_of_eq ?_)
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      field_simp
      ring
    have hT := htail.tsum_le_tsum hle hcs.summable
    rw [hcs.tsum_eq] at hT
    have h0 : llsPer_lterm 0 x = L / 2 - L ^ 2 / 2 := by
      rw [llsPer_lterm, if_pos rfl]
    rw [h0, hG]
    generalize ∑' j : ℕ, llsPer_lterm (2 * (j + 1)) x = T at hT
    have hγL : 0 ≤ Real.eulerMascheroniConstant * L := mul_nonneg (by linarith) (by linarith)
    have hLL : (1.0986 : ℝ) * 1.0986 ≤ L * L := mul_le_mul hL1 hL1 (by norm_num) (by linarith)
    linarith
  · -- odd characters
    simp only [ha, mul_zero, zero_add] at htail ⊢
    have hcs : HasSum (fun j : ℕ => -L * (1 / (2 * ((j + 1 : ℕ) : ℝ) + 1)
          - 1 / (2 * ((j + 1 : ℕ) : ℝ) + 3))
        + 1 / (2 * ((j + 1 : ℕ) : ℝ) + 1) ^ 2)
        (-L * (1 - (1 / (2 * ((0 : ℕ) : ℝ) + 1) - 1 / (2 * ((0 : ℕ) : ℝ) + 3)))
          + (Real.pi ^ 2 / 8 - 1 / (2 * ((0 : ℕ) : ℝ) + 1) ^ 2)) := by
      have h1 := (hasSum_nat_add_iff' 1).mpr llsPer_hasSum_odd_telescope
      have h2 := (hasSum_nat_add_iff' 1).mpr llsPer_hasSum_inv_odd_sq
      simp only [Finset.range_one, Finset.sum_singleton] at h1 h2
      exact (h1.mul_left _).add h2
    have hle : ∀ j : ℕ, llsPer_lterm (2 * (j + 1) + 1) x
        ≤ -L * (1 / (2 * ((j + 1 : ℕ) : ℝ) + 1) - 1 / (2 * ((j + 1 : ℕ) : ℝ) + 3))
          + 1 / (2 * ((j + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      intro j
      have h := llsPer_lterm_le (m := 2 * (j + 1) + 1) (by omega) hx0
      rw [← hLdef] at h
      refine h.trans (le_of_eq ?_)
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      field_simp
      ring
    have hT := htail.tsum_le_tsum hle hcs.summable
    rw [hcs.tsum_eq] at hT
    have h0 : llsPer_lterm 1 x = L / 3 - L + 1 - 1 / x := by
      rw [llsPer_lterm_one x]
    rw [h0, hG]
    generalize ∑' j : ℕ, llsPer_lterm (2 * (j + 1) + 1) x = T at hT
    norm_num at hT
    have hl2 := Real.log_two_gt_d9
    have hc : 0.9431 ≤ Real.log 2 + Real.eulerMascheroniConstant / 2 := by linarith
    rcases le_total x 4 with h4 | h4
    · have hx4 : 1 / 4 ≤ 1 / x := one_div_le_one_div_of_le hx0 h4
      have hprod := mul_le_mul hc hL1 (by norm_num) (by linarith)
      linarith
    · have hL4' := hL4 h4
      have hxi : 0 ≤ 1 / x := by positivity
      have hprod := mul_le_mul hc (show (1.386 : ℝ) ≤ L by linarith) (by norm_num)
        (by linarith)
      linarith

end DetPrimality.Bach
