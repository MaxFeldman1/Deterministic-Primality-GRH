import DetPrimality.Bach.ExplicitFormula
import DetPrimality.Bach.ExplicitPerronLog

/-!
# The Γ-part of the explicit formula (blueprint §3, Step 4) — fully proved

`gamma_part`: `I_Γ(x) := I[G - G(2)](x)` satisfies `|I_Γ(x)| ≤ log x + 4` for `x ≥ 1`
(in fact `≤ log x + 3`), and `(G - G(2))/(s(s+1))` is integrable on `Re s = 2`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

/-! ### Double poles -/

theorem perronI_inv_self {x : ℝ} (hx : 1 ≤ x) :
    perronI (fun s => 1 / s) x = (Real.log x : ℂ) - 1 + 1 / (x : ℂ) := by
  have hx0 : 0 < x := by linarith
  unfold perronI
  rw [show (fun s : ℂ => 1 / s / (s * (s + 1))) = fun s => 1 / (s ^ 2 * (s + 1)) by
    funext s; rw [div_div]; ring]
  rw [mellinInv_kernel_sq two_pos (inv_pos.mpr hx0), if_pos (inv_le_one_of_one_le₀ hx),
    Real.log_inv]
  push_cast
  ring

theorem perronI_inv_add_one {x : ℝ} (hx : 1 ≤ x) :
    perronI (fun s => 1 / (s + 1)) x = 1 - ((Real.log x : ℂ) + 1) / (x : ℂ) := by
  have hx0 : 0 < x := by linarith
  unfold perronI
  rw [show (fun s : ℂ => 1 / (s + 1) / (s * (s + 1))) = fun s => 1 / (s * (s + 1) ^ 2) by
    funext s; rw [div_div]; ring]
  rw [mellinInv_kernel_add_one_sq two_pos (inv_pos.mpr hx0), if_pos (inv_le_one_of_one_le₀ hx),
    Real.log_inv]
  push_cast
  ring

theorem vi_inv_self : VerticalIntegrable (fun s : ℂ => 1 / s / (s * (s + 1))) 2 := by
  refine VerticalIntegrable.congr_line ?_ (verticalIntegrable_kernel_sq (c := 2) two_pos)
  intro y
  simp only [div_div]
  ring

theorem vi_inv_add_one : VerticalIntegrable (fun s : ℂ => 1 / (s + 1) / (s * (s + 1))) 2 := by
  refine VerticalIntegrable.congr_line ?_ (verticalIntegrable_kernel_add_one_sq (c := 2) two_pos)
  intro y
  simp only [div_div]
  ring

/-! ### The individual trivial-zero terms -/

/-- Value of `I[1/(2+m) - 1/(s+m)](x)` (real). -/
noncomputable def rterm (m : ℕ) (x : ℝ) : ℝ :=
  if m = 0 then 3 / 2 - Real.log x - 3 / (2 * x)
  else if m = 1 then -2 / 3 + Real.log x / x + 2 / (3 * x)
  else -2 / (m * (m + 2)) + 3 / ((m - 1) * (m + 2) * x) - x ^ (-(m : ℝ)) / (m * (m - 1))

theorem rterm_zero (x : ℝ) : rterm 0 x = 3 / 2 - Real.log x - 3 / (2 * x) := by
  simp [rterm]

theorem rterm_one (x : ℝ) : rterm 1 x = -2 / 3 + Real.log x / x + 2 / (3 * x) := by
  simp [rterm]

theorem rterm_of_two_le {m : ℕ} (hm : 2 ≤ m) (x : ℝ) : rterm m x
    = -2 / (m * (m + 2)) + 3 / ((m - 1) * (m + 2) * x) - x ^ (-(m : ℝ)) / (m * (m - 1)) := by
  rw [rterm, if_neg (by omega), if_neg (by omega)]

theorem vi_gterm (m : ℕ) :
    VerticalIntegrable (fun s : ℂ => (1 / (2 + (m : ℂ)) - 1 / (s + m)) / (s * (s + 1))) 2 := by
  have hw : (-(m : ℂ)).re < 2 := by
    simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h := Integrable.sub (verticalIntegrable_const_kernel (1 / (2 + (m : ℂ))))
    (verticalIntegrable_inv_sub hw)
  unfold VerticalIntegrable
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply, sub_neg_eq_add, sub_div]

theorem perronI_gterm (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    perronI (fun s => 1 / (2 + (m : ℂ)) - 1 / (s + m)) x = (rterm m x : ℂ) := by
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [rterm_zero]
      simp only [Nat.cast_zero, add_zero]
      rw [perronI_sub (verticalIntegrable_const_kernel _) vi_inv_self hx0, perronI_const,
        perronI_one hx, perronI_inv_self hx]
      push_cast
      field_simp
      ring
    · rw [rterm_one]
      simp only [Nat.cast_one]
      rw [perronI_sub (verticalIntegrable_const_kernel _) vi_inv_add_one hx0, perronI_const,
        perronI_one hx, perronI_inv_add_one hx]
      push_cast
      field_simp
      ring
  · rw [perronI_trivTerm hm hx, rterm_of_two_le hm]
    have hc : (x : ℂ) ^ (-(m : ℂ)) = ((x ^ (-(m : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]; push_cast; rfl
    rw [hc]
    push_cast
    ring

/-! ### Domination -/

theorem rpow_three_halves {u : ℝ} (hu : 0 < u) : u ^ (3 / 2 : ℝ) = u * √u := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hu, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- The weights `w_k = (k+1)^{-3/2}`. -/
noncomputable def wk (k : ℕ) : ℝ := 1 / (((k : ℝ) + 1) * √((k : ℝ) + 1))

theorem wk_nonneg (k : ℕ) : 0 ≤ wk k := by unfold wk; positivity

theorem summable_wk : Summable wk := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2))
  refine h.congr (fun k => ?_)
  unfold wk
  push_cast
  rw [rpow_three_halves (by positivity)]

/-- `φ(y) = √|y| / (4 + y²)`. -/
noncomputable def phiG (y : ℝ) : ℝ := √|y| / ((2 : ℝ) ^ 2 + y ^ 2)

theorem integrable_phiG : Integrable phiG := by
  have hI : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(3 / 2 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  have hc : Continuous phiG :=
    Continuous.div (Real.continuous_sqrt.comp continuous_abs) (by fun_prop)
      (fun y => by positivity)
  refine (hI.const_mul 2).mono' hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hu : 0 < 1 + ‖y‖ := by positivity
  rw [Real.norm_of_nonneg (by unfold phiG; positivity), Real.rpow_neg hu.le,
    rpow_three_halves hu, Real.norm_eq_abs]
  unfold phiG
  have hsq : √|y| ≤ √(1 + |y|) := Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 < √(1 + |y|) := Real.sqrt_pos.mpr (by positivity)
  have hss : √(1 + |y|) * √(1 + |y|) = 1 + |y| := Real.mul_self_sqrt (by positivity)
  have key : √|y| * ((1 + |y|) * √(1 + |y|)) ≤ (1 + |y|) ^ 2 := by
    calc √|y| * ((1 + |y|) * √(1 + |y|)) ≤ √(1 + |y|) * ((1 + |y|) * √(1 + |y|)) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = (1 + |y|) * (√(1 + |y|) * √(1 + |y|)) := by ring
      _ = (1 + |y|) ^ 2 := by rw [hss]; ring
  have h2 : (1 + |y|) ^ 2 ≤ 2 * ((2 : ℝ) ^ 2 + y ^ 2) := by
    nlinarith [sq_abs y, abs_nonneg y, sq_nonneg (|y| - 1)]
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [key, h2]

theorem sqrt_aux {y M N K : ℝ} (hK : 0 < K) (hKM : K ≤ M) (hN : 0 < N)
    (hyMN : |y| * M ≤ N ^ 2) : |y| / (M * N) ≤ √|y| * (1 / (K * √K)) := by
  have hM : 0 < M := lt_of_lt_of_le hK hKM
  have h1 : √|y| * √M ≤ N := by
    rw [← Real.sqrt_mul (abs_nonneg y)]
    calc √(|y| * M) ≤ √(N ^ 2) := Real.sqrt_le_sqrt hyMN
      _ = N := Real.sqrt_sq hN.le
  have h2 : |y| * √M ≤ √|y| * N := by
    calc |y| * √M = √|y| * (√|y| * √M) := by
          rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg y)]
      _ ≤ √|y| * N := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
  have hsK : 0 < √K := Real.sqrt_pos.mpr hK
  have hsKM : √K ≤ √M := Real.sqrt_le_sqrt hKM
  have hsM : 0 < √M := Real.sqrt_pos.mpr hM
  calc |y| / (M * N) ≤ √|y| / (M * √M) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc |y| * (M * √M) = M * (|y| * √M) := by ring
          _ ≤ M * (√|y| * N) := mul_le_mul_of_nonneg_left h2 hM.le
          _ = √|y| * (M * N) := by ring
    _ ≤ √|y| / (K * √K) :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
          (mul_le_mul hKM hsKM hsK.le hM.le)
    _ = √|y| * (1 / (K * √K)) := by ring

theorem norm_gterm_le {m k : ℕ} (hmk : 2 * k ≤ m) (y : ℝ) :
    ‖1 / (2 + (m : ℂ)) - 1 / ((((2 : ℝ) : ℂ) + y * I) + m)‖ ≤ √|y| * wk k := by
  set s : ℂ := ((2 : ℝ) : ℂ) + y * I with hs
  set M : ℝ := 2 + m with hMdef
  have hk : (2 * k : ℝ) ≤ m := by exact_mod_cast hmk
  have hKM : (k : ℝ) + 1 ≤ M := by rw [hMdef]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h2m : (2 : ℂ) + m = ((M : ℝ) : ℂ) := by rw [hMdef]; push_cast; ring
  have hsm : s + m = ((M : ℝ) : ℂ) + y * I := by rw [hs, hMdef]; push_cast; ring
  have hMpos : 0 < M := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hN2 : ‖s + m‖ ^ 2 = M ^ 2 + y ^ 2 := by rw [hsm, normSq_line]
  have hsm0 : s + m ≠ 0 := by rw [hsm]; exact ne_zero_of_re_pos (by rw [line_re]; exact hMpos)
  have h2m0 : (2 : ℂ) + m ≠ 0 := by
    rw [h2m]; exact_mod_cast hMpos.ne'
  have hNpos : 0 < ‖s + m‖ := norm_pos_iff.mpr hsm0
  have hid : 1 / (2 + (m : ℂ)) - 1 / (s + m) = (y * I) / ((2 + (m : ℂ)) * (s + m)) := by
    rw [div_sub_div _ _ h2m0 hsm0, hs]
    push_cast
    ring
  rw [hid, norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, h2m, Complex.norm_real, Real.norm_of_nonneg hMpos.le]
  exact sqrt_aux (by positivity) hKM hNpos
    (by rw [hN2]; nlinarith [sq_abs y, abs_nonneg y, sq_nonneg (M - |y|)])

/-! ### Interchange of `∑_k` and `∫` -/

theorem hasSum_perronI_gamma {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun k : ℕ => perronI (fun s => 1 / (2 + ((2 * k + gammaShift χ : ℕ) : ℂ))
        - 1 / (s + ((2 * k + gammaShift χ : ℕ) : ℂ))) x)
      (perronI (fun s => Gfun χ s - Gfun χ 2) x) := by
  have hx0 : 0 < x := by linarith
  set m : ℕ → ℕ := fun k => 2 * k + gammaShift χ with hm
  have hmk : ∀ k, 2 * k ≤ m k := fun k => by simp [hm]
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
      ((Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2)
        / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))) := by
    intro y
    have hre : 0 < (((2 : ℝ) : ℂ) + y * I).re := by simp
    have h := ((hasSum_Gfun_sub χ hre).div_const
      ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))).mul_left
      (((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)))
    exact h.tsum_eq
  rw [integral_congr_ae (Eventually.of_forall hpt)] at hsumI
  have h2 := hsumI.const_smul (1 / (2 * Real.pi))
  exact h2

/-! ### Integrability of the Γ-part -/

theorem continuous_Gfun_line {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Continuous fun y : ℝ => Gfun χ (((2 : ℝ) : ℂ) + y * I) := by
  have hre : ∀ y : ℝ, 0 < (((2 : ℝ) : ℂ) + y * I).re := fun y => by simp
  have e : (fun y : ℝ => Gfun χ (((2 : ℝ) : ℂ) + y * I)) = fun y : ℝ =>
      -(Real.log Real.pi : ℂ) / 2 + digamma ((((2 : ℝ) : ℂ) + y * I + gammaShift χ) / 2) / 2 :=
    funext fun y => Gfun_eq χ (hre y)
  rw [e]
  have hd : Continuous fun y : ℝ => digamma ((((2 : ℝ) : ℂ) + y * I + gammaShift χ) / 2) := by
    refine differentiableOn_digamma.continuousOn.comp_continuous (by fun_prop) (fun y => ?_)
    show 0 < ((((2 : ℝ) : ℂ) + y * I + gammaShift χ) / 2).re
    simp
    positivity
  fun_prop

theorem vi_gamma {N : ℕ} (χ : DirichletCharacter ℂ N) :
    VerticalIntegrable (fun s => (Gfun χ s - Gfun χ 2) / (s * (s + 1))) 2 := by
  unfold VerticalIntegrable
  have hcont : Continuous fun y : ℝ => (Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2)
      / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1)) := by
    refine Continuous.div ((continuous_Gfun_line χ).sub continuous_const) (by fun_prop)
      (fun y => mul_ne_zero (ne_zero_of_re_pos (by simp))
        (ne_zero_of_re_pos (by simp; norm_num)))
  refine (integrable_phiG.const_mul (∑' k, wk k)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hre : 0 < (((2 : ℝ) : ℂ) + y * I).re := by simp
  have hG := hasSum_Gfun_sub χ hre
  have hbd : ‖Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2‖ ≤ √|y| * ∑' k, wk k :=
    hG.norm_le_of_bounded (summable_wk.hasSum.mul_left √|y|)
      (fun k => norm_gterm_le (by omega) y)
  have hK := norm_kernel_le (c := 2) two_pos y
  show ‖(Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2)
      / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖ ≤ (∑' k, wk k) * phiG y
  rw [div_eq_mul_one_div, norm_mul]
  unfold phiG
  calc ‖Gfun χ (((2 : ℝ) : ℂ) + y * I) - Gfun χ 2‖
        * ‖1 / ((((2 : ℝ) : ℂ) + y * I) * ((((2 : ℝ) : ℂ) + y * I) + 1))‖
      ≤ (√|y| * ∑' k, wk k) * (1 / ((2 : ℝ) ^ 2 + y ^ 2)) :=
        mul_le_mul hbd hK (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg wk_nonneg))
    _ = (∑' k, wk k) * (√|y| / ((2 : ℝ) ^ 2 + y ^ 2)) := by ring

theorem gammaShift_cases {N : ℕ} (χ : DirichletCharacter ℂ N) :
    gammaShift χ = 0 ∨ gammaShift χ = 1 := by
  unfold gammaShift
  split_ifs <;> simp

theorem hasSum_telescope :
    HasSum (fun j : ℕ => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity)]
  have hps : ∀ n : ℕ, ∑ j ∈ Finset.range n, 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))
      = 1 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring
  rw [show (fun n : ℕ => ∑ j ∈ Finset.range n, 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
      = fun n : ℕ => 1 - 1 / ((n : ℝ) + 1) from funext hps]
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at h
  exact h

theorem rterm_tail_bound (a j : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    |rterm (2 * (j + 1) + a) x| ≤ 3 / 2 * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
  have hx0 : 0 < x := by linarith
  have hm2 : 2 ≤ 2 * (j + 1) + a := by omega
  rw [rterm_of_two_le hm2]
  set M : ℝ := ((2 * (j + 1) + a : ℕ) : ℝ) with hMdef
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hM : 2 * (j : ℝ) + 2 ≤ M := by
    rw [hMdef]; push_cast; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have hP : 0 < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
  have hM1 : 0 < M - 1 := by linarith
  have hxp : 0 < x ^ (-M) := Real.rpow_pos_of_pos hx0 _
  have hxl : x ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hA : 2 / (M * (M + 2)) ≤ 1 / 2 * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    rw [div_le_iff₀ (by positivity)]
    rw [show 1 / 2 * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) * (M * (M + 2))
        = M * (M + 2) / (2 * (((j : ℝ) + 1) * ((j : ℝ) + 2))) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hM hM (by linarith) (by linarith)]
  have hC : x ^ (-M) / (M * (M - 1)) ≤ 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    calc x ^ (-M) / (M * (M - 1)) ≤ 1 / (M * (M - 1)) :=
          div_le_div_of_nonneg_right hxl (by positivity)
      _ ≤ 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
          apply one_div_le_one_div_of_le hP
          nlinarith [mul_le_mul hM hM (by linarith) (by linarith)]
  have hB : 3 / ((M - 1) * (M + 2) * x) ≤ 3 / 2 * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    calc 3 / ((M - 1) * (M + 2) * x) ≤ 3 / ((M - 1) * (M + 2)) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact le_mul_of_one_le_right (by positivity) hx
      _ ≤ 3 / 2 * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
          rw [show 3 / 2 * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
              = 3 / (2 * (((j : ℝ) + 1) * ((j : ℝ) + 2))) by field_simp]
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith [mul_le_mul hM hM (by linarith) (by linarith)]
  have hA0 : 0 ≤ 2 / (M * (M + 2)) := by positivity
  have hB0 : 0 ≤ 3 / ((M - 1) * (M + 2) * x) := by positivity
  have hC0 : 0 ≤ x ^ (-M) / (M * (M - 1)) := by positivity
  have hneg : -2 / (M * (M + 2)) = -(2 / (M * (M + 2))) := neg_div _ _
  rw [hneg, abs_le]
  constructor <;> linarith

/-- **Step 4b: the Γ-part.** -/
theorem gamma_part {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    VerticalIntegrable (fun s => (Gfun χ s - Gfun χ 2) / (s * (s + 1))) 2 ∧
    ‖perronI (fun s => Gfun χ s - Gfun χ 2) x‖ ≤ Real.log x + 4 := by
  have hx0 : 0 < x := by linarith
  refine ⟨vi_gamma χ, ?_⟩
  have hS := hasSum_perronI_gamma χ hx
  simp only [perronI_gterm _ hx] at hS
  have hR := Complex.hasSum_re hS
  have hIm := Complex.hasSum_im hS
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hR hIm
  have hI0im : (perronI (fun s => Gfun χ s - Gfun χ 2) x).im = 0 := hIm.unique hasSum_zero
  have hnorm : ‖perronI (fun s => Gfun χ s - Gfun χ 2) x‖
      = |(perronI (fun s => Gfun χ s - Gfun χ 2) x).re| := by
    rw [← Complex.re_add_im (perronI (fun s => Gfun χ s - Gfun χ 2) x), hI0im]
    simp
  rw [hnorm, ← hR.tsum_eq, hR.summable.tsum_eq_zero_add]
  have htail : Summable fun j : ℕ => rterm (2 * (j + 1) + gammaShift χ) x :=
    (summable_nat_add_iff (f := fun k : ℕ => rterm (2 * k + gammaShift χ) x) 1).mpr hR.summable
  have hc := hasSum_telescope
  have hcs : Summable fun j : ℕ => 3 / 2 * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) :=
    hc.summable.mul_left _
  have hcv : ∑' j : ℕ, 3 / 2 * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) = 3 / 2 := by
    rw [tsum_mul_left, hc.tsum_eq, mul_one]
  have hup : ∑' j : ℕ, rterm (2 * (j + 1) + gammaShift χ) x ≤ 3 / 2 := by
    rw [← hcv]
    exact htail.tsum_le_tsum (fun j => (abs_le.mp (rterm_tail_bound _ j hx)).2) hcs
  have hlo : -(3 / 2) ≤ ∑' j : ℕ, rterm (2 * (j + 1) + gammaShift χ) x := by
    rw [← hcv, ← tsum_neg]
    exact hcs.neg.tsum_le_tsum (fun j => (abs_le.mp (rterm_tail_bound _ j hx)).1) htail
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hxi : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  have hxi0 : 0 ≤ 1 / x := by positivity
  generalize ∑' j : ℕ, rterm (2 * (j + 1) + gammaShift χ) x = T at hup hlo
  rw [abs_le]
  rcases gammaShift_cases χ with h0 | h1
  · rw [show 2 * 0 + gammaShift χ = 0 by omega, rterm_zero]
    have e1 : 3 / (2 * x) = 3 / 2 * (1 / x) := by field_simp
    rw [e1]
    constructor <;> nlinarith
  · rw [show 2 * 0 + gammaShift χ = 1 by omega, rterm_one]
    have e1 : 2 / (3 * x) = 2 / 3 * (1 / x) := by field_simp
    have e2 : Real.log x / x ≤ 1 := by rw [div_le_one hx0]; linarith
    have e3 : 0 ≤ Real.log x / x := div_nonneg hlog hx0.le
    rw [e1]
    constructor <;> nlinarith

end DetPrimality.Bach
