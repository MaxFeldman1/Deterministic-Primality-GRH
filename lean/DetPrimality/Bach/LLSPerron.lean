import DetPrimality.Bach.ExplicitGamma
import DetPrimality.Bach.LLSDefs

/-!
# The Perron family with kernel `x^s / s²` (LLS Lemmas 1 and 2) — reusable infrastructure

`llsPer_perronL g x = (1/2πi) ∫_{(2)} g(s) x^s / s² ds` (as a Mellin inverse at `1/x`, exactly as
`perronI`).

* linearity: `llsPer_perronL_add/sub/const/const_mul/congr_line`;
* integrability: `llsPer_vi_const`, `llsPer_vi_inv_sub`, `llsPer_vi_inv_self`;
* residues (`x ≥ 1`):
  - `llsPer_perronL_one`       : `L[1] = log x`
  - `llsPer_perronL_inv_sub`   : `L[1/(s-w)] = x^w/w² - log x / w - 1/w²`  (`Re w < 2`, `w ≠ 0`)
  - `llsPer_perronL_inv_sub_one` : `L[1/(s-1)] = x - log x - 1`
  - `llsPer_perronL_inv_self`  : `L[1/s] = (log x)²/2`
  - `llsPer_perronL_hadamardTerm` : `L[1/(s-ρ) + 1/ρ] = x^ρ/ρ² - 1/ρ²`
  - `llsPer_perronL_zeroTerm`  : `L[1/(s-ρ) - 1/(2-ρ)] = llsPer_zeroTerm ρ x`
* Perron identity `llsPer_logPsi_eq_perronL` : `logPsi χ x = L[-L'/L(·,χ)](x)` for every Dirichlet
  character (any modulus `N ≠ 0`, including `N = 1`, i.e. `ζ`), `x ≥ 1`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology Asymptotics

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `llsPer_perronL g x = (1/2πi) ∫_{(2)} g(s) x^s / s² ds`. -/
noncomputable def llsPer_perronL (g : ℂ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 2 (fun s => g s / s ^ 2) x⁻¹

/-! ## Linearity -/

theorem llsPer_perronL_add {f g : ℂ → ℂ} (hf : VerticalIntegrable (fun s => f s / s ^ 2) 2)
    (hg : VerticalIntegrable (fun s => g s / s ^ 2) 2) {x : ℝ} (hx : 0 < x) :
    llsPer_perronL (fun s => f s + g s) x = llsPer_perronL f x + llsPer_perronL g x := by
  unfold llsPer_perronL
  rw [show (fun s : ℂ => (f s + g s) / s ^ 2)
      = fun s => f s / s ^ 2 + g s / s ^ 2 from funext fun s => add_div _ _ _]
  exact mellinInv_add hf hg (inv_pos.mpr hx)

theorem llsPer_perronL_sub {f g : ℂ → ℂ} (hf : VerticalIntegrable (fun s => f s / s ^ 2) 2)
    (hg : VerticalIntegrable (fun s => g s / s ^ 2) 2) {x : ℝ} (hx : 0 < x) :
    llsPer_perronL (fun s => f s - g s) x = llsPer_perronL f x - llsPer_perronL g x := by
  unfold llsPer_perronL
  rw [show (fun s : ℂ => (f s - g s) / s ^ 2)
      = fun s => f s / s ^ 2 - g s / s ^ 2 from funext fun s => sub_div _ _ _]
  exact mellinInv_sub hf hg (inv_pos.mpr hx)

theorem llsPer_perronL_const_mul (c : ℂ) (g : ℂ → ℂ) (x : ℝ) :
    llsPer_perronL (fun s => c * g s) x = c * llsPer_perronL g x := by
  unfold llsPer_perronL
  rw [← mellinInv_const_mul]
  congr 1
  funext s
  ring

theorem llsPer_perronL_const (c : ℂ) (x : ℝ) :
    llsPer_perronL (fun _ => c) x = c * llsPer_perronL (fun _ => 1) x := by
  rw [← llsPer_perronL_const_mul]
  simp

theorem llsPer_perronL_congr_line {f g : ℂ → ℂ}
    (h : ∀ y : ℝ, f ((2 : ℝ) + y * I) = g ((2 : ℝ) + y * I)) (x : ℝ) :
    llsPer_perronL f x = llsPer_perronL g x := by
  unfold llsPer_perronL
  exact mellinInv_congr_line (fun y => by simp only [h y]) _

/-! ## The kernel on the line `Re s = 2` -/

theorem llsPer_line_ne (y : ℝ) : ((2 : ℝ) : ℂ) + y * I ≠ 0 :=
  ne_zero_of_re_pos (by rw [line_re]; norm_num)

theorem llsPer_two_le_norm_line (y : ℝ) : 2 ≤ ‖((2 : ℝ) : ℂ) + y * I‖ := by
  have := Complex.re_le_norm (((2 : ℝ) : ℂ) + y * I)
  rwa [line_re] at this

theorem llsPer_norm_kernel (y : ℝ) :
    ‖1 / (((2 : ℝ) : ℂ) + y * I) ^ 2‖ = 1 / ((2 : ℝ) ^ 2 + y ^ 2) := by
  rw [norm_div, norm_one, norm_pow, normSq_line]

theorem llsPer_vi_const (c : ℂ) : VerticalIntegrable (fun s : ℂ => c / s ^ 2) 2 := by
  unfold VerticalIntegrable
  refine integrable_of_le_div_sq (M := ‖c‖) ?_ two_pos (fun y => ?_)
  · exact Continuous.div continuous_const (by fun_prop)
      (fun y => pow_ne_zero 2 (llsPer_line_ne y))
  · rw [norm_div, norm_pow, normSq_line]

theorem llsPer_vi_inv_sub {w : ℂ} (hw : w.re < 2) :
    VerticalIntegrable (fun s : ℂ => 1 / (s - w) / s ^ 2) 2 := by
  unfold VerticalIntegrable
  have hne : ∀ y : ℝ, ((2 : ℝ) : ℂ) + y * I - w ≠ 0 := fun y =>
    ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith)
  refine integrable_of_le_div_sq (M := 1 / (2 - w.re)) ?_ two_pos (fun y => ?_)
  · exact Continuous.div (Continuous.div continuous_const (by fun_prop) hne) (by fun_prop)
      (fun y => pow_ne_zero 2 (llsPer_line_ne y))
  · have hsw : 2 - w.re ≤ ‖((2 : ℝ) : ℂ) + y * I - w‖ := by
      have := Complex.re_le_norm (((2 : ℝ) : ℂ) + y * I - w)
      rw [Complex.sub_re, line_re] at this
      exact this
    have hcw : 0 < 2 - w.re := by linarith
    rw [norm_div, norm_div, norm_one, norm_pow, normSq_line]
    exact div_le_div_of_nonneg_right (one_div_le_one_div_of_le hcw hsw) (by positivity)

theorem llsPer_vi_inv_self : VerticalIntegrable (fun s : ℂ => 1 / s / s ^ 2) 2 := by
  unfold VerticalIntegrable
  refine integrable_of_le_div_sq (M := 1 / 2) ?_ two_pos (fun y => ?_)
  · exact Continuous.div (Continuous.div continuous_const (by fun_prop) llsPer_line_ne)
      (by fun_prop) (fun y => pow_ne_zero 2 (llsPer_line_ne y))
  · rw [norm_div, norm_div, norm_one, norm_pow, normSq_line]
    exact div_le_div_of_nonneg_right
      (one_div_le_one_div_of_le two_pos (llsPer_two_le_norm_line y)) (by positivity)

/-! ## Mellin inversion: `A/s + C/(s-w) - D/s²` -/

/-- `(A + C t^{-w} + D log t) · 1_{(0,1]}(t)`. -/
noncomputable def llsPer_mix (A C D w : ℂ) : ℝ → ℂ := fun t =>
  ioc3 A 0 C w t + iocLog 0 0 D 0 t

theorem llsPer_hasMellin_mix (A C D w : ℂ) {s : ℂ} (hs : 0 < s.re) (hsw : w.re < s.re) :
    HasMellin (llsPer_mix A C D w) s (A / s + C / (s - w) - D / s ^ 2) := by
  have h1 := hasMellin_ioc3 A 0 C w hs hsw
  have h2 := hasMellin_iocLog 0 0 D 0 hs
  have h := hasMellin_add h1.1 h2.1
  refine ⟨h.1, ?_⟩
  have key := h.2
  rw [h1.2, h2.2] at key
  refine key.trans ?_
  ring

theorem llsPer_mellinInv_mix (A C D w : ℂ) {c : ℝ} (hc : 0 < c) (hw : w.re < c)
    (hAC : A + C = 0) {x : ℝ} (hx : 0 < x)
    (hint : VerticalIntegrable (fun s => A / s + C / (s - w) - D / s ^ 2) c) :
    mellinInv c (fun s => A / s + C / (s - w) - D / s ^ 2) x
      = if x ≤ 1 then A + C * (x : ℂ) ^ (-w) + D * (Real.log x : ℂ) else 0 := by
  have hline : ∀ y : ℝ, (fun s => A / s + C / (s - w) - D / s ^ 2) (c + y * I)
      = mellin (llsPer_mix A C D w) (c + y * I) := by
    intro y
    exact ((llsPer_hasMellin_mix A C D w (by rw [line_re]; exact hc)
      (by rw [line_re]; exact hw)).2).symm
  rw [mellinInv_congr_line hline]
  have hre : ((c : ℂ)).re = c := by simp
  have hcont : ContinuousAt (llsPer_mix A C D w) x :=
    (continuousAt_ioc3 (by rw [add_zero]; exact hAC) hx).add
      (continuousAt_iocLog (by ring) hx)
  rw [mellinInv_mellin_eq c (llsPer_mix A C D w) hx
    (llsPer_hasMellin_mix A C D w (by rw [hre]; exact hc) (by rw [hre]; exact hw)).1
    (VerticalIntegrable.congr_line hline hint) hcont]
  unfold llsPer_mix
  split_ifs with h
  · rw [ioc3_of_mem ⟨hx, h⟩, iocLog_of_mem ⟨hx, h⟩]; ring
  · rw [ioc3_of_one_lt (not_le.mp h), iocLog_of_one_lt (not_le.mp h)]; ring

/-- `(1/2π)∫ x^{-s}/s² dy = -log x · 1_{x ≤ 1}`. -/
theorem llsPer_mellinInv_sq {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s : ℂ => 1 / s ^ 2) x = if x ≤ 1 then -(Real.log x : ℂ) else 0 := by
  have hline : ∀ y : ℝ, (fun s : ℂ => 1 / s ^ 2) (((2 : ℝ) : ℂ) + y * I)
      = (fun s : ℂ => (0 : ℂ) / s + 0 / (s - 0) - (-1) / s ^ 2) (((2 : ℝ) : ℂ) + y * I) := by
    intro y
    simp only
    ring
  rw [mellinInv_congr_line (F := fun s : ℂ => 1 / s ^ 2)
    (G := fun s : ℂ => (0 : ℂ) / s + 0 / (s - 0) - (-1) / s ^ 2) hline,
    llsPer_mellinInv_mix 0 0 (-1) 0 two_pos (by simp) (by ring) hx
      (VerticalIntegrable.congr_line hline (llsPer_vi_const 1))]
  split_ifs with h
  · ring
  · rfl

/-- `(1/2π)∫ x^{-s}/(s²(s-w)) dy = (-1/w² + x^{-w}/w² + log x / w) · 1_{x ≤ 1}`. -/
theorem llsPer_mellinInv_sq_inv_sub {w : ℂ} (hw : w.re < 2) (hw0 : w ≠ 0) {x : ℝ}
    (hx : 0 < x) :
    mellinInv 2 (fun s : ℂ => 1 / (s - w) / s ^ 2) x
      = if x ≤ 1 then -1 / w ^ 2 + 1 / w ^ 2 * (x : ℂ) ^ (-w) + 1 / w * (Real.log x : ℂ)
        else 0 := by
  have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s - w) / s ^ 2) (((2 : ℝ) : ℂ) + y * I)
      = (fun s : ℂ => (-1 / w ^ 2) / s + (1 / w ^ 2) / (s - w) - (1 / w) / s ^ 2)
        (((2 : ℝ) : ℂ) + y * I) := by
    intro y
    have h0 := llsPer_line_ne y
    have h2 : ((2 : ℝ) : ℂ) + y * I - w ≠ 0 :=
      ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith)
    simp only
    field_simp
    ring
  rw [mellinInv_congr_line (F := fun s : ℂ => 1 / (s - w) / s ^ 2)
    (G := fun s : ℂ => (-1 / w ^ 2) / s + (1 / w ^ 2) / (s - w) - (1 / w) / s ^ 2) hline,
    llsPer_mellinInv_mix _ _ _ w two_pos hw (by ring) hx
      (VerticalIntegrable.congr_line hline (llsPer_vi_inv_sub hw))]

/-! ## Mellin inversion: `1/s³` -/

/-- `(log t)² · 1_{(0,1]}(t)`. -/
noncomputable def llsPer_logsq : ℝ → ℂ := fun t => Real.log t • (Real.log t • ind1 t)

theorem llsPer_logsq_of_mem {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    llsPer_logsq t = (Real.log t : ℂ) ^ 2 := by
  simp only [llsPer_logsq, ind1, indicator_of_mem ht, Complex.real_smul]
  ring

theorem llsPer_logsq_of_one_lt {t : ℝ} (ht : 1 < t) : llsPer_logsq t = 0 := by
  simp [llsPer_logsq, ind1_of_one_lt ht]

theorem llsPer_hasMellin_logsq {s : ℂ} (hs : 0 < s.re) :
    HasMellin llsPer_logsq s (2 / s ^ 3) := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  set b : ℝ := s.re / 2 with hbdef
  have hb : 0 < b := by positivity
  have hloc : LocallyIntegrableOn (fun t => Real.log t • ind1 t) (Ioi 0) := by
    have h := (hasMellin_log_ind1 (s := 1) (by simp)).1
    simp only [MellinConvergent, sub_self, cpow_zero, one_smul] at h
    exact h.locallyIntegrableOn
  have htop : (fun t => Real.log t • ind1 t) =O[atTop] (fun t : ℝ => t ^ (-(s.re + 1))) := by
    have : (fun _ : ℝ => (0 : ℂ)) =ᶠ[atTop] (fun t => Real.log t • ind1 t) := by
      filter_upwards [eventually_gt_atTop 1] with t ht
      rw [ind1_of_one_lt ht, smul_zero]
    exact (isBigO_zero _ _).congr' this EventuallyEq.rfl
  have hbot : (fun t => Real.log t • ind1 t) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    refine IsBigO.of_bound (1 / b) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
    by_cases h1 : t ≤ 1
    · have hi : ind1 t = 1 := by
        unfold ind1; rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, h1⟩)]
      rw [hi, norm_smul, norm_one, mul_one, Real.norm_eq_abs,
        abs_of_nonpos (Real.log_nonpos ht0.le h1)]
      have := Real.log_le_rpow_div (inv_nonneg.mpr ht0.le) hb
      rw [Real.log_inv, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le] at this
      calc -Real.log t ≤ t ^ (-b) / b := this
        _ = 1 / b * t ^ (-b) := by ring
    · rw [ind1_of_one_lt (not_le.mp h1), smul_zero, norm_zero]
      exact mul_nonneg (one_div_pos.mpr hb).le (Real.rpow_nonneg ht0.le _)
  obtain ⟨hc, hd⟩ := mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := b) hloc htop
    (by linarith) hbot (by rw [hbdef]; linarith)
  have hev : mellin (fun t => Real.log t • ind1 t) =ᶠ[𝓝 s] fun z => -1 / z ^ 2 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (hasMellin_log_ind1 hz).2
  have hd2 : HasDerivAt (mellin (fun t => Real.log t • ind1 t)) (2 / s ^ 3) s := by
    have h := (hasDerivAt_const s (-1 : ℂ)).div (hasDerivAt_pow 2 s) (pow_ne_zero 2 hs0)
    have h' : HasDerivAt (fun z : ℂ => -1 / z ^ 2) (2 / s ^ 3) s := by
      refine h.congr_deriv ?_
      field_simp
      ring
    exact h'.congr_of_eventuallyEq hev
  exact ⟨hc, hd.unique hd2⟩

theorem llsPer_continuousAt_logsq {x : ℝ} (hx : 0 < x) : ContinuousAt llsPer_logsq x := by
  set g : ℝ → ℂ := fun u => ((Real.log u : ℝ) : ℂ) ^ 2 with hg
  have hu : 0 < min x 1 := lt_min hx one_pos
  have hgc : ContinuousAt g (min x 1) :=
    (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hu.ne')).pow 2
  have hmin : ContinuousAt (fun t : ℝ => min t 1) x :=
    (continuous_id.min continuous_const).continuousAt
  have hcomp : ContinuousAt (fun t : ℝ => g (min t 1)) x :=
    ContinuousAt.comp (f := fun t : ℝ => min t 1) hgc hmin
  refine hcomp.congr ?_
  filter_upwards [eventually_gt_nhds hx] with t ht
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1, llsPer_logsq_of_mem ⟨ht, ht1⟩]
  · push Not at ht1
    rw [min_eq_right ht1.le, llsPer_logsq_of_one_lt ht1, hg]
    simp

theorem llsPer_vi_two_div_cube : VerticalIntegrable (fun s : ℂ => 2 / s ^ 3) 2 := by
  unfold VerticalIntegrable
  refine integrable_of_le_div_sq (M := 1) ?_ two_pos (fun y => ?_)
  · exact Continuous.div continuous_const (by fun_prop)
      (fun y => pow_ne_zero 3 (llsPer_line_ne y))
  · have h2 := llsPer_two_le_norm_line y
    have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_div, norm_pow, hn2, pow_succ, normSq_line,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg y]

/-- `(1/2π)∫ x^{-s}/s³ dy = (log x)²/2 · 1_{x ≤ 1}`. -/
theorem llsPer_mellinInv_cube {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s : ℂ => 1 / s ^ 3) x
      = if x ≤ 1 then (Real.log x : ℂ) ^ 2 / 2 else 0 := by
  have hline : ∀ y : ℝ, (fun s : ℂ => 2 / s ^ 3) (((2 : ℝ) : ℂ) + y * I)
      = mellin llsPer_logsq (((2 : ℝ) : ℂ) + y * I) := by
    intro y
    exact ((llsPer_hasMellin_logsq (by rw [line_re]; norm_num)).2).symm
  have hre : (((2 : ℝ) : ℂ)).re = 2 := by simp
  have h2 : mellinInv 2 (fun s : ℂ => 2 / s ^ 3) x = llsPer_logsq x := by
    rw [mellinInv_congr_line hline]
    exact mellinInv_mellin_eq 2 llsPer_logsq hx
      (llsPer_hasMellin_logsq (by rw [hre]; norm_num)).1
      (VerticalIntegrable.congr_line hline llsPer_vi_two_div_cube)
      (llsPer_continuousAt_logsq hx)
  rw [show (fun s : ℂ => 1 / s ^ 3) = fun s => (1 / 2 : ℂ) * (2 / s ^ 3) by
    funext s; ring, mellinInv_const_mul, h2]
  split_ifs with h
  · rw [llsPer_logsq_of_mem ⟨hx, h⟩]; ring
  · rw [llsPer_logsq_of_one_lt (not_le.mp h)]; ring

/-! ## Residues -/

/-- `L[1](x) = log x`. -/
theorem llsPer_perronL_one {x : ℝ} (hx : 1 ≤ x) :
    llsPer_perronL (fun _ => 1) x = (Real.log x : ℂ) := by
  have hx0 : 0 < x := by linarith
  unfold llsPer_perronL
  rw [llsPer_mellinInv_sq (inv_pos.mpr hx0), if_pos (inv_le_one_of_one_le₀ hx), Real.log_inv]
  push_cast
  ring

/-- `L[1/(s-w)](x) = x^w/w² - log x / w - 1/w²` for `Re w < 2`, `w ≠ 0`, `x ≥ 1`. -/
theorem llsPer_perronL_inv_sub {w : ℂ} (hw : w.re < 2) (hw0 : w ≠ 0) {x : ℝ} (hx : 1 ≤ x) :
    llsPer_perronL (fun s => 1 / (s - w)) x
      = (x : ℂ) ^ w / w ^ 2 - (Real.log x : ℂ) / w - 1 / w ^ 2 := by
  have hx0 : 0 < x := by linarith
  unfold llsPer_perronL
  rw [llsPer_mellinInv_sq_inv_sub hw hw0 (inv_pos.mpr hx0), if_pos (inv_le_one_of_one_le₀ hx),
    ofReal_inv_cpow_neg hx0, Real.log_inv]
  push_cast
  ring

/-- The pole of `ζ`: `L[1/(s-1)](x) = x - log x - 1`. -/
theorem llsPer_perronL_inv_sub_one {x : ℝ} (hx : 1 ≤ x) :
    llsPer_perronL (fun s => 1 / (s - 1)) x = (x : ℂ) - (Real.log x : ℂ) - 1 := by
  rw [llsPer_perronL_inv_sub (by norm_num) one_ne_zero hx, cpow_one]
  ring

/-- `L[1/s](x) = (log x)²/2`. -/
theorem llsPer_perronL_inv_self {x : ℝ} (hx : 1 ≤ x) :
    llsPer_perronL (fun s => 1 / s) x = (Real.log x : ℂ) ^ 2 / 2 := by
  have hx0 : 0 < x := by linarith
  unfold llsPer_perronL
  rw [show (fun s : ℂ => 1 / s / s ^ 2) = fun s => 1 / s ^ 3 by
    funext s; rw [div_div]; ring]
  rw [llsPer_mellinInv_cube (inv_pos.mpr hx0), if_pos (inv_le_one_of_one_le₀ hx), Real.log_inv]
  push_cast
  ring

/-- Hadamard term: `L[1/(s-ρ) + 1/ρ](x) = x^ρ/ρ² - 1/ρ²`. -/
theorem llsPer_perronL_hadamardTerm {ρ : ℂ} (hρ : ρ.re < 2) (hρ0 : ρ ≠ 0) {x : ℝ}
    (hx : 1 ≤ x) :
    llsPer_perronL (fun s => 1 / (s - ρ) + 1 / ρ) x = (x : ℂ) ^ ρ / ρ ^ 2 - 1 / ρ ^ 2 := by
  have hx0 : 0 < x := by linarith
  rw [llsPer_perronL_add (llsPer_vi_inv_sub hρ) (llsPer_vi_const _) hx0,
    llsPer_perronL_inv_sub hρ hρ0 hx, llsPer_perronL_const, llsPer_perronL_one hx]
  field_simp
  ring

/-- The contribution of one nontrivial zero (base point `2`):
`x^ρ/ρ² - 1/ρ² - log x · (1/ρ + 1/(2-ρ))`. -/
noncomputable def llsPer_zeroTerm (ρ : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ ρ / ρ ^ 2 - 1 / ρ ^ 2 - (Real.log x : ℂ) * (1 / ρ + 1 / (2 - ρ))

/-- `L[1/(s-ρ) - 1/(2-ρ)](x) = llsPer_zeroTerm ρ x`. -/
theorem llsPer_perronL_zeroTerm {ρ : ℂ} (hρ : ρ.re < 2) (hρ0 : ρ ≠ 0) {x : ℝ} (hx : 1 ≤ x) :
    llsPer_perronL (fun s => 1 / (s - ρ) - 1 / (2 - ρ)) x = llsPer_zeroTerm ρ x := by
  have hx0 : 0 < x := by linarith
  rw [llsPer_perronL_sub (llsPer_vi_inv_sub hρ) (llsPer_vi_const _) hx0,
    llsPer_perronL_inv_sub hρ hρ0 hx, llsPer_perronL_const, llsPer_perronL_one hx,
    llsPer_zeroTerm]
  ring

/-! ## The Perron identity `logPsi χ x = L[-L'/L](x)` -/

theorem llsPer_kernel_integral {z : ℝ} (hz : 0 < z) :
    ∫ y : ℝ, (z : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
        (fun s : ℂ => 1 / s ^ 2) (((2 : ℝ) : ℂ) + y * I)
      = (2 * Real.pi : ℂ) * (if z ≤ 1 then -(Real.log z : ℂ) else 0) := by
  have h := llsPer_mellinInv_sq hz
  unfold mellinInv at h
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  rw [← h, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_one_div_cancel hpi, one_mul]

/-- **Perron identity** for the kernel `x^s/s²`: for every Dirichlet character `χ` (any modulus,
including `N = 1`) and `x ≥ 1`, `∑_{n ≤ x} Λ(n) χ(n) log(x/n) = L[-L'/L(·,χ)](x)`. -/
theorem llsPer_logPsi_eq_perronL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 1 ≤ x) :
    logPsi χ x = llsPer_perronL (fun s => -(deriv (LFunction χ) s / LFunction χ s)) x := by
  have hx0 : 0 < x := by linarith
  set f : ℕ → ℂ := fun n => χ (n : ZMod N) * (Λ n : ℂ) with hf
  set K : ℂ → ℂ := fun s => 1 / s ^ 2 with hK
  set F : ℕ → ℝ → ℂ := fun n y => if n = 0 then 0 else
    f n * ((((n : ℝ) / x : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) • K (((2 : ℝ) : ℂ) + y * I))
    with hFdef
  have hpos : ∀ n : ℕ, n ≠ 0 → 0 < (n : ℝ) / x := fun n hn =>
    div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hx0
  -- the Dirichlet series on the line
  have hLS : ∀ y : ℝ, -(deriv (LFunction χ) (((2 : ℝ) : ℂ) + y * I)
      / LFunction χ (((2 : ℝ) : ℂ) + y * I)) = LSeries f (((2 : ℝ) : ℂ) + y * I) := by
    intro y
    have hs : 1 < (((2 : ℝ) : ℂ) + y * I).re := by simp
    have h1 : LSeries f (((2 : ℝ) : ℂ) + y * I) = _ := LSeries_twist_vonMangoldt_eq χ hs
    rw [h1, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs, neg_div]
  -- pointwise expansion of the integrand
  have hpt : ∀ y : ℝ, ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
      (fun s => -(deriv (LFunction χ) s / LFunction χ s) / s ^ 2)
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
  have hKint : VerticalIntegrable K 2 := llsPer_vi_const 1
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
  have hsum : Summable fun n => ∫ y, ‖F n y‖ := by
    have h := ((LSeriesSummable_twist_vonMangoldt χ (s := 2) (by norm_num)).norm).mul_right
      (x ^ 2 * C)
    refine h.congr fun n => (hFnorm n).symm
  -- interchange
  have hint := integral_tsum_of_summable_integral_norm hFint hsum
  have hFn : ∀ n, ∫ y, F n y = if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ)
        * (if (n : ℝ) / x ≤ 1 then -((Real.log ((n : ℝ) / x) : ℝ) : ℂ) else 0)) := by
    intro n
    by_cases hn : n = 0
    · simp [hFdef, hn]
    · simp only [hFdef, hn, if_false]
      rw [integral_const_mul, llsPer_kernel_integral (hpos n hn)]
  unfold llsPer_perronL mellinInv
  rw [integral_congr_ae (Eventually.of_forall hpt), ← hint]
  simp_rw [hFn]
  rw [Complex.real_smul, ← tsum_mul_left]
  have hzero : ∀ n ∉ Finset.range (⌊x⌋₊ + 1),
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * (if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ)
        * (if (n : ℝ) / x ≤ 1 then -((Real.log ((n : ℝ) / x) : ℝ) : ℂ) else 0)))) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hxn : x < n := Nat.lt_of_floor_lt hn
    have h1 : 1 < (n : ℝ) / x := (one_lt_div hx0).mpr hxn
    split_ifs with h0 h2
    · simp
    · exact absurd h2 (not_le.mpr h1)
    · simp
  rw [tsum_eq_sum hzero]
  unfold logPsi
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnx : (n : ℝ) ≤ x :=
    (Nat.le_floor_iff hx0.le).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  by_cases h0 : n = 0
  · simp [h0]
  · have hle : (n : ℝ) / x ≤ 1 := by rw [div_le_one hx0]; exact hnx
    have hlog : Real.log ((n : ℝ) / x) = -Real.log (x / n) := by
      rw [← Real.log_inv, inv_div]
    rw [if_neg h0, if_pos hle, hf, hlog]
    push_cast
    field_simp

end DetPrimality.Bach
