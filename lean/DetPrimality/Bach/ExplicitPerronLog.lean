import DetPrimality.Bach.ExplicitPerron

/-!
# Double-pole Perron integrals (fully proved)

* `mellinInv_kernel_sq` : `(1/2π)∫ x^{-s} / (s²(s+1)) dy = (-1 + x - log x)·1_{x ≤ 1}`;
* `mellinInv_kernel_add_one_sq` : `(1/2π)∫ x^{-s} / (s(s+1)²) dy = (1 - x + x log x)·1_{x ≤ 1}`.

The Mellin transforms of `log t · 1_{(0,1]}` and `t log t · 1_{(0,1]}` are obtained by
differentiating `1/s`, `1/(s+1)` under the integral (`mellin_hasDerivAt_of_isBigO_rpow`).
-/

open Complex Set MeasureTheory Filter Topology Asymptotics

namespace DetPrimality.Bach

noncomputable def ind1 : ℝ → ℂ := indicator (Ioc 0 1) (fun _ : ℝ => (1 : ℂ))
noncomputable def indT : ℝ → ℂ := indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (1 : ℂ))

theorem norm_ind1_le (t : ℝ) : ‖ind1 t‖ ≤ 1 := by
  unfold ind1
  by_cases h : t ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem h]; simp
  · rw [indicator_of_notMem h]; simp

theorem norm_indT_le (t : ℝ) : ‖indT t‖ ≤ 1 := by
  unfold indT
  by_cases h : t ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem h, cpow_one, Complex.norm_real, Real.norm_of_nonneg h.1.le]; exact h.2
  · rw [indicator_of_notMem h]; simp

theorem ind1_of_one_lt {t : ℝ} (ht : 1 < t) : ind1 t = 0 :=
  indicator_of_notMem (fun h => by linarith [h.2]) _

theorem indT_of_one_lt {t : ℝ} (ht : 1 < t) : indT t = 0 :=
  indicator_of_notMem (fun h => by linarith [h.2]) _

theorem integrable_ind1 : Integrable ind1 :=
  (continuous_const.integrableOn_Ioc).integrable_indicator measurableSet_Ioc

theorem integrable_indT : Integrable indT := by
  unfold indT
  have h : (fun t : ℝ => (t : ℂ) ^ (1 : ℂ)) = fun t : ℝ => (t : ℂ) := funext fun t => cpow_one _
  rw [h]
  exact (Complex.continuous_ofReal.integrableOn_Ioc).integrable_indicator measurableSet_Ioc

theorem mellin_log_aux {f : ℝ → ℂ} (hfi : Integrable f) (hb : ∀ t, ‖f t‖ ≤ 1)
    (h0 : ∀ t, 1 < t → f t = 0) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t => Real.log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t => Real.log t • f t) s) s := by
  refine mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    (hfi.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ hs
  · have : (fun _ : ℝ => (0 : ℂ)) =ᶠ[atTop] f := by
      filter_upwards [eventually_gt_atTop 1] with t ht
      exact (h0 t ht).symm
    exact (isBigO_zero _ _).congr' this EventuallyEq.rfl
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact hb t

theorem hasMellin_log_ind1 {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t => Real.log t • ind1 t) s (-1 / s ^ 2) := by
  obtain ⟨hc, hd⟩ := mellin_log_aux integrable_ind1 norm_ind1_le (fun t ht => ind1_of_one_lt ht) hs
  have hev : mellin ind1 =ᶠ[𝓝 s] fun z => z⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    unfold ind1
    rw [(hasMellin_one_Ioc hz).2, one_div]
  have hd2 : HasDerivAt (mellin ind1) (-1 / s ^ 2) s := by
    have := (hasDerivAt_id s).inv (ne_zero_of_re_pos hs)
    exact this.congr_of_eventuallyEq hev
  exact ⟨hc, hd.unique hd2⟩

theorem hasMellin_log_indT {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t => Real.log t • indT t) s (-1 / (s + 1) ^ 2) := by
  obtain ⟨hc, hd⟩ := mellin_log_aux integrable_indT norm_indT_le (fun t ht => indT_of_one_lt ht) hs
  have hev : mellin indT =ᶠ[𝓝 s] fun z => (z + 1)⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    unfold indT
    rw [(hasMellin_cpow_Ioc 1 (by simp; linarith)).2, one_div]
  have hs1 : s + 1 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have hd2 : HasDerivAt (mellin indT) (-1 / (s + 1) ^ 2) s := by
    have := ((hasDerivAt_id s).add_const 1).inv hs1
    exact this.congr_of_eventuallyEq hev
  exact ⟨hc, hd.unique hd2⟩

/-- `(A + B t + D log t + E t log t) · 1_{(0,1]}(t)`. -/
noncomputable def iocLog (A B D E : ℂ) : ℝ → ℂ := fun t =>
  A • ind1 t + B • indT t + D • (Real.log t • ind1 t) + E • (Real.log t • indT t)

theorem iocLog_of_mem {A B D E : ℂ} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    iocLog A B D E t = A + B * t + D * Real.log t + E * (t * Real.log t) := by
  simp only [iocLog, ind1, indT, indicator_of_mem ht, cpow_one, smul_eq_mul, Complex.real_smul]
  ring

theorem iocLog_of_one_lt {A B D E : ℂ} {t : ℝ} (ht : 1 < t) : iocLog A B D E t = 0 := by
  simp [iocLog, ind1_of_one_lt ht, indT_of_one_lt ht]

theorem hasMellin_iocLog (A B D E : ℂ) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (iocLog A B D E) s (A / s + B / (s + 1) - D / s ^ 2 - E / (s + 1) ^ 2) := by
  obtain ⟨h1c, h1⟩ := hasMellin_one_Ioc hs
  obtain ⟨h2c, h2⟩ := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  obtain ⟨h3c, h3⟩ := hasMellin_log_ind1 hs
  obtain ⟨h4c, h4⟩ := hasMellin_log_indT hs
  have a1 := hasMellin_const_smul (f := ind1) h1c A
  have a2 := hasMellin_const_smul (f := indT) h2c B
  have a3 := hasMellin_const_smul h3c D
  have a4 := hasMellin_const_smul h4c E
  have a12 := hasMellin_add a1.1 a2.1
  have a123 := hasMellin_add a12.1 a3.1
  have a1234 := hasMellin_add a123.1 a4.1
  refine ⟨a1234.1, ?_⟩
  have key := a1234.2
  rw [a123.2, a12.2, a1.2, a2.2, a3.2, a4.2, h3, h4] at key
  unfold ind1 indT at key
  rw [h1, h2] at key
  refine key.trans ?_
  simp only [smul_eq_mul]
  ring

theorem continuousAt_iocLog {A B D E : ℂ} (hAB : A + B = 0) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (iocLog A B D E) x := by
  set g : ℝ → ℂ := fun u => A + B * u + D * Real.log u + E * (u * Real.log u) with hg
  have hu : 0 < min x 1 := lt_min hx one_pos
  have hlog : ContinuousAt (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) (min x 1) :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hu.ne')
  have hgc : ContinuousAt g (min x 1) := by
    have hid : ContinuousAt (fun u : ℝ => (u : ℂ)) (min x 1) :=
      Complex.continuous_ofReal.continuousAt
    exact ((continuousAt_const.add (continuousAt_const.mul hid)).add
      (continuousAt_const.mul hlog)).add (continuousAt_const.mul (hid.mul hlog))
  have hmin : ContinuousAt (fun t : ℝ => min t 1) x :=
    (continuous_id.min continuous_const).continuousAt
  have hcomp : ContinuousAt (fun t : ℝ => g (min t 1)) x :=
    ContinuousAt.comp (f := fun t : ℝ => min t 1) hgc hmin
  refine hcomp.congr ?_
  filter_upwards [eventually_gt_nhds hx] with t ht
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1, iocLog_of_mem ⟨ht, ht1⟩]
  · push Not at ht1
    rw [min_eq_right ht1.le, iocLog_of_one_lt ht1, hg]
    simp only [ofReal_one, Real.log_one, ofReal_zero, mul_zero, mul_one, add_zero]
    exact hAB

theorem mellinInv_iocLog (A B D E : ℂ) {c : ℝ} (hc : 0 < c) (hAB : A + B = 0) {x : ℝ}
    (hx : 0 < x)
    (hint : VerticalIntegrable (fun s => A / s + B / (s + 1) - D / s ^ 2 - E / (s + 1) ^ 2) c) :
    mellinInv c (fun s => A / s + B / (s + 1) - D / s ^ 2 - E / (s + 1) ^ 2) x
      = iocLog A B D E x := by
  have hline : ∀ y : ℝ, (fun s => A / s + B / (s + 1) - D / s ^ 2 - E / (s + 1) ^ 2) (c + y * I)
      = mellin (iocLog A B D E) (c + y * I) := by
    intro y
    exact ((hasMellin_iocLog A B D E (by rw [line_re]; exact hc)).2).symm
  rw [mellinInv_congr_line hline]
  have hre : ((c : ℂ)).re = c := by simp
  exact mellinInv_mellin_eq c (iocLog A B D E) hx
    (hasMellin_iocLog A B D E (by rw [hre]; exact hc)).1
    (VerticalIntegrable.congr_line hline hint) (continuousAt_iocLog hAB hx)

theorem norm_line_add_one_ge_one {c : ℝ} (hc : 0 < c) (y : ℝ) : 1 ≤ ‖(c : ℂ) + y * I + 1‖ := by
  have := Complex.re_le_norm ((c : ℂ) + y * I + 1)
  rw [Complex.add_re, line_re, Complex.one_re] at this
  linarith

theorem verticalIntegrable_kernel_sq {c : ℝ} (hc : 0 < c) :
    VerticalIntegrable (fun s : ℂ => 1 / (s ^ 2 * (s + 1))) c := by
  unfold VerticalIntegrable
  have h0 : ∀ y : ℝ, (c : ℂ) + y * I ≠ 0 := fun y => ne_zero_of_re_pos (by rw [line_re]; exact hc)
  have h1 : ∀ y : ℝ, (c : ℂ) + y * I + 1 ≠ 0 := fun y =>
    ne_zero_of_re_pos (by rw [Complex.add_re, line_re]; simp; linarith)
  refine integrable_of_le_div_sq (M := 1) ?_ hc (fun y => ?_)
  · exact Continuous.div continuous_const (by fun_prop)
      (fun y => mul_ne_zero (pow_ne_zero 2 (h0 y)) (h1 y))
  · have hs1 := norm_line_add_one_ge_one hc y
    rw [norm_div, norm_one, norm_mul, norm_pow, normSq_line]
    exact one_div_le_one_div_of_le (by positivity) (le_mul_of_one_le_right (by positivity) hs1)

theorem verticalIntegrable_kernel_add_one_sq {c : ℝ} (hc : 0 < c) :
    VerticalIntegrable (fun s : ℂ => 1 / (s * (s + 1) ^ 2)) c := by
  unfold VerticalIntegrable
  have h0 : ∀ y : ℝ, (c : ℂ) + y * I ≠ 0 := fun y => ne_zero_of_re_pos (by rw [line_re]; exact hc)
  have h1 : ∀ y : ℝ, (c : ℂ) + y * I + 1 ≠ 0 := fun y =>
    ne_zero_of_re_pos (by rw [Complex.add_re, line_re]; simp; linarith)
  refine integrable_of_le_div_sq (M := 1) ?_ hc (fun y => ?_)
  · exact Continuous.div continuous_const (by fun_prop)
      (fun y => mul_ne_zero (h0 y) (pow_ne_zero 2 (h1 y)))
  · have hs1 := norm_line_add_one_ge_one hc y
    have hss := norm_line_le_norm_line_add_one hc y
    have hpos : 0 < ‖(c : ℂ) + y * I‖ := norm_pos_iff.mpr (h0 y)
    rw [norm_div, norm_one, norm_mul, norm_pow, ← normSq_line]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [mul_le_mul_of_nonneg_left hss hpos.le]

/-- `(1/2π)∫ x^{-s}/(s²(s+1)) dy = (-1 + x - log x)·1_{x ≤ 1}` (`c > 0`, `x > 0`). -/
theorem mellinInv_kernel_sq {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    mellinInv c (fun s => 1 / (s ^ 2 * (s + 1))) x
      = if x ≤ 1 then -1 + (x : ℂ) - (Real.log x : ℂ) else 0 := by
  have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s ^ 2 * (s + 1))) (c + y * I)
      = (fun s : ℂ => (-1) / s + 1 / (s + 1) - (-1) / s ^ 2 - 0 / (s + 1) ^ 2) (c + y * I) := by
    intro y
    have h0 : (c : ℂ) + y * I ≠ 0 := ne_zero_of_re_pos (by rw [line_re]; exact hc)
    have h1 : (c : ℂ) + y * I + 1 ≠ 0 :=
      ne_zero_of_re_pos (by rw [Complex.add_re, line_re]; simp; linarith)
    simp only
    field_simp
    ring
  rw [mellinInv_congr_line (F := fun s : ℂ => 1 / (s ^ 2 * (s + 1)))
    (G := fun s : ℂ => (-1) / s + 1 / (s + 1) - (-1) / s ^ 2 - 0 / (s + 1) ^ 2) hline,
    mellinInv_iocLog (-1) 1 (-1) 0 hc (by ring) hx
      (VerticalIntegrable.congr_line hline (verticalIntegrable_kernel_sq hc))]
  split_ifs with h
  · rw [iocLog_of_mem ⟨hx, h⟩]; ring
  · rw [iocLog_of_one_lt (not_le.mp h)]

/-- `(1/2π)∫ x^{-s}/(s(s+1)²) dy = (1 - x + x log x)·1_{x ≤ 1}` (`c > 0`, `x > 0`). -/
theorem mellinInv_kernel_add_one_sq {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    mellinInv c (fun s => 1 / (s * (s + 1) ^ 2)) x
      = if x ≤ 1 then 1 - (x : ℂ) + x * (Real.log x : ℂ) else 0 := by
  have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s * (s + 1) ^ 2)) (c + y * I)
      = (fun s : ℂ => 1 / s + (-1) / (s + 1) - 0 / s ^ 2 - 1 / (s + 1) ^ 2) (c + y * I) := by
    intro y
    have h0 : (c : ℂ) + y * I ≠ 0 := ne_zero_of_re_pos (by rw [line_re]; exact hc)
    have h1 : (c : ℂ) + y * I + 1 ≠ 0 :=
      ne_zero_of_re_pos (by rw [Complex.add_re, line_re]; simp; linarith)
    simp only
    field_simp
    ring
  rw [mellinInv_congr_line (F := fun s : ℂ => 1 / (s * (s + 1) ^ 2))
    (G := fun s : ℂ => 1 / s + (-1) / (s + 1) - 0 / s ^ 2 - 1 / (s + 1) ^ 2) hline,
    mellinInv_iocLog 1 (-1) 0 1 hc (by ring) hx
      (VerticalIntegrable.congr_line hline (verticalIntegrable_kernel_add_one_sq hc))]
  split_ifs with h
  · rw [iocLog_of_mem ⟨hx, h⟩]; ring
  · rw [iocLog_of_one_lt (not_le.mp h)]

end DetPrimality.Bach
