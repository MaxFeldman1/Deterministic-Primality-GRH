import Mathlib

/-!
# Perron / Mellin inversion for the kernel `1/(s(s+1))` and its partial-fraction relatives

All results in this file are fully proved.

* `mellinInv_ioc3` : generic Mellin inversion for `t ↦ (A + B t + C t^{-w}) 1_{(0,1]}(t)`,
  whose Mellin transform is `A/s + B/(s+1) + C/(s-w)` (needs `A + B + C = 0` for continuity).
* `mellinInv_kernel` : `(1/2π) ∫ x^{-(c+iy)} / ((c+iy)(c+iy+1)) dy = (1 - x)₊`  (`c > 0`, `x > 0`).
* `mellinInv_kernel_inv_sub` : the same with the extra factor `1/(s-w)`
  (`Re w < c`, `w ∉ {0,-1}`): value `(-1/w + x/(w+1) + x^{-w}/(w(w+1)))·1_{x ≤ 1}`.
* `verticalIntegrable_kernel`, `verticalIntegrable_kernel_inv_sub`.
-/

open Complex Set MeasureTheory Filter Topology

namespace DetPrimality.Bach

/-- The model function `(A + B t + C t^{-w}) · 1_{(0,1]}(t)`. -/
noncomputable def ioc3 (A B C w : ℂ) : ℝ → ℂ := fun t =>
  A • indicator (Ioc 0 1) (fun _ : ℝ => (1 : ℂ)) t
    + B • indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (1 : ℂ)) t
    + C • indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (-w)) t

theorem ioc3_of_mem {A B C w : ℂ} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ioc3 A B C w t = A + B * t + C * (t : ℂ) ^ (-w) := by
  simp only [ioc3, indicator_of_mem ht, smul_eq_mul, mul_one, cpow_one]

theorem ioc3_of_one_lt {A B C w : ℂ} {t : ℝ} (ht : 1 < t) : ioc3 A B C w t = 0 := by
  have : t ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.2]
  simp only [ioc3, indicator_of_notMem this, smul_zero, add_zero]

theorem hasMellin_ioc3 (A B C w : ℂ) {s : ℂ} (hs : 0 < s.re) (hsw : w.re < s.re) :
    HasMellin (ioc3 A B C w) s (A / s + B / (s + 1) + C / (s - w)) := by
  obtain ⟨h1c, h1⟩ := hasMellin_one_Ioc hs
  obtain ⟨h2c, h2⟩ := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  obtain ⟨h3c, h3⟩ := hasMellin_cpow_Ioc (-w) (s := s) (by simp; linarith)
  have a1 := hasMellin_const_smul h1c A
  have a2 := hasMellin_const_smul h2c B
  have a3 := hasMellin_const_smul h3c C
  have a12 := hasMellin_add a1.1 a2.1
  have a123 := hasMellin_add a12.1 a3.1
  refine ⟨a123.1, ?_⟩
  have key := a123.2
  rw [a12.2, a1.2, a2.2, a3.2, h1, h2, h3] at key
  refine key.trans ?_
  simp only [smul_eq_mul, sub_eq_add_neg]
  ring

/-- If `A + B + C = 0` then `ioc3 A B C w` is continuous on `(0, ∞)`. -/
theorem continuousAt_ioc3 {A B C w : ℂ} (hABC : A + B + C = 0) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (ioc3 A B C w) x := by
  set g : ℝ → ℂ := fun u => A + B * u + C * (u : ℂ) ^ (-w) with hg
  have hu : 0 < min x 1 := lt_min hx one_pos
  have hgc : ContinuousAt g (min x 1) := by
    have h3 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-w)) (min x 1) :=
      continuousAt_ofReal_cpow_const _ _ (Or.inr hu.ne')
    exact (continuousAt_const.add (continuousAt_const.mul
      Complex.continuous_ofReal.continuousAt)).add (continuousAt_const.mul h3)
  have hmin : ContinuousAt (fun t : ℝ => min t 1) x :=
    (continuous_id.min continuous_const).continuousAt
  have hcomp : ContinuousAt (fun t : ℝ => g (min t 1)) x :=
    ContinuousAt.comp (f := fun t : ℝ => min t 1) hgc hmin
  refine hcomp.congr ?_
  filter_upwards [eventually_gt_nhds hx] with t ht
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1, ioc3_of_mem ⟨ht, ht1⟩]
  · push Not at ht1
    rw [min_eq_right ht1.le, ioc3_of_one_lt ht1, hg]
    simp only [ofReal_one, one_cpow, mul_one]
    exact hABC

/-- `mellinInv` only sees the values of `F` on the line `Re s = c`. -/
theorem mellinInv_congr_line {F G : ℂ → ℂ} {c : ℝ} (h : ∀ y : ℝ, F (c + y * I) = G (c + y * I))
    (x : ℝ) : mellinInv c F x = mellinInv c G x := by
  unfold mellinInv
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [h y]

theorem VerticalIntegrable.congr_line {F G : ℂ → ℂ} {c : ℝ}
    (h : ∀ y : ℝ, F (c + y * I) = G (c + y * I)) (hF : VerticalIntegrable F c) :
    VerticalIntegrable G c := by
  unfold VerticalIntegrable at *
  exact hF.congr (Eventually.of_forall fun y => h y)

/-- Generic Mellin inversion for `ioc3`. -/
theorem mellinInv_ioc3 (A B C w : ℂ) {c : ℝ} (hc : 0 < c) (hw : w.re < c) (hABC : A + B + C = 0)
    {x : ℝ} (hx : 0 < x)
    (hint : VerticalIntegrable (fun s => A / s + B / (s + 1) + C / (s - w)) c) :
    mellinInv c (fun s => A / s + B / (s + 1) + C / (s - w)) x = ioc3 A B C w x := by
  have hline : ∀ y : ℝ, (fun s => A / s + B / (s + 1) + C / (s - w)) (c + y * I)
      = mellin (ioc3 A B C w) (c + y * I) := by
    intro y
    have hre : ((c : ℂ) + y * I).re = c := by simp
    exact ((hasMellin_ioc3 A B C w (by rw [hre]; exact hc) (by rw [hre]; exact hw)).2).symm
  rw [mellinInv_congr_line hline]
  have hre : ((c : ℂ)).re = c := by simp
  refine mellinInv_mellin_eq c (ioc3 A B C w) hx
    (hasMellin_ioc3 A B C w (by rw [hre]; exact hc) (by rw [hre]; exact hw)).1
    (VerticalIntegrable.congr_line hline hint) (continuousAt_ioc3 hABC hx)

/-! ### Integrability on vertical lines -/

theorem integrable_of_le_div_sq {f : ℝ → ℂ} (hf : Continuous f) {c M : ℝ} (hc : 0 < c)
    (hM : ∀ y : ℝ, ‖f y‖ ≤ M / (c ^ 2 + y ^ 2)) : Integrable f := by
  set m := min (c ^ 2) 1 with hmdef
  have hm : 0 < m := lt_min (by positivity) one_pos
  have hM0 : 0 ≤ M := by
    have h := (norm_nonneg (f 0)).trans (hM 0)
    have : (0 : ℝ) < c ^ 2 + 0 ^ 2 := by positivity
    exact (div_nonneg_iff.mp h).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr this))
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (M / m))
    hf.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  refine (hM y).trans ?_
  have h1 : m * (1 + y ^ 2) ≤ c ^ 2 + y ^ 2 := by
    have : m ≤ c ^ 2 := min_le_left _ _
    have : m ≤ 1 := min_le_right _ _
    nlinarith [sq_nonneg y]
  calc M / (c ^ 2 + y ^ 2) ≤ M / (m * (1 + y ^ 2)) :=
        div_le_div_of_nonneg_left hM0 (by positivity) h1
    _ = M / m * (1 + y ^ 2)⁻¹ := by field_simp

theorem normSq_line (c y : ℝ) : ‖(c : ℂ) + y * I‖ ^ 2 = c ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro h; rw [h, zero_re] at hz; exact lt_irrefl _ hz

theorem line_re (c y : ℝ) : ((c : ℂ) + y * I).re = c := by simp

theorem norm_line_le_norm_line_add_one {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ‖(c : ℂ) + y * I‖ ≤ ‖(c : ℂ) + y * I + 1‖ := by
  have h1 := normSq_line c y
  have h2 := normSq_line (c + 1) y
  rw [show ((c + 1 : ℝ) : ℂ) + y * I = (c : ℂ) + y * I + 1 by push_cast; ring] at h2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [h1, h2]; nlinarith

theorem norm_kernel_le {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ‖1 / (((c : ℂ) + y * I) * ((c : ℂ) + y * I + 1))‖ ≤ 1 / (c ^ 2 + y ^ 2) := by
  set s : ℂ := (c : ℂ) + y * I
  have hs : 0 < ‖s‖ := lt_of_lt_of_le (by rw [line_re]; exact hc) (Complex.re_le_norm s)
  have hs1 := norm_line_le_norm_line_add_one hc y
  rw [← normSq_line c y, norm_div, norm_one, norm_mul]
  refine one_div_le_one_div_of_le (by positivity) ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left hs1 hs.le

theorem norm_kernel_inv_sub_le {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : w.re < c) (y : ℝ) :
    ‖1 / (((c : ℂ) + y * I) * ((c : ℂ) + y * I + 1) * ((c : ℂ) + y * I - w))‖
      ≤ (1 / (c - w.re)) / (c ^ 2 + y ^ 2) := by
  set s : ℂ := (c : ℂ) + y * I
  have hsw : c - w.re ≤ ‖s - w‖ := by
    have := Complex.re_le_norm (s - w)
    rw [Complex.sub_re, line_re] at this
    exact this
  have hcw : 0 < c - w.re := by linarith
  have h1 := norm_kernel_le hc y
  rw [show 1 / (s * (s + 1) * (s - w)) = 1 / (s * (s + 1)) * (1 / (s - w)) by
    rw [one_div_mul_one_div]]
  rw [norm_mul]
  have h2 : ‖1 / (s - w)‖ ≤ 1 / (c - w.re) := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hcw hsw
  calc ‖1 / (s * (s + 1))‖ * ‖1 / (s - w)‖ ≤ 1 / (c ^ 2 + y ^ 2) * (1 / (c - w.re)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (1 / (c - w.re)) / (c ^ 2 + y ^ 2) := by ring

theorem verticalIntegrable_kernel {c : ℝ} (hc : 0 < c) :
    VerticalIntegrable (fun s : ℂ => 1 / (s * (s + 1))) c := by
  unfold VerticalIntegrable
  refine integrable_of_le_div_sq ?_ hc (norm_kernel_le hc)
  refine Continuous.div continuous_const (by fun_prop) (fun y => ?_)
  exact mul_ne_zero (ne_zero_of_re_pos (by rw [line_re]; exact hc))
    (ne_zero_of_re_pos (by rw [Complex.add_re, line_re]; simp; linarith))

theorem verticalIntegrable_kernel_inv_sub {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : w.re < c) :
    VerticalIntegrable (fun s : ℂ => 1 / (s * (s + 1) * (s - w))) c := by
  unfold VerticalIntegrable
  refine integrable_of_le_div_sq ?_ hc (norm_kernel_inv_sub_le hc hw)
  refine Continuous.div continuous_const (by fun_prop) (fun y => ?_)
  refine mul_ne_zero (mul_ne_zero (ne_zero_of_re_pos (by rw [line_re]; exact hc))
    (ne_zero_of_re_pos (by rw [Complex.add_re, line_re]; simp; linarith)))
    (ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith))

/-! ### The Perron kernel -/

/-- **Perron kernel.** For `c > 0`, `x > 0`:
`(1/2π) ∫ x^{-(c+iy)} / ((c+iy)(c+iy+1)) dy = (1 - x)₊`. -/
theorem mellinInv_kernel {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    mellinInv c (fun s => 1 / (s * (s + 1))) x = if x ≤ 1 then ((1 - x : ℝ) : ℂ) else 0 := by
  have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s * (s + 1))) (c + y * I)
      = (fun s : ℂ => 1 / s + (-1) / (s + 1) + 0 / (s - 0)) (c + y * I) := by
    intro y
    have h0 : (c : ℂ) + y * I ≠ 0 := ne_zero_of_re_pos (by rw [line_re]; exact hc)
    have h1 : (c : ℂ) + y * I + 1 ≠ 0 :=
      ne_zero_of_re_pos (by rw [Complex.add_re, line_re]; simp; linarith)
    simp only
    field_simp
    ring
  rw [mellinInv_congr_line (F := fun s : ℂ => 1 / (s * (s + 1)))
    (G := fun s : ℂ => 1 / s + (-1) / (s + 1) + 0 / (s - 0)) hline,
    mellinInv_ioc3 1 (-1) 0 0 hc (by simp [hc]) (by ring) hx
    (VerticalIntegrable.congr_line hline (verticalIntegrable_kernel hc))]
  split_ifs with h
  · rw [ioc3_of_mem ⟨hx, h⟩]; push_cast; ring
  · rw [ioc3_of_one_lt (not_le.mp h)]

/-- **Kernel times `1/(s-w)`.** For `c > 0`, `Re w < c`, `w ≠ 0, -1`, `x > 0`. -/
theorem mellinInv_kernel_inv_sub {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : w.re < c) (hw0 : w ≠ 0)
    (hw1 : w + 1 ≠ 0) {x : ℝ} (hx : 0 < x) :
    mellinInv c (fun s => 1 / (s * (s + 1) * (s - w))) x
      = if x ≤ 1 then -1 / w + x / (w + 1) + (x : ℂ) ^ (-w) / (w * (w + 1)) else 0 := by
  have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s * (s + 1) * (s - w))) (c + y * I)
      = (fun s : ℂ => (-1 / w) / s + (1 / (w + 1)) / (s + 1) + (1 / (w * (w + 1))) / (s - w))
        (c + y * I) := by
    intro y
    have h0 : (c : ℂ) + y * I ≠ 0 := ne_zero_of_re_pos (by rw [line_re]; exact hc)
    have h1 : (c : ℂ) + y * I + 1 ≠ 0 :=
      ne_zero_of_re_pos (by rw [Complex.add_re, line_re]; simp; linarith)
    have h2 : (c : ℂ) + y * I - w ≠ 0 :=
      ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith)
    simp only
    field_simp
    ring
  have hABC : -1 / w + 1 / (w + 1) + 1 / (w * (w + 1)) = 0 := by
    field_simp; ring
  rw [mellinInv_congr_line (F := fun s : ℂ => 1 / (s * (s + 1) * (s - w)))
    (G := fun s : ℂ => (-1 / w) / s + (1 / (w + 1)) / (s + 1) + (1 / (w * (w + 1))) / (s - w))
    hline, mellinInv_ioc3 _ _ _ w hc hw hABC hx
    (VerticalIntegrable.congr_line hline (verticalIntegrable_kernel_inv_sub hc hw))]
  split_ifs with h
  · rw [ioc3_of_mem ⟨hx, h⟩]; ring
  · rw [ioc3_of_one_lt (not_le.mp h)]

end DetPrimality.Bach
