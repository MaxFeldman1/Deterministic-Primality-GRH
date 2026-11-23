import DetPrimality.Bach.LLSPerron
import DetPrimality.Bach.ExplicitZeros
import DetPrimality.Bach.R11ChiDefs

/-!
# Perron integrals with kernel `y^s / s^{j+1}` (designB (F3)) — reusable infrastructure

`r11Chi_perron j g y = (1/2πi) ∫_{(2)} g(s) y^s / s^{j+1} ds` (a Mellin inverse at `1/y`).

* linearity: `r11Chi_perron_add/sub/const_mul/const/congr_line`;
* integrability: `r11Chi_vi_of_bound`, `r11Chi_vi_const`, `r11Chi_vi_inv_sub`;
* `r11Chi_perron_one`     : `P_j[1](y) = log^j y / j!`  (`j ≥ 1`, `y ≥ 1`);
* `r11Chi_perron_inv_sub` : `P_j[1/(s-w)](y) = y^w/w^{j+1} - ∑_{i ≤ j} (log^i y / i!) / w^{j+1-i}`
  (`Re w < 2`, `w ≠ 0`, `y ≥ 1`)  — the residue formula (F3);
* `r11Chi_perron_LSeries` : `P_j[LSeries f](y) = ∑_{n < y} f(n) log^j(y/n) / j!` whenever
  `LSeriesSummable f 2`;
* `r11Chi_perron_hasSum_of_dom` : termwise integration under a product domination;
* `r11Chi_perron_hasSum_poles`  : termwise integration of `∑_i c_i (1/(s-w_i) - 1/(2-w_i))`,
  `Re w_i ≤ 3/2`, `∑ |c_i| / (1+|w_i|)² < ∞`, `j ≥ 3` (any index type).
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology Asymptotics

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `r11Chi_perron j g y = (1/2πi) ∫_{(2)} g(s) y^s / s^{j+1} ds`. -/
noncomputable def r11Chi_perron (j : ℕ) (g : ℂ → ℂ) (y : ℝ) : ℂ :=
  mellinInv 2 (fun s => g s / s ^ (j + 1)) y⁻¹

/-! ## Linearity -/

theorem r11Chi_perron_add {j : ℕ} {f g : ℂ → ℂ}
    (hf : VerticalIntegrable (fun s => f s / s ^ (j + 1)) 2)
    (hg : VerticalIntegrable (fun s => g s / s ^ (j + 1)) 2) {y : ℝ} (hy : 0 < y) :
    r11Chi_perron j (fun s => f s + g s) y = r11Chi_perron j f y + r11Chi_perron j g y := by
  unfold r11Chi_perron
  rw [show (fun s : ℂ => (f s + g s) / s ^ (j + 1))
      = fun s => f s / s ^ (j + 1) + g s / s ^ (j + 1) from funext fun s => add_div _ _ _]
  exact mellinInv_add hf hg (inv_pos.mpr hy)

theorem r11Chi_perron_sub {j : ℕ} {f g : ℂ → ℂ}
    (hf : VerticalIntegrable (fun s => f s / s ^ (j + 1)) 2)
    (hg : VerticalIntegrable (fun s => g s / s ^ (j + 1)) 2) {y : ℝ} (hy : 0 < y) :
    r11Chi_perron j (fun s => f s - g s) y = r11Chi_perron j f y - r11Chi_perron j g y := by
  unfold r11Chi_perron
  rw [show (fun s : ℂ => (f s - g s) / s ^ (j + 1))
      = fun s => f s / s ^ (j + 1) - g s / s ^ (j + 1) from funext fun s => sub_div _ _ _]
  exact mellinInv_sub hf hg (inv_pos.mpr hy)

theorem r11Chi_perron_const_mul (j : ℕ) (c : ℂ) (g : ℂ → ℂ) (y : ℝ) :
    r11Chi_perron j (fun s => c * g s) y = c * r11Chi_perron j g y := by
  unfold r11Chi_perron
  rw [← mellinInv_const_mul]
  congr 1
  funext s
  ring

theorem r11Chi_perron_const (j : ℕ) (c : ℂ) (y : ℝ) :
    r11Chi_perron j (fun _ => c) y = c * r11Chi_perron j (fun _ => 1) y := by
  rw [← r11Chi_perron_const_mul]
  simp

theorem r11Chi_perron_congr_line {j : ℕ} {f g : ℂ → ℂ}
    (h : ∀ t : ℝ, f ((2 : ℝ) + t * I) = g ((2 : ℝ) + t * I)) (y : ℝ) :
    r11Chi_perron j f y = r11Chi_perron j g y := by
  unfold r11Chi_perron
  exact mellinInv_congr_line (fun t => by simp only [h t]) _

/-! ## The kernel on the line `Re s = 2` -/

theorem r11Chi_norm_kernel_le {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    ‖1 / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖ ≤ 1 / ((2 : ℝ) ^ 2 + t ^ 2) := by
  have h2 := llsPer_two_le_norm_line t
  rw [norm_div, norm_one, norm_pow, ← normSq_line]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by linarith) (by omega)

/-- A function bounded and continuous on the line is integrable against `1/s^{j+1}`, `j ≥ 1`. -/
theorem r11Chi_vi_of_bound {j : ℕ} (hj : 1 ≤ j) {g : ℂ → ℂ} {M : ℝ}
    (hc : Continuous fun t : ℝ => g (((2 : ℝ) : ℂ) + t * I))
    (hM : ∀ t : ℝ, ‖g (((2 : ℝ) : ℂ) + t * I)‖ ≤ M) :
    VerticalIntegrable (fun s => g s / s ^ (j + 1)) 2 := by
  unfold VerticalIntegrable
  refine integrable_of_le_div_sq (M := M) ?_ two_pos (fun t => ?_)
  · exact hc.div (by fun_prop) (fun t => pow_ne_zero _ (llsPer_line_ne t))
  · have hk := r11Chi_norm_kernel_le hj t
    have hg := hM t
    rw [norm_div, norm_one] at hk
    show ‖g (((2 : ℝ) : ℂ) + t * I) / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖
      ≤ M / ((2 : ℝ) ^ 2 + t ^ 2)
    rw [norm_div]
    calc ‖g (((2 : ℝ) : ℂ) + t * I)‖ / ‖(((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖
        = ‖g (((2 : ℝ) : ℂ) + t * I)‖ * (1 / ‖(((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖) := by ring
      _ ≤ M * (1 / ((2 : ℝ) ^ 2 + t ^ 2)) :=
          mul_le_mul hg hk (by positivity) ((norm_nonneg _).trans hg)
      _ = M / ((2 : ℝ) ^ 2 + t ^ 2) := by ring

theorem r11Chi_vi_const {j : ℕ} (hj : 1 ≤ j) (c : ℂ) :
    VerticalIntegrable (fun s : ℂ => c / s ^ (j + 1)) 2 :=
  r11Chi_vi_of_bound hj (g := fun _ => c) (M := ‖c‖) continuous_const (fun _ => le_rfl)

theorem r11Chi_vi_inv_sub {j : ℕ} (hj : 1 ≤ j) {w : ℂ} (hw : w.re < 2) :
    VerticalIntegrable (fun s : ℂ => 1 / (s - w) / s ^ (j + 1)) 2 := by
  have hne : ∀ t : ℝ, ((2 : ℝ) : ℂ) + t * I - w ≠ 0 := fun t =>
    ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith)
  refine r11Chi_vi_of_bound hj (g := fun s => 1 / (s - w)) (M := 1 / (2 - w.re)) ?_ (fun t => ?_)
  · exact Continuous.div continuous_const (by fun_prop) hne
  · have hsw : 2 - w.re ≤ ‖((2 : ℝ) : ℂ) + t * I - w‖ := by
      have := Complex.re_le_norm (((2 : ℝ) : ℂ) + t * I - w)
      rw [Complex.sub_re, line_re] at this
      exact this
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by linarith) hsw

/-! ## Mellin transform of `log^n t · 1_{(0,1]}` -/

/-- `(log t)^n · 1_{(0,1]}(t)`. -/
noncomputable def r11Chi_logn (n : ℕ) : ℝ → ℂ := fun t => (Real.log t ^ n : ℝ) • ind1 t

theorem r11Chi_logn_of_mem {n : ℕ} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    r11Chi_logn n t = (Real.log t : ℂ) ^ n := by
  simp only [r11Chi_logn, ind1, indicator_of_mem ht, Complex.real_smul]
  push_cast
  ring

theorem r11Chi_logn_of_one_lt {n : ℕ} {t : ℝ} (ht : 1 < t) : r11Chi_logn n t = 0 := by
  simp [r11Chi_logn, ind1_of_one_lt ht]

theorem r11Chi_hasMellin_logn (n : ℕ) : ∀ {s : ℂ}, 0 < s.re →
    HasMellin (r11Chi_logn n) s ((-1) ^ n * (n.factorial : ℂ) / s ^ (n + 1)) := by
  induction n with
  | zero =>
    intro s hs
    have h := hasMellin_one_Ioc hs
    have e : r11Chi_logn 0 = indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ) := by
      funext t; simp [r11Chi_logn, ind1]
    rw [e]
    simpa using h
  | succ n ih =>
    intro s hs
    have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
    set b : ℝ := s.re / 2 with hbdef
    have hb : 0 < b := by positivity
    have hloc : LocallyIntegrableOn (r11Chi_logn n) (Ioi 0) := by
      have h := (ih (s := 1) (by simp)).1
      simp only [MellinConvergent, sub_self, cpow_zero, one_smul] at h
      exact h.locallyIntegrableOn
    have htop : (r11Chi_logn n) =O[atTop] (fun t : ℝ => t ^ (-(s.re + 1))) := by
      have : (fun _ : ℝ => (0 : ℂ)) =ᶠ[atTop] r11Chi_logn n := by
        filter_upwards [eventually_gt_atTop 1] with t ht
        rw [r11Chi_logn_of_one_lt ht]
      exact (isBigO_zero _ _).congr' this EventuallyEq.rfl
    set c : ℝ := b / (n + 1) with hcdef
    have hc : 0 < c := by positivity
    have hbot : (r11Chi_logn n) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
      refine IsBigO.of_bound ((1 / c) ^ n) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (0 : ℝ) < t := ht
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
      by_cases h1 : t ≤ 1
      · rw [r11Chi_logn_of_mem ⟨ht0, h1⟩, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (Real.log_nonpos ht0.le h1)]
        have h2 := Real.log_le_rpow_div (inv_nonneg.mpr ht0.le) hc
        rw [Real.log_inv, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le] at h2
        have h3 : (t ^ (-c)) ^ n ≤ t ^ (-b) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
          apply Real.rpow_le_rpow_of_exponent_ge ht0 h1
          have : c * n ≤ b := by
            rw [hcdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [hb, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          linarith
        calc (-Real.log t) ^ n ≤ (t ^ (-c) / c) ^ n :=
              pow_le_pow_left₀ (by linarith [Real.log_nonpos ht0.le h1]) h2 n
          _ = (1 / c) ^ n * (t ^ (-c)) ^ n := by rw [div_pow, one_div, inv_pow]; ring
          _ ≤ (1 / c) ^ n * t ^ (-b) := mul_le_mul_of_nonneg_left h3 (by positivity)
      · rw [not_le] at h1
        rw [r11Chi_logn_of_one_lt h1, norm_zero]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg ht0.le _)
    obtain ⟨hcv, hd⟩ := mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := b) hloc htop
      (by linarith) hbot (by rw [hbdef]; linarith)
    have hrec : (fun t => Real.log t • r11Chi_logn n t) = r11Chi_logn (n + 1) := by
      funext t
      simp only [r11Chi_logn, smul_smul]
      rw [pow_succ']
    rw [hrec] at hcv hd
    have hev : mellin (r11Chi_logn n)
        =ᶠ[𝓝 s] fun z => (-1) ^ n * (n.factorial : ℂ) / z ^ (n + 1) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
      exact (ih hz).2
    have hd2 : HasDerivAt (mellin (r11Chi_logn n))
        ((-1) ^ (n + 1) * ((n + 1).factorial : ℂ) / s ^ (n + 1 + 1)) s := by
      have h := (hasDerivAt_const s ((-1) ^ n * (n.factorial : ℂ))).div
        (hasDerivAt_pow (n + 1) s) (pow_ne_zero _ hs0)
      have h' : HasDerivAt (fun z : ℂ => (-1) ^ n * (n.factorial : ℂ) / z ^ (n + 1))
          ((-1) ^ (n + 1) * ((n + 1).factorial : ℂ) / s ^ (n + 1 + 1)) s := by
        refine h.congr_deriv ?_
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
      exact h'.congr_of_eventuallyEq hev
    exact ⟨hcv, hd.unique hd2⟩

theorem r11Chi_continuousAt_logn {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (r11Chi_logn n) x := by
  set g : ℝ → ℂ := fun u => ((Real.log u : ℝ) : ℂ) ^ n with hg
  have hu : 0 < min x 1 := lt_min hx one_pos
  have hgc : ContinuousAt g (min x 1) :=
    (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hu.ne')).pow n
  have hmin : ContinuousAt (fun t : ℝ => min t 1) x :=
    (continuous_id.min continuous_const).continuousAt
  have hcomp : ContinuousAt (fun t : ℝ => g (min t 1)) x :=
    ContinuousAt.comp (f := fun t : ℝ => min t 1) hgc hmin
  refine hcomp.congr ?_
  filter_upwards [eventually_gt_nhds hx] with t ht
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1, r11Chi_logn_of_mem ⟨ht, ht1⟩]
  · push Not at ht1
    rw [min_eq_right ht1.le, r11Chi_logn_of_one_lt ht1, hg]
    simp [show n ≠ 0 by omega]

/-- `(1/2π)∫ x^{-s}/s^{n+1} dt = (-log x)^n/n! · 1_{x ≤ 1}` (`n ≥ 1`). -/
theorem r11Chi_mellinInv_pow {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s : ℂ => 1 / s ^ (n + 1)) x
      = if x ≤ 1 then (-(Real.log x : ℂ)) ^ n / (n.factorial : ℂ) else 0 := by
  set a : ℂ := (-1) ^ n * (n.factorial : ℂ) with ha
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have ha0 : a ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hfac
  have hinv : 1 / a = (-1) ^ n / (n.factorial : ℂ) := by
    rw [ha, div_eq_div_iff ha0 hfac, ← mul_assoc, ← mul_pow]
    norm_num
  have hline : ∀ t : ℝ, (fun s : ℂ => a / s ^ (n + 1)) (((2 : ℝ) : ℂ) + t * I)
      = mellin (r11Chi_logn n) (((2 : ℝ) : ℂ) + t * I) := fun t =>
    ((r11Chi_hasMellin_logn n (by rw [line_re]; norm_num)).2).symm
  have hre : (((2 : ℝ) : ℂ)).re = 2 := by simp
  have h2 : mellinInv 2 (fun s : ℂ => a / s ^ (n + 1)) x = r11Chi_logn n x := by
    rw [mellinInv_congr_line hline]
    exact mellinInv_mellin_eq 2 (r11Chi_logn n) hx
      (r11Chi_hasMellin_logn n (by rw [hre]; norm_num)).1
      (VerticalIntegrable.congr_line hline (r11Chi_vi_const hn a))
      (r11Chi_continuousAt_logn hn hx)
  rw [show (fun s : ℂ => 1 / s ^ (n + 1)) = fun s => (1 / a) * (a / s ^ (n + 1)) by
    funext s; field_simp, mellinInv_const_mul, h2, hinv]
  split_ifs with h
  · rw [r11Chi_logn_of_mem ⟨hx, h⟩, neg_pow]
    ring
  · rw [r11Chi_logn_of_one_lt (not_le.mp h)]; ring

/-! ## Residues -/

/-- `P_j[1](y) = log^j y / j!`. -/
theorem r11Chi_perron_one {j : ℕ} (hj : 1 ≤ j) {y : ℝ} (hy : 1 ≤ y) :
    r11Chi_perron j (fun _ => 1) y = (Real.log y : ℂ) ^ j / (j.factorial : ℂ) := by
  have hy0 : 0 < y := by linarith
  unfold r11Chi_perron
  rw [r11Chi_mellinInv_pow hj (inv_pos.mpr hy0), if_pos (inv_le_one_of_one_le₀ hy), Real.log_inv]
  push_cast
  rw [neg_neg]

/-- **Residue formula (F3).** For `Re w < 2`, `w ≠ 0`, `y ≥ 1`, `j ≥ 1`:
`P_j[1/(s-w)](y) = y^w / w^{j+1} - ∑_{i=0}^{j} (log^i y / i!) / w^{j+1-i}`. -/
theorem r11Chi_perron_inv_sub {j : ℕ} (hj : 1 ≤ j) {w : ℂ} (hw : w.re < 2) (hw0 : w ≠ 0)
    {y : ℝ} (hy : 1 ≤ y) :
    r11Chi_perron j (fun s => 1 / (s - w)) y
      = (y : ℂ) ^ w / w ^ (j + 1)
        - ∑ i ∈ Finset.range (j + 1),
            (Real.log y : ℂ) ^ i / (i.factorial : ℂ) / w ^ (j + 1 - i) := by
  have hy0 : 0 < y := by linarith
  induction j, hj using Nat.le_induction with
  | base =>
    have h := llsPer_perronL_inv_sub hw hw0 hy
    have e : r11Chi_perron 1 (fun s => 1 / (s - w)) y
        = llsPer_perronL (fun s => 1 / (s - w)) y := rfl
    rw [e, h, Finset.sum_range_succ, Finset.sum_range_one]
    simp
    ring
  | succ j hj ih =>
    have hline : ∀ t : ℝ, (fun s : ℂ => 1 / (s - w) / s ^ (j + 1 + 1)) (((2 : ℝ) : ℂ) + t * I)
        = (fun s : ℂ => (1 / w) * (1 / (s - w) / s ^ (j + 1) - 1 / s ^ (j + 1 + 1)))
          (((2 : ℝ) : ℂ) + t * I) := by
      intro t
      have h0 := llsPer_line_ne t
      have h2 : ((2 : ℝ) : ℂ) + t * I - w ≠ 0 :=
        ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith)
      simp only
      field_simp
      ring
    have e : r11Chi_perron (j + 1) (fun s => 1 / (s - w)) y
        = (1 / w) * (r11Chi_perron j (fun s => 1 / (s - w)) y
          - r11Chi_perron (j + 1) (fun _ => 1) y) := by
      show mellinInv 2 (fun s : ℂ => 1 / (s - w) / s ^ (j + 1 + 1)) y⁻¹
        = (1 / w) * (mellinInv 2 (fun s : ℂ => 1 / (s - w) / s ^ (j + 1)) y⁻¹
          - mellinInv 2 (fun s : ℂ => 1 / s ^ (j + 1 + 1)) y⁻¹)
      rw [mellinInv_congr_line (F := fun s : ℂ => 1 / (s - w) / s ^ (j + 1 + 1))
          (G := fun s : ℂ => (1 / w) * (1 / (s - w) / s ^ (j + 1) - 1 / s ^ (j + 1 + 1))) hline,
        mellinInv_const_mul,
        mellinInv_sub (r11Chi_vi_inv_sub hj hw) (r11Chi_vi_const (by omega) 1)
          (inv_pos.mpr hy0)]
    have hsum : ∑ i ∈ Finset.range (j + 1),
          (Real.log y : ℂ) ^ i / (i.factorial : ℂ) / w ^ (j + 1 + 1 - i)
        = (1 / w) * ∑ i ∈ Finset.range (j + 1),
          (Real.log y : ℂ) ^ i / (i.factorial : ℂ) / w ^ (j + 1 - i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show j + 1 + 1 - i = (j + 1 - i) + 1 by omega, pow_succ]
      field_simp
    rw [e, ih, r11Chi_perron_one (by omega) hy, Finset.sum_range_succ _ (j + 1), hsum,
      show j + 1 + 1 - (j + 1) = 1 by omega, pow_one, pow_succ w (j + 1)]
    field_simp
    ring

/-! ## The Perron identity for a Dirichlet series -/

theorem r11Chi_kernel_integral {j : ℕ} (hj : 1 ≤ j) {z : ℝ} (hz : 0 < z) :
    ∫ t : ℝ, (z : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I)) •
        (fun s : ℂ => 1 / s ^ (j + 1)) (((2 : ℝ) : ℂ) + t * I)
      = (2 * Real.pi : ℂ)
        * (if z ≤ 1 then (-(Real.log z : ℂ)) ^ j / (j.factorial : ℂ) else 0) := by
  have h := r11Chi_mellinInv_pow hj hz
  unfold mellinInv at h
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  rw [← h, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_one_div_cancel hpi, one_mul]

/-- **Perron identity** for the kernel `y^s/s^{j+1}` (`j ≥ 1`): if `∑ f(n) n^{-s}` converges
absolutely at `s = 2`, then `(1/2πi)∫_{(2)} L(f,s) y^s/s^{j+1} ds = ∑_{n<y} f(n) log^j(y/n)/j!`. -/
theorem r11Chi_perron_LSeries {j : ℕ} (hj : 1 ≤ j) {f : ℕ → ℂ} (hf : LSeriesSummable f 2)
    {y : ℝ} (hy : 0 < y) :
    r11Chi_perron j (LSeries f) y
      = ∑ n ∈ Finset.range ⌈y⌉₊,
          f n * ((Real.log (y / n) : ℝ) : ℂ) ^ j / (j.factorial : ℂ) := by
  have hj0 : j ≠ 0 := by omega
  set K : ℂ → ℂ := fun s => 1 / s ^ (j + 1) with hK
  set F : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else
    f n * ((((n : ℝ) / y : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I)) • K (((2 : ℝ) : ℂ) + t * I))
    with hFdef
  have hpos : ∀ n : ℕ, n ≠ 0 → 0 < (n : ℝ) / y := fun n hn =>
    div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hy
  have hpt : ∀ t : ℝ, ((y⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I)) •
      (fun s => LSeries f s / s ^ (j + 1)) (((2 : ℝ) : ℂ) + t * I) = ∑' n : ℕ, F n t := by
    intro t
    set s : ℂ := ((2 : ℝ) : ℂ) + t * I with hs
    simp only
    rw [LSeries, smul_eq_mul, ← tsum_div_const, ← tsum_mul_left]
    congr 1
    funext n
    simp only [hFdef]
    split_ifs with hn
    · simp [hn]
    · rw [LSeries.term_of_ne_zero hn, smul_eq_mul, hK]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hcp : (((n : ℝ) / y : ℝ) : ℂ) ^ (-s)
          = ((y⁻¹ : ℝ) : ℂ) ^ (-s) * ((n : ℂ) ^ s)⁻¹ := by
        rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hn0 (inv_nonneg.mpr hy.le),
          cpow_neg, ofReal_natCast]
        ring
      rw [hcp]
      ring
  have hKint : VerticalIntegrable K 2 := r11Chi_vi_const hj 1
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    by_cases hn : n = 0
    · have : F n = fun _ => 0 := by funext t; simp [hFdef, hn]
      rw [this]; exact integrable_zero _ _ _
    · have h := (integrable_mellinInv_integrand hKint (hpos n hn)).const_mul (f n)
      refine h.congr (Eventually.of_forall fun t => ?_)
      simp [hFdef, hn, hK]
  set C : ℝ := ∫ t : ℝ, ‖K (((2 : ℝ) : ℂ) + t * I)‖ with hC
  have hFnorm : ∀ n, ∫ t, ‖F n t‖ = ‖LSeries.term f 2 n‖ * (y ^ 2 * C) := by
    intro n
    by_cases hn : n = 0
    · simp [hFdef, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hpt' : ∀ t : ℝ, ‖F n t‖ = (‖f n‖ * ((n : ℝ) / y) ^ (-(2 : ℝ)))
          * ‖K (((2 : ℝ) : ℂ) + t * I)‖ := by
        intro t
        simp only [hFdef, hn, if_false, norm_mul, norm_smul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos n hn)]
        have : (-(((2 : ℝ) : ℂ) + t * I)).re = -2 := by simp
        rw [this]
        ring
      rw [integral_congr_ae (Eventually.of_forall hpt'), integral_const_mul, ← hC,
        LSeries.norm_term_eq, if_neg hn]
      have h2 : (2 : ℂ).re = 2 := by simp
      rw [h2, Real.rpow_neg (div_nonneg hnpos.le hy.le), Real.div_rpow hnpos.le hy.le,
        Real.rpow_two, Real.rpow_two]
      field_simp
  have hsum : Summable fun n => ∫ t, ‖F n t‖ := by
    have h := (hf.norm).mul_right (y ^ 2 * C)
    refine h.congr fun n => (hFnorm n).symm
  have hint := integral_tsum_of_summable_integral_norm hFint hsum
  have hFn : ∀ n, ∫ t, F n t = if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ)
        * (if (n : ℝ) / y ≤ 1 then (-((Real.log ((n : ℝ) / y) : ℝ) : ℂ)) ^ j / (j.factorial : ℂ)
          else 0)) := by
    intro n
    by_cases hn : n = 0
    · simp [hFdef, hn]
    · simp only [hFdef, hn, if_false]
      rw [integral_const_mul, r11Chi_kernel_integral hj (hpos n hn)]
  unfold r11Chi_perron mellinInv
  rw [integral_congr_ae (Eventually.of_forall hpt), ← hint]
  simp_rw [hFn]
  rw [Complex.real_smul, ← tsum_mul_left]
  have hzero : ∀ n ∉ Finset.range ⌈y⌉₊,
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * (if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ)
        * (if (n : ℝ) / y ≤ 1 then (-((Real.log ((n : ℝ) / y) : ℝ) : ℂ)) ^ j / (j.factorial : ℂ)
          else 0)))) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt, Nat.ceil_le] at hn
    have h1 : 1 ≤ (n : ℝ) / y := (one_le_div hy).mpr hn
    split_ifs with h0 h2
    · simp
    · have : (n : ℝ) / y = 1 := le_antisymm h2 h1
      rw [this, Real.log_one]
      simp [hj0]
    · simp
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hny : (n : ℝ) < y := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  by_cases h0 : n = 0
  · simp [h0, hj0]
  · have hle : (n : ℝ) / y ≤ 1 := by rw [div_le_one hy]; exact hny.le
    have hlog : Real.log ((n : ℝ) / y) = -Real.log (y / n) := by
      rw [← Real.log_inv, inv_div]
    rw [if_neg h0, if_pos hle, hlog]
    push_cast
    field_simp

/-! ## Termwise integration -/

/-- **Termwise integration under a product domination** `‖T_i(s)/s^{j+1}‖ ≤ u_i φ(t)`. -/
theorem r11Chi_perron_hasSum_of_dom {ι : Type*} [Countable ι] (j : ℕ) (T : ι → ℂ → ℂ)
    (hvi : ∀ i, VerticalIntegrable (fun s => T i s / s ^ (j + 1)) 2)
    {u : ι → ℝ} (hu : Summable u) {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hb : ∀ i (t : ℝ), ‖T i (((2 : ℝ) : ℂ) + t * I) / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖
      ≤ u i * φ t)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun i => r11Chi_perron j (T i) y) (r11Chi_perron j (fun s => ∑' i, T i s) y) := by
  set c : ℝ → ℂ := fun t => ((y⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I)) with hc
  set F : ι → ℝ → ℂ := fun i t => c t • (T i (((2 : ℝ) : ℂ) + t * I)
    / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)) with hF
  have hFint : ∀ i, Integrable (F i) := fun i =>
    integrable_mellinInv_integrand (hvi i) (inv_pos.mpr hy)
  have hcn : ∀ t, ‖c t‖ = y ^ 2 := by
    intro t
    simp only [hc]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hy)]
    have hre : (-(((2 : ℝ) : ℂ) + t * I)).re = -2 := by simp
    rw [hre, Real.rpow_neg (inv_nonneg.mpr hy.le), Real.inv_rpow hy.le, inv_inv, Real.rpow_two]
  have hFnorm : ∀ i, ∫ t, ‖F i t‖ ≤ (y ^ 2 * ∫ t, φ t) * u i := by
    intro i
    calc ∫ t, ‖F i t‖ ≤ ∫ t, y ^ 2 * (u i * φ t) := by
          refine integral_mono (hFint i).norm ((hφ.const_mul _).const_mul _) fun t => ?_
          simp only [hF]
          rw [norm_smul, hcn]
          exact mul_le_mul_of_nonneg_left (hb i t) (by positivity)
      _ = (y ^ 2 * ∫ t, φ t) * u i := by
          rw [integral_const_mul, integral_const_mul]; ring
  have hFsum : Summable fun i => ∫ t, ‖F i t‖ :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg fun t => norm_nonneg _) hFnorm
      (hu.mul_left _)
  have hsum := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hpt : ∀ t : ℝ, ∑' i, F i t = c t • ((∑' i, T i (((2 : ℝ) : ℂ) + t * I))
      / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)) := by
    intro t
    simp only [hF, smul_eq_mul]
    rw [tsum_mul_left, tsum_div_const]
  rw [integral_congr_ae (Eventually.of_forall hpt)] at hsum
  exact hsum.const_smul (1 / (2 * Real.pi))

/-- Pointwise bound for one regularised pole on the line `Re s = 2` (`Re w ≤ 3/2`, `j ≥ 3`). -/
theorem r11Chi_pole_bound {j : ℕ} (hj : 3 ≤ j) {w : ℂ} (hw : w.re ≤ 3 / 2) (t : ℝ) :
    ‖(1 / ((((2 : ℝ) : ℂ) + t * I) - w) - 1 / (2 - w)) / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖
      ≤ 49 / 2 / (1 + ‖w‖) ^ 2 * (1 / ((2 : ℝ) ^ 2 + t ^ 2)) := by
  rw [← normSq_line]
  set s : ℂ := ((2 : ℝ) : ℂ) + t * I with hs
  have hsn : 2 ≤ ‖s‖ := llsPer_two_le_norm_line t
  have h1 : 1 / 2 ≤ ‖s - w‖ := by
    have := Complex.re_le_norm (s - w)
    rw [Complex.sub_re, hs, line_re] at this
    linarith
  have h2 : 1 / 2 ≤ ‖2 - w‖ := by
    have := Complex.re_le_norm (2 - w)
    rw [Complex.sub_re] at this
    norm_num at this
    linarith
  have h3 : 1 + ‖w‖ ≤ 7 * ‖2 - w‖ := by
    have : ‖w‖ ≤ ‖2 - w‖ + 2 := by
      calc ‖w‖ = ‖(2 : ℂ) - (2 - w)‖ := by ring_nf
        _ ≤ ‖(2 : ℂ)‖ + ‖2 - w‖ := norm_sub_le _ _
        _ = ‖2 - w‖ + 2 := by rw [Complex.norm_ofNat]; ring
    linarith
  have h4 : 1 + ‖w‖ ≤ 7 / 2 * ‖s‖ * ‖s - w‖ := by
    have : ‖w‖ ≤ ‖s‖ + ‖s - w‖ := by
      calc ‖w‖ = ‖s - (s - w)‖ := by ring_nf
        _ ≤ ‖s‖ + ‖s - w‖ := norm_sub_le _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hsn) (sub_nonneg.mpr h1)]
  have hW : 0 < 1 + ‖w‖ := by positivity
  have hA : 0 < ‖s - w‖ := by linarith
  have hB : 0 < ‖2 - w‖ := by linarith
  have hS : 0 < ‖s‖ := by linarith
  have hsw : s - w ≠ 0 := norm_pos_iff.mp hA
  have h2w : (2 : ℂ) - w ≠ 0 := norm_pos_iff.mp hB
  have hs0 : s ≠ 0 := norm_pos_iff.mp hS
  have ht : |t| ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s
    rwa [hs, show (((2 : ℝ) : ℂ) + t * I).im = t by simp] at this
  have hpow : ‖s‖ ^ 4 ≤ ‖s‖ ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hWW : (1 + ‖w‖) ^ 2 ≤ 49 / 2 * (‖s‖ * ‖s - w‖ * ‖2 - w‖) := by
    calc (1 + ‖w‖) ^ 2 = (1 + ‖w‖) * (1 + ‖w‖) := sq _
      _ ≤ (7 / 2 * ‖s‖ * ‖s - w‖) * (7 * ‖2 - w‖) := mul_le_mul h4 h3 hW.le (by positivity)
      _ = _ := by ring
  have h2s : (2 : ℂ) - s = -(t * I) := by rw [hs]; push_cast; ring
  have hid : (1 / (s - w) - 1 / (2 - w)) / s ^ (j + 1)
      = (-(t * I)) / ((s - w) * (2 - w)) / s ^ (j + 1) := by
    rw [← h2s]
    field_simp
    ring
  rw [hid, norm_div, norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, norm_pow, div_div, div_mul_div_comm, mul_one,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc |t| * ((1 + ‖w‖) ^ 2 * ‖s‖ ^ 2)
      ≤ ‖s‖ * (49 / 2 * (‖s‖ * ‖s - w‖ * ‖2 - w‖) * ‖s‖ ^ 2) := by gcongr
    _ = 49 / 2 * (‖s - w‖ * ‖2 - w‖ * ‖s‖ ^ 4) := by ring
    _ ≤ 49 / 2 * (‖s - w‖ * ‖2 - w‖ * ‖s‖ ^ (j + 1)) := by gcongr

theorem r11Chi_vi_pole {j : ℕ} (hj : 1 ≤ j) {w : ℂ} (hw : w.re < 2) (c : ℂ) :
    VerticalIntegrable (fun s : ℂ => c * (1 / (s - w) - 1 / (2 - w)) / s ^ (j + 1)) 2 := by
  have h := (Integrable.sub (r11Chi_vi_inv_sub hj hw) (r11Chi_vi_const hj (1 / (2 - w)))).const_mul c
  unfold VerticalIntegrable
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply]
  ring

theorem r11Chi_perron_hasSum_poles_aux {ι : Type*} [Countable ι] {j : ℕ} (hj : 3 ≤ j)
    (c w : ι → ℂ) (hw : ∀ i, (w i).re ≤ 3 / 2)
    (hs : Summable fun i => ‖c i‖ / (1 + ‖w i‖) ^ 2) {y : ℝ} (hy : 0 < y) :
    HasSum (fun i => c i * r11Chi_perron j (fun s => 1 / (s - w i) - 1 / (2 - w i)) y)
      (r11Chi_perron j (fun s => ∑' i, c i * (1 / (s - w i) - 1 / (2 - w i))) y) := by
  have h := r11Chi_perron_hasSum_of_dom j (fun i s => c i * (1 / (s - w i) - 1 / (2 - w i)))
    (fun i => r11Chi_vi_pole (by omega) (by linarith [hw i]) (c i))
    (hs.mul_left (49 / 2)) integrable_inv_four_add_sq (fun i t => ?_) hy
  · simpa only [r11Chi_perron_const_mul] using h
  · rw [mul_div_assoc, norm_mul]
    calc ‖c i‖ * ‖(1 / ((((2 : ℝ) : ℂ) + t * I) - w i) - 1 / (2 - w i))
          / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖
        ≤ ‖c i‖ * (49 / 2 / (1 + ‖w i‖) ^ 2 * (1 / ((2 : ℝ) ^ 2 + t ^ 2))) :=
          mul_le_mul_of_nonneg_left (r11Chi_pole_bound hj (hw i) t) (norm_nonneg _)
      _ = 49 / 2 * (‖c i‖ / (1 + ‖w i‖) ^ 2) * (1 / ((2 : ℝ) ^ 2 + t ^ 2)) := by ring

/-- **Termwise integration over a family of poles** (`j ≥ 3`): for any index type, coefficients
`c_i` and poles `w_i` with `Re w_i ≤ 3/2` and `∑ |c_i| / (1+|w_i|)² < ∞`,
`P_j[∑_i c_i (1/(s-w_i) - 1/(2-w_i))] = ∑_i c_i P_j[1/(s-w_i) - 1/(2-w_i)]`. -/
theorem r11Chi_perron_hasSum_poles {ι : Type*} {j : ℕ} (hj : 3 ≤ j) (c w : ι → ℂ)
    (hw : ∀ i, c i ≠ 0 → (w i).re ≤ 3 / 2)
    (hs : Summable fun i => ‖c i‖ / (1 + ‖w i‖) ^ 2) {y : ℝ} (hy : 0 < y) :
    HasSum (fun i => c i * r11Chi_perron j (fun s => 1 / (s - w i) - 1 / (2 - w i)) y)
      (r11Chi_perron j (fun s => ∑' i, c i * (1 / (s - w i) - 1 / (2 - w i))) y) := by
  set S : Set ι := Function.support (fun i => ‖c i‖ / (1 + ‖w i‖) ^ 2) with hSdef
  have : Countable S := hs.countable_support.to_subtype
  have hmem : ∀ i, c i ≠ 0 → i ∈ S := by
    intro i h
    rw [hSdef, Function.mem_support]
    exact div_ne_zero (norm_ne_zero_iff.mpr h) (by positivity)
  have hc0 : ∀ i : S, c i ≠ 0 := by
    intro i h0
    have h2 : (i : ι) ∈ Function.support (fun i => ‖c i‖ / (1 + ‖w i‖) ^ 2) := i.2
    rw [Function.mem_support] at h2
    exact h2 (by simp [h0])
  have h := r11Chi_perron_hasSum_poles_aux hj (fun i : S => c i) (fun i : S => w i)
    (fun i => hw i (hc0 i)) (hs.subtype S) hy
  have e : (fun s : ℂ => ∑' i : S, c i * (1 / (s - w i) - 1 / (2 - w i)))
      = fun s : ℂ => ∑' i, c i * (1 / (s - w i) - 1 / (2 - w i)) := by
    funext s
    refine tsum_subtype_eq_of_support_subset
      (f := fun i => c i * (1 / (s - w i) - 1 / (2 - w i))) ?_
    intro i hi
    apply hmem
    intro h0
    apply hi
    simp [h0]
  rw [e] at h
  refine (hasSum_subtype_iff_of_support_subset
    (f := fun i => c i * r11Chi_perron j (fun s => 1 / (s - w i) - 1 / (2 - w i)) y) ?_).mp h
  intro i hi
  apply hmem
  intro h0
  apply hi
  simp [h0]

/-! ## Integrability of the sums -/

/-- Under the product domination the sum itself is integrable on the line. -/
theorem r11Chi_vi_tsum_of_dom {ι : Type*} [Countable ι] (j : ℕ) (T : ι → ℂ → ℂ)
    (hvi : ∀ i, VerticalIntegrable (fun s => T i s / s ^ (j + 1)) 2)
    {u : ι → ℝ} (hu : Summable u) {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hb : ∀ i (t : ℝ), ‖T i (((2 : ℝ) : ℂ) + t * I) / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖
      ≤ u i * φ t) :
    VerticalIntegrable (fun s => (∑' i, T i s) / s ^ (j + 1)) 2 := by
  unfold VerticalIntegrable
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (∑' i, T i (((2 : ℝ) : ℂ) + t * I))
      / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)) := by
    have h := AEMeasurable.tsum (μ := volume) (L := SummationFilter.unconditional ι)
      (f := fun i (t : ℝ) => T i (((2 : ℝ) : ℂ) + t * I) / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1))
      (fun i => (hvi i).1.aemeasurable)
    refine (h.congr (Eventually.of_forall fun t => ?_)).aestronglyMeasurable
    exact tsum_div_const
  refine Integrable.mono' (hφ.const_mul (∑' i, u i)) hmeas (Eventually.of_forall fun t => ?_)
  show ‖(∑' i, T i (((2 : ℝ) : ℂ) + t * I)) / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖
    ≤ (∑' i, u i) * φ t
  rw [← tsum_div_const]
  have hsn : Summable fun i => ‖T i (((2 : ℝ) : ℂ) + t * I)
      / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i t) (hu.mul_right _)
  calc ‖∑' i, T i (((2 : ℝ) : ℂ) + t * I) / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖
      ≤ ∑' i, ‖T i (((2 : ℝ) : ℂ) + t * I) / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' i, u i * φ t := hsn.tsum_le_tsum (fun i => hb i t) (hu.mul_right _)
    _ = (∑' i, u i) * φ t := tsum_mul_right

/-- The sum over a family of poles is integrable against `1/s^{j+1}` (`j ≥ 3`). -/
theorem r11Chi_vi_poles {ι : Type*} {j : ℕ} (hj : 3 ≤ j) (c w : ι → ℂ)
    (hw : ∀ i, c i ≠ 0 → (w i).re ≤ 3 / 2)
    (hs : Summable fun i => ‖c i‖ / (1 + ‖w i‖) ^ 2) :
    VerticalIntegrable
      (fun s => (∑' i, c i * (1 / (s - w i) - 1 / (2 - w i))) / s ^ (j + 1)) 2 := by
  set S : Set ι := Function.support (fun i => ‖c i‖ / (1 + ‖w i‖) ^ 2) with hSdef
  have : Countable S := hs.countable_support.to_subtype
  have hmem : ∀ i, c i ≠ 0 → i ∈ S := by
    intro i h
    rw [hSdef, Function.mem_support]
    exact div_ne_zero (norm_ne_zero_iff.mpr h) (by positivity)
  have hc0 : ∀ i : S, c i ≠ 0 := by
    intro i h0
    have h2 : (i : ι) ∈ Function.support (fun i => ‖c i‖ / (1 + ‖w i‖) ^ 2) := i.2
    rw [Function.mem_support] at h2
    exact h2 (by simp [h0])
  have h := r11Chi_vi_tsum_of_dom j
    (fun (i : S) s => c i * (1 / (s - w i) - 1 / (2 - w i)))
    (fun i => r11Chi_vi_pole (by omega) (by linarith [hw i (hc0 i)]) (c i))
    ((hs.subtype S).mul_left (49 / 2)) integrable_inv_four_add_sq (fun i t => ?_)
  · have e : ∀ s : ℂ, ∑' i : S, c i * (1 / (s - w i) - 1 / (2 - w i))
        = ∑' i, c i * (1 / (s - w i) - 1 / (2 - w i)) := by
      intro s
      refine tsum_subtype_eq_of_support_subset
        (f := fun i => c i * (1 / (s - w i) - 1 / (2 - w i))) ?_
      intro i hi
      apply hmem
      intro h0
      apply hi
      simp [h0]
    simp only [e] at h
    exact h
  · rw [mul_div_assoc, norm_mul]
    calc ‖c i‖ * ‖(1 / ((((2 : ℝ) : ℂ) + t * I) - w i) - 1 / (2 - w i))
          / (((2 : ℝ) : ℂ) + t * I) ^ (j + 1)‖
        ≤ ‖c i‖ * (49 / 2 / (1 + ‖w i‖) ^ 2 * (1 / ((2 : ℝ) ^ 2 + t ^ 2))) :=
          mul_le_mul_of_nonneg_left (r11Chi_pole_bound hj (hw i (hc0 i)) t) (norm_nonneg _)
      _ = 49 / 2 * (‖c i‖ / (1 + ‖w i‖) ^ 2) * (1 / ((2 : ℝ) ^ 2 + t ^ 2)) := by ring

end DetPrimality.Bach
