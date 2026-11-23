import DetPrimality.Bach.LLSZetaLower
import DetPrimality.Bach.R11Defs

/-!
# Perron with the kernels `1/(s+1/2)^k`, `k = 2, 3, 4` (designB Lemma 2)

`r11Zx_Q k g x = (1/2πi) ∫_{(2)} g(s) x^s / (s+1/2)^k ds`.  In the variable `s + 1/2` this is the
kernel `y^s/s^{j+1}` (`k = j + 1`) of designB applied to `g(s - 1/2)`.

* Mellin transforms of `t^{1/2} log^i t · 1_{(0,1]}` (`r11Zx_hasMellin_p`);
* Mellin inversion of `D₀/u - D₁/u² + 2D₂/u³ - 6D₃/u⁴ + C/(s-w)`, `u = s + 1/2` (`r11Zx_mellinInv_mix`);
* residues `r11Zx_Q_one`, `r11Zx_Q_inv_sub` (`x ≥ 1`, `k ∈ {2,3,4}`);
* the Perron identity `r11Zx_perron`:
  `Q_k[-ζ'/ζ](x) = ∑_{n<x} Λ(n) √n log^{k-1}(x/n) / (√x (k-1)!)`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology Asymptotics

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-! ## Mellin transforms of `t^{1/2} log^i t` on `(0,1]` -/

/-- `t^{1/2} · 1_{(0,1]}(t)`. -/
noncomputable def r11Zx_h : ℝ → ℂ := indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ))

/-- `t^{1/2} log^i t · 1_{(0,1]}(t)`. -/
noncomputable def r11Zx_p (i : ℕ) : ℝ → ℂ := fun t => (Real.log t) ^ i • r11Zx_h t

theorem r11Zx_h_of_mem {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : r11Zx_h t = (t : ℂ) ^ (1 / 2 : ℂ) :=
  indicator_of_mem ht _

theorem r11Zx_h_of_notMem {t : ℝ} (ht : t ∉ Ioc (0 : ℝ) 1) : r11Zx_h t = 0 :=
  indicator_of_notMem ht _

theorem r11Zx_p_of_mem (i : ℕ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    r11Zx_p i t = (Real.log t : ℂ) ^ i * (t : ℂ) ^ (1 / 2 : ℂ) := by
  simp only [r11Zx_p, r11Zx_h_of_mem ht, Complex.real_smul]
  push_cast
  ring

theorem r11Zx_p_of_notMem (i : ℕ) {t : ℝ} (ht : t ∉ Ioc (0 : ℝ) 1) : r11Zx_p i t = 0 := by
  simp only [r11Zx_p, r11Zx_h_of_notMem ht, smul_zero]

theorem r11Zx_norm_p_le (i : ℕ) (t : ℝ) : ‖r11Zx_p i t‖ ≤ (2 * ((i : ℝ) + 1)) ^ i := by
  have hC : (0 : ℝ) ≤ (2 * ((i : ℝ) + 1)) ^ i := by positivity
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · obtain ⟨ht0, ht1⟩ := ht
    set c : ℝ := 1 / (2 * ((i : ℝ) + 1)) with hc
    have hc0 : 0 < c := by positivity
    have hcd : c⁻¹ = 2 * ((i : ℝ) + 1) := by rw [hc, one_div, inv_inv]
    have hlog : |Real.log t| ≤ t ^ (-c) / c := by
      rw [abs_of_nonpos (Real.log_nonpos ht0.le ht1)]
      have := Real.log_le_rpow_div (inv_nonneg.mpr ht0.le) hc0
      rwa [Real.log_inv, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le] at this
    have hpow : |Real.log t| ^ i ≤ t ^ (-c * i) * (2 * ((i : ℝ) + 1)) ^ i := by
      calc |Real.log t| ^ i ≤ (t ^ (-c) / c) ^ i := pow_le_pow_left₀ (abs_nonneg _) hlog i
        _ = t ^ (-c * i) * (2 * ((i : ℝ) + 1)) ^ i := by
          rw [div_eq_mul_inv, mul_pow, hcd, ← Real.rpow_natCast (t ^ (-c)) i,
            ← Real.rpow_mul ht0.le]
    have hci : c * i ≤ 1 / 2 := by
      rw [hc, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith
    have hexp : 0 ≤ -c * i + 1 / 2 := by linarith
    have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    rw [r11Zx_p, r11Zx_h_of_mem ⟨ht0, ht1⟩, norm_smul, Real.norm_eq_abs, abs_pow,
      Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre]
    calc |Real.log t| ^ i * t ^ (1 / 2 : ℝ)
        ≤ (t ^ (-c * i) * (2 * ((i : ℝ) + 1)) ^ i) * t ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg ht0.le _)
      _ = t ^ (-c * i + 1 / 2) * (2 * ((i : ℝ) + 1)) ^ i := by
          rw [Real.rpow_add ht0]; ring
      _ ≤ 1 * (2 * ((i : ℝ) + 1)) ^ i :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one ht0.le ht1 hexp) hC
      _ = (2 * ((i : ℝ) + 1)) ^ i := one_mul _
  · rw [r11Zx_p_of_notMem i ht, norm_zero]
    exact hC

theorem r11Zx_measurable_h : Measurable r11Zx_h :=
  (Complex.measurable_ofReal.pow_const _).indicator measurableSet_Ioc

theorem r11Zx_integrable_p (i : ℕ) : Integrable (r11Zx_p i) := by
  have hm : AEStronglyMeasurable (r11Zx_p i) volume :=
    ((Real.measurable_log.pow_const i).smul r11Zx_measurable_h).aestronglyMeasurable
  have hg : Integrable (indicator (Ioc (0 : ℝ) 1) (fun _ : ℝ => (2 * ((i : ℝ) + 1)) ^ i)) :=
    (continuous_const.integrableOn_Ioc).integrable_indicator measurableSet_Ioc
  refine hg.mono' hm (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem ht]; exact r11Zx_norm_p_le i t
  · rw [indicator_of_notMem ht, r11Zx_p_of_notMem i ht, norm_zero]

theorem r11Zx_mellin_log_aux {f : ℝ → ℂ} (hfi : Integrable f) {C : ℝ} (hb : ∀ t, ‖f t‖ ≤ C)
    (h0 : ∀ t, 1 < t → f t = 0) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t => Real.log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t => Real.log t • f t) s) s := by
  refine mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    (hfi.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ hs
  · have : (fun _ : ℝ => (0 : ℂ)) =ᶠ[atTop] f := by
      filter_upwards [eventually_gt_atTop 1] with t ht
      exact (h0 t ht).symm
    exact (isBigO_zero _ _).congr' this EventuallyEq.rfl
  · refine IsBigO.of_bound C (Eventually.of_forall fun t => ?_)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact hb t

theorem r11Zx_hasMellin_p (i : ℕ) : ∀ {s : ℂ}, 0 < s.re →
    HasMellin (r11Zx_p i) s ((-1) ^ i * (i.factorial : ℂ) / (s + 1 / 2) ^ (i + 1)) := by
  induction i with
  | zero =>
    intro s hs
    have hfun : r11Zx_p 0 = r11Zx_h := by
      funext t; simp [r11Zx_p]
    have h := hasMellin_cpow_Ioc (1 / 2 : ℂ) (s := s) (by
      have : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
      rw [this]; linarith)
    rw [hfun]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    unfold r11Zx_h
    rw [h2]
    simp
  | succ i ih =>
    intro s hs
    obtain ⟨hc, hd⟩ := r11Zx_mellin_log_aux (r11Zx_integrable_p i) (r11Zx_norm_p_le i)
      (fun t ht => r11Zx_p_of_notMem i (fun h => by linarith [h.2])) hs
    have hfun : (fun t => Real.log t • r11Zx_p i t) = r11Zx_p (i + 1) := by
      funext t
      simp only [r11Zx_p, smul_smul, pow_succ']
    have hA : s + 1 / 2 ≠ 0 := ne_zero_of_re_pos (by
      have : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
      rw [Complex.add_re, this]; linarith)
    have hev : mellin (r11Zx_p i) =ᶠ[𝓝 s]
        fun z => (-1) ^ i * (i.factorial : ℂ) / (z + 1 / 2) ^ (i + 1) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
      exact (ih hz).2
    have h1 := ((hasDerivAt_id s).add_const (1 / 2 : ℂ)).pow (i + 1)
    have h2 := (hasDerivAt_const s ((-1 : ℂ) ^ i * (i.factorial : ℂ))).div h1
      (pow_ne_zero _ hA)
    have hd2 : HasDerivAt (fun z : ℂ => (-1) ^ i * (i.factorial : ℂ) / (z + 1 / 2) ^ (i + 1))
        ((-1) ^ (i + 1) * ((i + 1).factorial : ℂ) / (s + 1 / 2) ^ (i + 1 + 1)) s := by
      refine h2.congr_deriv ?_
      simp only [Pi.pow_apply, id, Nat.add_sub_cancel]
      rw [div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hA)) (pow_ne_zero _ hA)]
      push_cast [Nat.factorial_succ]
      ring
    rw [← hfun]
    exact ⟨hc, hd.unique (hd2.congr_of_eventuallyEq hev)⟩

/-! ## The model function and its Mellin transform -/

theorem r11Zx_hm_smul {f : ℝ → ℂ} {s m : ℂ} (h : HasMellin f s m) (c : ℂ) :
    HasMellin (fun t => c • f t) s (c * m) := by
  have h1 := hasMellin_const_smul h.1 c
  exact ⟨h1.1, by rw [h1.2, h.2, smul_eq_mul]⟩

theorem r11Zx_hm_add {f g : ℝ → ℂ} {s m m' : ℂ} (hf : HasMellin f s m) (hg : HasMellin g s m') :
    HasMellin (fun t => f t + g t) s (m + m') := by
  have h1 := hasMellin_add hf.1 hg.1
  exact ⟨h1.1, by rw [h1.2, hf.2, hg.2]⟩

/-- `t^{1/2}(D₀ + D₁ log t + D₂ log²t + D₃ log³t) + C t^{-w}` on `(0,1]`. -/
noncomputable def r11Zx_mix (D0 D1 D2 D3 C w : ℂ) : ℝ → ℂ := fun t =>
  D0 • r11Zx_p 0 t + D1 • r11Zx_p 1 t + D2 • r11Zx_p 2 t + D3 • r11Zx_p 3 t
    + C • indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (-w)) t

noncomputable def r11Zx_F (D0 D1 D2 D3 C w : ℂ) : ℂ → ℂ := fun s =>
  D0 / (s + 1 / 2) - D1 / (s + 1 / 2) ^ 2 + 2 * D2 / (s + 1 / 2) ^ 3
    - 6 * D3 / (s + 1 / 2) ^ 4 + C / (s - w)

theorem r11Zx_mix_of_mem {D0 D1 D2 D3 C w : ℂ} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    r11Zx_mix D0 D1 D2 D3 C w t = (t : ℂ) ^ (1 / 2 : ℂ) * (D0 + D1 * (Real.log t : ℂ)
      + D2 * (Real.log t : ℂ) ^ 2 + D3 * (Real.log t : ℂ) ^ 3) + C * (t : ℂ) ^ (-w) := by
  simp only [r11Zx_mix, r11Zx_p_of_mem _ ht, indicator_of_mem ht, smul_eq_mul]
  ring

theorem r11Zx_mix_of_one_lt {D0 D1 D2 D3 C w : ℂ} {t : ℝ} (ht : 1 < t) :
    r11Zx_mix D0 D1 D2 D3 C w t = 0 := by
  have hn : t ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.2]
  simp only [r11Zx_mix, r11Zx_p_of_notMem _ hn, indicator_of_notMem hn, smul_zero, add_zero]

theorem r11Zx_hasMellin_mix (D0 D1 D2 D3 C w : ℂ) {s : ℂ} (hs : 0 < s.re) (hsw : w.re < s.re) :
    HasMellin (r11Zx_mix D0 D1 D2 D3 C w) s (r11Zx_F D0 D1 D2 D3 C w s) := by
  have h0 := r11Zx_hm_smul (r11Zx_hasMellin_p 0 hs) D0
  have h1 := r11Zx_hm_smul (r11Zx_hasMellin_p 1 hs) D1
  have h2 := r11Zx_hm_smul (r11Zx_hasMellin_p 2 hs) D2
  have h3 := r11Zx_hm_smul (r11Zx_hasMellin_p 3 hs) D3
  have h4 := r11Zx_hm_smul (hasMellin_cpow_Ioc (-w) (s := s) (by simp; linarith)) C
  have h := r11Zx_hm_add (r11Zx_hm_add (r11Zx_hm_add (r11Zx_hm_add h0 h1) h2) h3) h4
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [r11Zx_F, Nat.factorial]
  push_cast
  ring

theorem r11Zx_continuousAt_mix {D0 D1 D2 D3 C w : ℂ} (h0 : D0 + C = 0) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (r11Zx_mix D0 D1 D2 D3 C w) x := by
  set g : ℝ → ℂ := fun u => (u : ℂ) ^ (1 / 2 : ℂ) * (D0 + D1 * (Real.log u : ℂ)
      + D2 * (Real.log u : ℂ) ^ 2 + D3 * (Real.log u : ℂ) ^ 3) + C * (u : ℂ) ^ (-w) with hg
  have hu : 0 < min x 1 := lt_min hx one_pos
  have hlog : ContinuousAt (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) (min x 1) :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hu.ne')
  have hgc : ContinuousAt g (min x 1) := by
    have h3 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-w)) (min x 1) :=
      continuousAt_ofReal_cpow_const _ _ (Or.inr hu.ne')
    have h4 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (1 / 2 : ℂ)) (min x 1) :=
      continuousAt_ofReal_cpow_const _ _ (Or.inr hu.ne')
    exact (h4.mul (((continuousAt_const.add (continuousAt_const.mul hlog)).add
      (continuousAt_const.mul (hlog.pow 2))).add (continuousAt_const.mul (hlog.pow 3)))).add
      (continuousAt_const.mul h3)
  have hmin : ContinuousAt (fun t : ℝ => min t 1) x :=
    (continuous_id.min continuous_const).continuousAt
  have hcomp : ContinuousAt (fun t : ℝ => g (min t 1)) x :=
    ContinuousAt.comp (f := fun t : ℝ => min t 1) hgc hmin
  refine hcomp.congr ?_
  filter_upwards [eventually_gt_nhds hx] with t ht
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1, r11Zx_mix_of_mem ⟨ht, ht1⟩]
  · push Not at ht1
    rw [min_eq_right ht1.le, r11Zx_mix_of_one_lt ht1, hg]
    simp only [ofReal_one, Real.log_one, ofReal_zero, mul_zero, one_cpow, mul_one, add_zero,
      one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact h0

theorem r11Zx_mellinInv_mix (D0 D1 D2 D3 C w : ℂ) (hw : w.re < 2) (h0 : D0 + C = 0) {x : ℝ}
    (hx : 0 < x) (hint : VerticalIntegrable (r11Zx_F D0 D1 D2 D3 C w) 2) :
    mellinInv 2 (r11Zx_F D0 D1 D2 D3 C w) x
      = if x ≤ 1 then (x : ℂ) ^ (1 / 2 : ℂ) * (D0 + D1 * (Real.log x : ℂ)
        + D2 * (Real.log x : ℂ) ^ 2 + D3 * (Real.log x : ℂ) ^ 3) + C * (x : ℂ) ^ (-w)
        else 0 := by
  have hline : ∀ y : ℝ, (r11Zx_F D0 D1 D2 D3 C w) (((2 : ℝ) : ℂ) + y * I)
      = mellin (r11Zx_mix D0 D1 D2 D3 C w) (((2 : ℝ) : ℂ) + y * I) := by
    intro y
    exact ((r11Zx_hasMellin_mix D0 D1 D2 D3 C w (by rw [line_re]; norm_num)
      (by rw [line_re]; exact hw)).2).symm
  rw [mellinInv_congr_line hline]
  have hre : (((2 : ℝ) : ℂ)).re = 2 := by simp
  rw [mellinInv_mellin_eq 2 (r11Zx_mix D0 D1 D2 D3 C w) hx
    (r11Zx_hasMellin_mix D0 D1 D2 D3 C w (by rw [hre]; norm_num) (by rw [hre]; exact hw)).1
    (VerticalIntegrable.congr_line hline hint) (r11Zx_continuousAt_mix h0 hx)]
  split_ifs with h
  · rw [r11Zx_mix_of_mem ⟨hx, h⟩]
  · rw [r11Zx_mix_of_one_lt (not_le.mp h)]

/-! ## The line `Re s = 2` and the kernel `1/(s+1/2)^k` -/

theorem r11Zx_line_shift (y : ℝ) :
    ((2 : ℝ) : ℂ) + y * I + 1 / 2 = ((5 / 2 : ℝ) : ℂ) + y * I := by
  push_cast; ring

theorem r11Zx_line_half_ne (y : ℝ) : ((2 : ℝ) : ℂ) + y * I + 1 / 2 ≠ 0 := by
  rw [r11Zx_line_shift]
  exact ne_zero_of_re_pos (by rw [line_re]; norm_num)

theorem r11Zx_one_le_norm_line_half (y : ℝ) : 1 ≤ ‖((2 : ℝ) : ℂ) + y * I + 1 / 2‖ := by
  have := Complex.re_le_norm (((5 / 2 : ℝ) : ℂ) + y * I)
  rw [line_re] at this
  rw [r11Zx_line_shift]
  linarith

theorem r11Zx_norm_kernel_le {k : ℕ} (hk : 2 ≤ k) (y : ℝ) :
    ‖1 / (((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k‖ ≤ 1 / ((2 : ℝ) ^ 2 + y ^ 2) := by
  have hsq : ‖((2 : ℝ) : ℂ) + y * I + 1 / 2‖ ^ 2 = (5 / 2 : ℝ) ^ 2 + y ^ 2 := by
    rw [r11Zx_line_shift, normSq_line]
  rw [norm_div, norm_one, norm_pow]
  refine one_div_le_one_div_of_le (by positivity) ?_
  calc (2 : ℝ) ^ 2 + y ^ 2 ≤ ‖((2 : ℝ) : ℂ) + y * I + 1 / 2‖ ^ 2 := by
        rw [hsq]; norm_num
    _ ≤ ‖((2 : ℝ) : ℂ) + y * I + 1 / 2‖ ^ k :=
        pow_le_pow_right₀ (r11Zx_one_le_norm_line_half y) hk

/-- Integrability against `1/s²` implies integrability against `1/(s+1/2)^k`, `k ≥ 2`. -/
theorem r11Zx_vi_of_sq {g : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hg : VerticalIntegrable (fun s => g s / s ^ 2) 2) :
    VerticalIntegrable (fun s => g s / (s + 1 / 2) ^ k) 2 := by
  unfold VerticalIntegrable at hg ⊢
  have hcont : Continuous fun y : ℝ => (((2 : ℝ) : ℂ) + y * I) ^ 2
      / (((2 : ℝ) : ℂ) + y * I + 1 / 2) ^ k :=
    Continuous.div (by fun_prop) (by fun_prop) (fun y => pow_ne_zero k (r11Zx_line_half_ne y))
  have hm := hg.aestronglyMeasurable.mul hcont.aestronglyMeasurable
  refine hg.mono (hm.congr (Eventually.of_forall fun y => ?_)) (Eventually.of_forall fun y => ?_)
  · have h1 := llsPer_line_ne y
    have h2 := r11Zx_line_half_ne y
    simp only [Pi.mul_apply]
    field_simp
  · beta_reduce
    rw [div_eq_mul_one_div, norm_mul,
      div_eq_mul_one_div (g (((2 : ℝ) : ℂ) + y * I)) ((((2 : ℝ) : ℂ) + y * I) ^ 2), norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((r11Zx_norm_kernel_le hk y).trans_eq (llsPer_norm_kernel y).symm) (norm_nonneg _)

/-! ## The operator `Q_k` -/

/-- `r11Zx_Q k g x = (1/2πi) ∫_{(2)} g(s) x^s / (s+1/2)^k ds`. -/
noncomputable def r11Zx_Q (k : ℕ) (g : ℂ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 2 (fun s => g s / (s + 1 / 2) ^ k) x⁻¹

theorem r11Zx_Q_add {k : ℕ} {f g : ℂ → ℂ}
    (hf : VerticalIntegrable (fun s => f s / (s + 1 / 2) ^ k) 2)
    (hg : VerticalIntegrable (fun s => g s / (s + 1 / 2) ^ k) 2) {x : ℝ} (hx : 0 < x) :
    r11Zx_Q k (fun s => f s + g s) x = r11Zx_Q k f x + r11Zx_Q k g x := by
  unfold r11Zx_Q
  rw [show (fun s : ℂ => (f s + g s) / (s + 1 / 2) ^ k)
      = fun s => f s / (s + 1 / 2) ^ k + g s / (s + 1 / 2) ^ k from
    funext fun s => add_div _ _ _]
  exact mellinInv_add hf hg (inv_pos.mpr hx)

theorem r11Zx_Q_sub {k : ℕ} {f g : ℂ → ℂ}
    (hf : VerticalIntegrable (fun s => f s / (s + 1 / 2) ^ k) 2)
    (hg : VerticalIntegrable (fun s => g s / (s + 1 / 2) ^ k) 2) {x : ℝ} (hx : 0 < x) :
    r11Zx_Q k (fun s => f s - g s) x = r11Zx_Q k f x - r11Zx_Q k g x := by
  unfold r11Zx_Q
  rw [show (fun s : ℂ => (f s - g s) / (s + 1 / 2) ^ k)
      = fun s => f s / (s + 1 / 2) ^ k - g s / (s + 1 / 2) ^ k from
    funext fun s => sub_div _ _ _]
  exact mellinInv_sub hf hg (inv_pos.mpr hx)

theorem r11Zx_Q_const_mul (k : ℕ) (c : ℂ) (g : ℂ → ℂ) (x : ℝ) :
    r11Zx_Q k (fun s => c * g s) x = c * r11Zx_Q k g x := by
  unfold r11Zx_Q
  rw [← mellinInv_const_mul]
  congr 1
  funext s
  ring

theorem r11Zx_Q_const (k : ℕ) (c : ℂ) (x : ℝ) :
    r11Zx_Q k (fun _ => c) x = c * r11Zx_Q k (fun _ => 1) x := by
  rw [← r11Zx_Q_const_mul]
  simp

theorem r11Zx_Q_congr_line {k : ℕ} {f g : ℂ → ℂ}
    (h : ∀ y : ℝ, f ((2 : ℝ) + y * I) = g ((2 : ℝ) + y * I)) (x : ℝ) :
    r11Zx_Q k f x = r11Zx_Q k g x := by
  unfold r11Zx_Q
  exact mellinInv_congr_line (fun y => by simp only [h y]) _

theorem r11Zx_vi_const {k : ℕ} (hk : 2 ≤ k) (c : ℂ) :
    VerticalIntegrable (fun s : ℂ => c / (s + 1 / 2) ^ k) 2 :=
  r11Zx_vi_of_sq hk (llsPer_vi_const c)

theorem r11Zx_vi_inv_sub {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w.re < 2) :
    VerticalIntegrable (fun s : ℂ => 1 / (s - w) / (s + 1 / 2) ^ k) 2 :=
  r11Zx_vi_of_sq hk (llsPer_vi_inv_sub hw)

/-! ## Mellin inversion of the kernels -/

/-- `z^{1/2} (-log z)^{k-1}/(k-1)! · 1_{z ≤ 1}`. -/
noncomputable def r11Zx_kerval (k : ℕ) (z : ℝ) : ℂ :=
  if z ≤ 1 then (z : ℂ) ^ (1 / 2 : ℂ) * (-(Real.log z : ℂ)) ^ (k - 1) / ((k - 1).factorial : ℂ)
  else 0

theorem r11Zx_mellinInv_ker {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s : ℂ => 1 / (s + 1 / 2) ^ k) x = r11Zx_kerval k x := by
  unfold r11Zx_kerval
  rcases hk with rfl | rfl | rfl
  · have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s + 1 / 2) ^ 2) (((2 : ℝ) : ℂ) + y * I)
        = r11Zx_F 0 (-1) 0 0 0 0 (((2 : ℝ) : ℂ) + y * I) := by
      intro y; simp only [r11Zx_F]; ring
    rw [mellinInv_congr_line hline, r11Zx_mellinInv_mix _ _ _ _ _ _ (by simp) (by ring) hx
      (VerticalIntegrable.congr_line hline (r11Zx_vi_const le_rfl 1))]
    split_ifs with h
    · simp
    · rfl
  · have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s + 1 / 2) ^ 3) (((2 : ℝ) : ℂ) + y * I)
        = r11Zx_F 0 0 (1 / 2) 0 0 0 (((2 : ℝ) : ℂ) + y * I) := by
      intro y; simp only [r11Zx_F]; ring
    rw [mellinInv_congr_line hline, r11Zx_mellinInv_mix _ _ _ _ _ _ (by simp) (by ring) hx
      (VerticalIntegrable.congr_line hline (r11Zx_vi_const (by norm_num) 1))]
    split_ifs with h
    · simp; ring
    · rfl
  · have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s + 1 / 2) ^ 4) (((2 : ℝ) : ℂ) + y * I)
        = r11Zx_F 0 0 0 (-1 / 6) 0 0 (((2 : ℝ) : ℂ) + y * I) := by
      intro y; simp only [r11Zx_F]; ring
    rw [mellinInv_congr_line hline, r11Zx_mellinInv_mix _ _ _ _ _ _ (by simp) (by ring) hx
      (VerticalIntegrable.congr_line hline (r11Zx_vi_const (by norm_num) 1))]
    split_ifs with h
    · simp; ring
    · rfl

theorem r11Zx_pf2 {u a : ℂ} (hu : u ≠ 0) (ha : a ≠ 0) (hua : u - a ≠ 0) :
    1 / (u - a) / u ^ 2 = (-1 / a ^ 2) / u - (1 / a) / u ^ 2 + (1 / a ^ 2) / (u - a) := by
  field_simp
  ring

theorem r11Zx_pf3 {u a : ℂ} (hu : u ≠ 0) (ha : a ≠ 0) (hua : u - a ≠ 0) :
    1 / (u - a) / u ^ 3 = (-1 / a ^ 3) / u - (1 / a ^ 2) / u ^ 2 - (1 / a) / u ^ 3
      + (1 / a ^ 3) / (u - a) := by
  field_simp
  ring

theorem r11Zx_pf4 {u a : ℂ} (hu : u ≠ 0) (ha : a ≠ 0) (hua : u - a ≠ 0) :
    1 / (u - a) / u ^ 4 = (-1 / a ^ 4) / u - (1 / a ^ 3) / u ^ 2 - (1 / a ^ 2) / u ^ 3
      - (1 / a) / u ^ 4 + (1 / a ^ 4) / (u - a) := by
  field_simp
  ring

theorem r11Zx_mellinInv_ker_inv_sub {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) {w : ℂ} (hw : w.re < 2)
    (hw0 : w + 1 / 2 ≠ 0) {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s : ℂ => 1 / (s - w) / (s + 1 / 2) ^ k) x
      = if x ≤ 1 then (x : ℂ) ^ (-w) / (w + 1 / 2) ^ k - (x : ℂ) ^ (1 / 2 : ℂ)
          * ∑ i ∈ Finset.range k, (-(Real.log x : ℂ)) ^ i / (i.factorial : ℂ)
            / (w + 1 / 2) ^ (k - i)
        else 0 := by
  set a : ℂ := w + 1 / 2 with ha
  have hne : ∀ y : ℝ, ((2 : ℝ) : ℂ) + y * I - w ≠ 0 := fun y =>
    ne_zero_of_re_pos (by rw [Complex.sub_re, line_re]; linarith)
  have hsub : ∀ y : ℝ, ((2 : ℝ) : ℂ) + y * I - w = (((2 : ℝ) : ℂ) + y * I + 1 / 2) - a := by
    intro y; rw [ha]; ring
  rcases hk with rfl | rfl | rfl
  · have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s - w) / (s + 1 / 2) ^ 2) (((2 : ℝ) : ℂ) + y * I)
        = r11Zx_F (-1 / a ^ 2) (1 / a) 0 0 (1 / a ^ 2) w (((2 : ℝ) : ℂ) + y * I) := by
      intro y
      have h3 : (((2 : ℝ) : ℂ) + y * I + 1 / 2) - a ≠ 0 := by rw [← hsub]; exact hne y
      simp only [r11Zx_F]
      rw [hsub y, r11Zx_pf2 (r11Zx_line_half_ne y) hw0 h3]
      ring
    rw [mellinInv_congr_line hline, r11Zx_mellinInv_mix _ _ _ _ _ _ hw (by ring) hx
      (VerticalIntegrable.congr_line hline (r11Zx_vi_inv_sub le_rfl hw))]
    split_ifs with h
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      push_cast
      field_simp
      ring
    · rfl
  · have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s - w) / (s + 1 / 2) ^ 3) (((2 : ℝ) : ℂ) + y * I)
        = r11Zx_F (-1 / a ^ 3) (1 / a ^ 2) (-(1 / a) / 2) 0 (1 / a ^ 3) w
          (((2 : ℝ) : ℂ) + y * I) := by
      intro y
      have h3 : (((2 : ℝ) : ℂ) + y * I + 1 / 2) - a ≠ 0 := by rw [← hsub]; exact hne y
      simp only [r11Zx_F]
      rw [hsub y, r11Zx_pf3 (r11Zx_line_half_ne y) hw0 h3]
      ring
    rw [mellinInv_congr_line hline, r11Zx_mellinInv_mix _ _ _ _ _ _ hw (by ring) hx
      (VerticalIntegrable.congr_line hline (r11Zx_vi_inv_sub (by norm_num) hw))]
    split_ifs with h
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      push_cast
      field_simp
      ring
    · rfl
  · have hline : ∀ y : ℝ, (fun s : ℂ => 1 / (s - w) / (s + 1 / 2) ^ 4) (((2 : ℝ) : ℂ) + y * I)
        = r11Zx_F (-1 / a ^ 4) (1 / a ^ 3) (-(1 / a ^ 2) / 2) (1 / a / 6) (1 / a ^ 4) w
          (((2 : ℝ) : ℂ) + y * I) := by
      intro y
      have h3 : (((2 : ℝ) : ℂ) + y * I + 1 / 2) - a ≠ 0 := by rw [← hsub]; exact hne y
      simp only [r11Zx_F]
      rw [hsub y, r11Zx_pf4 (r11Zx_line_half_ne y) hw0 h3]
      ring
    rw [mellinInv_congr_line hline, r11Zx_mellinInv_mix _ _ _ _ _ _ hw (by ring) hx
      (VerticalIntegrable.congr_line hline (r11Zx_vi_inv_sub (by norm_num) hw))]
    split_ifs with h
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      push_cast
      field_simp
      ring
    · rfl

/-! ## Residues (`x ≥ 1`) -/

theorem r11Zx_cpow_half {z : ℝ} (hz : 0 ≤ z) : ((z : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√z : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hz]
  norm_num

/-- `Q_k[1](x) = x^{-1/2} log^{k-1} x/(k-1)!`. -/
noncomputable def r11Zx_one (k : ℕ) (x : ℝ) : ℂ :=
  (((√x)⁻¹ : ℝ) : ℂ) * (Real.log x : ℂ) ^ (k - 1) / ((k - 1).factorial : ℂ)

/-- `Q_k[1/(s-w)](x) = x^w/(w+1/2)^k - x^{-1/2} ∑_{i<k} (log^i x/i!) (w+1/2)^{i-k}`. -/
noncomputable def r11Zx_R (k : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ w / (w + 1 / 2) ^ k - (((√x)⁻¹ : ℝ) : ℂ)
    * ∑ i ∈ Finset.range k, (Real.log x : ℂ) ^ i / (i.factorial : ℂ) / (w + 1 / 2) ^ (k - i)

theorem r11Zx_Q_one {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) {x : ℝ} (hx : 1 ≤ x) :
    r11Zx_Q k (fun _ => 1) x = r11Zx_one k x := by
  have hx0 : 0 < x := by linarith
  unfold r11Zx_Q
  rw [r11Zx_mellinInv_ker hk (inv_pos.mpr hx0), r11Zx_kerval, if_pos (inv_le_one_of_one_le₀ hx),
    r11Zx_cpow_half (inv_nonneg.mpr hx0.le), Real.sqrt_inv, Real.log_inv, r11Zx_one]
  push_cast
  ring

theorem r11Zx_Q_inv_sub {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) {w : ℂ} (hw : w.re < 2)
    (hw0 : w + 1 / 2 ≠ 0) {x : ℝ} (hx : 1 ≤ x) :
    r11Zx_Q k (fun s => 1 / (s - w)) x = r11Zx_R k w x := by
  have hx0 : 0 < x := by linarith
  unfold r11Zx_Q
  rw [r11Zx_mellinInv_ker_inv_sub hk hw hw0 (inv_pos.mpr hx0), if_pos (inv_le_one_of_one_le₀ hx),
    r11Zx_cpow_half (inv_nonneg.mpr hx0.le), Real.sqrt_inv, Real.log_inv,
    ofReal_inv_cpow_neg hx0, r11Zx_R]
  push_cast
  ring_nf

/-! ## The Perron identity -/

theorem r11Zx_kernel_integral {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) {z : ℝ} (hz : 0 < z) :
    ∫ y : ℝ, (z : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
        (fun s : ℂ => 1 / (s + 1 / 2) ^ k) (((2 : ℝ) : ℂ) + y * I)
      = (2 * Real.pi : ℂ) * r11Zx_kerval k z := by
  have h := r11Zx_mellinInv_ker hk hz
  unfold mellinInv at h
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  rw [← h, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_one_div_cancel hpi, one_mul]

theorem r11Zx_two_le {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) : 2 ≤ k := by
  rcases hk with rfl | rfl | rfl <;> norm_num

/-- **Perron identity** for the kernel `x^s/(s+1/2)^k`:
`Q_k[-ζ'/ζ](x) = ∑_{n<x} Λ(n) √n log^{k-1}(x/n) / (√x (k-1)!)`. -/
theorem r11Zx_perron {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) {x : ℝ} (hx : 1 ≤ x) :
    r11Zx_Q k (fun s => -(deriv (LFunction χ₁) s / LFunction χ₁ s)) x
      = ∑ n ∈ Finset.range ⌈x⌉₊,
          ((Λ n * (√(n : ℝ) * Real.log (x / n) ^ (k - 1)) / (√x * ((k - 1).factorial : ℝ)) : ℝ)
            : ℂ) := by
  have hx0 : 0 < x := by linarith
  have hk2 := r11Zx_two_le hk
  set f : ℕ → ℂ := fun n => χ₁ (n : ZMod 1) * (Λ n : ℂ) with hf
  set K : ℂ → ℂ := fun s => 1 / (s + 1 / 2) ^ k with hK
  set F : ℕ → ℝ → ℂ := fun n y => if n = 0 then 0 else
    f n * ((((n : ℝ) / x : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) • K (((2 : ℝ) : ℂ) + y * I))
    with hFdef
  have hpos : ∀ n : ℕ, n ≠ 0 → 0 < (n : ℝ) / x := fun n hn =>
    div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hx0
  have hLS : ∀ y : ℝ, -(deriv (LFunction χ₁) (((2 : ℝ) : ℂ) + y * I)
      / LFunction χ₁ (((2 : ℝ) : ℂ) + y * I)) = LSeries f (((2 : ℝ) : ℂ) + y * I) := by
    intro y
    have hs : 1 < (((2 : ℝ) : ℂ) + y * I).re := by simp
    have h1 : LSeries f (((2 : ℝ) : ℂ) + y * I) = _ := LSeries_twist_vonMangoldt_eq χ₁ hs
    rw [h1, deriv_LFunction_eq_deriv_LSeries χ₁ hs, LFunction_eq_LSeries χ₁ hs, neg_div]
  have hpt : ∀ y : ℝ, ((x⁻¹ : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
      (fun s => -(deriv (LFunction χ₁) s / LFunction χ₁ s) / (s + 1 / 2) ^ k)
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
  have hKint : VerticalIntegrable K 2 := r11Zx_vi_const hk2 1
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
    have h := ((LSeriesSummable_twist_vonMangoldt χ₁ (s := 2) (by norm_num)).norm).mul_right
      (x ^ 2 * C)
    refine h.congr fun n => (hFnorm n).symm
  have hint := integral_tsum_of_summable_integral_norm hFint hsum
  have hFn : ∀ n, ∫ y, F n y = if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ) * r11Zx_kerval k ((n : ℝ) / x)) := by
    intro n
    by_cases hn : n = 0
    · simp [hFdef, hn]
    · simp only [hFdef, hn, if_false]
      rw [integral_const_mul, r11Zx_kernel_integral hk (hpos n hn)]
  unfold r11Zx_Q mellinInv
  rw [integral_congr_ae (Eventually.of_forall hpt), ← hint]
  simp_rw [hFn]
  rw [Complex.real_smul, ← tsum_mul_left]
  have hk1 : k - 1 ≠ 0 := by omega
  have hzero : ∀ n ∉ Finset.range ⌈x⌉₊,
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * (if n = 0 then 0 else
      f n * ((2 * Real.pi : ℂ) * r11Zx_kerval k ((n : ℝ) / x)))) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hxn : x ≤ n := Nat.ceil_le.mp hn
    have h1 : 1 ≤ (n : ℝ) / x := (one_le_div hx0).mpr hxn
    unfold r11Zx_kerval
    split_ifs with h0 h2
    · simp
    · have h3 : (n : ℝ) / x = 1 := le_antisymm h2 h1
      rw [h3, Real.log_one]
      simp [hk1]
    · simp
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnx : (n : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  by_cases h0 : n = 0
  · simp [h0]
  · have hle : (n : ℝ) / x ≤ 1 := by rw [div_le_one hx0]; exact hnx.le
    have hlog : Real.log ((n : ℝ) / x) = -Real.log (x / n) := by
      rw [← Real.log_inv, inv_div]
    have hχ : χ₁ (n : ZMod 1) = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
    have hsx : (√x : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hx0).ne'
    have hfac : (((k - 1).factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    rw [if_neg h0, r11Zx_kerval, if_pos hle, hf, r11Zx_cpow_half (hpos n h0).le, hlog,
      Real.sqrt_div (Nat.cast_nonneg n)]
    simp only [hχ]
    push_cast
    field_simp

end DetPrimality.Bach
