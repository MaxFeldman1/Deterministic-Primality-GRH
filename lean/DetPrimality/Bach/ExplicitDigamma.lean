import Mathlib

/-!
# Partial-fraction series for the digamma function

Main results (all fully proved):
* `DetPrimality.Bach.hasSum_digamma` :
  `Re s > 0 → HasSum (fun k => 1/(k+1) - 1/(k+s)) (digamma s + γ)`;
* `DetPrimality.Bach.digamma_eq_tsum` :
  `Re s > 0 → digamma s = -γ + ∑' k, (1/(k+1) - 1/(k+s))`;
* `DetPrimality.Bach.hasSum_digamma_sub` :
  `Re z > 0 → Re z₀ > 0 → HasSum (fun k => 1/(k+z₀) - 1/(k+z)) (digamma z - digamma z₀)`.

Proof: for real `x > 0` use convexity of `log Γ` (Bohr–Mollerup, as in Mathlib's
`Real.deriv_Gamma_nat`) to get `log (y-1) ≤ (log Γ)'(y) ≤ log y`, telescope with
`(log Γ)'(y+1) = (log Γ)'(y) + 1/y`; then extend to `Re s > 0` by the identity theorem
(both sides are holomorphic there; the series converges locally uniformly).
-/

open Complex Filter Topology Set

namespace DetPrimality.Bach

local notation "γ" => Real.eulerMascheroniConstant
local notation "lg" => (Real.log ∘ Real.Gamma)

section RealPart

private lemma lg_rec (x : ℝ) (hx : 0 < x) : lg (x + 1) = lg x + Real.log x := by
  simp only [Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_comm]

private lemma real_ne_neg_nat {x : ℝ} (hx : 0 < x) : ∀ m : ℕ, x ≠ -m := by
  intro m h
  have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  linarith

private lemma lg_diff {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ lg x :=
  (Real.differentiableAt_Gamma (real_ne_neg_nat hx)).log (Real.Gamma_pos_of_pos hx).ne'

private lemma lg_deriv_rec (x : ℝ) (hx : 0 < x) : deriv lg (x + 1) = deriv lg x + 1 / x := by
  rw [← deriv_comp_add_const, one_div, ← Real.deriv_log,
    ← deriv_add (lg_diff hx) (Real.differentiableAt_log hx.ne')]
  apply EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy using lg_rec y hy

private lemma lg_deriv_add_nat (x : ℝ) (hx : 0 < x) (N : ℕ) :
    deriv lg (x + N) = deriv lg x + ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + x) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    rw [Nat.cast_succ, ← add_assoc, lg_deriv_rec _ (by linarith), ih, Finset.sum_range_succ,
      add_comm x (N : ℝ)]
    ring

private lemma lg_deriv_bounds {y : ℝ} (hy : 1 < y) :
    Real.log (y - 1) ≤ deriv lg y ∧ deriv lg y ≤ Real.log y := by
  have hc : ConvexOn ℝ (Ioi 0) lg := Real.convexOn_log_Gamma
  have hy0 : 0 < y := by linarith
  constructor
  · refine (le_of_eq ?_).trans (hc.slope_le_deriv (mem_Ioi.mpr (by linarith : (0 : ℝ) < y - 1))
      (mem_Ioi.mpr hy0) (by linarith) (lg_diff hy0))
    have h := lg_rec (y - 1) (by linarith)
    rw [sub_add_cancel] at h
    rw [slope_def_field, show y - (y - 1) = (1 : ℝ) by ring, div_one, h]
    ring
  · refine (hc.deriv_le_slope (mem_Ioi.mpr hy0) (mem_Ioi.mpr (by linarith : (0 : ℝ) < y + 1))
      (by linarith) (lg_diff hy0)).trans (le_of_eq ?_)
    rw [slope_def_field, show y + 1 - y = (1 : ℝ) by ring, div_one, lg_rec y hy0]
    ring

private lemma lg_deriv_one : deriv lg 1 = -γ := by
  have h := (Real.hasDerivAt_Gamma_one.log (by rw [Real.Gamma_one]; norm_num)).deriv
  rw [Real.Gamma_one, div_one] at h
  exact h

private lemma tendsto_log_add_sub_log_add (a b : ℝ) :
    Tendsto (fun N : ℕ => Real.log (N + a) - Real.log (N + b)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (1 + a / N) / (1 + b / N)) atTop (𝓝 ((1 + 0) / (1 + 0))) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat a)).div
      (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat b)) (by norm_num))
  rw [show ((1 : ℝ) + 0) / (1 + 0) = 1 by norm_num] at h1
  have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1)
  rw [Real.log_one] at h2
  refine h2.congr' ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (|a| + |b|)
  filter_upwards [eventually_ge_atTop (M + 1)] with N hN
  have hNM : (M : ℝ) + 1 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have ha : 0 < (N : ℝ) + a := by linarith [neg_abs_le a, abs_nonneg b]
  have hb : 0 < (N : ℝ) + b := by linarith [neg_abs_le b, abs_nonneg a]
  simp only [Function.comp_apply]
  rw [← Real.log_div ha.ne' hb.ne']
  congr 1
  field_simp

/-- Real form of the digamma series. -/
private lemma hasSum_real_digamma {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x)) (deriv lg x + γ) := by
  -- summability
  set m := min x 1 with hmdef
  have hm : 0 < m := lt_min hx one_pos
  have hs2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact_mod_cast this
  have hbound : ∀ k : ℕ, ‖1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x)‖
      ≤ (|x - 1| / m) * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : 0 < (k : ℝ) + 1 := by linarith
    have h2 : 0 < (k : ℝ) + x := by linarith
    have h3 : m * ((k : ℝ) + 1) ≤ (k : ℝ) + x := by
      have : m ≤ x := min_le_left _ _
      have : m ≤ 1 := min_le_right _ _
      nlinarith
    rw [Real.norm_eq_abs, div_sub_div _ _ h1.ne' h2.ne', abs_div, abs_of_pos (mul_pos h1 h2),
      show 1 * ((k : ℝ) + x) - ((k : ℝ) + 1) * 1 = x - 1 by ring, div_mul_div_comm, mul_one]
    refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
    calc m * ((k : ℝ) + 1) ^ 2 = ((k : ℝ) + 1) * (m * ((k : ℝ) + 1)) := by ring
      _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + x) := mul_le_mul_of_nonneg_left h3 h1.le
  have hsum : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x)) :=
    Summable.of_norm_bounded (hs2.mul_left _) hbound
  -- partial sums
  have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x))
      = deriv lg x + γ - (deriv lg (x + N) - deriv lg (1 + N)) := by
    intro N
    rw [Finset.sum_sub_distrib, lg_deriv_add_nat x hx N, lg_deriv_add_nat 1 one_pos N,
      lg_deriv_one]
    ring
  have hD : Tendsto (fun N : ℕ => deriv lg (x + N) - deriv lg (1 + N)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_log_add_sub_log_add (x - 1) 1) (tendsto_log_add_sub_log_add x 0) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hA := (lg_deriv_bounds (y := x + N) (by linarith)).1
      have hB := (lg_deriv_bounds (y := 1 + N) (by linarith)).2
      rw [show x + (N : ℝ) - 1 = N + (x - 1) by ring] at hA
      rw [add_comm (1 : ℝ) N] at hB
      rw [add_comm (1 : ℝ) N]
      linarith
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hA := (lg_deriv_bounds (y := x + N) (by linarith)).2
      have hB := (lg_deriv_bounds (y := 1 + N) (by linarith)).1
      rw [show 1 + (N : ℝ) - 1 = N + 0 by ring] at hB
      rw [add_comm x (N : ℝ)] at hA ⊢
      linarith
  have hlim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
      (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x))) atTop (𝓝 (deriv lg x + γ)) := by
    have := (tendsto_const_nhds (x := deriv lg x + γ)).sub hD
    rw [sub_zero] at this
    exact this.congr fun N => (hpart N).symm
  have h1 := hsum.hasSum
  rw [tendsto_nhds_unique h1.tendsto_sum_nat hlim] at h1
  exact h1

end RealPart

section ComplexPart

private lemma hasDerivAt_complex_of_real {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
    (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

private lemma ne_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  have h1 := congrArg Complex.re h
  rw [Complex.neg_re, Complex.natCast_re] at h1
  have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  linarith

private lemma digamma_ofReal {x : ℝ} (hx : 0 < x) : digamma (x : ℂ) = ((deriv lg x : ℝ) : ℂ) := by
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -m := ne_neg_nat_of_re_pos (by simpa using hx)
  have hdR : DifferentiableAt ℝ Real.Gamma x := Real.differentiableAt_Gamma (real_ne_neg_nat hx)
  have hD := hasDerivAt_complex_of_real (differentiableAt_Gamma _ hne) hdR.hasDerivAt
    Complex.Gamma_ofReal
  have hG : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have hlog := (hdR.hasDerivAt.log hG).deriv
  rw [digamma_def, logDeriv_apply, hD.deriv, Complex.Gamma_ofReal]
  rw [show (Real.log ∘ Real.Gamma) = fun y => Real.log (Real.Gamma y) from rfl, hlog]
  push_cast
  rfl

theorem differentiableOn_digamma : DifferentiableOn ℂ digamma {z : ℂ | 0 < z.re} := by
  have hV : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (differentiableAt_Gamma z (ne_neg_nat_of_re_pos hz)).differentiableWithinAt
  have hG' := hG.deriv hV
  have hfun : digamma = fun z => deriv Gamma z / Gamma z := by
    funext z; rw [digamma_def, logDeriv_apply]
  rw [hfun]
  intro z hz
  exact (hG' z hz).div (hG z hz) (Gamma_ne_zero (ne_neg_nat_of_re_pos hz))

private lemma summable_inv_succ_sq : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  exact_mod_cast this

private lemma term_bound {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ) {w : ℂ} (hw : δ < w.re)
    (hwR : ‖w‖ < R) :
    ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)‖ ≤ ((R + 1) / δ) * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have h2 : (k : ℝ) + δ ≤ ‖(k : ℂ) + w‖ := by
    have := Complex.re_le_norm ((k : ℂ) + w)
    rw [Complex.add_re, Complex.natCast_re] at this
    linarith
  have h1ne : (k : ℂ) + 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have h2ne : (k : ℂ) + w ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; linarith
  rw [div_sub_div _ _ h1ne h2ne, norm_div, norm_mul, h1,
    show 1 * ((k : ℂ) + w) - ((k : ℂ) + 1) * 1 = w - 1 by ring, div_mul_div_comm, mul_one]
  have hnum : ‖w - 1‖ ≤ R + 1 := by
    calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ R + 1 := by rw [norm_one]; linarith
  have hden : δ * ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) * ‖(k : ℂ) + w‖ := by
    have h3 : δ * ((k : ℝ) + 1) ≤ (k : ℝ) + δ := by nlinarith
    calc δ * ((k : ℝ) + 1) ^ 2 = ((k : ℝ) + 1) * (δ * ((k : ℝ) + 1)) := by ring
      _ ≤ ((k : ℝ) + 1) * ‖(k : ℂ) + w‖ :=
        mul_le_mul_of_nonneg_left (h3.trans h2) (by linarith)
  exact div_le_div₀ (by linarith [norm_nonneg w]) hnum (by positivity) hden

private lemma differentiableOn_series {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    DifferentiableOn ℂ (fun w : ℂ => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)))
      ({z : ℂ | δ < z.re} ∩ Metric.ball 0 R) := by
  refine Complex.differentiableOn_tsum_of_summable_norm (summable_inv_succ_sq.mul_left _)
    (fun k => ?_) ((isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball)
    (fun k w hw => term_bound hδ hδ1 k hw.1 (by simpa using hw.2))
  intro w hw
  have hne : (k : ℂ) + w ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    rw [Complex.add_re, Complex.natCast_re, Complex.zero_re] at h1
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have : δ < w.re := hw.1
    linarith
  exact ((differentiableAt_const _).sub ((differentiableAt_const _).div
    ((differentiableAt_const _).add differentiableAt_id) hne)).differentiableWithinAt

private lemma digamma_eq_tsum_ofReal {x : ℝ} (hx : 0 < x) :
    digamma (x : ℂ) = -γ + ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)) := by
  rw [digamma_ofReal hx]
  have h := (hasSum_real_digamma hx).tsum_eq
  have h2 : (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)))
      = ((∑' k : ℕ, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1; funext k; push_cast; ring
  rw [h2, h]
  push_cast
  ring

/-- **Digamma series.** For `Re s > 0`, `ψ(s) = -γ + ∑_{k ≥ 0} (1/(k+1) - 1/(k+s))`. -/
theorem digamma_eq_tsum {s : ℂ} (hs : 0 < s.re) :
    digamma s = -γ + ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s)) := by
  set δ : ℝ := min s.re 1 / 2 with hδdef
  have hmin : 0 < min s.re 1 := lt_min hs one_pos
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith [min_le_right s.re 1]
  have hδs : δ < s.re := by rw [hδdef]; linarith [min_le_left s.re 1]
  have hδ1' : δ < (1 : ℂ).re := by rw [Complex.one_re, hδdef]; linarith [min_le_right s.re 1]
  set R : ℝ := ‖s‖ + 2 with hR
  set U := {z : ℂ | δ < z.re} ∩ Metric.ball (0 : ℂ) R with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt δ).inter (convex_ball (0 : ℂ) R)).isPreconnected
  have h1U : (1 : ℂ) ∈ U := ⟨hδ1', by
    rw [Metric.mem_ball, dist_zero_right, norm_one, hR]; linarith [norm_nonneg s]⟩
  have hsU : s ∈ U := ⟨hδs, by rw [Metric.mem_ball, dist_zero_right, hR]; linarith⟩
  have hf : AnalyticOnNhd ℂ digamma U :=
    (differentiableOn_digamma.mono (fun z hz => lt_trans hδ hz.1)).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ
      (fun z => -(γ : ℂ) + ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))) U :=
    ((differentiableOn_const _).add (differentiableOn_series hδ hδ1)).analyticOnNhd hUo
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ), digamma (x : ℂ)
      = -(γ : ℂ) + ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (x : ℂ))) := by
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds one_pos)] with x hx
    exact digamma_eq_tsum_ofReal hx
  have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := {(1 : ℝ)}ᶜ))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
      exact_mod_cast hx
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), digamma z
      = -(γ : ℂ) + ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) :=
    htend.frequently hev.frequently
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hUc h1U hfreq hsU

/-- `HasSum` form of the digamma series. -/
theorem hasSum_digamma {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s)) (digamma s + γ) := by
  set δ : ℝ := min s.re 1 / 2 with hδdef
  have hmin : 0 < min s.re 1 := lt_min hs one_pos
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith [min_le_right s.re 1]
  have hδs : δ < s.re := by rw [hδdef]; linarith [min_le_left s.re 1]
  have hsum : Summable (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s)) :=
    Summable.of_norm_bounded (summable_inv_succ_sq.mul_left _)
      (fun k => term_bound (R := ‖s‖ + 1) hδ hδ1 k hδs (by linarith))
  convert hsum.hasSum using 1
  rw [digamma_eq_tsum hs]
  ring

/-- Difference form: `ψ(z) - ψ(z₀) = ∑_{k ≥ 0} (1/(k+z₀) - 1/(k+z))` for `Re z, Re z₀ > 0`. -/
theorem hasSum_digamma_sub {z z₀ : ℂ} (hz : 0 < z.re) (hz₀ : 0 < z₀.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + z₀) - 1 / ((k : ℂ) + z)) (digamma z - digamma z₀) := by
  have h := (hasSum_digamma hz).sub (hasSum_digamma hz₀)
  have e1 : (fun k : ℕ => (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))
      - (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z₀)))
      = fun k : ℕ => 1 / ((k : ℂ) + z₀) - 1 / ((k : ℂ) + z) := by
    funext k; ring
  rw [e1, show digamma z + (γ : ℂ) - (digamma z₀ + γ) = digamma z - digamma z₀ by ring] at h
  exact h

end ComplexPart

end DetPrimality.Bach
