import DetPrimality.Bach.R11ZeroSumSeries

/-!
# Round 11, zero sums: certified digamma / trigamma values and `log π`

* `r11Zs_digamma_le` : `Re ψ(x) ≤ log(M+x) - 1/(2(M+x)) - ∑_{k<M} 1/(k+x)` (`x > 0`);
* `r11Zs_trigamma_ge` : `Re ψ'(x) ≥ ∑_{k<M} 1/(k+x)² + 1/(M+x-c) - 1/(M+j+x-c)`;
* `r11Zs_digamma_three_quarters` : `Re ψ(3/4) ≤ -1.085858`;
* `r11Zs_trigamma_three_quarters` : `Re ψ'(3/4) ≥ 2.54187`;
* `r11Zs_trigamma_five_quarters` : `Re ψ'(5/4) ≥ 1.19732`;
* `r11Zs_log_pi_gt` : `log π > 1.14472`.
-/

open Complex Filter Topology

namespace DetPrimality.Bach

/-! ## The trapezoid inequality for `1/t` -/

lemma r11Zs_log_trap {a : ℝ} (ha : 0 < a) :
    Real.log (a + 1) - Real.log a ≤ 1 / (2 * a) + 1 / (2 * (a + 1)) := by
  have h1 := Real.hasSum_log_one_add_inv ha
  set t : ℝ := 1 / (2 * a + 1) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one (by linarith)]; linarith
  have ht2 : t ^ 2 < 1 := by nlinarith
  have h2 : HasSum (fun k : ℕ => 2 * t * (t ^ 2) ^ k) (2 * t * (1 - t ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (sq_nonneg t) ht2).mul_left (2 * t)
  have hle := hasSum_le (fun k : ℕ => ?_) h1 h2
  · have e1 : Real.log (1 + a⁻¹) = Real.log (a + 1) - Real.log a := by
      rw [← Real.log_div (by linarith) ha.ne']
      congr 1
      field_simp
    have e2 : 2 * t * (1 - t ^ 2)⁻¹ = 1 / (2 * a) + 1 / (2 * (a + 1)) := by
      have e3 : 1 - t ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
        rw [ht]; field_simp; ring
      rw [e3, ht]
      field_simp
      ring
    rw [e1, e2] at hle
    exact hle
  · have hk : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have e : t ^ (2 * k + 1) = t * (t ^ 2) ^ k := by rw [pow_succ, pow_mul]; ring
    rw [e]
    have hpos : 0 ≤ t * (t ^ 2) ^ k := by positivity
    calc 2 * (1 / (2 * (k : ℝ) + 1)) * (t * (t ^ 2) ^ k)
        ≤ 2 * 1 * (t * (t ^ 2) ^ k) := by gcongr
      _ = 2 * t * (t ^ 2) ^ k := by ring

/-! ## Digamma: upper bound -/

/-- `b_n = log(n+x) - 1/(2(n+x)) - ∑_{k<n} 1/(k+x)` (decreasing, with limit `ψ(x)`). -/
noncomputable def r11Zs_b (x : ℝ) (n : ℕ) : ℝ :=
  Real.log (n + x) - 1 / (2 * (n + x)) - ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + x)

lemma r11Zs_b_antitone {x : ℝ} (hx : 0 < x) : Antitone (r11Zs_b x) := by
  refine antitone_nat_of_succ_le fun n => ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h := r11Zs_log_trap (a := (n : ℝ) + x) (by linarith)
  unfold r11Zs_b
  rw [Finset.sum_range_succ]
  push_cast
  have e1 : (n : ℝ) + 1 + x = (n : ℝ) + x + 1 := by ring
  rw [e1]
  have e2 : 1 / (2 * ((n : ℝ) + x)) = 1 / ((n : ℝ) + x) - 1 / (2 * ((n : ℝ) + x)) := by
    have : (n : ℝ) + x ≠ 0 := by linarith
    field_simp
    ring
  linarith

theorem r11Zs_digamma_le {x : ℝ} (hx : 0 < x) (M : ℕ) :
    (digamma (x : ℂ)).re ≤ r11Zs_b x M := by
  have hs := hasSum_digamma (s := (x : ℂ)) (by simpa using hx)
  have hre := Complex.hasSum_re hs
  have hterm : ∀ k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (x : ℂ))).re
      = 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x) := by
    intro k
    have e : (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (x : ℂ)))
        = ((1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re]
  simp_rw [hterm] at hre
  rw [add_re, ofReal_re] at hre
  have h1 := hre.tendsto_sum_nat
  have h2 := Real.tendsto_harmonic_sub_log
  have h3 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h4 := (h1.sub h2).sub h3
  rw [add_sub_cancel_right, sub_zero] at h4
  refine le_of_tendsto h4 ?_
  filter_upwards [eventually_ge_atTop (max M 1)] with n hn
  have hnM : M ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hanti := r11Zs_b_antitone hx hnM
  refine le_trans ?_ hanti
  unfold r11Zs_b
  have hH : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
    rw [harmonic]
    push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [one_div]
  rw [hH, Finset.sum_sub_distrib]
  have hlog : Real.log n ≤ Real.log (n + x) := Real.log_le_log (by linarith) (by linarith)
  have hdiv : 1 / (2 * ((n : ℝ) + x)) ≤ (1 / 2 : ℝ) / n := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  linarith

/-! ## Trigamma: lower bound -/

lemma r11Zs_inv_sq_tele {x c : ℝ} (M : ℕ) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) (hcM : c < M + x)
    (hcond : c * (1 - c) ≤ (M + x) * (1 - 2 * c)) (j : ℕ) :
    ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + x) ^ 2 + 1 / (M + x - c) - 1 / ((M + j : ℕ) + x - c)
      ≤ ∑ k ∈ Finset.range (M + j), 1 / ((k : ℝ) + x) ^ 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : M + (j + 1) = M + j + 1 := rfl
    rw [e, Finset.sum_range_succ]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    set y : ℝ := ((M + j : ℕ) : ℝ) + x with hy
    have hyM : (M : ℝ) + x ≤ y := by rw [hy]; push_cast; linarith
    have hy0 : 0 < y - c := by linarith
    have hstep : 1 / (y - c) - 1 / (y + 1 - c) ≤ 1 / y ^ 2 := by
      have hy1 : 0 < y + 1 - c := by linarith
      have hypos : 0 < y := by linarith
      rw [div_sub_div _ _ hy0.ne' hy1.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : c * (1 - c) ≤ y * (1 - 2 * c) :=
        hcond.trans (mul_le_mul_of_nonneg_right hyM (by linarith))
      nlinarith
    have e2 : (((M + j + 1 : ℕ) : ℝ)) + x - c = y + 1 - c := by rw [hy]; push_cast; ring
    rw [e2]
    have e3 : (((M + j : ℕ) : ℝ)) + x - c = y - c := by rw [hy]
    rw [e3] at ih
    linarith

theorem r11Zs_trigamma_ge {x c : ℝ} (hx : 0 < x) (M : ℕ) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2)
    (hcM : c < M + x) (hcond : c * (1 - c) ≤ (M + x) * (1 - 2 * c)) (j : ℕ) :
    ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + x) ^ 2 + 1 / (M + x - c) - 1 / ((M + j : ℕ) + x - c)
      ≤ (deriv digamma (x : ℂ)).re := by
  have hmem : (0 : ℝ) < ((x : ℂ)).re := by simpa using hx
  have hd : HasDerivAt digamma (deriv digamma (x : ℂ)) (x : ℂ) :=
    (differentiableOn_digamma.differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hmem)).hasDerivAt
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hmap : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[<] x) (𝓝[≠] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have : y ≠ x := ne_of_lt hy
      simpa using this
  have htend : Tendsto (fun y : ℝ => (slope digamma (x : ℂ) (y : ℂ)).re) (𝓝[<] x)
      (𝓝 (deriv digamma (x : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp (hslope.comp hmap)
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsLT (show x / 2 < x by linarith)] with y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : 0 < y := by linarith
  have hs := hasSum_digamma_sub (z := (y : ℂ)) (z₀ := (x : ℂ)) (by simpa using hy0) hmem
  have hre := Complex.hasSum_re hs
  have hterm : ∀ k : ℕ, (1 / ((k : ℂ) + (x : ℂ)) - 1 / ((k : ℂ) + (y : ℂ))).re
      = 1 / ((k : ℝ) + x) - 1 / ((k : ℝ) + y) := by
    intro k
    have e : (1 / ((k : ℂ) + (x : ℂ)) - 1 / ((k : ℂ) + (y : ℂ)))
        = ((1 / ((k : ℝ) + x) - 1 / ((k : ℝ) + y) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re]
  simp_rw [hterm] at hre
  have hre2 := hre.div_const (y - x)
  have hslope_eq : (slope digamma (x : ℂ) (y : ℂ)).re
      = (digamma (y : ℂ) - digamma (x : ℂ)).re / (y - x) := by
    rw [slope_def_field, ← Complex.ofReal_sub, Complex.div_ofReal_re]
  rw [hslope_eq]
  have hnn : ∀ k : ℕ, 1 / ((k : ℝ) + x) ^ 2
      ≤ (1 / ((k : ℝ) + x) - 1 / ((k : ℝ) + y)) / (y - x) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hkx : 0 < (k : ℝ) + x := by linarith
    have hky : 0 < (k : ℝ) + y := by linarith
    have hyx : y - x < 0 := by linarith
    have e : (1 / ((k : ℝ) + x) - 1 / ((k : ℝ) + y)) / (y - x)
        = 1 / (((k : ℝ) + x) * ((k : ℝ) + y)) := by
      have : y - x ≠ 0 := hyx.ne
      field_simp
      ring
    rw [e]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hpos : ∀ k : ℕ, 0 ≤ (1 / ((k : ℝ) + x) - 1 / ((k : ℝ) + y)) / (y - x) := fun k =>
    le_trans (by positivity) (hnn k)
  have h1 := sum_le_hasSum (Finset.range (M + j)) (fun k _ => hpos k) hre2
  have h2 : ∑ k ∈ Finset.range (M + j), 1 / ((k : ℝ) + x) ^ 2
      ≤ ∑ k ∈ Finset.range (M + j), (1 / ((k : ℝ) + x) - 1 / ((k : ℝ) + y)) / (y - x) :=
    Finset.sum_le_sum fun k _ => hnn k
  have h3 := r11Zs_inv_sq_tele (x := x) M hc0 hc hcM hcond j
  linarith

/-! ## Certificates and values -/

theorem r11Zs_cert_digamma :
    (66281049763 / 10000000000 : ℚ) ≤ ∑ k ∈ Finset.range 255, 1 / ((k : ℚ) + 3 / 4) := by
  decide +kernel

theorem r11Zs_cert_trigamma34 :
    (25108743793 / 10000000000 : ℚ) ≤ ∑ k ∈ Finset.range 32, 1 / ((k : ℚ) + 3 / 4) ^ 2 := by
  decide +kernel

theorem r11Zs_cert_trigamma54 :
    (11667971749 / 10000000000 : ℚ) ≤ ∑ k ∈ Finset.range 32, 1 / ((k : ℚ) + 5 / 4) ^ 2 := by
  decide +kernel

theorem r11Zs_cert_pi :
    2 ^ 216464 * (10 ^ 6) ^ 2 ^ 17 ≤ 3141592 ^ 2 ^ 17 := by decide +kernel

/-- `Re ψ(3/4) ≤ -1.085858` (true value `-1.0858609`). -/
theorem r11Zs_digamma_three_quarters : (digamma (3 / 4)).re ≤ -1.085858 := by
  have h := r11Zs_digamma_le (x := 3 / 4) (by norm_num) 255
  rw [show ((3 / 4 : ℝ) : ℂ) = 3 / 4 by norm_num] at h
  unfold r11Zs_b at h
  have hc := (Rat.cast_le (K := ℝ)).mpr r11Zs_cert_digamma
  have hsum : ((∑ k ∈ Finset.range 255, 1 / ((k : ℚ) + 3 / 4) : ℚ) : ℝ)
      = ∑ k ∈ Finset.range 255, 1 / ((k : ℝ) + 3 / 4) := by
    push_cast; rfl
  rw [hsum, show ((66281049763 / 10000000000 : ℚ) : ℝ) = 66281049763 / 10000000000 by
    norm_num] at hc
  have hlog : Real.log (((255 : ℕ) : ℝ) + 3 / 4) ≤ 8 * Real.log 2 - 1 / 1024 := by
    have e : (((255 : ℕ) : ℝ) + 3 / 4) = 2 ^ 8 * (1023 / 1024) := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1023 / 1024 by norm_num)
    push_cast
    linarith
  have h2 := Real.log_two_lt_d9
  have e3 : (1 : ℝ) / (2 * (((255 : ℕ) : ℝ) + 3 / 4)) = 2 / 1023 := by norm_num
  rw [e3] at h
  linarith

/-- `Re ψ'(3/4) ≥ 2.54187` (true value `2.5418796`). -/
theorem r11Zs_trigamma_three_quarters : (2.54187 : ℝ) ≤ (deriv digamma (3 / 4)).re := by
  have h := r11Zs_trigamma_ge (x := 3 / 4) (c := 49 / 100) (by norm_num) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (10 ^ 9)
  rw [show ((3 / 4 : ℝ) : ℂ) = 3 / 4 by norm_num] at h
  have hc := (Rat.cast_le (K := ℝ)).mpr r11Zs_cert_trigamma34
  have hsum : ((∑ k ∈ Finset.range 32, 1 / ((k : ℚ) + 3 / 4) ^ 2 : ℚ) : ℝ)
      = ∑ k ∈ Finset.range 32, 1 / ((k : ℝ) + 3 / 4) ^ 2 := by
    push_cast; rfl
  rw [hsum, show ((25108743793 / 10000000000 : ℚ) : ℝ) = 25108743793 / 10000000000 by
    norm_num] at hc
  have e1 : (1 : ℝ) / (((32 : ℕ) : ℝ) + 3 / 4 - 49 / 100) = 100 / 3226 := by norm_num
  have e2 : (1 : ℝ) / (((32 + 10 ^ 9 : ℕ) : ℝ) + 3 / 4 - 49 / 100) ≤ 1 / 10 ^ 9 := by
    apply one_div_le_one_div_of_le (by norm_num)
    push_cast
    norm_num
  rw [e1] at h
  norm_num at h hc e2 ⊢
  linarith

/-- `Re ψ'(5/4) ≥ 1.19732` (true value `1.1973292`). -/
theorem r11Zs_trigamma_five_quarters : (1.19732 : ℝ) ≤ (deriv digamma (5 / 4)).re := by
  have h := r11Zs_trigamma_ge (x := 5 / 4) (c := 49 / 100) (by norm_num) 32 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (10 ^ 9)
  rw [show ((5 / 4 : ℝ) : ℂ) = 5 / 4 by norm_num] at h
  have hc := (Rat.cast_le (K := ℝ)).mpr r11Zs_cert_trigamma54
  have hsum : ((∑ k ∈ Finset.range 32, 1 / ((k : ℚ) + 5 / 4) ^ 2 : ℚ) : ℝ)
      = ∑ k ∈ Finset.range 32, 1 / ((k : ℝ) + 5 / 4) ^ 2 := by
    push_cast; rfl
  rw [hsum, show ((11667971749 / 10000000000 : ℚ) : ℝ) = 11667971749 / 10000000000 by
    norm_num] at hc
  have e1 : (1 : ℝ) / (((32 : ℕ) : ℝ) + 5 / 4 - 49 / 100) = 100 / 3276 := by norm_num
  have e2 : (1 : ℝ) / (((32 + 10 ^ 9 : ℕ) : ℝ) + 5 / 4 - 49 / 100) ≤ 1 / 10 ^ 9 := by
    apply one_div_le_one_div_of_le (by norm_num)
    push_cast
    norm_num
  rw [e1] at h
  norm_num at h hc e2 ⊢
  linarith

/-- `log π > 1.14472` (true value `1.1447299`). -/
theorem r11Zs_log_pi_gt : (1.14472 : ℝ) < Real.log Real.pi := by
  have h1 : (2 : ℝ) ^ 216464 ≤ Real.pi ^ 2 ^ 17 := by
    have h2 : (3.141592 : ℝ) ^ 2 ^ 17 ≤ Real.pi ^ 2 ^ 17 :=
      pow_le_pow_left₀ (by norm_num) Real.pi_gt_d6.le _
    have h3 : (2 : ℝ) ^ 216464 ≤ (3.141592 : ℝ) ^ 2 ^ 17 := by
      rw [show (3.141592 : ℝ) = 3141592 / 10 ^ 6 by norm_num, div_pow,
        le_div_iff₀ (by positivity)]
      exact_mod_cast r11Zs_cert_pi
    exact h3.trans h2
  have := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  have h2 := Real.log_two_gt_d9
  linarith

end DetPrimality.Bach
