import DetPrimality.Bach.R11ChiDefs

/-!
# Round 11, Lemma 3: certified upper bounds for `F_k = ∑ Λ(n) log^k n · n^{-3/2}`, `k ≤ 3`

With `D_j = ∑ log^j n · n^{-3/2}` the Leibniz identities
`D_{k+1} = ∑_{i ≤ k} C(k,i) F_{k-i} D_i` (`r11Chi_leibniz`) follow by differentiating
`LSeries Λ · LSeries 1 = LSeries log` on `Re s > 1`.  `D_0, …, D_4` are bounded on both sides:
the terms `n ≤ 256` by exact rational arithmetic (`decide +kernel`), the tails by telescoping
against the antiderivative `t^{-1/2} P_j(log t)`.

Results: `r11Chi_F_summable`, `r11Chi_F_bounds`
(`1.5048 ≤ F_0 ≤ 1.5058`, `3.851 ≤ F_1 ≤ 3.859`, `15.89 ≤ F_2 ≤ 15.96`, `F_3 ≤ 96.4`),
and the corollaries `r11Chi_F1_le`, `r11Chi_F2_le`, `r11Chi_F3_le`.
-/

open Complex

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `D_j = ∑ log^j n · n^{-3/2}`. -/
noncomputable def r11Chi_D (j : ℕ) : ℝ := ∑' n : ℕ, Real.log n ^ j / (n : ℝ) ^ (3 / 2 : ℝ)

/-! ## L-series glue -/

theorem r11Chi_logMul_iterate (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = Complex.log n ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show Complex.log n * (LSeries.logMul^[k] f) n = _
    rw [ih]; ring

theorem r11Chi_abscissa_iterate (f : ℕ → ℂ) (k : ℕ) :
    LSeries.abscissaOfAbsConv (LSeries.logMul^[k] f) = LSeries.abscissaOfAbsConv f := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]

theorem r11Chi_abscissa_lt {f : ℕ → ℂ} (hf : ∀ s : ℂ, 1 < s.re → LSeriesSummable f s) {s : ℂ}
    (hs : 1 < s.re) : LSeries.abscissaOfAbsConv f < s.re := by
  have h := (hf (((1 + s.re) / 2 : ℝ) : ℂ)
    (by rw [Complex.ofReal_re]; linarith)).abscissaOfAbsConv_le
  refine lt_of_le_of_lt h ?_
  rw [Complex.ofReal_re]
  exact_mod_cast (by linarith : (1 + s.re) / 2 < s.re)

theorem r11Chi_hasDerivAt_iter {f : ℕ → ℂ} (hf : ∀ s : ℂ, 1 < s.re → LSeriesSummable f s)
    (i : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (LSeries (LSeries.logMul^[i] f)) (-LSeries (LSeries.logMul^[i + 1] f) s) s := by
  rw [Function.iterate_succ_apply']
  exact LSeries_hasDerivAt (by rw [r11Chi_abscissa_iterate]; exact r11Chi_abscissa_lt hf hs)

theorem r11Chi_LSeries_real (f : ℕ → ℝ) (k : ℕ) :
    LSeries (LSeries.logMul^[k] (fun n => (f n : ℂ))) ((3 / 2 : ℝ) : ℂ)
      = ((∑' n : ℕ, f n * Real.log n ^ k / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [← szs_LSeries_ofReal (fun n => f n * Real.log n ^ k) (by norm_num)]
  refine LSeries_congr (fun {n} _ => ?_) _
  rw [r11Chi_logMul_iterate, ← Complex.natCast_log]
  push_cast; ring

theorem r11Chi_summable_real (f : ℕ → ℝ)
    (hf : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (f n : ℂ)) s) (k : ℕ) :
    Summable fun n : ℕ => f n * Real.log n ^ k / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have h : LSeriesSummable (LSeries.logMul^[k] (fun n => (f n : ℂ))) ((3 / 2 : ℝ) : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      rw [r11Chi_abscissa_iterate]
      exact r11Chi_abscissa_lt hf (by rw [Complex.ofReal_re]; norm_num))
  rw [LSeriesSummable_congr (g := fun n => ((f n * Real.log n ^ k : ℝ) : ℂ)) _ (fun {n} _ => by
    rw [r11Chi_logMul_iterate, ← Complex.natCast_log]; push_cast; ring)] at h
  unfold LSeriesSummable at h
  rw [show LSeries.term (fun n => ((f n * Real.log n ^ k : ℝ) : ℂ)) ((3 / 2 : ℝ) : ℂ)
      = fun n => ((f n * Real.log n ^ k / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) from
    funext fun n => szs_term_ofReal _ (by norm_num) n] at h
  exact Complex.summable_ofReal.mp h

theorem r11Chi_summable_one {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun _ : ℕ => (((1 : ℝ)) : ℂ)) s :=
  (LSeriesSummable_congr s (fun {n} _ => by simp)).mpr (LSeriesSummable_one_iff.mpr hs)

/-- **Summability of `F_k`.** -/
theorem r11Chi_F_summable (k : ℕ) :
    Summable fun n : ℕ => Λ n * Real.log n ^ k / (n : ℝ) ^ (3 / 2 : ℝ) :=
  r11Chi_summable_real (fun n => Λ n)
    (fun _ hs => ArithmeticFunction.LSeriesSummable_vonMangoldt hs) k

theorem r11Chi_D_summable (j : ℕ) :
    Summable fun n : ℕ => Real.log n ^ j / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have h := r11Chi_summable_real (fun _ => (1 : ℝ)) (fun _ hs => r11Chi_summable_one hs) j
  simpa only [one_mul] using h

/-! ## The Leibniz identities -/

noncomputable def r11Chi_A (i : ℕ) (s : ℂ) : ℂ :=
  LSeries (LSeries.logMul^[i] (fun n : ℕ => ((Λ n : ℝ) : ℂ))) s

noncomputable def r11Chi_Z (j : ℕ) (s : ℂ) : ℂ :=
  LSeries (LSeries.logMul^[j] (fun _ : ℕ => (((1 : ℝ)) : ℂ))) s

theorem r11Chi_hA (i : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (r11Chi_A i) (-r11Chi_A (i + 1) s) s :=
  r11Chi_hasDerivAt_iter (fun _ hs => ArithmeticFunction.LSeriesSummable_vonMangoldt hs) i hs

theorem r11Chi_hZ (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (r11Chi_Z j) (-r11Chi_Z (j + 1) s) s :=
  r11Chi_hasDerivAt_iter (fun _ hs => r11Chi_summable_one hs) j hs

theorem r11Chi_deriv_unique {f g f' g' : ℂ → ℂ}
    (hfg : ∀ s : ℂ, 1 < s.re → f s = g s)
    (hf : ∀ s : ℂ, 1 < s.re → HasDerivAt f (f' s) s)
    (hg : ∀ s : ℂ, 1 < s.re → HasDerivAt g (g' s) s) (s : ℂ) (hs : 1 < s.re) :
    f' s = g' s := by
  have hev : f =ᶠ[nhds s] g := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact hfg z hz
  exact (hf s hs).unique ((hg s hs).congr_of_eventuallyEq hev)

theorem r11Chi_E0 {s : ℂ} (hs : 1 < s.re) : r11Chi_A 0 s * r11Chi_Z 0 s = r11Chi_Z 1 s := by
  have h1 := LSeries_convolution' (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (LSeriesSummable_one_iff.mpr hs)
  rw [ArithmeticFunction.convolution_vonMangoldt_const_one] at h1
  have hZ0 : r11Chi_Z 0 s = LSeries 1 s := by
    unfold r11Chi_Z
    exact LSeries_congr (fun {n} _ => by simp) s
  have hZ1 : r11Chi_Z 1 s = LSeries (fun n : ℕ => Complex.log n) s := by
    unfold r11Chi_Z
    exact LSeries_congr (fun {n} _ => by rw [r11Chi_logMul_iterate]; simp) s
  rw [hZ0, hZ1, h1]
  rfl

theorem r11Chi_E1 {s : ℂ} (hs : 1 < s.re) :
    r11Chi_A 1 s * r11Chi_Z 0 s + r11Chi_A 0 s * r11Chi_Z 1 s = r11Chi_Z 2 s := by
  have h := r11Chi_deriv_unique (f := fun s => r11Chi_A 0 s * r11Chi_Z 0 s) (g := r11Chi_Z 1)
    (f' := fun s => -r11Chi_A 1 s * r11Chi_Z 0 s + r11Chi_A 0 s * -r11Chi_Z 1 s)
    (g' := fun s => -r11Chi_Z 2 s)
    (fun s hs => r11Chi_E0 hs) (fun s hs => (r11Chi_hA 0 hs).mul (r11Chi_hZ 0 hs))
    (fun s hs => r11Chi_hZ 1 hs) s hs
  beta_reduce at h
  linear_combination -h

theorem r11Chi_E2 {s : ℂ} (hs : 1 < s.re) :
    r11Chi_A 2 s * r11Chi_Z 0 s + 2 * (r11Chi_A 1 s * r11Chi_Z 1 s)
      + r11Chi_A 0 s * r11Chi_Z 2 s = r11Chi_Z 3 s := by
  have h := r11Chi_deriv_unique
    (f := fun s => r11Chi_A 1 s * r11Chi_Z 0 s + r11Chi_A 0 s * r11Chi_Z 1 s) (g := r11Chi_Z 2)
    (f' := fun s => (-r11Chi_A 2 s * r11Chi_Z 0 s + r11Chi_A 1 s * -r11Chi_Z 1 s)
      + (-r11Chi_A 1 s * r11Chi_Z 1 s + r11Chi_A 0 s * -r11Chi_Z 2 s))
    (g' := fun s => -r11Chi_Z 3 s)
    (fun s hs => r11Chi_E1 hs)
    (fun s hs => ((r11Chi_hA 1 hs).mul (r11Chi_hZ 0 hs)).add
      ((r11Chi_hA 0 hs).mul (r11Chi_hZ 1 hs)))
    (fun s hs => r11Chi_hZ 2 hs) s hs
  beta_reduce at h
  linear_combination -h

theorem r11Chi_E3 {s : ℂ} (hs : 1 < s.re) :
    r11Chi_A 3 s * r11Chi_Z 0 s + 3 * (r11Chi_A 2 s * r11Chi_Z 1 s)
      + 3 * (r11Chi_A 1 s * r11Chi_Z 2 s) + r11Chi_A 0 s * r11Chi_Z 3 s = r11Chi_Z 4 s := by
  have h := r11Chi_deriv_unique
    (f := fun s => r11Chi_A 2 s * r11Chi_Z 0 s + 2 * (r11Chi_A 1 s * r11Chi_Z 1 s)
      + r11Chi_A 0 s * r11Chi_Z 2 s) (g := r11Chi_Z 3)
    (f' := fun s => (-r11Chi_A 3 s * r11Chi_Z 0 s + r11Chi_A 2 s * -r11Chi_Z 1 s)
      + 2 * (-r11Chi_A 2 s * r11Chi_Z 1 s + r11Chi_A 1 s * -r11Chi_Z 2 s)
      + (-r11Chi_A 1 s * r11Chi_Z 2 s + r11Chi_A 0 s * -r11Chi_Z 3 s))
    (g' := fun s => -r11Chi_Z 4 s)
    (fun s hs => r11Chi_E2 hs)
    (fun s hs => (((r11Chi_hA 2 hs).mul (r11Chi_hZ 0 hs)).add
      (((r11Chi_hA 1 hs).mul (r11Chi_hZ 1 hs)).const_mul 2)).add
      ((r11Chi_hA 0 hs).mul (r11Chi_hZ 2 hs)))
    (fun s hs => r11Chi_hZ 3 hs) s hs
  beta_reduce at h
  linear_combination -h

theorem r11Chi_A_val (i : ℕ) : r11Chi_A i ((3 / 2 : ℝ) : ℂ) = (r11Chi_F i : ℂ) :=
  r11Chi_LSeries_real (fun n => Λ n) i

theorem r11Chi_Z_val (j : ℕ) : r11Chi_Z j ((3 / 2 : ℝ) : ℂ) = (r11Chi_D j : ℂ) := by
  have h := r11Chi_LSeries_real (fun _ => (1 : ℝ)) j
  simp only [one_mul] at h
  exact h

/-- **Leibniz identities** `D_{k+1} = ∑_i C(k,i) F_{k-i} D_i`, `k ≤ 3`. -/
theorem r11Chi_leibniz :
    r11Chi_F 0 * r11Chi_D 0 = r11Chi_D 1 ∧
    r11Chi_F 1 * r11Chi_D 0 + r11Chi_F 0 * r11Chi_D 1 = r11Chi_D 2 ∧
    r11Chi_F 2 * r11Chi_D 0 + 2 * (r11Chi_F 1 * r11Chi_D 1) + r11Chi_F 0 * r11Chi_D 2
      = r11Chi_D 3 ∧
    r11Chi_F 3 * r11Chi_D 0 + 3 * (r11Chi_F 2 * r11Chi_D 1) + 3 * (r11Chi_F 1 * r11Chi_D 2)
      + r11Chi_F 0 * r11Chi_D 3 = r11Chi_D 4 := by
  have hs : 1 < (((3 / 2 : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; norm_num
  have e0 := r11Chi_E0 hs
  have e1 := r11Chi_E1 hs
  have e2 := r11Chi_E2 hs
  have e3 := r11Chi_E3 hs
  simp only [r11Chi_A_val, r11Chi_Z_val] at e0 e1 e2 e3
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast e0
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3

/-! ## Rational bounds for `log n` -/

def r11Chi_lqU (n : ℕ) : ℚ := ((Nat.log2 (n ^ 4096) + 1 : ℕ) : ℚ) / 4096

def r11Chi_lqL (n : ℕ) : ℚ := ((Nat.log2 (n ^ 4096) : ℕ) : ℚ) / 4096

theorem r11Chi_lqU_nonneg (n : ℕ) : 0 ≤ r11Chi_lqU n := by
  unfold r11Chi_lqU; positivity

theorem r11Chi_lqL_nonneg (n : ℕ) : 0 ≤ r11Chi_lqL n := by
  unfold r11Chi_lqL; positivity

theorem r11Chi_log_le (n : ℕ) (hn : 0 < n) :
    Real.log n ≤ (r11Chi_lqU n : ℝ) * Real.log 2 := by
  have h1 : n ^ 4096 < 2 ^ (Nat.log2 (n ^ 4096) + 1) := Nat.lt_log2_self
  have h3 : ((n : ℝ)) ^ 4096 ≤ (2 : ℝ) ^ (Nat.log2 (n ^ 4096) + 1) := by exact_mod_cast h1.le
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h4 := Real.log_le_log (by positivity) h3
  rw [Real.log_pow, Real.log_pow] at h4
  rw [r11Chi_lqU]
  push_cast at h4 ⊢
  linarith

theorem r11Chi_le_log (n : ℕ) (hn : 0 < n) :
    (r11Chi_lqL n : ℝ) * Real.log 2 ≤ Real.log n := by
  have h1 : 2 ^ Nat.log2 (n ^ 4096) ≤ n ^ 4096 := Nat.log2_self_le (pow_pos hn 4096).ne'
  have h3 : (2 : ℝ) ^ Nat.log2 (n ^ 4096) ≤ ((n : ℝ)) ^ 4096 := by exact_mod_cast h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h4 := Real.log_le_log (by positivity) h3
  rw [Real.log_pow, Real.log_pow] at h4
  rw [r11Chi_lqL]
  push_cast at h4 ⊢
  linarith

theorem r11Chi_term_le (j n : ℕ) :
    Real.log ((n + 1 : ℕ) : ℝ) ^ j / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)
      ≤ ((r11Chi_lqU (n + 1) ^ j * szs_ru (n + 1) : ℚ) : ℝ) * Real.log 2 ^ j := by
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := r11Chi_log_le (n + 1) (Nat.succ_pos n)
  have h2 := szs_inv_rpow_le (n + 1)
  have h0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hq : (0 : ℝ) ≤ (r11Chi_lqU (n + 1) : ℝ) := Rat.cast_nonneg.mpr (r11Chi_lqU_nonneg _)
  have h3 : Real.log ((n + 1 : ℕ) : ℝ) ^ j ≤ ((r11Chi_lqU (n + 1) : ℝ) * Real.log 2) ^ j :=
    pow_le_pow_left₀ h0 h1 j
  rw [Rat.cast_mul, Rat.cast_pow]
  calc Real.log ((n + 1 : ℕ) : ℝ) ^ j / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)
      = Real.log ((n + 1 : ℕ) : ℝ) ^ j * (1 / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) := by ring
    _ ≤ ((r11Chi_lqU (n + 1) : ℝ) * Real.log 2) ^ j * (szs_ru (n + 1) : ℝ) :=
        mul_le_mul h3 h2 (by positivity) (pow_nonneg (mul_nonneg hq hl2p.le) j)
    _ = _ := by rw [mul_pow]; ring

theorem r11Chi_le_term (j n : ℕ) :
    ((r11Chi_lqL (n + 1) ^ j * szs_rl (n + 1) : ℚ) : ℝ) * Real.log 2 ^ j
      ≤ Real.log ((n + 1 : ℕ) : ℝ) ^ j / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := r11Chi_le_log (n + 1) (Nat.succ_pos n)
  have h2 := szs_le_inv_rpow (n + 1)
  have h0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hq : (0 : ℝ) ≤ (r11Chi_lqL (n + 1) : ℝ) := Rat.cast_nonneg.mpr (r11Chi_lqL_nonneg _)
  have hr : (0 : ℝ) ≤ (szs_rl (n + 1) : ℝ) :=
    Rat.cast_nonneg.mpr (by unfold szs_rl; positivity)
  have h3 : ((r11Chi_lqL (n + 1) : ℝ) * Real.log 2) ^ j ≤ Real.log ((n + 1 : ℕ) : ℝ) ^ j :=
    pow_le_pow_left₀ (mul_nonneg hq hl2p.le) h1 j
  rw [Rat.cast_mul, Rat.cast_pow]
  calc (r11Chi_lqL (n + 1) : ℝ) ^ j * (szs_rl (n + 1) : ℝ) * Real.log 2 ^ j
      = ((r11Chi_lqL (n + 1) : ℝ) * Real.log 2) ^ j * (szs_rl (n + 1) : ℝ) := by
        rw [mul_pow]; ring
    _ ≤ Real.log ((n + 1 : ℕ) : ℝ) ^ j * (1 / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :=
        mul_le_mul h3 h2 hr (pow_nonneg h0 j)
    _ = _ := by ring

/-- Rational upper bound for `∑_{1 ≤ n ≤ 256} log^j n · n^{-3/2} / log^j 2`. -/
def r11Chi_U (j : ℕ) : ℚ := ∑ n ∈ Finset.range 256, r11Chi_lqU (n + 1) ^ j * szs_ru (n + 1)

/-- Rational lower bound for `∑_{1 ≤ n ≤ 255} log^j n · n^{-3/2} / log^j 2`. -/
def r11Chi_L (j : ℕ) : ℚ := ∑ n ∈ Finset.range 255, r11Chi_lqL (n + 1) ^ j * szs_rl (n + 1)

theorem r11Chi_partial_le (j : ℕ) :
    ∑ n ∈ Finset.range 257, Real.log (n : ℝ) ^ j / (n : ℝ) ^ (3 / 2 : ℝ)
      ≤ (r11Chi_U j : ℝ) * Real.log 2 ^ j := by
  rw [Finset.sum_range_succ', Nat.cast_zero, Real.zero_rpow (by norm_num), div_zero, add_zero,
    r11Chi_U, Rat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun n _ => r11Chi_term_le j n

theorem r11Chi_partial_ge (j : ℕ) :
    (r11Chi_L j : ℝ) * Real.log 2 ^ j
      ≤ ∑ n ∈ Finset.range 256, Real.log (n : ℝ) ^ j / (n : ℝ) ^ (3 / 2 : ℝ) := by
  rw [Finset.sum_range_succ', Nat.cast_zero, Real.zero_rpow (by norm_num), div_zero, add_zero,
    r11Chi_L, Rat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun n _ => r11Chi_le_term j n

/-! ## Certificates -/

theorem r11Chi_cert_U0 : r11Chi_U 0 ≤ 248750 / 100000 := by decide +kernel
theorem r11Chi_cert_U1 : r11Chi_U 1 ≤ 431385 / 100000 := by decide +kernel
theorem r11Chi_cert_U2 : r11Chi_U 2 ≤ 1743722 / 100000 := by decide +kernel
theorem r11Chi_cert_U3 : r11Chi_U 3 ≤ 8712106 / 100000 := by decide +kernel
theorem r11Chi_cert_U4 : r11Chi_U 4 ≤ 49322580 / 100000 := by decide +kernel
theorem r11Chi_cert_L0 : 248725 / 100000 ≤ r11Chi_L 0 := by decide +kernel
theorem r11Chi_cert_L1 : 431128 / 100000 ≤ r11Chi_L 1 := by decide +kernel
theorem r11Chi_cert_L2 : 1741948 / 100000 ≤ r11Chi_L 2 := by decide +kernel
theorem r11Chi_cert_L3 : 8698327 / 100000 ≤ r11Chi_L 3 := by decide +kernel
theorem r11Chi_cert_L4 : 49214065 / 100000 ≤ r11Chi_L 4 := by decide +kernel

/-! ## Tails -/

/-- `P_0 = 2`, `P_{j+1}(L) = 2 L^{j+1} + 2 (j+1) P_j(L)`. -/
noncomputable def r11Chi_P : ℕ → ℝ → ℝ
  | 0, _ => 2
  | j + 1, L => 2 * L ^ (j + 1) + 2 * ((j : ℝ) + 1) * r11Chi_P j L

theorem r11Chi_P_nonneg (j : ℕ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ r11Chi_P j L := by
  induction j with
  | zero => rw [r11Chi_P]; norm_num
  | succ j ih => rw [r11Chi_P]; positivity

theorem r11Chi_P_mono (j : ℕ) {L M : ℝ} (hL : 0 ≤ L) (hLM : L ≤ M) :
    r11Chi_P j L ≤ r11Chi_P j M := by
  induction j with
  | zero => rw [r11Chi_P, r11Chi_P]
  | succ j ih =>
    rw [r11Chi_P, r11Chi_P]
    have h1 := pow_le_pow_left₀ hL hLM (j + 1)
    have h2 := mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ 2 * ((j : ℝ) + 1))
    linarith

/-- Antiderivative of `-log^j t · t^{-3/2}`. -/
noncomputable def r11Chi_G (j : ℕ) (t : ℝ) : ℝ :=
  r11Chi_P j (Real.log t) * t ^ (-(1 / 2) : ℝ)

theorem r11Chi_hasDerivAt_G (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (r11Chi_G j) (-(Real.log t ^ j / t ^ (3 / 2 : ℝ))) t := by
  have h2 : HasDerivAt (fun t : ℝ => t ^ (-(1 / 2) : ℝ))
      (-(1 / 2) * t ^ (-(1 / 2) - 1 : ℝ)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have e1 : t ^ (-(1 / 2) - 1 : ℝ) = t ^ (-(3 / 2) : ℝ) := by
    congr 1; norm_num
  have e2 : t ^ (-(1 / 2) : ℝ) = t * t ^ (-(3 / 2) : ℝ) := by
    rw [show (-(1 / 2) : ℝ) = 1 + -(3 / 2) by norm_num, Real.rpow_add ht, Real.rpow_one]
  have e3 : ∀ x : ℝ, x / t ^ (3 / 2 : ℝ) = x * t ^ (-(3 / 2) : ℝ) := fun x => by
    rw [Real.rpow_neg ht.le, div_eq_mul_inv]
  induction j with
  | zero =>
    have h := h2.const_mul 2
    have e : r11Chi_G 0 = fun t : ℝ => 2 * t ^ (-(1 / 2) : ℝ) := by
      funext t; simp only [r11Chi_G, r11Chi_P]
    rw [e]
    refine h.congr_deriv ?_
    rw [e3, e1]
    ring
  | succ j ih =>
    have hl : HasDerivAt (fun t : ℝ => Real.log t ^ (j + 1))
        (((j : ℝ) + 1) * Real.log t ^ j * t⁻¹) t := by
      have := (Real.hasDerivAt_log ht.ne').pow (j + 1)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at this
      exact this
    have h := ((hl.mul h2).const_mul 2).add (ih.const_mul (2 * ((j : ℝ) + 1)))
    have e : r11Chi_G (j + 1) = fun t : ℝ => 2 * (Real.log t ^ (j + 1) * t ^ (-(1 / 2) : ℝ))
        + 2 * ((j : ℝ) + 1) * r11Chi_G j t := by
      funext t; simp only [r11Chi_G, r11Chi_P]; ring
    rw [e]
    refine h.congr_deriv ?_
    simp only [e3, e1, e2]
    have ht' := ht.ne'
    generalize t ^ (-(3 / 2) : ℝ) = u
    field_simp
    ring

theorem r11Chi_f_anti {j : ℕ} (hj : j ≤ 4) {s t : ℝ} (hs : 16 ≤ s) (hst : s ≤ t) :
    Real.log t ^ j / t ^ (3 / 2 : ℝ) ≤ Real.log s ^ j / s ^ (3 / 2 : ℝ) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [pow_zero]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hs0 _)
      (Real.rpow_le_rpow hs0.le hst (by norm_num))
  · have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
    have hj4 : (j : ℝ) ≤ 4 := by exact_mod_cast hj
    set a : ℝ := 3 / (2 * j) with ha
    have ha0 : 0 < a := by positivity
    have hexp : Real.exp a⁻¹ ≤ 16 := by
      have hl2 := Real.log_two_gt_d9
      have h16 : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
      have h1 : a⁻¹ ≤ Real.log 16 := by
        rw [h16, ha, inv_div]
        have : 2 * (j : ℝ) / 3 ≤ 8 / 3 := by linarith
        linarith
      calc Real.exp a⁻¹ ≤ Real.exp (Real.log 16) := Real.exp_le_exp.mpr h1
        _ = 16 := Real.exp_log (by norm_num)
    have hanti := Real.log_div_self_rpow_antitoneOn ha0
    have h := hanti (Set.mem_Ici.mpr (hexp.trans hs))
      (Set.mem_Ici.mpr (hexp.trans (hs.trans hst))) hst
    simp only at h
    have hlt0 : 0 ≤ Real.log t / t ^ a :=
      div_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg ht0.le _)
    have hp := pow_le_pow_left₀ hlt0 h j
    have e : ∀ x : ℝ, 0 < x → (x ^ a) ^ j = x ^ (3 / 2 : ℝ) := fun x hx => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      congr 1
      rw [ha]; field_simp
    rw [div_pow, div_pow, e t ht0, e s hs0] at hp
    exact hp

theorem r11Chi_tele {j : ℕ} (hj : j ≤ 4) {x : ℝ} (hx : 16 ≤ x) :
    Real.log (x + 1) ^ j / (x + 1) ^ (3 / 2 : ℝ) ≤ r11Chi_G j x - r11Chi_G j (x + 1) ∧
    r11Chi_G j x - r11Chi_G j (x + 1) ≤ Real.log x ^ j / x ^ (3 / 2 : ℝ) := by
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (r11Chi_G j)
    (fun t => -(Real.log t ^ j / t ^ (3 / 2 : ℝ))) (by linarith : x < x + 1)
    (fun t ht => (r11Chi_hasDerivAt_G j (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => r11Chi_hasDerivAt_G j (by linarith [ht.1]))
  rw [add_sub_cancel_left, div_one] at hceq
  have h1 := r11Chi_f_anti hj (hx.trans hc.1.le) hc.2.le
  have h2 := r11Chi_f_anti hj hx hc.1.le
  constructor <;> linarith

theorem r11Chi_term_nonneg (j n : ℕ) : 0 ≤ Real.log (n : ℝ) ^ j / (n : ℝ) ^ (3 / 2 : ℝ) :=
  div_nonneg (pow_nonneg (Real.log_natCast_nonneg n) j) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem r11Chi_D_le {j : ℕ} (hj : j ≤ 4) :
    r11Chi_D j ≤ (r11Chi_U j : ℝ) * Real.log 2 ^ j + r11Chi_G j 256 := by
  unfold r11Chi_D
  refine Real.tsum_le_of_sum_range_le (r11Chi_term_nonneg j) fun N => ?_
  have htele := szs_sum_range_le_of_tele
    (fun n : ℕ => Real.log (n : ℝ) ^ j / (n : ℝ) ^ (3 / 2 : ℝ))
    (fun n : ℕ => r11Chi_G j n) 256 (r11Chi_term_nonneg j)
    (fun n _ => by
      show 0 ≤ r11Chi_P j (Real.log (n : ℝ)) * (n : ℝ) ^ (-(1 / 2) : ℝ)
      exact mul_nonneg (r11Chi_P_nonneg j (Real.log_natCast_nonneg n))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n hn => by
      have hn' : (16 : ℝ) ≤ n := by
        have : (256 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have := (r11Chi_tele hj hn').1
      simp only [Nat.cast_add, Nat.cast_one]
      exact this) N
  have hfin := r11Chi_partial_le j
  have e : (256 + 1 : ℕ) = 257 := rfl
  beta_reduce at htele
  rw [e, show (((256 : ℕ) : ℝ)) = 256 by norm_num] at htele
  linarith

theorem r11Chi_D_ge {j : ℕ} (hj : j ≤ 4) :
    (r11Chi_L j : ℝ) * Real.log 2 ^ j + r11Chi_G j 256 - r11Chi_G j (2 ^ 64) ≤ r11Chi_D j := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((256 + k : ℕ) : ℝ) = 2 ^ 64 := ⟨2 ^ 64 - 256, by norm_num⟩
  have hsum := r11Chi_D_summable j
  have htele := szs_sum_range_ge_of_tele
    (fun n : ℕ => Real.log (n : ℝ) ^ j / (n : ℝ) ^ (3 / 2 : ℝ))
    (fun n : ℕ => r11Chi_G j n) 256
    (fun n hn => by
      have hn' : (16 : ℝ) ≤ n := by
        have : (256 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have := (r11Chi_tele hj hn').2
      simp only [Nat.cast_add, Nat.cast_one]
      exact this) k
  have hle := hsum.sum_le_tsum (Finset.range (256 + k)) (fun i _ => r11Chi_term_nonneg j i)
  have hfin := r11Chi_partial_ge j
  beta_reduce at htele
  rw [hk, show (((256 : ℕ) : ℝ)) = 256 by norm_num] at htele
  unfold r11Chi_D
  linarith

theorem r11Chi_G_256 (j : ℕ) : r11Chi_G j 256 = r11Chi_P j (8 * Real.log 2) / 16 := by
  unfold r11Chi_G
  have hr : (256 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 16 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, show (256 : ℝ) = 16 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  have hl : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  rw [hr, hl]; ring

theorem r11Chi_G_big (j : ℕ) : r11Chi_G j (2 ^ 64) ≤ r11Chi_P j 45 / 2 ^ 32 := by
  unfold r11Chi_G
  have hr : ((2 : ℝ) ^ 64) ^ (-(1 / 2) : ℝ) = 1 / 2 ^ 32 := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      show ((2 : ℝ) ^ 64) = (2 ^ 32) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
    norm_num
  have hl2 := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log ((2 : ℝ) ^ 64) = 64 * Real.log 2 := by
    rw [Real.log_pow]; norm_num
  rw [hr, hl]
  have := r11Chi_P_mono j (L := 64 * Real.log 2) (M := 45) (by positivity) (by linarith)
  have h32 : (0 : ℝ) < 2 ^ 32 := by positivity
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right this h32.le

theorem r11Chi_D_le' {j : ℕ} (hj : j ≤ 4) {c : ℝ} (hc0 : 0 ≤ c) (hc : (r11Chi_U j : ℝ) ≤ c) :
    r11Chi_D j ≤ c * (0.6931471808 : ℝ) ^ j + r11Chi_P j (8 * 0.6931471808) / 16 := by
  have h := r11Chi_D_le hj
  have hl2 := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [r11Chi_G_256] at h
  have h1 : (r11Chi_U j : ℝ) * Real.log 2 ^ j ≤ c * (0.6931471808 : ℝ) ^ j :=
    mul_le_mul hc (pow_le_pow_left₀ hl2p.le (by linarith) j) (by positivity) hc0
  have h2 := r11Chi_P_mono j (L := 8 * Real.log 2) (M := 8 * 0.6931471808) (by positivity)
    (by linarith)
  linarith

theorem r11Chi_D_ge' {j : ℕ} (hj : j ≤ 4) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ (r11Chi_L j : ℝ)) :
    c * (0.6931471803 : ℝ) ^ j + r11Chi_P j (8 * 0.6931471803) / 16 - r11Chi_P j 45 / 2 ^ 32
      ≤ r11Chi_D j := by
  have h := r11Chi_D_ge hj
  have hl2 := Real.log_two_gt_d9
  have hb := r11Chi_G_big j
  rw [r11Chi_G_256] at h
  have h1 : c * (0.6931471803 : ℝ) ^ j ≤ (r11Chi_L j : ℝ) * Real.log 2 ^ j :=
    mul_le_mul hc (pow_le_pow_left₀ (by norm_num) (by linarith) j) (by positivity)
      (hc0.trans hc)
  have h2 := r11Chi_P_mono j (L := 8 * 0.6931471803) (M := 8 * Real.log 2) (by norm_num)
    (by linarith)
  linarith

/-! ## Two-sided bounds for `D_0, …, D_4` -/

theorem r11Chi_D0_le : r11Chi_D 0 ≤ 2.6125 := by
  have h := r11Chi_D_le' (j := 0) (by norm_num) (c := 2.4875) (by norm_num)
    (((Rat.cast_le (K := ℝ)).mpr r11Chi_cert_U0).trans (le_of_eq (by norm_num)))
  norm_num [r11Chi_P] at h ⊢
  linarith

theorem r11Chi_D1_le : r11Chi_D 1 ≤ 3.9333 := by
  have h := r11Chi_D_le' (j := 1) (by norm_num) (c := 4.31385) (by norm_num)
    (((Rat.cast_le (K := ℝ)).mpr r11Chi_cert_U1).trans (le_of_eq (by norm_num)))
  norm_num [r11Chi_P] at h ⊢
  linarith

theorem r11Chi_D2_le : r11Chi_D 2 ≤ 15.994 := by
  have h := r11Chi_D_le' (j := 2) (by norm_num) (c := 17.43722) (by norm_num)
    (((Rat.cast_le (K := ℝ)).mpr r11Chi_cert_U2).trans (le_of_eq (by norm_num)))
  norm_num [r11Chi_P] at h ⊢
  linarith

theorem r11Chi_D3_le : r11Chi_D 3 ≤ 96.0244 := by
  have h := r11Chi_D_le' (j := 3) (by norm_num) (c := 87.12106) (by norm_num)
    (((Rat.cast_le (K := ℝ)).mpr r11Chi_cert_U3).trans (le_of_eq (by norm_num)))
  norm_num [r11Chi_P] at h ⊢
  linarith

theorem r11Chi_D4_le : r11Chi_D 4 ≤ 768.1283 := by
  have h := r11Chi_D_le' (j := 4) (by norm_num) (c := 493.2258) (by norm_num)
    (((Rat.cast_le (K := ℝ)).mpr r11Chi_cert_U4).trans (le_of_eq (by norm_num)))
  norm_num [r11Chi_P] at h ⊢
  linarith

theorem r11Chi_D0_ge : (2.6122 : ℝ) ≤ r11Chi_D 0 := by
  have h := r11Chi_D_ge' (j := 0) (by norm_num) (c := 2.48725) (by norm_num)
    ((le_of_eq (by norm_num)).trans ((Rat.cast_le (K := ℝ)).mpr r11Chi_cert_L0))
  norm_num [r11Chi_P] at h ⊢
  linarith

theorem r11Chi_D1_ge : (3.9314 : ℝ) ≤ r11Chi_D 1 := by
  have h := r11Chi_D_ge' (j := 1) (by norm_num) (c := 4.31128) (by norm_num)
    ((le_of_eq (by norm_num)).trans ((Rat.cast_le (K := ℝ)).mpr r11Chi_cert_L1))
  norm_num [r11Chi_P] at h ⊢
  linarith

theorem r11Chi_D2_ge : (15.9854 : ℝ) ≤ r11Chi_D 2 := by
  have h := r11Chi_D_ge' (j := 2) (by norm_num) (c := 17.41948) (by norm_num)
    ((le_of_eq (by norm_num)).trans ((Rat.cast_le (K := ℝ)).mpr r11Chi_cert_L2))
  norm_num [r11Chi_P] at h ⊢
  linarith

theorem r11Chi_D3_ge : (95.9783 : ℝ) ≤ r11Chi_D 3 := by
  have h := r11Chi_D_ge' (j := 3) (by norm_num) (c := 86.98327) (by norm_num)
    ((le_of_eq (by norm_num)).trans ((Rat.cast_le (K := ℝ)).mpr r11Chi_cert_L3))
  norm_num [r11Chi_P] at h ⊢
  linarith

/-! ## Bounds for `F_0, …, F_3` -/

theorem r11Chi_F_nonneg (k : ℕ) : 0 ≤ r11Chi_F k :=
  tsum_nonneg fun n => div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (pow_nonneg (Real.log_natCast_nonneg n) k)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Certified bounds (true values `F_0 = 1.505235`, `F_1 = 3.854962`, `F_2 = 15.930203`,
`F_3 = 95.949549`). -/
theorem r11Chi_F_bounds :
    (1.5048 ≤ r11Chi_F 0 ∧ r11Chi_F 0 ≤ 1.5058) ∧ (3.851 ≤ r11Chi_F 1 ∧ r11Chi_F 1 ≤ 3.859) ∧
    (15.89 ≤ r11Chi_F 2 ∧ r11Chi_F 2 ≤ 15.96) ∧ r11Chi_F 3 ≤ 96.4 := by
  obtain ⟨i0, i1, i2, i3⟩ := r11Chi_leibniz
  have hF0 := r11Chi_F_nonneg 0
  have hF1 := r11Chi_F_nonneg 1
  have hF2 := r11Chi_F_nonneg 2
  have hF3 := r11Chi_F_nonneg 3
  have d0h := r11Chi_D0_le
  have d1h := r11Chi_D1_le
  have d2h := r11Chi_D2_le
  have d3h := r11Chi_D3_le
  have d4h := r11Chi_D4_le
  have d0l := r11Chi_D0_ge
  have d1l := r11Chi_D1_ge
  have d2l := r11Chi_D2_ge
  have d3l := r11Chi_D3_ge
  generalize r11Chi_F 0 = F0 at *
  generalize r11Chi_F 1 = F1 at *
  generalize r11Chi_F 2 = F2 at *
  generalize r11Chi_F 3 = F3 at *
  generalize r11Chi_D 0 = D0 at *
  generalize r11Chi_D 1 = D1 at *
  generalize r11Chi_D 2 = D2 at *
  generalize r11Chi_D 3 = D3 at *
  generalize r11Chi_D 4 = D4 at *
  -- F0
  have a1 : F0 * D0 ≤ F0 * 2.6125 := mul_le_mul_of_nonneg_left d0h hF0
  have a2 : F0 * 2.6122 ≤ F0 * D0 := mul_le_mul_of_nonneg_left d0l hF0
  have f0l : (1.5048 : ℝ) ≤ F0 := by linarith
  have f0h : F0 ≤ 1.5058 := by linarith
  -- F1
  have b1 : (1.5048 : ℝ) * 3.9314 ≤ F0 * D1 := mul_le_mul f0l d1l (by norm_num) hF0
  have b2 : F0 * D1 ≤ 1.5058 * 3.9333 := mul_le_mul f0h d1h (by linarith) (by norm_num)
  have b3 : F1 * D0 ≤ F1 * 2.6125 := mul_le_mul_of_nonneg_left d0h hF1
  have b4 : F1 * 2.6122 ≤ F1 * D0 := mul_le_mul_of_nonneg_left d0l hF1
  have f1l : (3.851 : ℝ) ≤ F1 := by linarith
  have f1h : F1 ≤ 3.859 := by linarith
  -- F2
  have c1 : (3.851 : ℝ) * 3.9314 ≤ F1 * D1 := mul_le_mul f1l d1l (by norm_num) hF1
  have c2 : F1 * D1 ≤ 3.859 * 3.9333 := mul_le_mul f1h d1h (by linarith) (by norm_num)
  have c3 : (1.5048 : ℝ) * 15.9854 ≤ F0 * D2 := mul_le_mul f0l d2l (by norm_num) hF0
  have c4 : F0 * D2 ≤ 1.5058 * 15.994 := mul_le_mul f0h d2h (by linarith) (by norm_num)
  have c5 : F2 * D0 ≤ F2 * 2.6125 := mul_le_mul_of_nonneg_left d0h hF2
  have c6 : F2 * 2.6122 ≤ F2 * D0 := mul_le_mul_of_nonneg_left d0l hF2
  have f2l : (15.89 : ℝ) ≤ F2 := by linarith
  have f2h : F2 ≤ 15.96 := by linarith
  -- F3
  have e1 : (15.89 : ℝ) * 3.9314 ≤ F2 * D1 := mul_le_mul f2l d1l (by norm_num) hF2
  have e2 : (3.851 : ℝ) * 15.9854 ≤ F1 * D2 := mul_le_mul f1l d2l (by norm_num) hF1
  have e3 : (1.5048 : ℝ) * 95.9783 ≤ F0 * D3 := mul_le_mul f0l d3l (by norm_num) hF0
  have e4 : F3 * 2.6122 ≤ F3 * D0 := mul_le_mul_of_nonneg_left d0l hF3
  have f3h : F3 ≤ 96.4 := by linarith
  exact ⟨⟨f0l, f0h⟩, ⟨f1l, f1h⟩, ⟨f2l, f2h⟩, f3h⟩

theorem r11Chi_F1_le : r11Chi_F 1 ≤ 5.31 := by
  have := r11Chi_F_bounds.2.1.2
  linarith

theorem r11Chi_F2_le : r11Chi_F 2 ≤ 17.5 := by
  have := r11Chi_F_bounds.2.2.1.2
  linarith

theorem r11Chi_F3_le : r11Chi_F 3 ≤ 102.3 := by
  have := r11Chi_F_bounds.2.2.2
  linarith

#print axioms r11Chi_F_summable
#print axioms r11Chi_F_bounds
#print axioms r11Chi_F1_le
#print axioms r11Chi_F2_le
#print axioms r11Chi_F3_le

end DetPrimality.Bach
