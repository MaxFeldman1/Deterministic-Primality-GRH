import DetPrimality.Bach.R11ChiDefs
import DetPrimality.Bach.R11ZeroSumNum

/-!
# Round 11: certified upper bounds for `F₁, F₂, F₃`, `F_k = ∑ Λ(n) log^k n · n^{-3/2}`

With `D_j = ∑ log^j n · n^{-3/2}` (`D₀ = ζ(3/2)`), differentiating `(∑ Λ n^{-s}) ζ(s) = -ζ'(s)`:

* `F₀ D₀ = D₁`, `F₁ D₀ + F₀ D₁ = D₂`,
* `F₂ D₀ + 2 F₁ D₁ + F₀ D₂ = D₃`,
* `F₃ D₀ + 3 F₂ D₁ + 3 F₁ D₂ + F₀ D₃ = D₄`.

The smooth sums `D_j` are bounded as in `R11ZeroSumNum` (exact integer partial sums for
`n < 256` plus trapezoid/midpoint tails; the family `r11F_P` extends `r11Zs_P` to `log⁴`).

Results: `F₁ ≤ 3.85497`, `15.93013 ≤ F₂ ≤ 15.93026`, `F₃ ≤ 95.9504`
(true: `3.854963`, `15.930204`, `95.949549`).
-/

open Complex Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## The convolution identities -/

noncomputable def r11F_A (j : ℕ) (s : ℂ) : ℂ :=
  LSeries (LSeries.logMul^[j] (fun n : ℕ => ((Λ n : ℝ) : ℂ))) s

noncomputable def r11F_B (j : ℕ) (s : ℂ) : ℂ :=
  LSeries (LSeries.logMul^[j] (1 : ℕ → ℂ)) s

/-- `D_j = ∑ log^j n · n^{-3/2}`. -/
noncomputable def r11F_D (j : ℕ) : ℝ := ∑' n : ℕ, Real.log n ^ j / (n : ℝ) ^ (3 / 2 : ℝ)

lemma r11F_abscissa_iter (f : ℕ → ℂ) (j : ℕ) :
    LSeries.abscissaOfAbsConv (LSeries.logMul^[j] f) = LSeries.abscissaOfAbsConv f := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]

lemma r11F_A_hasDerivAt (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (r11F_A j) (-(r11F_A (j + 1) s)) s := by
  have h0 : LSeries.abscissaOfAbsConv (fun n : ℕ => ((Λ n : ℝ) : ℂ)) ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
  have h : LSeries.abscissaOfAbsConv (LSeries.logMul^[j] (fun n : ℕ => ((Λ n : ℝ) : ℂ)))
      < (s.re : EReal) := by
    rw [r11F_abscissa_iter]
    exact lt_of_le_of_lt h0 (EReal.coe_lt_coe_iff.mpr hs)
  have h1 := LSeries_hasDerivAt h
  show HasDerivAt (LSeries (LSeries.logMul^[j] (fun n : ℕ => ((Λ n : ℝ) : ℂ))))
    (-(LSeries (LSeries.logMul^[j + 1] (fun n : ℕ => ((Λ n : ℝ) : ℂ))) s)) s
  rw [Function.iterate_succ_apply']
  exact h1

lemma r11F_B_hasDerivAt (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (r11F_B j) (-(r11F_B (j + 1) s)) s := by
  have h0 : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => LSeriesSummable_one_iff.mpr (by simpa using hy))
  have h : LSeries.abscissaOfAbsConv (LSeries.logMul^[j] (1 : ℕ → ℂ)) < (s.re : EReal) := by
    rw [r11F_abscissa_iter]
    exact lt_of_le_of_lt h0 (EReal.coe_lt_coe_iff.mpr hs)
  have h1 := LSeries_hasDerivAt h
  show HasDerivAt (LSeries (LSeries.logMul^[j] (1 : ℕ → ℂ)))
    (-(LSeries (LSeries.logMul^[j + 1] (1 : ℕ → ℂ)) s)) s
  rw [Function.iterate_succ_apply']
  exact h1

lemma r11F_step (f g f' g' : ℂ → ℂ) (hf : ∀ s : ℂ, 1 < s.re → HasDerivAt f (f' s) s)
    (hg : ∀ s : ℂ, 1 < s.re → HasDerivAt g (g' s) s) (h : ∀ s : ℂ, 1 < s.re → f s = g s) :
    ∀ s : ℂ, 1 < s.re → f' s = g' s := by
  intro s hs
  have hev : f =ᶠ[𝓝 s] g := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
      using h z hz
  exact (hf s hs).unique ((hg s hs).congr_of_eventuallyEq hev)

lemma r11F_I0 : ∀ s : ℂ, 1 < s.re → r11F_A 0 s * r11F_B 0 s = r11F_B 1 s := by
  intro s hs
  have hlg : LSeries.logMul (1 : ℕ → ℂ) = fun n : ℕ => Complex.log (n : ℂ) := by
    funext n; simp [LSeries.logMul]
  have h1 := LSeries_convolution' (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (LSeriesSummable_one_iff.mpr hs)
  rw [ArithmeticFunction.convolution_vonMangoldt_const_one] at h1
  show LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ)) s * LSeries (1 : ℕ → ℂ) s
    = LSeries (LSeries.logMul (1 : ℕ → ℂ)) s
  rw [hlg, h1]

lemma r11F_I1 : ∀ s : ℂ, 1 < s.re →
    -(r11F_A 1 s) * r11F_B 0 s + r11F_A 0 s * -(r11F_B 1 s) = -(r11F_B 2 s) :=
  r11F_step (fun s => r11F_A 0 s * r11F_B 0 s) (fun s => r11F_B 1 s)
    (fun s => -(r11F_A 1 s) * r11F_B 0 s + r11F_A 0 s * -(r11F_B 1 s)) (fun s => -(r11F_B 2 s))
    (fun s hs => r11Zs_hasDerivAt_congr ((r11F_A_hasDerivAt 0 hs).mul (r11F_B_hasDerivAt 0 hs))
      (fun _ => rfl) rfl)
    (fun s hs => r11F_B_hasDerivAt 1 hs) r11F_I0

lemma r11F_I2 : ∀ s : ℂ, 1 < s.re →
    r11F_A 2 s * r11F_B 0 s + 2 * (r11F_A 1 s * r11F_B 1 s) + r11F_A 0 s * r11F_B 2 s
      = r11F_B 3 s :=
  r11F_step (fun s => -(r11F_A 1 s) * r11F_B 0 s + r11F_A 0 s * -(r11F_B 1 s))
    (fun s => -(r11F_B 2 s))
    (fun s => r11F_A 2 s * r11F_B 0 s + 2 * (r11F_A 1 s * r11F_B 1 s) + r11F_A 0 s * r11F_B 2 s)
    (fun s => r11F_B 3 s)
    (fun s hs => r11Zs_hasDerivAt_congr
      (((r11F_A_hasDerivAt 1 hs).neg.mul (r11F_B_hasDerivAt 0 hs)).add
        ((r11F_A_hasDerivAt 0 hs).mul (r11F_B_hasDerivAt 1 hs).neg))
      (fun _ => rfl) (by simp only [Pi.neg_apply]; ring))
    (fun s hs => r11Zs_hasDerivAt_congr (r11F_B_hasDerivAt 2 hs).neg (fun _ => rfl) (by ring))
    r11F_I1

lemma r11F_I3 : ∀ s : ℂ, 1 < s.re →
    -(r11F_A 3 s * r11F_B 0 s + 3 * (r11F_A 2 s * r11F_B 1 s) + 3 * (r11F_A 1 s * r11F_B 2 s)
      + r11F_A 0 s * r11F_B 3 s) = -(r11F_B 4 s) :=
  r11F_step
    (fun s => r11F_A 2 s * r11F_B 0 s + 2 * (r11F_A 1 s * r11F_B 1 s) + r11F_A 0 s * r11F_B 2 s)
    (fun s => r11F_B 3 s)
    (fun s => -(r11F_A 3 s * r11F_B 0 s + 3 * (r11F_A 2 s * r11F_B 1 s)
      + 3 * (r11F_A 1 s * r11F_B 2 s) + r11F_A 0 s * r11F_B 3 s))
    (fun s => -(r11F_B 4 s))
    (fun s hs => r11Zs_hasDerivAt_congr
      ((((r11F_A_hasDerivAt 2 hs).mul (r11F_B_hasDerivAt 0 hs)).add
        (((r11F_A_hasDerivAt 1 hs).mul (r11F_B_hasDerivAt 1 hs)).const_mul 2)).add
        ((r11F_A_hasDerivAt 0 hs).mul (r11F_B_hasDerivAt 2 hs)))
      (fun _ => rfl) (by ring))
    (fun s hs => r11F_B_hasDerivAt 3 hs) r11F_I2

lemma r11F_iter (f : ℕ → ℝ) (j : ℕ) :
    LSeries.logMul^[j] (fun n : ℕ => ((f n : ℝ) : ℂ))
      = fun n : ℕ => ((f n * Real.log n ^ j : ℝ) : ℂ) := by
  induction j with
  | zero => funext n; simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext n
    simp only [LSeries.logMul]
    rw [← Complex.natCast_log]
    push_cast
    ring

lemma r11F_A_val (j : ℕ) : r11F_A j (3 / 2) = ((r11Chi_F j : ℝ) : ℂ) := by
  have h32 : (3 / 2 : ℝ) ≠ 0 := by norm_num
  show LSeries (LSeries.logMul^[j] (fun n : ℕ => ((Λ n : ℝ) : ℂ))) (3 / 2) = _
  rw [r11F_iter, ← r11Zs_three_halves, szs_LSeries_ofReal _ h32]
  rfl

lemma r11F_B_val (j : ℕ) : r11F_B j (3 / 2) = ((r11F_D j : ℝ) : ℂ) := by
  have h32 : (3 / 2 : ℝ) ≠ 0 := by norm_num
  have e1 : (1 : ℕ → ℂ) = fun n : ℕ => (((fun _ : ℕ => (1 : ℝ)) n : ℝ) : ℂ) := by
    funext n; simp
  show LSeries (LSeries.logMul^[j] (1 : ℕ → ℂ)) (3 / 2) = _
  rw [e1, r11F_iter, ← r11Zs_three_halves, szs_LSeries_ofReal _ h32]
  congr 1
  exact tsum_congr fun n => by rw [one_mul]

theorem r11F_F2_mul :
    r11Chi_F 2 * r11F_D 0 + 2 * (r11Chi_F 1 * r11F_D 1) + r11Chi_F 0 * r11F_D 2 = r11F_D 3 := by
  have h := r11F_I2 (3 / 2) r11Zs_one_lt_re
  simp only [r11F_A_val, r11F_B_val] at h
  exact_mod_cast h

theorem r11F_F3_mul :
    r11Chi_F 3 * r11F_D 0 + 3 * (r11Chi_F 2 * r11F_D 1) + 3 * (r11Chi_F 1 * r11F_D 2)
      + r11Chi_F 0 * r11F_D 3 = r11F_D 4 := by
  have h := r11F_I3 (3 / 2) r11Zs_one_lt_re
  simp only [r11F_A_val, r11F_B_val] at h
  have h' : -(r11Chi_F 3 * r11F_D 0 + 3 * (r11Chi_F 2 * r11F_D 1)
      + 3 * (r11Chi_F 1 * r11F_D 2) + r11Chi_F 0 * r11F_D 3) = -(r11F_D 4) := by
    exact_mod_cast h
  linarith

lemma r11F_F0_eq : r11Chi_F 0 = r11Zs_F0 :=
  tsum_congr fun n => by rw [pow_zero, mul_one]

lemma r11F_F1_eq : r11Chi_F 1 = r11Zs_F1 :=
  tsum_congr fun n => by rw [pow_one]

lemma r11F_D0_eq : r11F_D 0 = r11Zs_Zs :=
  tsum_congr fun n => by rw [pow_zero]

lemma r11F_D1_eq : r11F_D 1 = r11Zs_D1 :=
  tsum_congr fun n => by rw [pow_one]

lemma r11F_D2_eq : r11F_D 2 = r11Zs_D2 := rfl

lemma r11F_F_nonneg (k : ℕ) : 0 ≤ r11Chi_F k :=
  tsum_nonneg fun n => div_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-! ## The family `(c₄ log⁴ t + … + c₀) t^a` -/

noncomputable def r11F_P (c0 c1 c2 c3 c4 a : ℝ) (t : ℝ) : ℝ :=
  (c4 * Real.log t ^ 4 + c3 * Real.log t ^ 3 + c2 * Real.log t ^ 2 + c1 * Real.log t + c0)
    * t ^ a

lemma r11F_P_hasDerivAt (c0 c1 c2 c3 c4 a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (r11F_P c0 c1 c2 c3 c4 a)
      (r11F_P (c1 + a * c0) (2 * c2 + a * c1) (3 * c3 + a * c2) (4 * c4 + a * c3) (a * c4)
        (a - 1) t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have h1 : HasDerivAt (fun t : ℝ => c4 * Real.log t ^ 4 + c3 * Real.log t ^ 3
        + c2 * Real.log t ^ 2 + c1 * Real.log t + c0)
      (c4 * (4 * Real.log t ^ 3 * t⁻¹) + c3 * (3 * Real.log t ^ 2 * t⁻¹)
        + c2 * (2 * Real.log t * t⁻¹) + c1 * t⁻¹) t := by
    have := (((((hl.pow 4).const_mul c4).add ((hl.pow 3).const_mul c3)).add
      ((hl.pow 2).const_mul c2)).add (hl.const_mul c1)).add_const c0
    refine this.congr_deriv ?_
    norm_num
  have h2 : HasDerivAt (fun t : ℝ => t ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h3 := h1.mul h2
  have e : t ^ a = t ^ (a - 1) * t := by
    rw [Real.rpow_sub_one ht.ne']; field_simp
  show HasDerivAt (fun t : ℝ => (c4 * Real.log t ^ 4 + c3 * Real.log t ^ 3
    + c2 * Real.log t ^ 2 + c1 * Real.log t + c0) * t ^ a) _ t
  refine h3.congr_deriv ?_
  unfold r11F_P
  rw [e]
  generalize t ^ (a - 1) = u
  field_simp
  ring

lemma r11F_log_ge_four {t : ℝ} (ht : 64 ≤ t) : 4 ≤ Real.log t := by
  have h1 : Real.log 64 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have h2 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have h3 := Real.log_two_gt_d9
  linarith

lemma r11F_P_nonneg {c0 c1 c2 c3 c4 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) (a : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t = 0 ∨ 1 ≤ t) : 0 ≤ r11F_P c0 c1 c2 c3 c4 a t := by
  unfold r11F_P
  have hl : 0 ≤ Real.log t := by
    rcases ht1 with rfl | h
    · simp
    · exact Real.log_nonneg h
  have := Real.rpow_nonneg ht a
  positivity

lemma r11F_P_convex (c0 c1 c2 c3 c4 a : ℝ)
    (h : ∀ L : ℝ, 4 ≤ L → 0 ≤ ((a - 1) * (a * c4)) * L ^ 4
      + (4 * (a * c4) + (a - 1) * (4 * c4 + a * c3)) * L ^ 3
      + (3 * (4 * c4 + a * c3) + (a - 1) * (3 * c3 + a * c2)) * L ^ 2
      + (2 * (3 * c3 + a * c2) + (a - 1) * (2 * c2 + a * c1)) * L
      + ((2 * c2 + a * c1) + (a - 1) * (c1 + a * c0))) :
    ConvexOn ℝ (Set.Ici 64) (r11F_P c0 c1 c2 c3 c4 a) := by
  have hpos : ∀ t ∈ Set.Ici (64 : ℝ), 0 < t := fun t ht => lt_of_lt_of_le (by norm_num) ht
  have hmono : MonotoneOn (r11F_P (c1 + a * c0) (2 * c2 + a * c1) (3 * c3 + a * c2)
      (4 * c4 + a * c3) (a * c4) (a - 1)) (Set.Ici 64) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 64)
      (fun t ht => (r11F_P_hasDerivAt _ _ _ _ _ _ (hpos t ht)).continuousAt.continuousWithinAt)
      (fun t ht => (r11F_P_hasDerivAt _ _ _ _ _ _
        (hpos t (interior_subset ht))).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    have ht' := interior_subset ht
    rw [(r11F_P_hasDerivAt _ _ _ _ _ _ (hpos t ht')).deriv]
    unfold r11F_P
    refine mul_nonneg ?_ (Real.rpow_nonneg (hpos t ht').le _)
    have := h (Real.log t) (r11F_log_ge_four ht')
    linarith
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 64)
    (fun t ht => (r11F_P_hasDerivAt _ _ _ _ _ _ (hpos t ht)).continuousAt.continuousWithinAt)
    (fun t ht => (r11F_P_hasDerivAt _ _ _ _ _ _
      (hpos t (interior_subset ht))).differentiableAt.differentiableWithinAt) ?_
  intro x hx y hy hxy
  rw [(r11F_P_hasDerivAt c0 c1 c2 c3 c4 a (hpos x (interior_subset hx))).deriv,
    (r11F_P_hasDerivAt c0 c1 c2 c3 c4 a (hpos y (interior_subset hy))).deriv]
  exact hmono (interior_subset hx) (interior_subset hy) hxy

/-- Tail bounds for `∑ f(n)`, `f = r11F_P c (-3/2)` convex on `[64, ∞)` with antiderivative
`-A`, `A = r11F_P d (-1/2)`. -/
theorem r11F_tsum_bounds {c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4)
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) (hd4 : 0 ≤ d4)
    (hA : ∀ t : ℝ, 0 < t → HasDerivAt (r11F_P d0 d1 d2 d3 d4 (-(1 / 2)))
      (-(r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) t)) t)
    (hconv : ConvexOn ℝ (Set.Ici 64) (r11F_P c0 c1 c2 c3 c4 (-(3 / 2)))) :
    Summable (fun n : ℕ => r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) n) ∧
    (∑' n : ℕ, r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) n
      ≤ ∑ n ∈ Finset.range 256, r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) n
        + r11F_P d0 d1 d2 d3 d4 (-(1 / 2)) (255 + 1 / 2)) ∧
    ∀ j : ℕ, ∑ n ∈ Finset.range 256, r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) n
        + (r11F_P d0 d1 d2 d3 d4 (-(1 / 2)) 256 + r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) 256 / 2)
        - (r11F_P d0 d1 d2 d3 d4 (-(1 / 2)) ((256 + j : ℕ) : ℝ)
          + r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) ((256 + j : ℕ) : ℝ) / 2)
      ≤ ∑' n : ℕ, r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) n := by
  set f := r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) with hf
  set A := r11F_P d0 d1 d2 d3 d4 (-(1 / 2)) with hAdef
  have hnn : ∀ n : ℕ, 0 ≤ f n := fun n => by
    refine r11F_P_nonneg hc0 hc1 hc2 hc3 hc4 _ (Nat.cast_nonneg n) ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp
    · right; exact_mod_cast hn
  have hAnn : ∀ t : ℝ, 1 ≤ t → 0 ≤ A t := fun t ht =>
    r11F_P_nonneg hd0 hd1 hd2 hd3 hd4 _ (by linarith) (Or.inr ht)
  have hup := szs_sum_range_le_of_tele (fun n : ℕ => f n) (fun n : ℕ => A ((n : ℝ) + 1 / 2)) 255
    hnn (fun n hn => hAnn _ (by
      have : (255 : ℝ) ≤ n := by exact_mod_cast hn
      linarith))
    (fun n hn => by
      have hn' : (255 : ℝ) ≤ n := by exact_mod_cast hn
      have hsub : Set.Icc ((n : ℝ) + 1 - 1 / 2) ((n : ℝ) + 1 + 1 / 2) ⊆ Set.Ici 64 := fun t ht =>
        Set.mem_Ici.mpr (by linarith [ht.1])
      have := r11Zs_midpoint (f := f) (A := A) (n := (n : ℝ) + 1) (hconv.subset hsub
        (convex_Icc _ _)) (fun t ht => hA t (by linarith [ht.1]))
      push_cast
      rw [show (n : ℝ) + 1 - 1 / 2 = (n : ℝ) + 1 / 2 by ring] at this
      exact this)
  have hsum : Summable (fun n : ℕ => f n) := summable_of_sum_range_le hnn hup
  have hle := Real.tsum_le_of_sum_range_le hnn hup
  refine ⟨hsum, ?_, fun j => ?_⟩
  · have e : ((255 : ℕ) : ℝ) + 1 / 2 = 255 + 1 / 2 := by norm_num
    rw [e] at hle
    exact hle
  · have hlow := szs_sum_range_ge_of_tele (fun n : ℕ => f n)
      (fun n : ℕ => A (n : ℝ) + f (n : ℝ) / 2) 256
      (fun n hn => by
        have hn' : (256 : ℝ) ≤ n := by exact_mod_cast hn
        have hsub : Set.Icc (n : ℝ) ((n : ℝ) + 1) ⊆ Set.Ici 64 := fun t ht =>
          Set.mem_Ici.mpr (by linarith [ht.1])
        have := r11Zs_trapezoid (f := f) (A := A) (n := (n : ℝ)) (hconv.subset hsub
          (convex_Icc _ _)) (fun t ht => hA t (by linarith [ht.1]))
        push_cast
        linarith) j
    have h2 := hsum.sum_le_tsum (Finset.range (256 + j)) (fun i _ => hnn i)
    have e : ((256 : ℕ) : ℝ) = 256 := by norm_num
    simp only [e] at hlow
    linarith

theorem r11F_anti {c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 : ℝ} (h0 : d1 + -(1 / 2) * d0 = -c0)
    (h1 : 2 * d2 + -(1 / 2) * d1 = -c1) (h2 : 3 * d3 + -(1 / 2) * d2 = -c2)
    (h3 : 4 * d4 + -(1 / 2) * d3 = -c3) (h4 : -(1 / 2) * d4 = -c4) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (r11F_P d0 d1 d2 d3 d4 (-(1 / 2))) (-(r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) t)) t := by
  have h := r11F_P_hasDerivAt d0 d1 d2 d3 d4 (-(1 / 2)) ht
  rw [h0, h1, h2, h3, h4, show (-(1 / 2) - 1 : ℝ) = -(3 / 2) by norm_num] at h
  refine h.congr_deriv ?_
  unfold r11F_P
  ring

theorem r11F_P_256 (c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 : ℝ) :
    r11F_P d0 d1 d2 d3 d4 (-(1 / 2)) 256
      = (d4 * (4096 * Real.log 2 ^ 4) + d3 * (512 * Real.log 2 ^ 3)
        + d2 * (64 * Real.log 2 ^ 2) + d1 * (8 * Real.log 2) + d0) / 16 ∧
    r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) 256
      = (c4 * (4096 * Real.log 2 ^ 4) + c3 * (512 * Real.log 2 ^ 3)
        + c2 * (64 * Real.log 2 ^ 2) + c1 * (8 * Real.log 2) + c0) / 4096 := by
  have hlog : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  obtain ⟨h1, h2⟩ := r11Zs_rpow_sq (s := 16) (by norm_num)
  rw [show (16 : ℝ) ^ 2 = 256 by norm_num] at h1 h2
  unfold r11F_P
  rw [hlog, h1, h2]
  constructor <;> ring

theorem r11F_P_big (c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 : ℝ) {T : ℝ} (hT : T = 2 ^ 80) :
    r11F_P d0 d1 d2 d3 d4 (-(1 / 2)) T
      = (d4 * (40960000 * Real.log 2 ^ 4) + d3 * (512000 * Real.log 2 ^ 3)
        + d2 * (6400 * Real.log 2 ^ 2) + d1 * (80 * Real.log 2) + d0) / 2 ^ 40 ∧
    r11F_P c0 c1 c2 c3 c4 (-(3 / 2)) T
      = (c4 * (40960000 * Real.log 2 ^ 4) + c3 * (512000 * Real.log 2 ^ 3)
        + c2 * (6400 * Real.log 2 ^ 2) + c1 * (80 * Real.log 2) + c0) / 2 ^ 120 := by
  have hlog : Real.log T = 80 * Real.log 2 := by
    rw [hT, Real.log_pow]; norm_num
  obtain ⟨h1, h2⟩ := r11Zs_rpow_sq (s := 2 ^ 40) (by positivity)
  rw [show ((2 : ℝ) ^ 40) ^ 2 = 2 ^ 80 by norm_num, ← hT] at h1 h2
  unfold r11F_P
  rw [hlog, h1, h2]
  constructor <;> ring

/-! ## Integer certificates and partial sums -/

set_option maxRecDepth 100000 in
theorem r11F_cert_D2u :
    r11Zs_sumTo (fun n => (r11Zs_tab n + 1) ^ 2 * r11Zs_ru n) 256
      ≤ 21059734239410903056597277 := by decide +kernel

set_option maxRecDepth 100000 in
theorem r11F_cert_D3l :
    110270983227439189192831476461699
      ≤ r11Zs_sumTo (fun n => r11Zs_tab n ^ 3 * r11Zs_rl n) 256 := by decide +kernel

set_option maxRecDepth 100000 in
theorem r11F_cert_D3u :
    r11Zs_sumTo (fun n => (r11Zs_tab n + 1) ^ 3 * r11Zs_ru n) 256
      ≤ 110271046500215799704321855730211 := by decide +kernel

set_option maxRecDepth 100000 in
theorem r11F_cert_D4u :
    r11Zs_sumTo (fun n => (r11Zs_tab n + 1) ^ 4 * r11Zs_ru n) 256
      ≤ 654217381743791035135003147061585399201 := by decide +kernel

theorem r11F_part_lower (k C : ℕ)
    (hc : C ≤ r11Zs_sumTo (fun n => r11Zs_tab n ^ k * r11Zs_rl n) 256) :
    (C : ℝ) * (Real.log 2 ^ k / ((2 ^ 20) ^ k * 2 ^ 40))
      ≤ ∑ n ∈ Finset.range 256, Real.log n ^ k * (n : ℝ) ^ (-(3 / 2) : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc' : (C : ℝ) ≤ ((r11Zs_sumTo (fun n => r11Zs_tab n ^ k * r11Zs_rl n) 256 : ℕ) : ℝ) :=
    Nat.cast_le.mpr hc
  rw [r11Zs_sumTo_cast] at hc'
  have h : ∑ n ∈ Finset.range 256,
        ((r11Zs_tab n ^ k * r11Zs_rl n : ℕ) : ℝ) * (Real.log 2 ^ k / ((2 ^ 20) ^ k * 2 ^ 40))
      ≤ ∑ n ∈ Finset.range 256, Real.log n ^ k * (n : ℝ) ^ (-(3 / 2) : ℝ) := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨h1, h2, -, h4, h5, -⟩ := r11Zs_term n hn
    have hL : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    push_cast
    calc (r11Zs_tab n : ℝ) ^ k * (r11Zs_rl n : ℝ) * (Real.log 2 ^ k / ((2 ^ 20) ^ k * 2 ^ 40))
        = ((r11Zs_tab n : ℝ) * Real.log 2 / 2 ^ 20) ^ k * ((r11Zs_rl n : ℝ) / 2 ^ 40) := by
          rw [div_pow, mul_pow]; field_simp
      _ ≤ Real.log (n : ℝ) ^ k * (n : ℝ) ^ (-(3 / 2) : ℝ) :=
          mul_le_mul (pow_le_pow_left₀ h4 h5 k) h2 h1 (pow_nonneg hL k)
  rw [← Finset.sum_mul] at h
  have h7 := mul_le_mul_of_nonneg_right hc'
    (by positivity : (0 : ℝ) ≤ Real.log 2 ^ k / ((2 ^ 20) ^ k * 2 ^ 40))
  linarith

theorem r11F_part_upper (k C : ℕ)
    (hc : r11Zs_sumTo (fun n => (r11Zs_tab n + 1) ^ k * r11Zs_ru n) 256 ≤ C) :
    ∑ n ∈ Finset.range 256, Real.log n ^ k * (n : ℝ) ^ (-(3 / 2) : ℝ)
      ≤ (C : ℝ) * (Real.log 2 ^ k / ((2 ^ 20) ^ k * 2 ^ 40)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc' : ((r11Zs_sumTo (fun n => (r11Zs_tab n + 1) ^ k * r11Zs_ru n) 256 : ℕ) : ℝ)
      ≤ (C : ℝ) := Nat.cast_le.mpr hc
  rw [r11Zs_sumTo_cast] at hc'
  have h : ∑ n ∈ Finset.range 256, Real.log n ^ k * (n : ℝ) ^ (-(3 / 2) : ℝ)
      ≤ ∑ n ∈ Finset.range 256, (((r11Zs_tab n + 1) ^ k * r11Zs_ru n : ℕ) : ℝ)
        * (Real.log 2 ^ k / ((2 ^ 20) ^ k * 2 ^ 40)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := r11Zs_term n hn
    have hx : 0 ≤ (n : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hL : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    push_cast
    calc Real.log (n : ℝ) ^ k * (n : ℝ) ^ (-(3 / 2) : ℝ)
        ≤ (((r11Zs_tab n : ℝ) + 1) * Real.log 2 / 2 ^ 20) ^ k * ((r11Zs_ru n : ℝ) / 2 ^ 40) :=
          mul_le_mul (pow_le_pow_left₀ hL h6 k) h3 hx (pow_nonneg (le_trans hL h6) k)
      _ = _ := by rw [div_pow, mul_pow]; field_simp
  rw [← Finset.sum_mul] at h
  have h7 := mul_le_mul_of_nonneg_right hc'
    (by positivity : (0 : ℝ) ≤ Real.log 2 ^ k / ((2 ^ 20) ^ k * 2 ^ 40))
  linarith

/-! ## The smooth sums `D₂, D₃, D₄` -/

lemma r11F_log2_pow_le (k : ℕ) : Real.log 2 ^ k ≤ (0.6931471808 : ℝ) ^ k :=
  pow_le_pow_left₀ (Real.log_pos (by norm_num)).le Real.log_two_lt_d9.le k

lemma r11F_le_log2_pow (k : ℕ) : (0.6931471803 : ℝ) ^ k ≤ Real.log 2 ^ k :=
  pow_le_pow_left₀ (by norm_num) Real.log_two_gt_d9.le k

lemma r11F_half_log_pow (k : ℕ) : Real.log (255 + 1 / 2 : ℝ) ^ k ≤ (5.5432244 : ℝ) ^ k := by
  obtain ⟨g1, g2, -, -⟩ := r11Zs_half_facts
  have := Real.log_two_lt_d9
  exact pow_le_pow_left₀ g1 (by linarith) k

theorem r11F_D2_upper : r11F_D 2 ≤ 15.989564 := by
  have hconv := r11Zs_P_convex 0 0 1 (-(3 / 2)) (fun L hL => by
    norm_num
    nlinarith [sq_nonneg (L - 2)])
  obtain ⟨hsum, hup, hlow⟩ := r11Zs_tsum_bounds (c0 := 0) (c1 := 0) (c2 := 1) (d0 := 16)
    (d1 := 8) (d2 := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (r11Zs_anti (by norm_num) (by norm_num) (by norm_num)) hconv
  have heq : ∑' n : ℕ, r11Zs_P 0 0 1 (-(3 / 2)) n = r11F_D 2 :=
    tsum_congr fun n => by rw [r11Zs_P_apply_nat]; congr 1; ring
  rw [heq] at hup
  obtain ⟨g1, g2, g3, g4⟩ := r11Zs_half_facts
  have q1 := r11F_half_log_pow 1
  have q2 := r11F_half_log_pow 2
  rw [pow_one] at q1
  have hA : r11Zs_P 16 8 2 (-(1 / 2)) (255 + 1 / 2)
      ≤ (2 * 5.5432244 ^ 2 + 8 * 5.5432244 + 16) * (1000000000 / 15984367363) := by
    unfold r11Zs_P
    exact mul_le_mul (by linarith) g4 g3 (by norm_num)
  have p := r11F_part_upper 2 _ r11F_cert_D2u
  have hp : ∑ n ∈ Finset.range 256, r11Zs_P 0 0 1 (-(3 / 2)) n
      = ∑ n ∈ Finset.range 256, Real.log n ^ 2 * (n : ℝ) ^ (-(3 / 2) : ℝ) :=
    Finset.sum_congr rfl fun n _ => by unfold r11Zs_P; ring
  have l2 := r11F_log2_pow_le 2
  have p' : ∑ n ∈ Finset.range 256, r11Zs_P 0 0 1 (-(3 / 2)) n
      ≤ (21059734239410903056597277 : ℝ) * (0.6931471808 ^ 2 / ((2 ^ 20) ^ 2 * 2 ^ 40)) := by
    rw [hp]
    refine p.trans ?_
    push_cast
    gcongr
  norm_num at hA p' hup ⊢
  linarith

theorem r11F_D3_bounds : 96.00097 ≤ r11F_D 3 ∧ r11F_D 3 ≤ 96.00106 := by
  have hconv := r11F_P_convex 0 0 0 1 0 (-(3 / 2)) (fun L hL => by
    norm_num
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ L) (by linarith : (0 : ℝ) ≤ L))
      (by linarith : (0 : ℝ) ≤ L - 4), sq_nonneg L])
  obtain ⟨hsum, hup, hlow⟩ := r11F_tsum_bounds (c0 := 0) (c1 := 0) (c2 := 0) (c3 := 1) (c4 := 0)
    (d0 := 96) (d1 := 48) (d2 := 12) (d3 := 2) (d4 := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (r11F_anti (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hconv
  have heq : ∑' n : ℕ, r11F_P 0 0 0 1 0 (-(3 / 2)) n = r11F_D 3 :=
    tsum_congr fun n => by
      unfold r11F_P
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv]
      congr 1; ring
  rw [heq] at hup hlow
  have hp : ∑ n ∈ Finset.range 256, r11F_P 0 0 0 1 0 (-(3 / 2)) n
      = ∑ n ∈ Finset.range 256, Real.log n ^ 3 * (n : ℝ) ^ (-(3 / 2) : ℝ) :=
    Finset.sum_congr rfl fun n _ => by unfold r11F_P; ring
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  constructor
  · obtain ⟨j, hj⟩ := r11Zs_big_exists
    have hlow' := hlow j
    obtain ⟨e1, e2⟩ := r11F_P_256 0 0 0 1 0 96 48 12 2 0
    obtain ⟨e3, e4⟩ := r11F_P_big 0 0 0 1 0 96 48 12 2 0 hj
    rw [e1, e2, e3, e4] at hlow'
    have p := r11F_part_lower 3 _ r11F_cert_D3l
    have p' : (110270983227439189192831476461699 : ℝ)
          * (0.6931471803 ^ 3 / ((2 ^ 20) ^ 3 * 2 ^ 40))
        ≤ ∑ n ∈ Finset.range 256, r11F_P 0 0 0 1 0 (-(3 / 2)) n := by
      rw [hp]
      refine le_trans ?_ p
      have := r11F_le_log2_pow 3
      push_cast
      gcongr
    have a2 := r11F_le_log2_pow 2
    have a3 := r11F_le_log2_pow 3
    have a4 := r11F_le_log2_pow 4
    have b2 : Real.log 2 ^ 2 ≤ 0.7 ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have b3 : Real.log 2 ^ 3 ≤ 0.7 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have b4 : Real.log 2 ^ 4 ≤ 0.7 ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    norm_num at hlow' p' a2 a3 a4 b2 b3 b4 ⊢
    linarith
  · obtain ⟨g1, g2, g3, g4⟩ := r11Zs_half_facts
    have q1 := r11F_half_log_pow 1
    have q2 := r11F_half_log_pow 2
    have q3 := r11F_half_log_pow 3
    rw [pow_one] at q1
    have hA : r11F_P 96 48 12 2 0 (-(1 / 2)) (255 + 1 / 2)
        ≤ (2 * 5.5432244 ^ 3 + 12 * 5.5432244 ^ 2 + 48 * 5.5432244 + 96)
          * (1000000000 / 15984367363) := by
      unfold r11F_P
      exact mul_le_mul (by linarith) g4 g3 (by norm_num)
    have p := r11F_part_upper 3 _ r11F_cert_D3u
    have p' : ∑ n ∈ Finset.range 256, r11F_P 0 0 0 1 0 (-(3 / 2)) n
        ≤ (110271046500215799704321855730211 : ℝ)
          * (0.6931471808 ^ 3 / ((2 ^ 20) ^ 3 * 2 ^ 40)) := by
      rw [hp]
      refine p.trans ?_
      have := r11F_log2_pow_le 3
      push_cast
      gcongr
    norm_num at hA p' hup ⊢
    linarith

theorem r11F_D4_upper : r11F_D 4 ≤ 768.0026 := by
  have hconv := r11F_P_convex 0 0 0 0 1 (-(3 / 2)) (fun L hL => by
    have hq : (0 : ℝ) ≤ 15 / 4 * L ^ 2 - 16 * L + 12 := by nlinarith [sq_nonneg (L - 4)]
    have := mul_nonneg (sq_nonneg L) hq
    norm_num
    nlinarith)
  obtain ⟨hsum, hup, hlow⟩ := r11F_tsum_bounds (c0 := 0) (c1 := 0) (c2 := 0) (c3 := 0) (c4 := 1)
    (d0 := 768) (d1 := 384) (d2 := 96) (d3 := 16) (d4 := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (r11F_anti (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hconv
  have heq : ∑' n : ℕ, r11F_P 0 0 0 0 1 (-(3 / 2)) n = r11F_D 4 :=
    tsum_congr fun n => by
      unfold r11F_P
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv]
      congr 1; ring
  rw [heq] at hup
  have hp : ∑ n ∈ Finset.range 256, r11F_P 0 0 0 0 1 (-(3 / 2)) n
      = ∑ n ∈ Finset.range 256, Real.log n ^ 4 * (n : ℝ) ^ (-(3 / 2) : ℝ) :=
    Finset.sum_congr rfl fun n _ => by unfold r11F_P; ring
  obtain ⟨g1, g2, g3, g4⟩ := r11Zs_half_facts
  have q1 := r11F_half_log_pow 1
  have q2 := r11F_half_log_pow 2
  have q3 := r11F_half_log_pow 3
  have q4 := r11F_half_log_pow 4
  rw [pow_one] at q1
  have hA : r11F_P 768 384 96 16 2 (-(1 / 2)) (255 + 1 / 2)
      ≤ (2 * 5.5432244 ^ 4 + 16 * 5.5432244 ^ 3 + 96 * 5.5432244 ^ 2 + 384 * 5.5432244 + 768)
        * (1000000000 / 15984367363) := by
    unfold r11F_P
    exact mul_le_mul (by linarith) g4 g3 (by norm_num)
  have p := r11F_part_upper 4 _ r11F_cert_D4u
  have p' : ∑ n ∈ Finset.range 256, r11F_P 0 0 0 0 1 (-(3 / 2)) n
      ≤ (654217381743791035135003147061585399201 : ℝ)
        * (0.6931471808 ^ 4 / ((2 ^ 20) ^ 4 * 2 ^ 40)) := by
    rw [hp]
    refine p.trans ?_
    have := r11F_log2_pow_le 4
    push_cast
    gcongr
  norm_num at hA p' hup ⊢
  linarith

/-! ## `F₁, F₂, F₃` -/

lemma r11F_mul_le {a b x y : ℝ} (ha : a ≤ x) (hb : b ≤ y) (h0 : 0 ≤ a) (h0' : 0 ≤ b) :
    a * b ≤ x * y := mul_le_mul ha hb h0' (h0.trans ha)

/-- `F₁ ≤ 3.85497` (true value `3.854963`). -/
theorem r11F_F1_upper : r11Chi_F 1 ≤ 3.85497 := by
  obtain ⟨hZ1, hZ2⟩ := r11Zs_Zs_bounds
  obtain ⟨hD1, hD2⟩ := r11Zs_D1_bounds
  obtain ⟨hF1, hF2⟩ := r11Zs_F0_bounds
  have hD := r11F_D2_upper
  have hmul := r11Zs_F1_mul
  rw [← r11F_F1_eq, ← r11F_D2_eq] at hmul
  have h0 := r11F_F_nonneg 1
  have h1 := mul_le_mul_of_nonneg_left hZ1 h0
  have h2 : (1.5052349 : ℝ) * 3.9322388 ≤ r11Zs_F0 * r11Zs_D1 :=
    r11F_mul_le hF1 hD1 (by norm_num) (by norm_num)
  norm_num at h2
  linarith

/-- `15.93013 ≤ F₂ ≤ 15.93026` (true value `15.930204`). -/
theorem r11F_F2_bounds : 15.93013 ≤ r11Chi_F 2 ∧ r11Chi_F 2 ≤ 15.93026 := by
  obtain ⟨hZ1, hZ2⟩ := r11Zs_Zs_bounds
  obtain ⟨hD1, hD2⟩ := r11Zs_D1_bounds
  obtain ⟨hF1, hF2⟩ := r11Zs_F0_bounds
  have hD2l := r11Zs_D2_lower
  have hD2u := r11F_D2_upper
  obtain ⟨hD3l, hD3u⟩ := r11F_D3_bounds
  have hF1l := r11Zs_F1_lower
  have hF1u := r11F_F1_upper
  have hmul := r11F_F2_mul
  rw [r11F_D0_eq, r11F_D1_eq, r11F_F0_eq] at hmul
  rw [← r11F_F1_eq] at hF1l
  rw [← r11F_D2_eq] at hD2l
  have h0 := r11F_F_nonneg 2
  have h1 := mul_le_mul_of_nonneg_left hZ1 h0
  have h1' := mul_le_mul_of_nonneg_left hZ2 h0
  have h2 : (3.8549585 : ℝ) * 3.9322388 ≤ r11Chi_F 1 * r11Zs_D1 :=
    r11F_mul_le hF1l hD1 (by norm_num) (by norm_num)
  have h3 : (1.5052349 : ℝ) * 15.9895518 ≤ r11Zs_F0 * r11F_D 2 :=
    r11F_mul_le hF1 hD2l (by norm_num) (by norm_num)
  have h4 : r11Chi_F 1 * r11Zs_D1 ≤ 3.85497 * 3.9322416 :=
    r11F_mul_le hF1u hD2 (r11F_F_nonneg 1) (by linarith)
  have h5 : r11Zs_F0 * r11F_D 2 ≤ 1.5052362 * 15.989564 :=
    r11F_mul_le hF2 hD2u (by linarith) (by linarith)
  norm_num at h2 h3 h4 h5
  constructor <;> linarith

/-- `F₃ ≤ 95.9504` (true value `95.949549`). -/
theorem r11F_F3_upper : r11Chi_F 3 ≤ 95.9504 := by
  obtain ⟨hZ1, hZ2⟩ := r11Zs_Zs_bounds
  obtain ⟨hD1, hD2⟩ := r11Zs_D1_bounds
  obtain ⟨hF1, hF2⟩ := r11Zs_F0_bounds
  have hD2l := r11Zs_D2_lower
  obtain ⟨hD3l, hD3u⟩ := r11F_D3_bounds
  have hD4 := r11F_D4_upper
  have hF1l := r11Zs_F1_lower
  obtain ⟨hF2l, hF2u⟩ := r11F_F2_bounds
  have hmul := r11F_F3_mul
  rw [r11F_D0_eq, r11F_D1_eq, r11F_F0_eq] at hmul
  rw [← r11F_F1_eq] at hF1l
  rw [← r11F_D2_eq] at hD2l
  have h0 := r11F_F_nonneg 3
  have h1 := mul_le_mul_of_nonneg_left hZ1 h0
  have h2 : (15.93013 : ℝ) * 3.9322388 ≤ r11Chi_F 2 * r11Zs_D1 :=
    r11F_mul_le hF2l hD1 (by norm_num) (by norm_num)
  have h3 : (3.8549585 : ℝ) * 15.9895518 ≤ r11Chi_F 1 * r11F_D 2 :=
    r11F_mul_le hF1l hD2l (by norm_num) (by norm_num)
  have h4 : (1.5052349 : ℝ) * 96.00097 ≤ r11Zs_F0 * r11F_D 3 :=
    r11F_mul_le hF1 hD3l (by norm_num) (by norm_num)
  norm_num at h2 h3 h4
  linarith

theorem r11F_F1 : r11Chi_F 1 ≤ 5.31 := r11F_F1_upper.trans (by norm_num)

theorem r11F_F2 : r11Chi_F 2 ≤ 17.5 := r11F_F2_bounds.2.trans (by norm_num)

theorem r11F_F3 : r11Chi_F 3 ≤ 102.3 := r11F_F3_upper.trans (by norm_num)

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r11F_F1
#print axioms DetPrimality.Bach.r11F_F2
#print axioms DetPrimality.Bach.r11F_F3
