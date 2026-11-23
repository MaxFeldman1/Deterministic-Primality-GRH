import DetPrimality.Bach.SharpZeroSum

/-!
# Round 11, zero sums: second-order tail bounds for `∑ log^k n · n^{-3/2}`

For a convex `f` with `A' = -f` (`A(t) = ∫_t^∞ f`):

* trapezoid: `A(n) - A(n+1) ≤ (f(n) + f(n+1))/2`, hence `∑_{n ≥ N} f(n) ≥ A(N) + f(N)/2`;
* midpoint: `f(n) ≤ A(n-½) - A(n+½)`, hence `∑_{n ≥ N} f(n) ≤ A(N-½)`.

Applied to `f = P(log t) t^{-3/2}`, `A = Q(log t) t^{-1/2}` (`r11Zs_P`), with cut-off `N = 256`
(`r11Zs_tsum_bounds`).
-/

namespace DetPrimality.Bach

/-! ## Trapezoid and midpoint inequalities -/

lemma r11Zs_trapezoid {f A : ℝ → ℝ} {n : ℝ} (hconv : ConvexOn ℝ (Set.Icc n (n + 1)) f)
    (hA : ∀ t ∈ Set.Icc n (n + 1), HasDerivAt A (-f t) t) :
    A n - A (n + 1) ≤ (f n + f (n + 1)) / 2 := by
  set φ : ℝ → ℝ := fun t => (t - t ^ 2 / 2) * f n + t ^ 2 / 2 * f (n + 1) + A (n + t) with hφ
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt φ ((1 - t) * f n + t * f (n + 1) - f (n + t)) t := by
    intro t ht
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h1 : HasDerivAt (fun t : ℝ => (t - t ^ 2 / 2) * f n + t ^ 2 / 2 * f (n + 1))
        ((1 - 2 * t / 2) * f n + 2 * t / 2 * f (n + 1)) t :=
      (((hasDerivAt_id' t).sub (hsq.div_const 2)).mul_const _).add
        ((hsq.div_const 2).mul_const _)
    have h2 : HasDerivAt (fun t : ℝ => A (n + t)) (-f (n + t)) t :=
      (hA (n + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩).comp_const_add n t
    exact (h1.add h2).congr_deriv (by ring)
  have hmono : MonotoneOn φ (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    have ht' := interior_subset ht
    rw [(hder t ht').deriv]
    have h := hconv.2 (show n ∈ Set.Icc n (n + 1) from ⟨le_rfl, by linarith⟩)
      (show n + 1 ∈ Set.Icc n (n + 1) from ⟨by linarith, le_rfl⟩)
      (show (0 : ℝ) ≤ 1 - t by linarith [ht'.2]) ht'.1 (by ring)
    simp only [smul_eq_mul] at h
    rw [show (1 - t) * n + t * (n + 1) = n + t by ring] at h
    linarith
  have h := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [hφ] at h
  norm_num at h
  linarith

lemma r11Zs_midpoint {f A : ℝ → ℝ} {n : ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (n - 1 / 2) (n + 1 / 2)) f)
    (hA : ∀ t ∈ Set.Icc (n - 1 / 2) (n + 1 / 2), HasDerivAt A (-f t) t) :
    f n ≤ A (n - 1 / 2) - A (n + 1 / 2) := by
  set φ : ℝ → ℝ := fun h => A (n - h) - A (n + h) - 2 * h * f n with hφ
  have hder : ∀ h ∈ Set.Icc (0 : ℝ) (1 / 2),
      HasDerivAt φ (f (n - h) + f (n + h) - 2 * f n) h := by
    intro h hh
    have h1 : HasDerivAt (fun h : ℝ => A (n - h)) (- -f (n - h)) h :=
      (hA (n - h) ⟨by linarith [hh.2], by linarith [hh.1]⟩).comp_const_sub n h
    have h2 : HasDerivAt (fun h : ℝ => A (n + h)) (-f (n + h)) h :=
      (hA (n + h) ⟨by linarith [hh.1], by linarith [hh.2]⟩).comp_const_add n h
    have h3 : HasDerivAt (fun h : ℝ => 2 * h * f n) (2 * 1 * f n) h :=
      ((hasDerivAt_id' h).const_mul 2).mul_const _
    exact ((h1.sub h2).sub h3).congr_deriv (by ring)
  have hmono : MonotoneOn φ (Set.Icc 0 (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    have ht' := interior_subset ht
    rw [(hder t ht').deriv]
    have h := hconv.2
      (show n - t ∈ Set.Icc (n - 1 / 2) (n + 1 / 2) from
        ⟨by linarith [ht'.2], by linarith [ht'.1]⟩)
      (show n + t ∈ Set.Icc (n - 1 / 2) (n + 1 / 2) from
        ⟨by linarith [ht'.1], by linarith [ht'.2]⟩)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at h
    rw [show (1 / 2 : ℝ) * (n - t) + 1 / 2 * (n + t) = n by ring] at h
    linarith
  have h := hmono (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [hφ] at h
  norm_num at h
  linarith

/-! ## The family `(c₂ log² t + c₁ log t + c₀) t^a` -/

noncomputable def r11Zs_P (c0 c1 c2 a : ℝ) (t : ℝ) : ℝ :=
  (c2 * Real.log t ^ 2 + c1 * Real.log t + c0) * t ^ a

lemma r11Zs_P_hasDerivAt (c0 c1 c2 a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (r11Zs_P c0 c1 c2 a)
      (r11Zs_P (c1 + a * c0) (2 * c2 + a * c1) (a * c2) (a - 1) t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have h1 : HasDerivAt (fun t : ℝ => c2 * Real.log t ^ 2 + c1 * Real.log t + c0)
      (c2 * (2 * Real.log t * t⁻¹) + c1 * t⁻¹) t := by
    have := (((hl.pow 2).const_mul c2).add (hl.const_mul c1)).add_const c0
    refine this.congr_deriv ?_
    norm_num
  have h2 : HasDerivAt (fun t : ℝ => t ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h3 := h1.mul h2
  have e : t ^ a = t ^ (a - 1) * t := by
    rw [Real.rpow_sub_one ht.ne']; field_simp
  show HasDerivAt (fun t : ℝ => (c2 * Real.log t ^ 2 + c1 * Real.log t + c0) * t ^ a) _ t
  refine h3.congr_deriv ?_
  unfold r11Zs_P
  rw [e]
  generalize t ^ (a - 1) = u
  field_simp
  ring

lemma r11Zs_log_ge_two {t : ℝ} (ht : 8 ≤ t) : 2 ≤ Real.log t := by
  have h1 : Real.log 8 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have h2 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h3 := Real.log_two_gt_d9
  linarith

lemma r11Zs_P_nonneg {c0 c1 c2 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (a : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t = 0 ∨ 1 ≤ t) : 0 ≤ r11Zs_P c0 c1 c2 a t := by
  unfold r11Zs_P
  have hl : 0 ≤ Real.log t := by
    rcases ht1 with rfl | h
    · simp
    · exact Real.log_nonneg h
  have := Real.rpow_nonneg ht a
  positivity

lemma r11Zs_P_convex (c0 c1 c2 a : ℝ)
    (h : ∀ L : ℝ, 2 ≤ L → 0 ≤ ((a - 1) * (a * c2)) * L ^ 2
      + (2 * (a * c2) + (a - 1) * (2 * c2 + a * c1)) * L
      + ((2 * c2 + a * c1) + (a - 1) * (c1 + a * c0))) :
    ConvexOn ℝ (Set.Ici 8) (r11Zs_P c0 c1 c2 a) := by
  have hpos : ∀ t ∈ Set.Ici (8 : ℝ), 0 < t := fun t ht => lt_of_lt_of_le (by norm_num) ht
  have hmono : MonotoneOn (r11Zs_P (c1 + a * c0) (2 * c2 + a * c1) (a * c2) (a - 1))
      (Set.Ici 8) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 8)
      (fun t ht => (r11Zs_P_hasDerivAt _ _ _ _ (hpos t ht)).continuousAt.continuousWithinAt)
      (fun t ht => (r11Zs_P_hasDerivAt _ _ _ _
        (hpos t (interior_subset ht))).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    have ht' := interior_subset ht
    rw [(r11Zs_P_hasDerivAt _ _ _ _ (hpos t ht')).deriv]
    unfold r11Zs_P
    refine mul_nonneg ?_ (Real.rpow_nonneg (hpos t ht').le _)
    have := h (Real.log t) (r11Zs_log_ge_two ht')
    linarith
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 8)
    (fun t ht => (r11Zs_P_hasDerivAt _ _ _ _ (hpos t ht)).continuousAt.continuousWithinAt)
    (fun t ht => (r11Zs_P_hasDerivAt _ _ _ _
      (hpos t (interior_subset ht))).differentiableAt.differentiableWithinAt) ?_
  intro x hx y hy hxy
  rw [(r11Zs_P_hasDerivAt c0 c1 c2 a (hpos x (interior_subset hx))).deriv,
    (r11Zs_P_hasDerivAt c0 c1 c2 a (hpos y (interior_subset hy))).deriv]
  exact hmono (interior_subset hx) (interior_subset hy) hxy

/-! ## Telescoping bounds with cut-off `256` -/

/-- Tail bounds for `∑ f(n)`, `f = r11Zs_P c (-3/2)` convex on `[8, ∞)` with antiderivative
`-A`, `A = r11Zs_P d (-1/2)`. -/
theorem r11Zs_tsum_bounds {c0 c1 c2 d0 d1 d2 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (hA : ∀ t : ℝ, 0 < t → HasDerivAt (r11Zs_P d0 d1 d2 (-(1 / 2)))
      (-(r11Zs_P c0 c1 c2 (-(3 / 2)) t)) t)
    (hconv : ConvexOn ℝ (Set.Ici 8) (r11Zs_P c0 c1 c2 (-(3 / 2)))) :
    Summable (fun n : ℕ => r11Zs_P c0 c1 c2 (-(3 / 2)) n) ∧
    (∑' n : ℕ, r11Zs_P c0 c1 c2 (-(3 / 2)) n
      ≤ ∑ n ∈ Finset.range 256, r11Zs_P c0 c1 c2 (-(3 / 2)) n
        + r11Zs_P d0 d1 d2 (-(1 / 2)) (255 + 1 / 2)) ∧
    ∀ j : ℕ, ∑ n ∈ Finset.range 256, r11Zs_P c0 c1 c2 (-(3 / 2)) n
        + (r11Zs_P d0 d1 d2 (-(1 / 2)) 256 + r11Zs_P c0 c1 c2 (-(3 / 2)) 256 / 2)
        - (r11Zs_P d0 d1 d2 (-(1 / 2)) ((256 + j : ℕ) : ℝ)
          + r11Zs_P c0 c1 c2 (-(3 / 2)) ((256 + j : ℕ) : ℝ) / 2)
      ≤ ∑' n : ℕ, r11Zs_P c0 c1 c2 (-(3 / 2)) n := by
  set f := r11Zs_P c0 c1 c2 (-(3 / 2)) with hf
  set A := r11Zs_P d0 d1 d2 (-(1 / 2)) with hAdef
  have hnn : ∀ n : ℕ, 0 ≤ f n := fun n => by
    refine r11Zs_P_nonneg hc0 hc1 hc2 _ (Nat.cast_nonneg n) ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp
    · right; exact_mod_cast hn
  have hAnn : ∀ t : ℝ, 1 ≤ t → 0 ≤ A t := fun t ht =>
    r11Zs_P_nonneg hd0 hd1 hd2 _ (by linarith) (Or.inr ht)
  -- upper bound
  have hup := szs_sum_range_le_of_tele (fun n : ℕ => f n) (fun n : ℕ => A ((n : ℝ) + 1 / 2)) 255
    hnn (fun n hn => hAnn _ (by
      have : (255 : ℝ) ≤ n := by exact_mod_cast hn
      linarith))
    (fun n hn => by
      have hn' : (255 : ℝ) ≤ n := by exact_mod_cast hn
      have hsub : Set.Icc ((n : ℝ) + 1 - 1 / 2) ((n : ℝ) + 1 + 1 / 2) ⊆ Set.Ici 8 := fun t ht =>
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
        have hsub : Set.Icc (n : ℝ) ((n : ℝ) + 1) ⊆ Set.Ici 8 := fun t ht =>
          Set.mem_Ici.mpr (by linarith [ht.1])
        have := r11Zs_trapezoid (f := f) (A := A) (n := (n : ℝ)) (hconv.subset hsub
          (convex_Icc _ _)) (fun t ht => hA t (by linarith [ht.1]))
        push_cast
        linarith) j
    have h2 := hsum.sum_le_tsum (Finset.range (256 + j)) (fun i _ => hnn i)
    have e : ((256 : ℕ) : ℝ) = 256 := by norm_num
    simp only [e] at hlow
    linarith

end DetPrimality.Bach
