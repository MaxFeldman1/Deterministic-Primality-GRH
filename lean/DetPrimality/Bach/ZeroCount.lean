import Mathlib
import DetPrimality.Bach.Handoffs

/-!
# Zero counting via Jensen's formula ⟹ `∑ m_ρ / |ρ|² < ∞`

Proves `summable_zeroOrd_div_normSq_of_growth`: under the growth hypothesis `GrowthLtTwo` for
`completedLFunction χ`, the nontrivial zeros of `L(s, χ)` (with multiplicity) satisfy
`∑_ρ m_ρ / |ρ|² < ∞`.

Steps:
1. `count_le_of_growth`: Jensen's inequality (`AnalyticOnNhd.sum_divisor_le`) on the discs
   `|s - c| ≤ 2^k` (bound on the circle of radius `2^(k+1)`) gives
   `#{zeros in |s - c| ≤ 2^k} ≤ A·3^k + B`.
2. `summable_of_dyadic_count`: abstract dyadic summation, `∑ m(ρ)/max(1,|ρ-c|)² < ∞`.
3. `zeroOrd_eq_analyticOrderNatAt_completed`: in the critical strip `zeroOrd χ ρ` equals the
   order of vanishing of `completedLFunction χ` (since `1/gammaFactor` is entire and
   nonvanishing for `Re s > 0`).
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-! ## Step 2: abstract dyadic summation -/

/-- The dyadic weight `w r k = 4^{-k}` if `r ≤ 2^k`, else `0`. -/
noncomputable def ZeroCount.dyw (r : ℝ) (k : ℕ) : ℝ := if r ≤ 2 ^ k then (1 / 4 : ℝ) ^ k else 0

lemma ZeroCount.dyw_nonneg (r : ℝ) (k : ℕ) : 0 ≤ ZeroCount.dyw r k := by
  unfold ZeroCount.dyw; split_ifs <;> positivity

lemma ZeroCount.summable_dyw (r : ℝ) : Summable (ZeroCount.dyw r) := by
  refine Summable.of_nonneg_of_le (ZeroCount.dyw_nonneg r) (fun k => ?_)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 4 : ℝ) < 1))
  unfold ZeroCount.dyw; split_ifs <;> [exact le_rfl; positivity]

lemma ZeroCount.one_div_max_sq_le (r : ℝ) :
    1 / (max 1 r) ^ 2 ≤ 4 * ∑' k : ℕ, ZeroCount.dyw r k := by
  have hex : ∃ k : ℕ, r ≤ 2 ^ k := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn.le⟩
  classical
  obtain ⟨k0, hk0spec, hmin⟩ : ∃ k0 : ℕ, r ≤ 2 ^ k0 ∧ ∀ j < k0, ¬ r ≤ 2 ^ j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hle : (1 / 4 : ℝ) ^ k0 ≤ ∑' k : ℕ, ZeroCount.dyw r k := by
    have := (ZeroCount.summable_dyw r).le_tsum k0 (fun j _ => ZeroCount.dyw_nonneg r j)
    simpa [ZeroCount.dyw, hk0spec] using this
  have hmax : (1 : ℝ) ≤ max 1 r := le_max_left _ _
  cases k0 with
  | zero =>
    rw [pow_zero] at hle
    have : 1 / (max 1 r) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  | succ j =>
    have hj : ¬ r ≤ 2 ^ j := hmin j (Nat.lt_succ_self j)
    push Not at hj
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hr : max 1 r = r := max_eq_right (by linarith)
    have e : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h4 : 4 * (1 / 4 : ℝ) ^ (j + 1) = 1 / ((2 : ℝ) ^ j) ^ 2 := by
      rw [e, pow_succ, one_div_pow]; ring
    calc 1 / (max 1 r) ^ 2 = 1 / r ^ 2 := by rw [hr]
      _ ≤ 1 / ((2 : ℝ) ^ j) ^ 2 := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_left₀ (by positivity) hj.le 2
      _ = 4 * (1 / 4 : ℝ) ^ (j + 1) := h4.symm
      _ ≤ 4 * ∑' k : ℕ, ZeroCount.dyw r k := by linarith

/-- Abstract dyadic summation: if the mass of `m` in each disc `|ρ - c| ≤ 2^k` is at most
`A·3^k + B`, then `∑ m(ρ) / max(1, |ρ - c|)² < ∞`. -/
theorem ZeroCount.summable_of_dyadic_count {m : ℂ → ℝ} (hm : ∀ ρ, 0 ≤ m ρ) (c : ℂ) (A B : ℝ)
    (hcount : ∀ (k : ℕ) (T : Finset ℂ), ∑ ρ ∈ T with ‖ρ - c‖ ≤ 2 ^ k, m ρ ≤ A * 3 ^ k + B) :
    Summable fun ρ : ℂ => m ρ / (max 1 ‖ρ - c‖) ^ 2 := by
  have hgeo : Summable fun k : ℕ => A * (3 / 4 : ℝ) ^ k + B * (1 / 4 : ℝ) ^ k :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A).add
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left B)
  refine summable_of_sum_le (c := 4 * ∑' k : ℕ, (A * (3 / 4 : ℝ) ^ k + B * (1 / 4 : ℝ) ^ k))
    (fun ρ => div_nonneg (hm ρ) (by positivity)) fun T => ?_
  have hterm : ∀ ρ ∈ T, m ρ / (max 1 ‖ρ - c‖) ^ 2
      ≤ 4 * ∑' k : ℕ, m ρ * ZeroCount.dyw ‖ρ - c‖ k := by
    intro ρ _
    rw [tsum_mul_left, div_eq_mul_one_div]
    have := mul_le_mul_of_nonneg_left (ZeroCount.one_div_max_sq_le ‖ρ - c‖) (hm ρ)
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum
    (fun ρ _ => (ZeroCount.summable_dyw _).mul_left (m ρ))]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Summable.tsum_le_tsum (fun k => ?_)
    (summable_sum fun ρ _ => (ZeroCount.summable_dyw _).mul_left (m ρ)) hgeo
  have h1 : ∑ ρ ∈ T, m ρ * ZeroCount.dyw ‖ρ - c‖ k
      = (1 / 4 : ℝ) ^ k * ∑ ρ ∈ T with ‖ρ - c‖ ≤ 2 ^ k, m ρ := by
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    unfold ZeroCount.dyw
    split_ifs <;> ring
  have h2 : A * (3 / 4 : ℝ) ^ k + B * (1 / 4 : ℝ) ^ k = (1 / 4 : ℝ) ^ k * (A * 3 ^ k + B) := by
    have : (3 / 4 : ℝ) ^ k = 3 ^ k * (1 / 4 : ℝ) ^ k := by rw [← mul_pow]; norm_num
    rw [this]; ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left (hcount k T) (by positivity)

/-! ## Step 1: Jensen zero counting -/

lemma ZeroCount.divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} (hf : Differentiable ℂ f) (U : Set ℂ)
    {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (fun x _ => hf.analyticAt x) hz, analyticOrderNatAt]
  generalize analyticOrderAt f z = e
  induction e using ENat.recTopCoe <;> simp

lemma ZeroCount.two_rpow_three_halves_le : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ 3 := by
  have h1 : ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = 8 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  nlinarith

lemma ZeroCount.two_pow_rpow_le (k : ℕ) : ((2 : ℝ) ^ k) ^ ((3 : ℝ) / 2) ≤ 3 ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_natCast]
  exact pow_le_pow_left₀ (by positivity) ZeroCount.two_rpow_three_halves_le k

/-- **Jensen zero counting.**  An entire function with `f c ≠ 0` and growth
`‖f s‖ ≤ exp (C (1+‖s‖)^{3/2})` has at most `A·3^k + B` zeros (with multiplicity) in the disc
`|s - c| ≤ 2^k`. -/
theorem ZeroCount.count_le_of_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    (hc : f c ≠ 0) {C : ℝ} (hC : 0 < C)
    (hG : ∀ s : ℂ, ‖f s‖ ≤ Real.exp (C * (1 + ‖s‖) ^ ((3 : ℝ) / 2))) :
    ∃ A B : ℝ, ∀ (k : ℕ) (T : Finset ℂ),
      ∑ ρ ∈ T with ‖ρ - c‖ ≤ 2 ^ k, (analyticOrderNatAt f ρ : ℝ) ≤ A * 3 ^ k + B := by
  set D : ℝ := 3 + ‖c‖ with hD
  have hDpos : 0 < D := by positivity
  set a0 : ℝ := C * D ^ ((3 : ℝ) / 2) with ha0def
  have ha0 : 0 ≤ a0 := by positivity
  set b : ℝ := Real.log ‖f c‖ with hb
  refine ⟨2 * a0, 2 * |b|, fun k T => ?_⟩
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall c |(2 : ℝ) ^ (k + 1)|) :=
    fun x _ => hf.analyticAt x
  -- bound on the circle of radius `2^(k+1)`
  have hbound : ∀ z ∈ Metric.sphere c |(2 : ℝ) ^ (k + 1)|,
      ‖f z‖ ≤ Real.exp (a0 * 3 ^ k) := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos (by positivity)] at hz
    have hz' : 1 + ‖z‖ ≤ D * 2 ^ k := by
      have : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        have := norm_add_le (z - c) c; simpa using this
      rw [hz, pow_succ] at this
      rw [hD]; nlinarith [mul_le_mul_of_nonneg_left h2k (norm_nonneg c)]
    refine (hG z).trans (Real.exp_le_exp.mpr ?_)
    rw [ha0def, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    calc (1 + ‖z‖) ^ ((3 : ℝ) / 2) ≤ (D * 2 ^ k) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) hz' (by norm_num)
      _ = D ^ ((3 : ℝ) / 2) * ((2 : ℝ) ^ k) ^ ((3 : ℝ) / 2) :=
          Real.mul_rpow hDpos.le (by positivity)
      _ ≤ D ^ ((3 : ℝ) / 2) * 3 ^ k :=
          mul_le_mul_of_nonneg_left (ZeroCount.two_pow_rpow_le k) (by positivity)
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := (2 : ℝ) ^ k) (R := (2 : ℝ) ^ (k + 1))
    (M := Real.exp (a0 * 3 ^ k)) (by positivity)
    (by rw [abs_of_pos (by positivity), abs_of_pos (by positivity), pow_succ]; linarith)
    (Real.one_le_exp (by positivity)) hfa hc hbound
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)] at hJ
  have hR : (2 : ℝ) ^ (k + 1) / 2 ^ k = 2 := by rw [pow_succ]; field_simp
  rw [hR, Real.log_div (Real.exp_pos _).ne' (norm_ne_zero_iff.mpr hc), Real.log_exp] at hJ
  -- compare the finite sum with the finsum of the divisor
  set Dv := MeromorphicOn.divisor f (Metric.closedBall c ((2 : ℝ) ^ k)) with hDv
  have hfin : Dv.support.Finite := Dv.finiteSupport (isCompact_closedBall _ _)
  have hsum : ∑ ρ ∈ T with ‖ρ - c‖ ≤ 2 ^ k, (analyticOrderNatAt f ρ : ℝ)
      ≤ ((∑ᶠ u, Dv u : ℤ) : ℝ) := by
    have e1 : ∑ ρ ∈ T with ‖ρ - c‖ ≤ 2 ^ k, (analyticOrderNatAt f ρ : ℝ)
        = ((∑ ρ ∈ T with ‖ρ - c‖ ≤ 2 ^ k, Dv ρ : ℤ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      rw [Finset.mem_filter] at hρ
      rw [hDv, ZeroCount.divisor_eq_analyticOrderNatAt hf _
        (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hρ.2)]
      simp
    rw [e1]
    have hsub : Function.support Dv ⊆ ((T.filter fun ρ => ‖ρ - c‖ ≤ 2 ^ k) ∪ hfin.toFinset :
        Finset ℂ) := by
      intro x hx; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hx
    rw [finsum_eq_sum_of_support_subset Dv hsub]
    exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun x _ _ => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun y _ => hf.analyticAt y)) x)
  refine hsum.trans (hJ.trans ?_)
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [div_le_iff₀ (by linarith)]
  have hb' : -b ≤ |b| := neg_le_abs b
  have hpos : 0 ≤ a0 * 3 ^ k := by positivity
  have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * a0 * 3 ^ k + 2 * |b|)
    (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 2)
  nlinarith [abs_nonneg b]

/-! ## Step 3: `zeroOrd` vs the order of `completedLFunction` -/

lemma ZeroCount.differentiable_inv_gammaFactor {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ fun s => (gammaFactor χ s)⁻¹ := by
  rcases χ.even_or_odd with h | h
  · simp_rw [h.gammaFactor_def]; exact differentiable_Gammaℝ_inv
  · simp_rw [h.gammaFactor_def]
    exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

lemma ZeroCount.gammaFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- For `Re ρ > 0`, the order of `L(·, χ)` at `ρ` equals that of `completedLFunction χ`. -/
lemma ZeroCount.analyticOrderNatAt_LFunction_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) {ρ : ℂ} (hρ : 0 < ρ.re) :
    analyticOrderNatAt (LFunction χ) ρ = analyticOrderNatAt (completedLFunction χ) ρ := by
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at hρ
  have hev : LFunction χ =ᶠ[nhds ρ] (completedLFunction χ * fun s => (gammaFactor χ s)⁻¹) := by
    filter_upwards [eventually_ne_nhds hρ0] with s hs
    rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs), Pi.mul_apply, div_eq_mul_inv]
  have hΛ : AnalyticAt ℂ (completedLFunction χ) ρ :=
    (differentiable_completedLFunction hχ1).analyticAt ρ
  have hg : AnalyticAt ℂ (fun s => (gammaFactor χ s)⁻¹) ρ :=
    (ZeroCount.differentiable_inv_gammaFactor χ).analyticAt ρ
  have hg0 : analyticOrderAt (fun s => (gammaFactor χ s)⁻¹) ρ = 0 :=
    hg.analyticOrderAt_eq_zero.mpr (inv_ne_zero (ZeroCount.gammaFactor_ne_zero χ hρ))
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_congr hev,
    analyticOrderAt_mul hΛ hg, hg0, add_zero]

lemma ZeroCount.zeroOrd_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (ρ : ℂ) : zeroOrd χ ρ ≤ analyticOrderNatAt (completedLFunction χ) ρ := by
  unfold zeroOrd
  split_ifs with h
  · exact (ZeroCount.analyticOrderNatAt_LFunction_eq χ hχ1 h.1).le
  · exact Nat.zero_le _

lemma ZeroCount.completedLFunction_two_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) : completedLFunction χ 2 ≠ 0 := by
  intro h
  have hL := LFunction_eq_completed_div_gammaFactor χ 2 (Or.inl two_ne_zero)
  rw [h, zero_div] at hL
  exact LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by norm_num) hL

/-! ## Main theorem -/

/-- `∑_ρ m_ρ / |ρ|² < ∞` over the nontrivial zeros of `L(s, χ)`, given the growth bound
`GrowthLtTwo (completedLFunction χ)`.  (Primitivity is not needed.) -/
theorem summable_zeroOrd_div_normSq_of_growth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hG : GrowthLtTwo (completedLFunction χ)) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2 := by
  set f := completedLFunction χ with hfdef
  have hf : Differentiable ℂ f := differentiable_completedLFunction hχ1
  have hf2 : f 2 ≠ 0 := ZeroCount.completedLFunction_two_ne_zero χ hχ1
  obtain ⟨C, hC, hbound⟩ := hG
  obtain ⟨A, B, hcount⟩ := ZeroCount.count_le_of_growth hf hf2 hC hbound
  set m : ℂ → ℝ := fun ρ => (analyticOrderNatAt f ρ : ℝ) with hm
  have hsum := (ZeroCount.summable_of_dyadic_count (m := m) (fun ρ => by positivity) 2 A B
    hcount).mul_left 9
  refine Summable.of_norm_bounded_eventually hsum ?_
  rw [Filter.eventually_cofinite]
  have hfin : (MeromorphicOn.divisor f (Metric.closedBall 2 3)).support.Finite :=
    (MeromorphicOn.divisor f _).finiteSupport (isCompact_closedBall _ _)
  refine hfin.subset fun ρ hρ => ?_
  simp only [Set.mem_ofPred_eq] at hρ
  have hle : (zeroOrd χ ρ : ℝ) ≤ m ρ := by
    simp only [hm]; exact_mod_cast ZeroCount.zeroOrd_le χ hχ1 ρ
  by_cases hz : zeroOrd χ ρ = 0
  · exfalso; apply hρ
    rw [hz]; simp only [Nat.cast_zero, zero_div, norm_zero]; positivity
  by_cases hn : 1 ≤ ‖ρ‖
  · exfalso; apply hρ
    rw [Real.norm_of_nonneg (by positivity)]
    have hρ2 : ‖ρ - 2‖ ≤ ‖ρ‖ + 2 := by
      have := norm_sub_le ρ 2; simpa using this
    have hmax : max 1 ‖ρ - 2‖ ≤ 3 * ‖ρ‖ := max_le (by linarith) (by linarith)
    have hmaxpos : 0 < max 1 ‖ρ - 2‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hnpos : 0 < ‖ρ‖ := by linarith
    calc (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2 ≤ m ρ / ‖ρ‖ ^ 2 :=
          div_le_div_of_nonneg_right hle (by positivity)
      _ = 9 * m ρ / (3 * ‖ρ‖) ^ 2 := by field_simp; ring
      _ ≤ 9 * m ρ / (max 1 ‖ρ - 2‖) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ hmaxpos.le hmax 2)
      _ = 9 * (m ρ / (max 1 ‖ρ - 2‖) ^ 2) := by ring
  · push Not at hn
    have hmem : ρ ∈ Metric.closedBall (2 : ℂ) 3 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have := norm_sub_le ρ 2; simp at this; linarith
    rw [Function.mem_support, ZeroCount.divisor_eq_analyticOrderNatAt hf _ hmem]
    have : 1 ≤ analyticOrderNatAt f ρ :=
      (Nat.one_le_iff_ne_zero.mpr hz).trans (ZeroCount.zeroOrd_le χ hχ1 ρ)
    omega

end DetPrimality.Bach
