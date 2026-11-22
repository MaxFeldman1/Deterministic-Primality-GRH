import DetPrimality.Bach.Handoffs

/-!
# Genus-1 Hadamard partial fractions for entire functions of order `< 2`

For an entire `f` with `f 0 ≠ 0` and `GrowthLtTwo f` we prove (no infinite products needed):

* `summable_order_div_normSq` : `∑_ρ m_ρ / |ρ|² < ∞` (Jensen, dyadic shells);
* `logDeriv_eq_tsum` : `f'/f (s) = f'/f (0) + ∑_ρ m_ρ (1/(s-ρ) + 1/ρ)`
  (divide out the zeros in `|ρ| ≤ r`, Borel–Carathéodory for the logarithm of the quotient,
  Cauchy estimate + Schwarz lemma, let `r → ∞`).

Here `m_ρ = analyticOrderNatAt f ρ`.
-/

open Complex Metric Set Filter Topology

namespace DetPrimality.Bach.Hadamard

/-! ### Elementary real estimates -/

lemma rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * √x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

lemma growth_bound {C r : ℝ} (hC : 0 < C) (hr : 1 ≤ r) :
    C * (1 + 2 * r) ^ ((3 : ℝ) / 2) ≤ 6 * C * (r * √r) := by
  have hr0 : 0 ≤ r := by linarith
  rw [rpow_three_halves (by linarith)]
  have h1 : √(1 + 2 * r) ≤ 2 * √r := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hr0]; linarith
  have h3 : (1 + 2 * r) * √(1 + 2 * r) ≤ (3 * r) * (2 * √r) :=
    mul_le_mul (by linarith) h1 (Real.sqrt_nonneg _) (by linarith)
  calc C * ((1 + 2 * r) * √(1 + 2 * r)) ≤ C * ((3 * r) * (2 * √r)) :=
        mul_le_mul_of_nonneg_left h3 hC.le
    _ = 6 * C * (r * √r) := by ring

lemma final_alg (K n t : ℝ) (ht : 0 < t) :
    16 * (K * (t * t * t)) / (t * t) / (t * t / 4) * n = 64 * K * n / t := by
  field_simp
  ring

/-! ### Orders of zeros and division by finitely many zeros -/

section general

variable {f : ℂ → ℂ}

lemma order_ne_top (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (ρ : ℂ) :
    analyticOrderAt f ρ ≠ ⊤ := by
  intro h
  rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ (fun z => hf.analyticAt z)] at h
  exact h0 (by rw [h]; rfl)

lemma orderNat_eq_zero_iff (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (ρ : ℂ) :
    analyticOrderNatAt f ρ = 0 ↔ f ρ ≠ 0 := by
  rw [analyticOrderNatAt, ENat.toNat_eq_zero]
  simp [order_ne_top hf h0 ρ, (hf.analyticAt ρ).analyticOrderAt_eq_zero]

/-- Divide an entire function by `(z - a)^n`, `n` the order of vanishing at `a`. -/
lemma exists_factor_sub {g : ℂ → ℂ} (hg : Differentiable ℂ g) (a : ℂ)
    (hord : analyticOrderAt g a ≠ ⊤) :
    ∃ g₁ : ℂ → ℂ, Differentiable ℂ g₁ ∧ g₁ a ≠ 0 ∧
      ∀ z, g z = (z - a) ^ analyticOrderNatAt g a * g₁ z := by
  classical
  obtain ⟨g₀, hg₀, hg₀a, hev⟩ := (hg.analyticAt a).analyticOrderAt_ne_top.mp hord
  refine ⟨fun z => if z = a then g₀ a else g z / (z - a) ^ analyticOrderNatAt g a, ?_,
    by simp [hg₀a], ?_⟩
  · intro z
    by_cases hz : z = a
    · have : (fun z => if z = a then g₀ a else g z / (z - a) ^ analyticOrderNatAt g a)
          =ᶠ[𝓝 z] g₀ := by
        rw [hz]
        filter_upwards [hev] with w hw
        by_cases hwa : w = a
        · simp [hwa]
        · have h2 : (w - a) ^ analyticOrderNatAt g a ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hwa)
          simp only [if_neg hwa]
          rw [hw, smul_eq_mul]
          field_simp
      refine this.differentiableAt_iff.mpr ?_
      rw [hz]; exact hg₀.differentiableAt
    · have : (fun z => if z = a then g₀ a else g z / (z - a) ^ analyticOrderNatAt g a)
          =ᶠ[𝓝 z] fun w => g w / (w - a) ^ analyticOrderNatAt g a := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        simp [show w ≠ a from hw]
      refine this.differentiableAt_iff.mpr ?_
      exact (hg z).div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hz))
  · intro z
    by_cases hz : z = a
    · have h := hev.self_of_nhds
      simp only [sub_self, smul_eq_mul] at h
      simp only [hz, if_true, sub_self]
      exact h
    · have h2 : (z - a) ^ analyticOrderNatAt g a ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
      simp only [if_neg hz]
      field_simp

lemma exists_factor_one {g : ℂ → ℂ} (hg : Differentiable ℂ g) {a : ℂ} (ha : a ≠ 0)
    (hord : analyticOrderAt g a ≠ ⊤) :
    ∃ (n : ℕ) (g₁ : ℂ → ℂ), Differentiable ℂ g₁ ∧ g₁ a ≠ 0 ∧
      ∀ z, g z = (1 - z / a) ^ n * g₁ z := by
  obtain ⟨g₁, hg₁, hg₁a, h⟩ := exists_factor_sub hg a hord
  refine ⟨analyticOrderNatAt g a, fun z => (-a) ^ analyticOrderNatAt g a * g₁ z,
    hg₁.const_mul _, mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr ha)) hg₁a, fun z => ?_⟩
  have e : z - a = (1 - z / a) * (-a) := by (field_simp; ring)
  rw [h z, ← mul_assoc, ← mul_pow, ← e]

/-- Divide an entire function by a finite product of linear factors killing all its zeros
in a given finite set. -/
lemma exists_factor_finset (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (Z : Finset ℂ) :
    ∃ (e : ℂ → ℕ) (g : ℂ → ℂ), Differentiable ℂ g ∧ (∀ ρ ∈ Z, g ρ ≠ 0) ∧
      ∀ z, f z = (∏ ρ ∈ Z, (1 - z / ρ) ^ e ρ) * g z := by
  classical
  induction Z using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, f, hf, by simp, by simp⟩
  | insert a Z ha ih =>
    obtain ⟨e, g, hg, hgZ, hfg⟩ := ih
    have hupd : ∀ (n : ℕ) (z : ℂ), ∏ ρ ∈ Z, (1 - z / ρ) ^ Function.update e a n ρ
        = ∏ ρ ∈ Z, (1 - z / ρ) ^ e ρ := fun n z =>
      Finset.prod_congr rfl fun ρ hρ => by
        rw [Function.update_of_ne]; rintro rfl; exact ha hρ
    by_cases ha0 : a = 0
    · refine ⟨Function.update e a 0, g, hg, ?_, ?_⟩
      · intro ρ hρ
        rcases Finset.mem_insert.mp hρ with h | hρ
        · intro hgρ
          have hg0 : g 0 = 0 := by rwa [h, ha0] at hgρ
          apply h0; rw [hfg 0, hg0, mul_zero]
        · exact hgZ ρ hρ
      · intro z
        rw [Finset.prod_insert ha, Function.update_self, pow_zero, one_mul, hupd, hfg z]
    · have hord : analyticOrderAt g a ≠ ⊤ := by
        intro htop
        rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero a (fun z => hg.analyticAt z)] at htop
        apply h0; rw [hfg 0, htop]; simp
      obtain ⟨n, g₁, hg₁, hg₁a, hgg₁⟩ := exists_factor_one hg ha0 hord
      refine ⟨Function.update e a n, g₁, hg₁, ?_, ?_⟩
      · intro ρ hρ
        rcases Finset.mem_insert.mp hρ with h | hρ
        · rw [h]; exact hg₁a
        · intro h; exact hgZ ρ hρ (by rw [hgg₁, h, mul_zero])
      · intro z
        rw [Finset.prod_insert ha, Function.update_self, hupd, hfg z, hgg₁ z]
        ring

lemma order_eq_of_factor {g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {Z : Finset ℂ} {e : ℂ → ℕ} (hfg : ∀ z, f z = (∏ ρ ∈ Z, (1 - z / ρ) ^ e ρ) * g z) {ρ : ℂ}
    (hρ : ρ ∈ Z) (hρ0 : ρ ≠ 0) (hgρ : g ρ ≠ 0) :
    analyticOrderAt f ρ = e ρ := by
  classical
  rw [(hf.analyticAt ρ).analyticOrderAt_eq_natCast]
  refine ⟨fun z => (-1 / ρ) ^ e ρ * ((∏ ρ' ∈ Z.erase ρ, (1 - z / ρ') ^ e ρ') * g z), ?_, ?_, ?_⟩
  · apply Differentiable.analyticAt
    refine Differentiable.const_mul (Differentiable.mul ?_ hg) _
    exact Differentiable.fun_finsetProd fun ρ' _ => by fun_prop
  · refine mul_ne_zero (pow_ne_zero _ (div_ne_zero (by norm_num) hρ0)) (mul_ne_zero ?_ hgρ)
    rw [Finset.prod_ne_zero_iff]
    intro ρ' hρ'
    obtain ⟨hne, -⟩ := Finset.mem_erase.mp hρ'
    apply pow_ne_zero
    by_cases h0 : ρ' = 0
    · simp [h0]
    · rw [sub_ne_zero]; intro h; rw [eq_div_iff h0, one_mul] at h; exact hne h
  · refine Filter.Eventually.of_forall fun z => ?_
    have e1 : (1 - z / ρ) = (z - ρ) * (-1 / ρ) := by (field_simp; ring)
    rw [hfg z, ← Finset.mul_prod_erase Z _ hρ, smul_eq_mul, e1, mul_pow]
    ring

/-! ### Zeros in a disc and Jensen's bound -/

/-- The zeros of `f` in a closed disc form a finite set, and Jensen's inequality bounds
their number (with multiplicity). -/
lemma exists_zero_finset (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ Z : Finset ℂ, (∀ ρ, ρ ∈ Z ↔ ‖ρ‖ ≤ r ∧ f ρ = 0) ∧
      ∀ M : ℝ, 1 ≤ M → (∀ z : ℂ, ‖z‖ = 2 * r → ‖f z‖ ≤ M) →
        ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) ≤ Real.log (M / ‖f 0‖) / Real.log 2 := by
  have hA : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have habs : |r| = r := abs_of_pos hr
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hfin : (MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|)).finiteSupport (isCompact_closedBall 0 |r|)
  have hDin : ∀ ρ ∈ closedBall (0 : ℂ) |r|,
      MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|) ρ = (analyticOrderNatAt f ρ : ℤ) := by
    intro ρ hρ
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hA.mono (subset_univ _)) hρ,
      ← Nat.cast_analyticOrderNatAt (order_ne_top hf h0 ρ)]
    simp
  have hDout : ∀ ρ ∉ closedBall (0 : ℂ) |r|,
      MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|) ρ = 0 := fun ρ hρ =>
    (MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|)).apply_eq_zero_of_notMem hρ
  refine ⟨hfin.toFinset, fun ρ => ?_, fun M hM hb => ?_⟩
  · rw [Set.Finite.mem_toFinset, Function.mem_support]
    by_cases hρ : ρ ∈ closedBall (0 : ℂ) |r|
    · rw [hDin ρ hρ]
      have h1 : ‖ρ‖ ≤ r := by simpa [habs] using hρ
      have := orderNat_eq_zero_iff hf h0 ρ
      constructor
      · intro h
        refine ⟨h1, ?_⟩
        by_contra h2
        exact h (by exact_mod_cast this.mpr h2)
      · rintro ⟨-, h2⟩ h
        exact (this.mp (by exact_mod_cast h)) h2
    · rw [hDout ρ hρ]
      have h1 : ¬ ‖ρ‖ ≤ r := by simpa [habs] using hρ
      simp [h1]
  · have key := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := r) (R := 2 * r) (M := M)
      (f := f) (by rw [habs]; exact hr) (by rw [habs, abs_of_pos h2r]; linarith) hM
      (hA.mono (subset_univ _)) h0
      (fun z hz => hb z (by
        rw [abs_of_pos h2r] at hz
        simpa using hz))
    have h2 : (2 * r / r) = 2 := by field_simp
    rw [h2] at key
    refine le_trans (le_of_eq ?_) key
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by simp)]
    push_cast
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρ' : MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|) ρ ≠ 0 := by simpa using hρ
    have hin : ρ ∈ closedBall (0 : ℂ) |r| := by
      by_contra h; exact hρ' (hDout ρ h)
    rw [hDin ρ hin]; simp

lemma count_le (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {C : ℝ} (hC : 0 < C)
    (hb : ∀ s : ℂ, ‖f s‖ ≤ Real.exp (C * (1 + ‖s‖) ^ ((3 : ℝ) / 2))) {r : ℝ} (hr : 1 ≤ r) :
    ∃ Z : Finset ℂ, (∀ ρ, ρ ∈ Z ↔ ‖ρ‖ ≤ r ∧ f ρ = 0) ∧
      ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) ≤
        (6 * C + |Real.log ‖f 0‖|) / Real.log 2 * (r * √r) := by
  obtain ⟨Z, hZ, hcount⟩ := exists_zero_finset hf h0 (by linarith : (0 : ℝ) < r)
  refine ⟨Z, hZ, ?_⟩
  have hM := hcount (Real.exp (C * (1 + 2 * r) ^ ((3 : ℝ) / 2)))
    (Real.one_le_exp (by positivity)) (fun z hz => by have := hb z; rwa [hz] at this)
  refine hM.trans ?_
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.log_div (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr h0), Real.log_exp,
    div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlog2]
  have h1 := growth_bound hC hr
  have h2 : 1 ≤ r * √r := by
    have : 1 ≤ √r := Real.one_le_sqrt.mpr hr
    nlinarith
  have h3 : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := neg_le_abs _
  have h4 : 0 ≤ |Real.log ‖f 0‖| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 h4]

/-- **Convergence exponent ≤ 2**: `∑ m_ρ / |ρ|² < ∞` for an entire function of order `< 2`. -/
theorem summable_order_div_normSq (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hG : GrowthLtTwo f) :
    Summable fun ρ : ℂ => (analyticOrderNatAt f ρ : ℝ) / ‖ρ‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hb⟩ := hG
  obtain ⟨δ, hδ0, hδ1, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z : ℂ, ‖z‖ < δ → f z ≠ 0 := by
    have := hf.continuous.continuousAt.eventually_ne h0
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp this
    refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun z hz => h ?_⟩
    rw [dist_zero_right]; exact lt_of_lt_of_le hz (min_le_left _ _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (6 * C + |Real.log ‖f 0‖|) / Real.log 2 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    rw [hA]; positivity
  have hpow : ∀ k : ℕ, (1 : ℝ) ≤ 2 ^ k := fun k => one_le_pow₀ (by norm_num)
  choose Z hZ hcount using fun k : ℕ => count_le hf h0 hC hb (hpow k)
  have hcount' : ∀ k, ∑ ρ ∈ Z k, (analyticOrderNatAt f ρ : ℝ) ≤ A * 3 ^ k := by
    intro k
    refine (hcount k).trans ?_
    rw [← hA]
    have h1 : √((2 : ℝ) ^ k) ≤ (3 / 2) ^ k := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [← pow_mul, mul_comm k 2, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have h2 : (2 : ℝ) ^ k * √((2 : ℝ) ^ k) ≤ 3 ^ k := by
      calc (2 : ℝ) ^ k * √((2 : ℝ) ^ k) ≤ 2 ^ k * (3 / 2) ^ k := by gcongr
        _ = 3 ^ k := by rw [← mul_pow]; norm_num
    exact mul_le_mul_of_nonneg_left h2 hA0
  have h4gen : ∀ j : ℕ, (4 : ℝ) ^ (j + 1) = 4 * (2 ^ j) ^ 2 := by
    intro j
    have : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
    rw [this, pow_succ]; ring
  have hδsq : δ ^ 2 ≤ 1 := pow_le_one₀ hδ0.le hδ1
  refine summable_of_sum_le (c := 4 / δ ^ 2 * (A * 4))
    (fun ρ => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) fun F => ?_
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ ρ ∈ F, ‖ρ‖ ≤ 2 ^ K := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ ρ ∈ F, ‖ρ‖) (one_lt_two : (1 : ℝ) < 2)
    exact ⟨K, fun ρ hρ => (Finset.single_le_sum (f := fun ρ : ℂ => ‖ρ‖)
      (fun _ _ => norm_nonneg _) hρ).trans hK.le⟩
  have hpt : ∀ ρ ∈ F, (analyticOrderNatAt f ρ : ℝ) / ‖ρ‖ ^ 2 ≤
      4 / δ ^ 2 * ∑ k ∈ Finset.range (K + 1), (1 / 4 : ℝ) ^ k *
        (if ρ ∈ Z k then (analyticOrderNatAt f ρ : ℝ) else 0) := by
    intro ρ hρ
    have hnn : 0 ≤ ∑ k ∈ Finset.range (K + 1), (1 / 4 : ℝ) ^ k *
        (if ρ ∈ Z k then (analyticOrderNatAt f ρ : ℝ) else 0) :=
      Finset.sum_nonneg fun k _ => by positivity
    by_cases hord : analyticOrderNatAt f ρ = 0
    · rw [hord]; simp only [Nat.cast_zero, zero_div]; positivity
    · have hfρ : f ρ = 0 := by
        by_contra h; exact hord ((orderNat_eq_zero_iff hf h0 ρ).mpr h)
      have hρδ : δ ≤ ‖ρ‖ := by
        by_contra h; exact hδ ρ (not_le.mp h) hfρ
      have hρpos : 0 < ‖ρ‖ := lt_of_lt_of_le hδ0 hρδ
      have hex : ∃ k : ℕ, ‖ρ‖ ≤ 2 ^ k := ⟨K, hK ρ hρ⟩
      have hk1 : ‖ρ‖ ≤ 2 ^ (Nat.find hex) := Nat.find_spec hex
      have hkK : Nat.find hex ≤ K := Nat.find_min' hex (hK ρ hρ)
      have hmem : ρ ∈ Z (Nat.find hex) := (hZ _ ρ).mpr ⟨hk1, hfρ⟩
      have hkey : δ ^ 2 * 4 ^ (Nat.find hex) ≤ 4 * ‖ρ‖ ^ 2 := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with hk0 | hk0
        · rw [hk0, pow_zero, mul_one]
          nlinarith [mul_self_le_mul_self hδ0.le hρδ]
        · have hlt : ¬ ‖ρ‖ ≤ 2 ^ (Nat.find hex - 1) := Nat.find_min hex (by omega)
          have hlt' : (2 : ℝ) ^ (Nat.find hex - 1) < ‖ρ‖ := not_le.mp hlt
          have h4 : (4 : ℝ) ^ (Nat.find hex) = 4 * (2 ^ (Nat.find hex - 1)) ^ 2 := by
            have := h4gen (Nat.find hex - 1)
            rwa [Nat.sub_add_cancel hk0] at this
          have h5 : ((2 : ℝ) ^ (Nat.find hex - 1)) ^ 2 ≤ ‖ρ‖ ^ 2 :=
            pow_le_pow_left₀ (by positivity) hlt'.le 2
          rw [h4]
          nlinarith [mul_le_mul_of_nonneg_right hδsq (sq_nonneg ((2 : ℝ) ^ (Nat.find hex - 1)))]
      have hsingle : (1 / 4 : ℝ) ^ (Nat.find hex) * (analyticOrderNatAt f ρ : ℝ) ≤
          ∑ k ∈ Finset.range (K + 1), (1 / 4 : ℝ) ^ k *
            (if ρ ∈ Z k then (analyticOrderNatAt f ρ : ℝ) else 0) := by
        have := Finset.single_le_sum (f := fun k => (1 / 4 : ℝ) ^ k *
            (if ρ ∈ Z k then (analyticOrderNatAt f ρ : ℝ) else 0))
          (fun k _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hkK))
        simpa [hmem] using this
      have hm : (0 : ℝ) ≤ analyticOrderNatAt f ρ := Nat.cast_nonneg _
      calc (analyticOrderNatAt f ρ : ℝ) / ‖ρ‖ ^ 2
          ≤ 4 / δ ^ 2 * ((1 / 4 : ℝ) ^ (Nat.find hex) * (analyticOrderNatAt f ρ : ℝ)) := by
            rw [div_le_iff₀ (pow_pos hρpos 2)]
            have e : 4 / δ ^ 2 * ((1 / 4 : ℝ) ^ (Nat.find hex) * (analyticOrderNatAt f ρ : ℝ))
                * ‖ρ‖ ^ 2
                = (analyticOrderNatAt f ρ : ℝ) * (4 * ‖ρ‖ ^ 2) / (δ ^ 2 * 4 ^ (Nat.find hex)) := by
              rw [one_div, inv_pow]; field_simp
            rw [e, le_div_iff₀ (by positivity)]
            exact mul_le_mul_of_nonneg_left hkey hm
        _ ≤ _ := mul_le_mul_of_nonneg_left hsingle (by positivity)
  calc ∑ ρ ∈ F, (analyticOrderNatAt f ρ : ℝ) / ‖ρ‖ ^ 2
      ≤ ∑ ρ ∈ F, 4 / δ ^ 2 * ∑ k ∈ Finset.range (K + 1), (1 / 4 : ℝ) ^ k *
          (if ρ ∈ Z k then (analyticOrderNatAt f ρ : ℝ) else 0) := Finset.sum_le_sum hpt
    _ = 4 / δ ^ 2 * ∑ k ∈ Finset.range (K + 1), (1 / 4 : ℝ) ^ k *
          ∑ ρ ∈ F, (if ρ ∈ Z k then (analyticOrderNatAt f ρ : ℝ) else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ 4 / δ ^ 2 * ∑ k ∈ Finset.range (K + 1), (1 / 4 : ℝ) ^ k * (A * 3 ^ k) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans ?_ (hcount' k)
        rw [← Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).2)
          (fun _ _ _ => Nat.cast_nonneg _)
    _ = 4 / δ ^ 2 * (A * ∑ k ∈ Finset.range (K + 1), (3 / 4 : ℝ) ^ k) := by
        congr 1; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [div_pow, div_pow, one_pow]; ring
    _ ≤ 4 / δ ^ 2 * (A * 4) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hA0) (by positivity)
        rw [geom_sum_eq (by norm_num) _, div_le_iff_of_neg (by norm_num)]
        have : (0 : ℝ) ≤ (3 / 4) ^ (K + 1) := by positivity
        linarith

/-- If `∑ m_ρ/|ρ|² < ∞` then the genus-1 partial fraction series converges absolutely. -/
lemma summable_partialFraction {m : ℂ → ℕ}
    (hS : Summable fun ρ : ℂ => (m ρ : ℝ) / ‖ρ‖ ^ 2) (s : ℂ) :
    Summable fun ρ : ℂ => (m ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  have hRpos : 0 < 2 * ‖s‖ + 1 := by positivity
  have hev : ∀ᶠ ρ in cofinite, (m ρ : ℝ) / ‖ρ‖ ^ 2 < 1 / (2 * ‖s‖ + 1) ^ 2 :=
    hS.tendsto_cofinite_zero.eventually (gt_mem_nhds (by positivity))
  refine Summable.of_norm_bounded_eventually (hS.mul_left (2 * ‖s‖)) ?_
  filter_upwards [hev, Filter.eventually_cofinite_ne (0 : ℂ)] with ρ hρ hρ0
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  by_cases hm : m ρ = 0
  · simp [hm]
  · have hm1 : (1 : ℝ) ≤ m ρ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hρR : 2 * ‖s‖ + 1 ≤ ‖ρ‖ := by
      by_contra h
      have h' : ‖ρ‖ < 2 * ‖s‖ + 1 := not_le.mp h
      have : 1 / (2 * ‖s‖ + 1) ^ 2 ≤ (m ρ : ℝ) / ‖ρ‖ ^ 2 :=
        div_le_div₀ (by positivity) hm1 (pow_pos hρpos 2) (pow_le_pow_left₀ hρpos.le h'.le 2)
      linarith
    have hsρ : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
      have := norm_sub_norm_le ρ s
      rw [norm_sub_rev] at this
      linarith [norm_nonneg s]
    have hsρpos : 0 < ‖s - ρ‖ := by linarith
    have hsρ0 : s - ρ ≠ 0 := norm_pos_iff.mp hsρpos
    have e : (1 / (s - ρ) + 1 / ρ) = s / ((s - ρ) * ρ) := by (field_simp; ring)
    rw [norm_mul, e, norm_div, norm_mul, Complex.norm_natCast]
    have : ‖s‖ / (‖s - ρ‖ * ‖ρ‖) ≤ 2 * ‖s‖ / ‖ρ‖ ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos hsρpos hρpos) (pow_pos hρpos 2)]
      nlinarith [norm_nonneg s,
        mul_le_mul_of_nonneg_left hsρ (mul_nonneg (norm_nonneg s) hρpos.le)]
    calc (m ρ : ℝ) * (‖s‖ / (‖s - ρ‖ * ‖ρ‖)) ≤ (m ρ : ℝ) * (2 * ‖s‖ / ‖ρ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = 2 * ‖s‖ * ((m ρ : ℝ) / ‖ρ‖ ^ 2) := by ring

/-! ### The Borel–Carathéodory step -/

/-- Key estimate: the logarithmic derivative of `f` differs from the partial fraction sum
over the zeros in `|ρ| ≤ r` (normalised at `0`) by `O(|s| / √r)`. -/
lemma logDeriv_approx (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {C : ℝ} (hC : 0 < C)
    (hb : ∀ s : ℂ, ‖f s‖ ≤ Real.exp (C * (1 + ‖s‖) ^ ((3 : ℝ) / 2))) {r : ℝ} (hr : 1 ≤ r)
    {s : ℂ} (hs : ‖s‖ < r / 4) (hfs : f s ≠ 0) :
    ∃ Z : Finset ℂ, (∀ ρ, ρ ∈ Z ↔ ‖ρ‖ ≤ r ∧ f ρ = 0) ∧
      ‖deriv f s / f s - deriv f 0 / f 0
          - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖
        ≤ 64 * (6 * C + |Real.log ‖f 0‖|) * ‖s‖ / √r := by
  classical
  have hr0 : 0 < r := by linarith
  obtain ⟨Z, hZ, -⟩ := exists_zero_finset hf h0 hr0
  refine ⟨Z, hZ, ?_⟩
  obtain ⟨e, g, hg, hgZ, hfg⟩ := exists_factor_finset hf h0 Z
  have hZ0 : ∀ ρ ∈ Z, ρ ≠ 0 := fun ρ hρ h => h0 (h ▸ ((hZ ρ).mp hρ).2)
  have he : ∀ ρ ∈ Z, e ρ = analyticOrderNatAt f ρ := by
    intro ρ hρ
    have := order_eq_of_factor hf hg hfg hρ (hZ0 ρ hρ) (hgZ ρ hρ)
    simp [analyticOrderNatAt, this]
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, ∀ z, P z = ∏ ρ ∈ Z, (1 - z / ρ) ^ e ρ := ⟨_, fun _ => rfl⟩
  have hPeq : P = fun z => ∏ ρ ∈ Z, (1 - z / ρ) ^ e ρ := funext hP
  have hPd : Differentiable ℂ P := by
    rw [hPeq]; exact Differentiable.fun_finsetProd fun ρ _ => by fun_prop
  have hfg' : ∀ z, f z = P z * g z := fun z => by rw [hP z]; exact hfg z
  have hP0 : P 0 = 1 := by rw [hP 0]; simp
  have hg0 : g 0 = f 0 := by rw [hfg' 0, hP0, one_mul]
  have hgne : ∀ z : ℂ, ‖z‖ ≤ r → g z ≠ 0 := by
    intro z hz hgz
    have : f z = 0 := by rw [hfg' z, hgz, mul_zero]
    exact hgZ z ((hZ z).mpr ⟨hz, this⟩) hgz
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (C * (1 + 2 * r) ^ ((3 : ℝ) / 2)) := ⟨_, rfl⟩
  have hgbd_sphere : ∀ z : ℂ, ‖z‖ = 2 * r → ‖g z‖ ≤ E := by
    intro z hz
    have hfac : ∀ ρ ∈ Z, 1 ≤ ‖(1 - z / ρ) ^ e ρ‖ := by
      intro ρ hρ
      rw [norm_pow]
      apply one_le_pow₀
      have hρr : ‖ρ‖ ≤ r := ((hZ ρ).mp hρ).1
      have hρ0 : 0 < ‖ρ‖ := norm_pos_iff.mpr (hZ0 ρ hρ)
      have h1 : 2 ≤ ‖z / ρ‖ := by
        rw [norm_div, hz, le_div_iff₀ hρ0]; linarith
      have h2 := norm_sub_norm_le (z / ρ) 1
      rw [norm_one, norm_sub_rev] at h2
      linarith
    have hP1 : 1 ≤ ‖P z‖ := by
      calc (1 : ℝ) = ∏ ρ ∈ Z, (1 : ℝ) := by simp
        _ ≤ ∏ ρ ∈ Z, ‖(1 - z / ρ) ^ e ρ‖ := Finset.prod_le_prod (fun _ _ => zero_le_one) hfac
        _ = ‖P z‖ := by rw [hP z, norm_prod]
    have hPz : P z ≠ 0 := fun h => by rw [h, norm_zero] at hP1; linarith
    have hgz : ‖g z‖ = ‖f z‖ / ‖P z‖ := by
      rw [hfg' z, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hPz)]
    rw [hgz]
    calc ‖f z‖ / ‖P z‖ ≤ ‖f z‖ / 1 := by gcongr
      _ = ‖f z‖ := div_one _
      _ ≤ E := by have := hb z; rwa [hz, ← hE] at this
  have h2r : (2 * r) ≠ 0 := (mul_pos two_pos hr0).ne'
  have hgbd : ∀ z : ℂ, ‖z‖ ≤ 2 * r → ‖g z‖ ≤ E := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) (2 * r))
      isBounded_ball hg.diffContOnCl (fun w hw => ?_) ?_
    · rw [frontier_ball (0 : ℂ) h2r] at hw
      exact hgbd_sphere w (by simpa using hw)
    · rw [closure_ball (0 : ℂ) h2r]
      simpa using hz
  -- the logarithmic derivative of `g`
  obtain ⟨L, hL⟩ : ∃ L : ℂ → ℂ, ∀ z, L z = deriv g z / g z := ⟨_, fun _ => rfl⟩
  have hLd : DifferentiableOn ℂ L (ball 0 r) := by
    have : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball 0 r) := by
      refine DifferentiableOn.div (fun z _ => ?_) hg.differentiableOn fun z hz => hgne z ?_
      · exact (hg.analyticAt z).deriv.differentiableAt.differentiableWithinAt
      · exact (mem_ball_zero_iff.mp hz).le
    exact this.congr fun z _ => hL z
  -- a logarithm `h` of `g / g 0` on the disc
  obtain ⟨h, hh0, hh⟩ := (hLd.isExactOn_ball).with_val_at 0 0
  have hhd : DifferentiableOn ℂ h (ball 0 r) := fun z hz =>
    (hh z hz).differentiableAt.differentiableWithinAt
  have hexp : ∀ z ∈ ball (0 : ℂ) r, g z = g 0 * Complex.exp (h z) := by
    have hφd : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt (fun z => g z * Complex.exp (-h z)) 0 z := by
      intro z hz
      have h1 : HasDerivAt (fun z => g z * Complex.exp (-h z))
          (deriv g z * Complex.exp (-h z) + g z * (Complex.exp (-h z) * -L z)) z :=
        (hg z).hasDerivAt.mul ((hh z hz).neg.cexp)
      have e0 : deriv g z * Complex.exp (-h z) + g z * (Complex.exp (-h z) * -L z) = 0 := by
        have := hgne z (mem_ball_zero_iff.mp hz).le
        rw [hL z]
        field_simp
        ring
      rwa [e0] at h1
    have hconst : ∀ z ∈ ball (0 : ℂ) r,
        g z * Complex.exp (-h z) = g 0 * Complex.exp (-h 0) := by
      intro z hz
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball 0 r).isPreconnected
        (fun w hw => (hφd w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => (hφd w hw).deriv) hz (mem_ball_self hr0)
    intro z hz
    have := hconst z hz
    rw [hh0, neg_zero, Complex.exp_zero, mul_one] at this
    rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  -- the bound on the real part
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (6 * C + |Real.log ‖f 0‖|) * (r * √r) := ⟨_, rfl⟩
  have hsr : 1 ≤ √r := Real.one_le_sqrt.mpr hr
  have hrsr : 1 ≤ r * √r := by nlinarith
  have hMpos : 0 < M := by
    rw [hM]
    exact mul_pos (add_pos_of_pos_of_nonneg (by linarith) (abs_nonneg _)) (by linarith)
  have hf0 : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hre : ∀ z ∈ ball (0 : ℂ) r, (h z).re ≤ M := by
    intro z hz
    have hz' : ‖z‖ ≤ r := (mem_ball_zero_iff.mp hz).le
    have h1 : ‖g z‖ = ‖f 0‖ * Real.exp (h z).re := by
      rw [hexp z hz, norm_mul, Complex.norm_exp, hg0]
    have h2 : ‖g z‖ ≤ E := hgbd z (by linarith)
    have h3 : Real.exp (h z).re ≤ E / ‖f 0‖ := by
      rw [le_div_iff₀ hf0]; rw [h1] at h2; linarith
    have h4 : (h z).re ≤ Real.log (E / ‖f 0‖) :=
      calc (h z).re = Real.log (Real.exp (h z).re) := (Real.log_exp _).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos _) h3
    rw [hE, Real.log_div (Real.exp_ne_zero _) hf0.ne', Real.log_exp] at h4
    have h5 := growth_bound hC hr
    have h6 : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := neg_le_abs _
    have h7 := mul_le_mul_of_nonneg_left hrsr (abs_nonneg (Real.log ‖f 0‖))
    rw [hM]; nlinarith
  -- Borel–Carathéodory
  have hbc : ∀ z : ℂ, ‖z‖ ≤ r / 2 → ‖h z‖ ≤ 2 * M := by
    intro z hz
    have hzb : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr (by linarith)
    have := Complex.borelCaratheodory_zero hMpos hhd (fun w hw => hre w hw) hr0 hzb hh0
    refine this.trans ?_
    rw [div_le_iff₀ (by linarith)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  -- Cauchy estimate
  have hLbd : ∀ z : ℂ, ‖z‖ ≤ r / 4 → ‖L z‖ ≤ 8 * M / r := by
    intro z hz
    have hzb : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr (by linarith)
    have hsub : closedBall z (r / 4) ⊆ ball (0 : ℂ) r := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_ball_zero_iff]
      have := norm_add_le (w - z) z
      rw [sub_add_cancel] at this
      linarith
    have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := h) (c := z)
      (R := r / 4) (C := 2 * M) (by linarith) (hhd.diffContOnCl_ball hsub) (fun w hw => hbc w (by
        rw [mem_sphere, dist_eq_norm] at hw
        have := norm_add_le (w - z) z
        rw [sub_add_cancel] at this
        linarith))
    rw [(hh z hzb).deriv] at key
    refine key.trans (le_of_eq ?_)
    field_simp
    ring
  -- Schwarz lemma
  have hschwarz : ‖L s - L 0‖ ≤ 16 * M / r / (r / 4) * ‖s‖ := by
    have hmaps : MapsTo L (ball (0 : ℂ) (r / 4)) (closedBall (L 0) (16 * M / r)) := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm]
      have h1 := hLbd z (mem_ball_zero_iff.mp hz).le
      have h2 := hLbd 0 (by rw [norm_zero]; linarith)
      have h3 := norm_sub_le (L z) (L 0)
      have : 16 * M / r = 8 * M / r + 8 * M / r := by ring
      linarith
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball (f := L) (c := 0) (R₁ := r / 4)
      (R₂ := 16 * M / r) (z := s) (hLd.mono (ball_subset_ball (by linarith))) hmaps
      (mem_ball_zero_iff.mpr hs)
    rwa [dist_eq_norm, dist_zero_right] at this
  -- logarithmic derivative of the factorisation
  have hld : ∀ z, f z ≠ 0 → deriv f z / f z = ∑ ρ ∈ Z, (e ρ : ℂ) / (z - ρ) + L z := by
    intro z hfz
    have hPz : P z ≠ 0 := fun h => hfz (by rw [hfg' z, h, zero_mul])
    have hgz : g z ≠ 0 := fun h => hfz (by rw [hfg' z, h, mul_zero])
    have hfeq : f = fun z => P z * g z := funext hfg'
    have h1 : logDeriv f z = logDeriv P z + logDeriv g z := by
      rw [hfeq]; exact logDeriv_mul z hPz hgz (hPd z) (hg z)
    have hfac : ∀ ρ ∈ Z, (1 - z / ρ) ^ e ρ ≠ 0 := by
      intro ρ hρ h
      apply hPz; rw [hP z]; exact Finset.prod_eq_zero hρ h
    have h2 : logDeriv P z = ∑ ρ ∈ Z, (e ρ : ℂ) / (z - ρ) := by
      have hlp := logDeriv_prod (s := Z) (f := fun ρ z => (1 - z / ρ) ^ e ρ) (x := z) hfac
        (fun ρ _ => by fun_prop)
      rw [hPeq]
      refine hlp.trans (Finset.sum_congr rfl fun ρ hρ => ?_)
      have hρ0 := hZ0 ρ hρ
      have hzρ : z ≠ ρ := fun h => hfz (h ▸ ((hZ ρ).mp hρ).2)
      have hbase : (1 - z / ρ) ≠ 0 := by
        rw [sub_ne_zero]; intro h; rw [eq_div_iff hρ0, one_mul] at h; exact hzρ h.symm
      show logDeriv (fun z : ℂ => (1 - z / ρ) ^ e ρ) z = _
      rw [logDeriv_fun_pow (f := fun z : ℂ => 1 - z / ρ) (by fun_prop) (e ρ), logDeriv_apply]
      have hd : deriv (fun z : ℂ => 1 - z / ρ) z = -(1 / ρ) := by
        have : HasDerivAt (fun z : ℂ => 1 - z / ρ) (-(1 / ρ)) z := by
          simpa using ((hasDerivAt_id z).div_const ρ).const_sub 1
        exact this.deriv
      rw [hd]
      have : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
      field_simp
      ring
    rw [← logDeriv_apply, h1, h2, logDeriv_apply, hL z]
  have e1 := hld s hfs
  have e2 := hld 0 h0
  have hsum : deriv f s / f s - deriv f 0 / f 0
      - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) = L s - L 0 := by
    rw [e1, e2]
    have : ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
        = ∑ ρ ∈ Z, (e ρ : ℂ) / (s - ρ) - ∑ ρ ∈ Z, (e ρ : ℂ) / (0 - ρ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      rw [← he ρ hρ, zero_sub, div_neg]; ring
    rw [this]; ring
  rw [hsum]
  refine hschwarz.trans (le_of_eq ?_)
  obtain ⟨t, ht, hrt, htr⟩ : ∃ t : ℝ, 0 < t ∧ r = t * t ∧ √r = t :=
    ⟨√r, by linarith, (Real.mul_self_sqrt hr0.le).symm, rfl⟩
  rw [hM, htr, hrt]
  exact final_alg _ _ t ht

/-- **Genus-1 Hadamard partial fraction** for an entire function of order `< 2` with
`f 0 ≠ 0`:  `f'/f(s) = f'/f(0) + ∑_ρ m_ρ (1/(s-ρ) + 1/ρ)`. -/
theorem logDeriv_eq_tsum (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hG : GrowthLtTwo f)
    {s : ℂ} (hfs : f s ≠ 0) :
    deriv f s / f s = deriv f 0 / f 0
      + ∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  classical
  have hS := summable_order_div_normSq hf h0 hG
  have hb := summable_partialFraction hS s
  obtain ⟨C, hC, hbd⟩ := hG
  suffices h : ∀ ε > 0, ‖deriv f s / f s - deriv f 0 / f 0
      - ∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ ≤ ε by
    have h0' : ‖deriv f s / f s - deriv f 0 / f 0
        - ∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ = 0 :=
      le_antisymm (le_of_forall_pos_le_add (by intro ε hε; simpa using h ε hε)) (norm_nonneg _)
    have := norm_eq_zero.mp h0'
    linear_combination this
  intro ε hε
  have ht : Tendsto (fun F : Finset ℂ =>
      ∑ ρ ∈ F, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) atTop
      (𝓝 (∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))) := hb.hasSum
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.mp
    (ht.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 64 * (6 * C + |Real.log ‖f 0‖|) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = max (max 1 (4 * ‖s‖ + 1))
      (max (∑ ρ ∈ F₀, ‖ρ‖) ((2 * K * ‖s‖ / ε) ^ 2)) := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by rw [hr]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hr2 : ‖s‖ < r / 4 := by
    have : 4 * ‖s‖ + 1 ≤ r := by rw [hr]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hr3 : ∀ ρ ∈ F₀, ‖ρ‖ ≤ r := fun ρ hρ => by
    rw [hr]
    exact (Finset.single_le_sum (f := fun ρ : ℂ => ‖ρ‖) (fun _ _ => norm_nonneg _) hρ).trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hr4 : (2 * K * ‖s‖ / ε) ^ 2 ≤ r := by
    rw [hr]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨Z, hZ, hZb⟩ := logDeriv_approx hf h0 hC hbd hr1 hr2 hfs
  have hsumeq : ∑ ρ ∈ Z ∪ F₀, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
    symm
    refine Finset.sum_subset Finset.subset_union_left fun ρ hρ hρZ => ?_
    have hρF : ρ ∈ F₀ := by
      rcases Finset.mem_union.mp hρ with h | h
      · exact absurd h hρZ
      · exact h
    have hfρ : f ρ ≠ 0 := fun h => hρZ ((hZ ρ).mpr ⟨hr3 ρ hρF, h⟩)
    rw [(orderNat_eq_zero_iff hf h0 ρ).mpr hfρ]; simp
  have h1 := hF₀ (Z ∪ F₀) Finset.subset_union_right
  rw [dist_eq_norm, hsumeq] at h1
  have h2 : 64 * (6 * C + |Real.log ‖f 0‖|) * ‖s‖ / √r ≤ ε / 2 := by
    have hsr : 0 < √r := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_iff₀ hsr, ← hK]
    have h3 := Real.sqrt_le_sqrt hr4
    rw [Real.sqrt_sq (div_nonneg (mul_nonneg (mul_nonneg zero_le_two hK0) (norm_nonneg _))
      hε.le)] at h3
    rw [div_le_iff₀ hε] at h3
    linarith
  calc ‖deriv f s / f s - deriv f 0 / f 0
        - ∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖
      = ‖(deriv f s / f s - deriv f 0 / f 0
          - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
        + (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
          - ∑' ρ : ℂ, (analyticOrderNatAt f ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))‖ := by
        congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hZb.trans h2) h1.le
    _ = ε := by ring

end general

end DetPrimality.Bach.Hadamard
