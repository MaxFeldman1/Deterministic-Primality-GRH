import DetPrimality.Bach.HadamardGeneral

/-!
# Hadamard partial fractions for the completed Dirichlet L-function

Specialisation of `HadamardGeneral` to `completedLFunction χ` (`χ` primitive, `χ ≠ 1`):

* `zeroOrd_eq_order` : `zeroOrd χ ρ` is the order of vanishing of `completedLFunction χ` at `ρ`;
* `hadamardLogDeriv_of_growth` : `GrowthLtTwo (completedLFunction χ) → HadamardLogDeriv χ`;
* `summable_zeroOrd_div_normSq_proof` : `∑ zeroOrd χ ρ / |ρ|² < ∞` (given the growth bound);
* `re_logDeriv_eq_tsum_proof` : the statement of `Blueprint.re_logDeriv_eq_tsum`, from
  `HadamardLogDeriv χ`, the summability and the functional equation.
-/

open Complex DirichletCharacter Filter Topology
open scoped ComplexConjugate

namespace DetPrimality.Bach

/-! ### Reflection `z ↦ conj (F (1 - conj z))` -/

namespace Hadamard

lemma differentiable_reflect {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (fun z => conj (F (1 - conj z))) := by
  intro z
  have h1 : DifferentiableAt ℂ (fun w => F (1 - w)) (conj z) :=
    (hF _).comp _ ((differentiableAt_const _).sub differentiableAt_id)
  have h2 := h1.conj_conj
  rw [Complex.conj_conj] at h2
  exact h2

lemma order_reflect {F : ℂ → ℂ} (hF : Differentiable ℂ F) (ρ : ℂ) :
    analyticOrderAt (fun z => conj (F (1 - conj z))) (1 - conj ρ) = analyticOrderAt F ρ := by
  have hR := differentiable_reflect hF
  by_cases htop : analyticOrderAt F ρ = ⊤
  · have hF0 : F = 0 :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ (fun z => hF.analyticAt z)).mp htop
    rw [htop, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero _ (fun z => hR.analyticAt z)]
    funext z; simp [hF0]
  · obtain ⟨G, hG, hGρ, hFG⟩ := exists_factor_sub hF ρ htop
    rw [← Nat.cast_analyticOrderNatAt htop, (hR.analyticAt _).analyticOrderAt_eq_natCast]
    refine ⟨fun z => (-1) ^ analyticOrderNatAt F ρ * conj (G (1 - conj z)), ?_, ?_,
      Filter.Eventually.of_forall fun z => ?_⟩
    · exact ((differentiable_reflect hG).const_mul _).analyticAt _
    · simp [hGρ]
    · simp only [smul_eq_mul]
      rw [hFG, map_mul, map_pow, ← mul_assoc, ← mul_pow]
      congr 2
      simp only [map_sub, map_one, Complex.conj_conj]
      ring

end Hadamard

section

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-! ### Basic facts on `gammaFactor` and `completedLFunction` -/

lemma modulus_ne_one {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) : q ≠ 1 :=
  fun h => hχ1 (level_one' χ h)

lemma chi_inv_ne_one {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) : χ⁻¹ ≠ 1 :=
  _root_.inv_ne_one.mpr hχ1

lemma gammaFactor_ne_zero (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

lemma differentiable_gammaFactor_inv (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ fun s => (gammaFactor χ s)⁻¹ := by
  rcases χ.even_or_odd with h | h
  · simp_rw [h.gammaFactor_def]; exact differentiable_Gammaℝ_inv
  · simp_rw [h.gammaFactor_def]
    exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

lemma LFunction_eq_mul (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) (s : ℂ) :
    LFunction χ s = completedLFunction χ s * (gammaFactor χ s)⁻¹ := by
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inr (modulus_ne_one hχ1)), div_eq_mul_inv]

lemma completed_eq_mul (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ s = gammaFactor χ s * LFunction χ s := by
  have := gammaFactor_ne_zero χ hs
  rw [LFunction_eq_mul χ hχ1 s]
  field_simp

lemma completed_ne_zero_of_one_le_re (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) : completedLFunction χ s ≠ 0 := by
  rw [completed_eq_mul χ hχ1 (by linarith)]
  exact mul_ne_zero (gammaFactor_ne_zero χ (by linarith))
    (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hs)

lemma rootNumber_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    rootNumber χ ≠ 0 := by
  intro h
  have h2 := hχ.completedLFunction_one_sub (-1)
  rw [h, mul_zero, zero_mul] at h2
  exact completed_ne_zero_of_one_le_re χ hχ1 (s := 1 - (-1))
    (by rw [sub_re, neg_re, one_re]; norm_num) h2

lemma natCast_cpow_ne_zero' (w : ℂ) : (q : ℂ) ^ w ≠ 0 := by
  rw [cpow_ne_zero_iff]; left; exact Nat.cast_ne_zero.mpr (NeZero.ne q)

lemma completed_ne_zero_of_re_nonpos {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {s : ℂ} (hs : s.re ≤ 0) : completedLFunction χ s ≠ 0 := by
  have h := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at h
  rw [h]
  exact mul_ne_zero (mul_ne_zero (natCast_cpow_ne_zero' _) (rootNumber_ne_zero hχ hχ1))
    (completed_ne_zero_of_one_le_re χ⁻¹ (chi_inv_ne_one hχ1) (by rw [sub_re, one_re]; linarith))

lemma completed_ne_zero_of_not_strip {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {ρ : ℂ} (h : ¬ (0 < ρ.re ∧ ρ.re < 1)) : completedLFunction χ ρ ≠ 0 := by
  by_cases h1 : ρ.re ≤ 0
  · exact completed_ne_zero_of_re_nonpos hχ hχ1 h1
  · refine completed_ne_zero_of_one_le_re χ hχ1 ?_
    by_contra h2
    exact h ⟨not_le.mp h1, not_le.mp h2⟩

lemma completed_zero_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    completedLFunction χ 0 ≠ 0 :=
  completed_ne_zero_of_re_nonpos hχ hχ1 (by simp)

/-- For primitive `χ ≠ 1`, the multiplicity `zeroOrd χ ρ` of `ρ` as a nontrivial zero of
`L(s, χ)` is the order of vanishing of the completed L-function at `ρ` (for *every* `ρ`). -/
theorem zeroOrd_eq_order {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (ρ : ℂ) : zeroOrd χ ρ = analyticOrderNatAt (completedLFunction χ) ρ := by
  have hΛ := differentiable_completedLFunction hχ1
  have h0 := completed_zero_ne_zero hχ hχ1
  unfold zeroOrd
  split_ifs with h
  · have hL : LFunction χ = completedLFunction χ * fun s => (gammaFactor χ s)⁻¹ :=
      funext fun s => LFunction_eq_mul χ hχ1 s
    have h1 : analyticOrderAt (fun s => (gammaFactor χ s)⁻¹) ρ = 0 := by
      rw [((differentiable_gammaFactor_inv χ).analyticAt ρ).analyticOrderAt_eq_zero]
      exact inv_ne_zero (gammaFactor_ne_zero χ h.1)
    simp only [analyticOrderNatAt]
    rw [hL, analyticOrderAt_mul (hΛ.analyticAt ρ)
      ((differentiable_gammaFactor_inv χ).analyticAt ρ), h1, add_zero]
  · exact ((Hadamard.orderNat_eq_zero_iff hΛ h0 ρ).mpr
      (completed_ne_zero_of_not_strip hχ hχ1 h)).symm

end

/-! ### Main results -/

/-- **Hadamard partial fraction for `completedLFunction χ`**, given the growth bound. -/
theorem hadamardLogDeriv_of_growth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hG : GrowthLtTwo (completedLFunction χ)) :
    HadamardLogDeriv χ := by
  have hΛ := differentiable_completedLFunction hχ1
  have h0 := completed_zero_ne_zero hχ hχ1
  refine ⟨deriv (completedLFunction χ) 0 / completedLFunction χ 0, fun s hs => ?_⟩
  rw [Hadamard.logDeriv_eq_tsum hΛ h0 hG hs]
  congr 1
  exact tsum_congr fun ρ => by rw [zeroOrd_eq_order hχ hχ1 ρ]

/-- `∑_ρ 1/|ρ|² < ∞` over the nontrivial zeros, given the growth bound. -/
theorem summable_zeroOrd_div_normSq_proof {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hG : GrowthLtTwo (completedLFunction χ)) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2 := by
  have := Hadamard.summable_order_div_normSq (differentiable_completedLFunction hχ1)
    (completed_zero_ne_zero hχ hχ1) hG
  simpa only [zeroOrd_eq_order hχ hχ1] using this

/-! ### Complex conjugation symmetry -/

section

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

lemma Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul]
  have h1 : conj s / 2 = conj (s / 2) := by rw [map_div₀, map_ofNat]
  have h2 : -conj s / 2 = conj (-s / 2) := by rw [map_div₀, map_neg, map_ofNat]
  rw [h1, h2, Gamma_conj,
    cpow_conj _ _ (by rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne),
    conj_ofReal]

lemma inv_even_iff (χ : DirichletCharacter ℂ q) : χ⁻¹.Even ↔ χ.Even := by
  unfold DirichletCharacter.Even
  rw [MulChar.inv_apply_eq_inv', inv_eq_one]

lemma gammaFactor_inv_conj (χ : DirichletCharacter ℂ q) (s : ℂ) :
    gammaFactor χ⁻¹ (conj s) = conj (gammaFactor χ s) := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, ((inv_even_iff χ).mpr h).gammaFactor_def, Gammaℝ_conj]
  · have h' : χ⁻¹.Odd := by
      rcases χ⁻¹.even_or_odd with h2 | h2
      · exact absurd ((inv_even_iff χ).mp h2) h.not_even
      · exact h2
    rw [h.gammaFactor_def, h'.gammaFactor_def, ← Gammaℝ_conj, map_add, map_one]

lemma LFunction_inv_conj_of_one_lt_re (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ⁻¹ (conj s) = conj (LFunction χ s) := by
  rw [LFunction_eq_LSeries χ hs, LFunction_eq_LSeries χ⁻¹ (by simpa using hs), LSeries, LSeries,
    conj_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      cpow_conj _ _ (by rw [natCast_arg]; exact Real.pi_pos.ne), conj_natCast,
      ← MulChar.star_apply']
    rfl

/-- `Λ(conj s, χ⁻¹) = conj Λ(s, χ)`. -/
theorem completed_inv_conj {χ : DirichletCharacter ℂ q} (hχ1 : χ ≠ 1) (s : ℂ) :
    completedLFunction χ⁻¹ (conj s) = conj (completedLFunction χ s) := by
  have hΛ := differentiable_completedLFunction hχ1
  have hΛi := differentiable_completedLFunction (chi_inv_ne_one hχ1)
  have hF : Differentiable ℂ (fun z => conj (completedLFunction χ⁻¹ (conj z))) := by
    intro z
    have h2 := (hΛi (conj z)).conj_conj
    rw [Complex.conj_conj] at h2
    exact h2
  have heq : (fun z => conj (completedLFunction χ⁻¹ (conj z))) = completedLFunction χ := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (z₀ := (2 : ℂ)) (fun z _ => hF.analyticAt z)
      (fun z _ => hΛ.analyticAt z)
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz1 : (1 : ℝ) < z.re := hz
    have hz' : 1 < (conj z).re := by rw [conj_re]; exact hz1
    show conj (completedLFunction χ⁻¹ (conj z)) = completedLFunction χ z
    rw [completed_eq_mul χ⁻¹ (chi_inv_ne_one hχ1) (by linarith), gammaFactor_inv_conj,
      completed_eq_mul χ hχ1 (by linarith : 0 < z.re), map_mul, Complex.conj_conj]
    congr 1
    have := LFunction_inv_conj_of_one_lt_re χ⁻¹ hz'
    rw [inv_inv, Complex.conj_conj] at this
    exact this.symm
  have h : conj (completedLFunction χ⁻¹ (conj s)) = completedLFunction χ s := congrFun heq s
  rw [← h, Complex.conj_conj]

/-- The functional equation in the form `Λ(z) = c(z) · conj Λ(1 - conj z)`. -/
lemma completed_eq_reflect {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (z : ℂ) : completedLFunction χ z
      = (q : ℂ) ^ (1 - z - 1 / 2) * rootNumber χ * conj (completedLFunction χ (1 - conj z)) := by
  have h := hχ.completedLFunction_one_sub (1 - z)
  rw [sub_sub_cancel] at h
  have h2 := completed_inv_conj hχ1 (1 - conj z)
  rw [map_sub, map_one, Complex.conj_conj] at h2
  rw [h, h2]

lemma differentiable_reflFactor (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (fun z : ℂ => (q : ℂ) ^ (1 - z - 1 / 2) * rootNumber χ) := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  refine Differentiable.mul_const (fun z => ?_) _
  exact (((differentiableAt_const _).sub differentiableAt_id).sub_const _).const_cpow (Or.inl hq)

/-- Zeros of `Λ(·, χ)` are symmetric under `ρ ↦ 1 - conj ρ`, with multiplicity. -/
theorem order_completed_reflect {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (ρ : ℂ) :
    analyticOrderNatAt (completedLFunction χ) (1 - conj ρ)
      = analyticOrderNatAt (completedLFunction χ) ρ := by
  have hΛ := differentiable_completedLFunction hχ1
  have hc := differentiable_reflFactor χ
  have hfe : completedLFunction χ = (fun z : ℂ => (q : ℂ) ^ (1 - z - 1 / 2) * rootNumber χ) *
      (fun z : ℂ => conj (completedLFunction χ (1 - conj z))) :=
    funext fun z => completed_eq_reflect hχ hχ1 z
  have hc0 : analyticOrderAt (fun z : ℂ => (q : ℂ) ^ (1 - z - 1 / 2) * rootNumber χ)
      (1 - conj ρ) = 0 := by
    rw [(hc.analyticAt _).analyticOrderAt_eq_zero]
    exact mul_ne_zero (natCast_cpow_ne_zero' _) (rootNumber_ne_zero hχ hχ1)
  have key : analyticOrderAt (completedLFunction χ) (1 - conj ρ)
      = analyticOrderAt (completedLFunction χ) ρ := by
    conv_lhs => rw [hfe]
    rw [analyticOrderAt_mul (hc.analyticAt _) ((Hadamard.differentiable_reflect hΛ).analyticAt _),
      hc0, zero_add, Hadamard.order_reflect hΛ]
  simp only [analyticOrderNatAt, key]

lemma zeroOrd_reflect {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (ρ : ℂ) :
    zeroOrd χ (1 - conj ρ) = zeroOrd χ ρ := by
  rw [zeroOrd_eq_order hχ hχ1, zeroOrd_eq_order hχ hχ1, order_completed_reflect hχ hχ1]

/-- Logarithmic derivative of the functional equation:
`Λ'/Λ(z) = -log q - conj (Λ'/Λ(1 - conj z))`. -/
theorem logDeriv_completed_reflect {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {z : ℂ} (hz : completedLFunction χ z ≠ 0) :
    deriv (completedLFunction χ) z / completedLFunction χ z
      = -(Real.log q : ℂ) - conj (deriv (completedLFunction χ) (1 - conj z)
          / completedLFunction χ (1 - conj z)) := by
  have hΛ := differentiable_completedLFunction hχ1
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hfe : completedLFunction χ = fun z => (q : ℂ) ^ (1 - z - 1 / 2) * rootNumber χ *
      conj (completedLFunction χ (1 - conj z)) :=
    funext fun z => completed_eq_reflect hχ hχ1 z
  have hcz : (q : ℂ) ^ (1 - z - 1 / 2) * rootNumber χ ≠ 0 :=
    mul_ne_zero (natCast_cpow_ne_zero' _) (rootNumber_ne_zero hχ hχ1)
  have hRz : conj (completedLFunction χ (1 - conj z)) ≠ 0 := by
    intro h; apply hz; rw [completed_eq_reflect hχ hχ1 z, h, mul_zero]
  have h1 : logDeriv (completedLFunction χ) z
      = logDeriv (fun z : ℂ => (q : ℂ) ^ (1 - z - 1 / 2) * rootNumber χ) z
        + logDeriv (fun z => conj (completedLFunction χ (1 - conj z))) z := by
    conv_lhs => rw [hfe]
    exact logDeriv_mul z hcz hRz (differentiable_reflFactor χ z)
      (Hadamard.differentiable_reflect hΛ z)
  have h2 : logDeriv (fun z : ℂ => (q : ℂ) ^ (1 - z - 1 / 2) * rootNumber χ) z
      = -(Real.log q : ℂ) := by
    have hd : HasDerivAt (fun z : ℂ => 1 - z - 1 / 2) (-1) z := by
      simpa using ((hasDerivAt_id z).const_sub 1).sub_const (1 / 2)
    have hcd := (hd.const_cpow (Or.inl hq)).mul_const (rootNumber χ)
    simp only [logDeriv_apply]
    rw [hcd.deriv, natCast_log]
    have := natCast_cpow_ne_zero' (q := q) (1 - z - 1 / 2)
    have hW := rootNumber_ne_zero hχ hχ1
    rw [show (q : ℂ) ^ (1 - z - 1 / 2) * Complex.log q * -1 * rootNumber χ
        = (-Complex.log q) * ((q : ℂ) ^ (1 - z - 1 / 2) * rootNumber χ) by ring,
      mul_div_cancel_right₀ _ (mul_ne_zero this hW)]
  have h3 : logDeriv (fun z => conj (completedLFunction χ (1 - conj z))) z
      = -conj (deriv (completedLFunction χ) (1 - conj z) / completedLFunction χ (1 - conj z)) := by
    have hRd : deriv (fun z => conj (completedLFunction χ (1 - conj z))) z
        = conj (-(deriv (completedLFunction χ) (1 - conj z))) := by
      have := congrFun (deriv_conj_conj (f := fun w => completedLFunction χ (1 - w))) z
      simp only [Function.comp_apply] at this
      rw [deriv_comp_const_sub] at this
      exact this
    rw [logDeriv_apply, hRd, map_neg, map_div₀, neg_div]
  rw [← logDeriv_apply, h1, h2, h3]
  ring

end

/-! ### The real part formula -/

lemma summable_re_inv {m : ℂ → ℕ} (hS : Summable fun ρ : ℂ => (m ρ : ℝ) / ‖ρ‖ ^ 2)
    (hm : ∀ ρ, m ρ ≠ 0 → |ρ.re| ≤ 1) : Summable fun ρ : ℂ => (m ρ : ℝ) * (1 / ρ).re := by
  refine Summable.of_norm_bounded hS fun ρ => ?_
  by_cases h : m ρ = 0
  · simp [h]
  · rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast, one_div, Complex.inv_re,
      Complex.normSq_eq_norm_sq, abs_div, abs_of_nonneg (sq_nonneg ‖ρ‖)]
    calc (m ρ : ℝ) * (|ρ.re| / ‖ρ‖ ^ 2) ≤ (m ρ : ℝ) * (1 / ‖ρ‖ ^ 2) := by
          gcongr; exact hm ρ h
      _ = (m ρ : ℝ) / ‖ρ‖ ^ 2 := by ring

lemma re_partialFraction {m : ℂ → ℕ} (hS : Summable fun ρ : ℂ => (m ρ : ℝ) / ‖ρ‖ ^ 2)
    (hd : Summable fun ρ : ℂ => (m ρ : ℝ) * (1 / ρ).re) (w : ℂ) :
    Summable (fun ρ : ℂ => (m ρ : ℝ) * (1 / (w - ρ)).re) ∧
    (∑' ρ : ℂ, (m ρ : ℂ) * (1 / (w - ρ) + 1 / ρ)).re
      = ∑' ρ : ℂ, (m ρ : ℝ) * (1 / (w - ρ)).re + ∑' ρ : ℂ, (m ρ : ℝ) * (1 / ρ).re := by
  have hb := Hadamard.summable_partialFraction hS w
  have hre : Summable fun ρ : ℂ => ((m ρ : ℂ) * (1 / (w - ρ) + 1 / ρ)).re :=
    Complex.reCLM.summable hb
  have hpt : ∀ ρ : ℂ, ((m ρ : ℂ) * (1 / (w - ρ) + 1 / ρ)).re
      = (m ρ : ℝ) * (1 / (w - ρ)).re + (m ρ : ℝ) * (1 / ρ).re := by
    intro ρ
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.add_re]; ring
  have ha : Summable fun ρ : ℂ => (m ρ : ℝ) * (1 / (w - ρ)).re := by
    refine (hre.sub hd).congr fun ρ => ?_
    rw [hpt]; ring
  refine ⟨ha, ?_⟩
  rw [Complex.re_tsum hb, tsum_congr hpt, ha.tsum_add hd]

/-- **§2.2** (`Blueprint.re_logDeriv_eq_tsum`), from the Hadamard partial fraction, the
summability of `∑ 1/|ρ|²` and the functional equation. -/
theorem re_logDeriv_eq_tsum_proof {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) (hH : HadamardLogDeriv χ)
    {s : ℂ} (hs : 1 < s.re) :
    (deriv (LFunction χ) s / LFunction χ s + deriv (gammaFactor χ) s / gammaFactor χ s).re
      = -(Real.log q) / 2 + ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (s - ρ)).re := by
  obtain ⟨B, hB⟩ := hH
  have hs0 : 0 < s.re := by linarith
  have hΛs : completedLFunction χ s ≠ 0 := completed_ne_zero_of_one_le_re χ hχ1 hs.le
  have hΛτ : completedLFunction χ (1 - conj s) ≠ 0 :=
    completed_ne_zero_of_re_nonpos hχ hχ1 (by rw [sub_re, one_re, conj_re]; linarith)
  -- Step 1: the left-hand side is `Re Λ'/Λ(s)`.
  have hstep1 : deriv (LFunction χ) s / LFunction χ s
      + deriv (gammaFactor χ) s / gammaFactor χ s
      = deriv (completedLFunction χ) s / completedLFunction χ s := by
    have hγ0 := gammaFactor_ne_zero χ hs0
    have hγd : DifferentiableAt ℂ (gammaFactor χ) s := by
      have h1 := ((differentiable_gammaFactor_inv χ) s).inv (inv_ne_zero hγ0)
      exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by simp)
    have hev : completedLFunction χ =ᶠ[𝓝 s] fun z => gammaFactor χ z * LFunction χ z := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (0 : ℝ) < s.re from hs0)] with z hz
      exact completed_eq_mul χ hχ1 hz
    have h1 : deriv (completedLFunction χ) s
        = deriv (fun z => gammaFactor χ z * LFunction χ z) s := hev.deriv_eq
    have h2 : completedLFunction χ s = gammaFactor χ s * LFunction χ s :=
      completed_eq_mul χ hχ1 hs0
    have h3 := logDeriv_mul s hγ0 (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hs.le) hγd
      (differentiable_LFunction hχ1 s)
    simp only [logDeriv_apply] at h3
    rw [h1, h2, h3, add_comm]
  -- Step 2: real parts of the two Hadamard expansions.
  have hm : ∀ ρ, zeroOrd χ ρ ≠ 0 → |ρ.re| ≤ 1 := by
    intro ρ h
    unfold zeroOrd at h
    split_ifs at h with h1
    · rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
    · exact absurd rfl h
  have hd := summable_re_inv hS hm
  obtain ⟨ha, hre_s⟩ := re_partialFraction hS hd s
  obtain ⟨ha', hre_τ⟩ := re_partialFraction hS hd (1 - conj s)
  have e1 := hB s hΛs
  have e2 := hB (1 - conj s) hΛτ
  have hrefl := congrArg Complex.re (logDeriv_completed_reflect hχ hχ1 hΛs)
  rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.conj_re] at hrefl
  -- Step 3: symmetry of the zeros.
  have hsym : ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (1 - conj s - ρ)).re
      = -∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (s - ρ)).re := by
    have hinv : Function.Involutive (fun z : ℂ => 1 - conj z) := fun z => by simp
    have h := (hinv.toPerm _).tsum_eq
      (fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * (1 / (1 - conj s - ρ)).re)
    rw [← h, ← tsum_neg]
    refine tsum_congr fun ρ => ?_
    show (zeroOrd χ (1 - conj ρ) : ℝ) * (1 / (1 - conj s - (1 - conj ρ))).re
      = -((zeroOrd χ ρ : ℝ) * (1 / (s - ρ)).re)
    rw [zeroOrd_reflect hχ hχ1 ρ]
    have h1 : (1 - conj s - (1 - conj ρ)) = conj (ρ - s) := by rw [map_sub]; ring
    have h2 : (1 / conj (ρ - s)).re = -(1 / (s - ρ)).re := by
      rw [one_div, ← map_inv₀, Complex.conj_re, ← neg_sub s ρ, inv_neg, Complex.neg_re, one_div]
    rw [h1, h2]; ring
  have hX : (deriv (completedLFunction χ) s / completedLFunction χ s).re
      = B.re + (∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (s - ρ)).re
        + ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ρ).re) := by
    rw [e1, Complex.add_re, hre_s]
  have hY : (deriv (completedLFunction χ) (1 - conj s) / completedLFunction χ (1 - conj s)).re
      = B.re + (-∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (s - ρ)).re
        + ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ρ).re) := by
    rw [e2, Complex.add_re, hre_τ, hsym]
  rw [hstep1]
  linarith

/-- `re_logDeriv_eq_tsum` from the growth bound alone. -/
theorem re_logDeriv_eq_tsum_of_growth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hG : GrowthLtTwo (completedLFunction χ))
    {s : ℂ} (hs : 1 < s.re) :
    (deriv (LFunction χ) s / LFunction χ s + deriv (gammaFactor χ) s / gammaFactor χ s).re
      = -(Real.log q) / 2 + ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (s - ρ)).re :=
  re_logDeriv_eq_tsum_proof χ hχ hχ1 (summable_zeroOrd_div_normSq_proof χ hχ hχ1 hG)
    (hadamardLogDeriv_of_growth χ hχ hχ1 hG) hs

end DetPrimality.Bach
