import DetPrimality.Bach.Handoffs

/-!
# Growth of the completed Dirichlet L-function (order `< 2`)

Main result: `DetPrimality.Bach.growth_completedLFunction`:
for any Dirichlet character `χ ≠ 1` (primitive or not),
`GrowthLtTwo (completedLFunction χ)`, i.e. `‖Λ(s,χ)‖ ≤ exp (C (1+‖s‖)^{3/2})`.

Route (no functional equation needed):
* `completedLFunction χ = ZMod.completedLFunction₀ χ` for `χ ≠ 1` (pole terms vanish), which is
  `q^{-s} • ∑ χ(j) (Λ₀^{even}_j(s/2)/2 + Λ^{odd}_j((s+1)/2)/2)`.
* For an abstract `WeakFEPair` whose kernels have exponential decay `C e^{-p x}` on `[1,∞)`,
  `‖Λ₀(s)‖ ≤ K · m! · (1/p)^m` with `m = ⌈|Re s| + k⌉ + 1`, by bounding the Mellin integrand
  pointwise by `A(s) · h(t)` with a fixed integrable `h` (`1` on `(0,1]`, `t^{-2}` on `(1,∞)`),
  using `e^{-y} y^m ≤ m!` (on `(0,1)` via the functional equation `f(t) = ε t^{-k} g(1/t)`).
* `m! R^m ≤ exp((2 + log R) m^{3/2})`.
* Closure of `GrowthLtTwo` under `+`, `*`, constants, finite sums, `q^{-s}`, `s ↦ s/2`, `(s+1)/2`.
-/

open Complex Real MeasureTheory Set Filter Asymptotics DirichletCharacter HurwitzZeta

namespace DetPrimality.Bach

/-! ## Closure properties of `GrowthLtTwo` -/

lemma one_le_growthWeight (s : ℂ) : (1 : ℝ) ≤ (1 + ‖s‖) ^ ((3 : ℝ) / 2) :=
  Real.one_le_rpow (by linarith [norm_nonneg s]) (by norm_num)

lemma growthLtTwo_of_bound (f : ℂ → ℂ) (K C : ℝ)
    (h : ∀ s, ‖f s‖ ≤ K * Real.exp (C * (1 + ‖s‖) ^ ((3 : ℝ) / 2))) : GrowthLtTwo f := by
  refine ⟨|K| + max C 0 + 1, by positivity, fun s => ?_⟩
  set u := (1 + ‖s‖) ^ ((3 : ℝ) / 2) with hu_def
  have hu : 1 ≤ u := one_le_growthWeight s
  have hK : K ≤ Real.exp |K| := (le_abs_self K).trans (by linarith [Real.add_one_le_exp |K|])
  have h1 : |K| ≤ |K| * u := le_mul_of_one_le_right (abs_nonneg K) hu
  have h2 : C * u ≤ max C 0 * u := mul_le_mul_of_nonneg_right (le_max_left C 0) (by linarith)
  calc ‖f s‖ ≤ K * Real.exp (C * u) := h s
    _ ≤ Real.exp |K| * Real.exp (C * u) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = Real.exp (|K| + C * u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((|K| + max C 0 + 1) * u) := Real.exp_le_exp.mpr (by nlinarith)

lemma growthLtTwo_zero : GrowthLtTwo (fun _ : ℂ => (0 : ℂ)) :=
  growthLtTwo_of_bound _ 0 0 (fun s => by simp)

lemma growthLtTwo_add {f g : ℂ → ℂ} (hf : GrowthLtTwo f) (hg : GrowthLtTwo g) :
    GrowthLtTwo (fun s => f s + g s) := by
  obtain ⟨C₁, -, h₁⟩ := hf
  obtain ⟨C₂, -, h₂⟩ := hg
  refine growthLtTwo_of_bound _ 2 (max C₁ C₂) (fun s => ?_)
  have hu : 0 ≤ (1 + ‖s‖) ^ ((3 : ℝ) / 2) := by positivity
  have e1 : Real.exp (C₁ * (1 + ‖s‖) ^ ((3 : ℝ) / 2))
      ≤ Real.exp (max C₁ C₂ * (1 + ‖s‖) ^ ((3 : ℝ) / 2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
  have e2 : Real.exp (C₂ * (1 + ‖s‖) ^ ((3 : ℝ) / 2))
      ≤ Real.exp (max C₁ C₂ * (1 + ‖s‖) ^ ((3 : ℝ) / 2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hu)
  calc ‖f s + g s‖ ≤ ‖f s‖ + ‖g s‖ := norm_add_le _ _
    _ ≤ _ := by linarith [h₁ s, h₂ s]

lemma growthLtTwo_mul {f g : ℂ → ℂ} (hf : GrowthLtTwo f) (hg : GrowthLtTwo g) :
    GrowthLtTwo (fun s => f s * g s) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, by linarith, fun s => ?_⟩
  rw [norm_mul, add_mul, Real.exp_add]
  exact mul_le_mul (h₁ s) (h₂ s) (norm_nonneg _) (Real.exp_pos _).le

lemma growthLtTwo_const_mul (c : ℂ) {f : ℂ → ℂ} (hf : GrowthLtTwo f) :
    GrowthLtTwo (fun s => c * f s) := by
  obtain ⟨C, -, h⟩ := hf
  refine growthLtTwo_of_bound _ ‖c‖ C (fun s => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h s) (norm_nonneg c)

lemma growthLtTwo_div_const (c : ℂ) {f : ℂ → ℂ} (hf : GrowthLtTwo f) :
    GrowthLtTwo (fun s => f s / c) := by
  simp_rw [div_eq_inv_mul]
  exact growthLtTwo_const_mul _ hf

lemma growthLtTwo_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ S, GrowthLtTwo (f i)) : GrowthLtTwo (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using growthLtTwo_zero
  | insert a S ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact growthLtTwo_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma growthLtTwo_comp {f : ℂ → ℂ} (φ : ℂ → ℂ) (hφ : ∀ s, ‖φ s‖ ≤ 1 + ‖s‖)
    (hf : GrowthLtTwo f) : GrowthLtTwo (fun s => f (φ s)) := by
  obtain ⟨C, hC, h⟩ := hf
  refine growthLtTwo_of_bound _ 1 (C * 2 ^ ((3 : ℝ) / 2)) (fun s => ?_)
  have hle : (1 + ‖φ s‖) ^ ((3 : ℝ) / 2) ≤ (2 * (1 + ‖s‖)) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) (by linarith [hφ s, norm_nonneg s]) (by norm_num)
  calc ‖f (φ s)‖ ≤ Real.exp (C * (1 + ‖φ s‖) ^ ((3 : ℝ) / 2)) := h _
    _ ≤ Real.exp (C * (2 * (1 + ‖s‖)) ^ ((3 : ℝ) / 2)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hC.le)
    _ = 1 * Real.exp (C * 2 ^ ((3 : ℝ) / 2) * (1 + ‖s‖) ^ ((3 : ℝ) / 2)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]; ring_nf

lemma growthLtTwo_natCast_cpow_neg (N : ℕ) [NeZero N] :
    GrowthLtTwo (fun s : ℂ => (N : ℂ) ^ (-s)) := by
  refine growthLtTwo_of_bound _ 1 (Real.log N) (fun s => ?_)
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re,
    Real.rpow_def_of_pos (by exact_mod_cast hN), one_mul]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg N)
  have h1 : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  linarith [neg_le_abs s.re, Complex.abs_re_le_norm s,
    Real.self_le_rpow_of_one_le h1 (by norm_num : (1 : ℝ) ≤ 3 / 2)]

/-! ## Elementary real inequalities -/

lemma exp_neg_mul_pow_le_factorial {y : ℝ} (hy : 0 ≤ y) (m : ℕ) :
    Real.exp (-y) * y ^ m ≤ (m.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (x := y) hy m
  rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos m)] at h
  calc Real.exp (-y) * y ^ m ≤ Real.exp (-y) * (Real.exp y * m.factorial) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = m.factorial := by rw [← mul_assoc, ← Real.exp_add]; simp

lemma factorial_mul_pow_le_exp {R : ℝ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) :
    (m.factorial : ℝ) * R ^ m ≤ Real.exp ((2 + Real.log R) * (m : ℝ) ^ ((3 : ℝ) / 2)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h32 : (m : ℝ) ^ ((3 : ℝ) / 2) = m * (m : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hm0, Real.rpow_one]
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hlog : Real.log m ≤ 2 * (m : ℝ) ^ ((1 : ℝ) / 2) :=
    (Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 1 / 2)).trans (le_of_eq (by ring))
  have hmm : (m : ℝ) ^ m = Real.exp (m * Real.log m) := by
    rw [Real.exp_nat_mul, Real.exp_log hm0]
  have hR' : R ^ m = Real.exp (m * Real.log R) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hm32 : (m : ℝ) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) := Real.self_le_rpow_of_one_le hm1 (by norm_num)
  have a1 : (m : ℝ) * Real.log m ≤ m * (2 * (m : ℝ) ^ ((1 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hlog hm0.le
  have a2 : (m : ℝ) * Real.log R ≤ (m : ℝ) ^ ((3 : ℝ) / 2) * Real.log R :=
    mul_le_mul_of_nonneg_right hm32 hlogR
  calc (m.factorial : ℝ) * R ^ m ≤ (m : ℝ) ^ m * R ^ m :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = Real.exp (m * Real.log m + m * Real.log R) := by rw [hmm, hR', Real.exp_add]
    _ ≤ Real.exp ((2 + Real.log R) * (m : ℝ) ^ ((3 : ℝ) / 2)) :=
        Real.exp_le_exp.mpr (by nlinarith)

/-- Upgrade an `IsBigO atTop` exponential-decay statement for a function continuous on
`(0,∞)` to a uniform bound on `[1,∞)`. -/
lemma exists_exp_bound {φ : ℝ → ℝ} (hc : ContinuousOn φ (Ioi 0)) {p : ℝ} (hp : 0 ≤ p)
    (hφ : φ =O[atTop] fun x => Real.exp (-p * x)) :
    ∃ C, 0 ≤ C ∧ ∀ x, 1 ≤ x → |φ x| ≤ C * Real.exp (-p * x) := by
  obtain ⟨c, hc'⟩ := hφ.bound
  obtain ⟨A, hA⟩ := eventually_atTop.mp hc'
  set B := max A 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := B)).exists_bound_of_continuousOn
    (hc.mono fun x hx => lt_of_lt_of_le one_pos hx.1)
  have hC0 : 0 ≤ max c 0 + max M 0 * Real.exp (p * B) :=
    add_nonneg (le_max_right _ _) (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le)
  refine ⟨max c 0 + max M 0 * Real.exp (p * B), hC0, fun x hx => ?_⟩
  have he : 0 < Real.exp (-p * x) := Real.exp_pos _
  have hc0 : 0 ≤ max c 0 * Real.exp (-p * x) := mul_nonneg (le_max_right _ _) he.le
  rcases le_total x B with hxB | hxB
  · have h1 := hM x ⟨hx, hxB⟩
    rw [Real.norm_eq_abs] at h1
    have h2 : 1 ≤ Real.exp (p * B) * Real.exp (-p * x) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [mul_nonneg hp (sub_nonneg.mpr hxB)])
    have h3 : max M 0 ≤ max M 0 * (Real.exp (p * B) * Real.exp (-p * x)) :=
      le_mul_of_one_le_right (le_max_right _ _) h2
    have h4 := le_max_left M 0
    nlinarith
  · have h2 := hA x (le_trans (le_max_left _ _) hxB)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos he] at h2
    have h3 := mul_le_mul_of_nonneg_right (le_max_left c 0) he.le
    have h4 : 0 ≤ max M 0 * Real.exp (p * B) * Real.exp (-p * x) :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le) he.le
    nlinarith

/-! ## The Mellin-transform bound for a `WeakFEPair` -/

/-- Core estimate: if both kernels of a `WeakFEPair` decay like `C e^{-p x}` on `[1, ∞)`, then
its entire completed function `Λ₀` has growth of order `≤ 3/2`. -/
theorem growthLtTwo_Λ₀ (P : WeakFEPair ℂ) {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hf : ∀ x : ℝ, 1 ≤ x → ‖P.f x - P.f₀‖ ≤ C * Real.exp (-p * x))
    (hg : ∀ x : ℝ, 1 ≤ x → ‖P.g x - P.g₀‖ ≤ C * Real.exp (-p * x)) :
    GrowthLtTwo P.Λ₀ := by
  set h : ℝ → ℝ := fun t => if t ≤ 1 then 1 else t ^ (-2 : ℝ) with hh_def
  have hint : IntegrableOn h (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun t ht => ?_)
        measurableSet_Ioc
      simp [hh_def, ht.2]
    · refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).congr_fun
        (fun t ht => ?_) measurableSet_Ioi
      simp [hh_def, not_le.mpr (show (1 : ℝ) < t from ht)]
  set I₀ := ∫ t in Ioi (0 : ℝ), h t with hI₀_def
  have hh0 : ∀ t, 0 ≤ h t := fun t => by
    simp only [hh_def]; split_ifs with ht1
    · exact zero_le_one
    · exact Real.rpow_nonneg (by linarith [not_le.mp ht1]) _
  have hI₀ : 0 ≤ I₀ := setIntegral_nonneg measurableSet_Ioi (fun t _ => hh0 t)
  set R := max 1 p⁻¹ with hR_def
  have hR : 1 ≤ R := le_max_left _ _
  set k := P.k with hk_def
  have hk : 0 < k := P.hk
  set K := C * (1 + ‖P.ε‖) * I₀ with hK_def
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC (by positivity)) hI₀
  set D := (2 + Real.log R) * (k + 2) ^ ((3 : ℝ) / 2) with hD_def
  refine growthLtTwo_of_bound _ K D (fun s => ?_)
  set σ := s.re with hσ_def
  set m := ⌈|σ| + k⌉₊ + 1 with hm_def
  have hceil : (⌈|σ| + k⌉₊ : ℝ) < |σ| + k + 1 := Nat.ceil_lt_add_one (by linarith [abs_nonneg σ])
  have hceil' : |σ| + k ≤ (⌈|σ| + k⌉₊ : ℝ) := Nat.le_ceil _
  have hmR : (m : ℝ) = ⌈|σ| + k⌉₊ + 1 := by simp [hm_def]
  have hσabs := le_abs_self σ
  have hσabs' := neg_abs_le σ
  have hmσ1 : σ + 1 ≤ (m : ℝ) := by linarith
  have hmσ2 : k - σ + 1 ≤ (m : ℝ) := by linarith
  set A := C * (1 + ‖P.ε‖) * ((m.factorial : ℝ) * p⁻¹ ^ m) with hA_def
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ A * h t := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    have hre : (s - 1).re = σ - 1 := by simp [hσ_def]
    rw [hre]
    rcases lt_trichotomy t 1 with h1 | rfl | h1
    · -- `0 < t < 1`: use the functional equation `f t = ε t^{-k} g (1/t)`.
      have hF : P.f_modif t = P.f t - (P.ε * ↑(t ^ (-k))) • P.g₀ := by
        rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr h1.le),
          indicator_of_mem (mem_Ioo.mpr ⟨ht, h1⟩), zero_add]
      have hfe := P.h_feq (1 / t) (one_div_pos.mpr ht)
      rw [one_div_one_div] at hfe
      have htk : (1 / t) ^ k = t ^ (-k) := by
        rw [Real.rpow_neg ht.le, one_div, Real.inv_rpow ht.le]
      have hht : h t = 1 := by simp [hh_def, h1.le]
      rw [hF, hfe, htk, ← smul_sub, norm_smul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), hht]
      have hgb := hg (1 / t) (one_le_one_div ht h1.le)
      have hexp := exp_neg_mul_pow_le_factorial
        (by positivity : (0 : ℝ) ≤ p * (1 / t)) m
      rw [← neg_mul] at hexp
      have e1 : t ^ (σ - 1) * t ^ (-k)
          = t ^ (σ - 1 - k + m) * (p⁻¹ ^ m * (p * (1 / t)) ^ m) := by
        rw [← mul_pow, show p⁻¹ * (p * (1 / t)) = t⁻¹ by field_simp, inv_pow,
          ← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht, ← Real.rpow_add ht]
        congr 1; ring
      have hte : t ^ (σ - 1 - k + m) ≤ 1 := Real.rpow_le_one ht.le h1.le (by linarith)
      have hte0 : 0 ≤ t ^ (σ - 1 - k + m) := by positivity
      have hpm : 0 ≤ p⁻¹ ^ m := by positivity
      have hεC : 0 ≤ ‖P.ε‖ * C := mul_nonneg (norm_nonneg _) hC
      calc t ^ (σ - 1) * (‖P.ε‖ * t ^ (-k) * ‖P.g (1 / t) - P.g₀‖)
          = ‖P.ε‖ * (t ^ (σ - 1) * t ^ (-k)) * ‖P.g (1 / t) - P.g₀‖ := by ring
        _ ≤ ‖P.ε‖ * (t ^ (σ - 1) * t ^ (-k)) * (C * Real.exp (-p * (1 / t))) :=
            mul_le_mul_of_nonneg_left hgb (by positivity)
        _ = (‖P.ε‖ * C) * t ^ (σ - 1 - k + m) * p⁻¹ ^ m
              * (Real.exp (-p * (1 / t)) * (p * (1 / t)) ^ m) := by rw [e1]; ring
        _ ≤ (‖P.ε‖ * C) * 1 * p⁻¹ ^ m * (m.factorial : ℝ) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hte hεC) hpm) hexp
              (by positivity) (mul_nonneg (mul_nonneg hεC zero_le_one) hpm)
        _ ≤ A * 1 := by
            have : 0 ≤ C * ((m.factorial : ℝ) * p⁻¹ ^ m) := mul_nonneg hC (by positivity)
            simp only [hA_def]; nlinarith
    · -- `t = 1`: `f_modif 1 = 0`.
      have : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
      rw [this, norm_zero, mul_zero]
      exact mul_nonneg hA (hh0 1)
    · -- `t > 1`: exponential decay of `f - f₀`.
      have hF : P.f_modif t = P.f t - P.f₀ := by
        rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (show t ∈ Ioi 1 from h1),
          indicator_of_notMem (fun hm => absurd hm.2 (not_lt.mpr h1.le)), add_zero]
      have hht : h t = t ^ (-2 : ℝ) := by simp [hh_def, not_le.mpr h1]
      rw [hF, hht]
      have hfb := hf t h1.le
      have hexp := exp_neg_mul_pow_le_factorial (by positivity : (0 : ℝ) ≤ p * t) m
      rw [← neg_mul] at hexp
      have e2 : t ^ (σ - 1) = t ^ (σ - 1 - m) * (p⁻¹ ^ m * (p * t) ^ m) := by
        rw [← mul_pow, inv_mul_cancel_left₀ hp.ne', ← Real.rpow_natCast, ← Real.rpow_add ht]
        congr 1; ring
      have hte : t ^ (σ - 1 - m) ≤ t ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
      have hpm : 0 ≤ p⁻¹ ^ m := by positivity
      calc t ^ (σ - 1) * ‖P.f t - P.f₀‖ ≤ t ^ (σ - 1) * (C * Real.exp (-p * t)) :=
            mul_le_mul_of_nonneg_left hfb (by positivity)
        _ = C * t ^ (σ - 1 - m) * p⁻¹ ^ m * (Real.exp (-p * t) * (p * t) ^ m) := by
            rw [e2]; ring
        _ ≤ C * t ^ (-2 : ℝ) * p⁻¹ ^ m * (m.factorial : ℝ) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hte hC) hpm) hexp
              (by positivity) (mul_nonneg (mul_nonneg hC (by positivity)) hpm)
        _ ≤ A * t ^ (-2 : ℝ) := by
            have : 0 ≤ ‖P.ε‖ * C * ((m.factorial : ℝ) * p⁻¹ ^ m) * t ^ (-2 : ℝ) :=
              mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hC) (by positivity)) (by positivity)
            simp only [hA_def]; nlinarith
  -- integrate the pointwise bound
  have hnorm : ‖P.Λ₀ s‖ ≤ A * I₀ := by
    have := norm_integral_le_of_norm_le (hint.const_mul A)
      (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
    calc ‖P.Λ₀ s‖ = ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • P.f_modif t‖ := rfl
      _ ≤ ∫ t in Ioi (0 : ℝ), A * h t := this
      _ = A * I₀ := integral_const_mul _ _
  -- bound `m! p⁻ᵐ` by `exp (D (1+‖s‖)^{3/2})`
  have hm1 : 1 ≤ m := by simp [hm_def]
  have hpR : p⁻¹ ^ m ≤ R ^ m := pow_le_pow_left₀ (by positivity) (le_max_right _ _) m
  have hfacR := factorial_mul_pow_le_exp hR hm1
  have hmle : (m : ℝ) ≤ (k + 2) * (1 + ‖s‖) := by
    have := Complex.abs_re_le_norm s
    nlinarith [norm_nonneg s]
  have hm32 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (k + 2) ^ ((3 : ℝ) / 2) * (1 + ‖s‖) ^ ((3 : ℝ) / 2) := by
    rw [← Real.mul_rpow (by linarith) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hmle (by norm_num)
  have hlogR : 0 ≤ 2 + Real.log R := by linarith [Real.log_nonneg hR]
  have hexpD : Real.exp ((2 + Real.log R) * (m : ℝ) ^ ((3 : ℝ) / 2))
      ≤ Real.exp (D * (1 + ‖s‖) ^ ((3 : ℝ) / 2)) := by
    apply Real.exp_le_exp.mpr
    rw [hD_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left hm32 hlogR
  have hfm : (m.factorial : ℝ) * p⁻¹ ^ m ≤ Real.exp (D * (1 + ‖s‖) ^ ((3 : ℝ) / 2)) :=
    (mul_le_mul_of_nonneg_left hpR (by positivity)).trans (hfacR.trans hexpD)
  calc ‖P.Λ₀ s‖ ≤ A * I₀ := hnorm
    _ = (C * (1 + ‖P.ε‖) * I₀) * ((m.factorial : ℝ) * p⁻¹ ^ m) := by simp only [hA_def]; ring
    _ ≤ K * Real.exp (D * (1 + ‖s‖) ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hfm hK

/-- Version of `growthLtTwo_Λ₀` with independent decay constants for `f` and `g`. -/
theorem growthLtTwo_Λ₀' (P : WeakFEPair ℂ)
    (hf : ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ x : ℝ, 1 ≤ x → ‖P.f x - P.f₀‖ ≤ C * Real.exp (-p * x))
    (hg : ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ x : ℝ, 1 ≤ x → ‖P.g x - P.g₀‖ ≤ C * Real.exp (-p * x)) :
    GrowthLtTwo P.Λ₀ := by
  obtain ⟨C₁, p₁, hC₁, hp₁, h₁⟩ := hf
  obtain ⟨C₂, p₂, hC₂, hp₂, h₂⟩ := hg
  have key : ∀ (C q : ℝ), C ≤ max C₁ C₂ → min p₁ p₂ ≤ q → ∀ x : ℝ, 1 ≤ x →
      C * Real.exp (-q * x) ≤ max C₁ C₂ * Real.exp (-(min p₁ p₂) * x) := by
    intro C q hC hq x hx
    exact mul_le_mul hC (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
      (le_trans hC₁ (le_max_left _ _))
  exact growthLtTwo_Λ₀ P (C := max C₁ C₂) (p := min p₁ p₂) (le_trans hC₁ (le_max_left _ _))
    (lt_min hp₁ hp₂)
    (fun x hx => (h₁ x hx).trans (key C₁ p₁ (le_max_left _ _) (min_le_left _ _) x hx))
    (fun x hx => (h₂ x hx).trans (key C₂ p₂ (le_max_right _ _) (min_le_right _ _) x hx))

/-! ## Hurwitz zeta functions -/

lemma norm_ofReal_sub_ofReal (r c : ℝ) : ‖(r : ℂ) - (c : ℂ)‖ = |r - c| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma growthLtTwo_hurwitzEven_Λ₀ (a : UnitAddCircle) :
    GrowthLtTwo (hurwitzEvenFEPair a).Λ₀ := by
  apply growthLtTwo_Λ₀'
  · obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub a
    obtain ⟨C, hC, hb⟩ := exists_exp_bound ((continuousOn_evenKernel a).sub continuousOn_const)
      hp.le hO
    refine ⟨C, p, hC, hp, fun x hx => ?_⟩
    have : ‖(hurwitzEvenFEPair a).f x - (hurwitzEvenFEPair a).f₀‖
        = |evenKernel a x - (if a = 0 then 1 else 0)| := by
      change ‖((evenKernel a x : ℝ) : ℂ) - (if a = 0 then 1 else 0)‖ = _
      split_ifs
      · simpa using norm_ofReal_sub_ofReal (evenKernel a x) 1
      · simp
    rw [this]; exact hb x hx
  · obtain ⟨p, hp, hO⟩ := isBigO_atTop_cosKernel_sub a
    obtain ⟨C, hC, hb⟩ := exists_exp_bound ((continuousOn_cosKernel a).sub continuousOn_const)
      hp.le hO
    refine ⟨C, p, hC, hp, fun x hx => ?_⟩
    have : ‖(hurwitzEvenFEPair a).g x - (hurwitzEvenFEPair a).g₀‖ = |cosKernel a x - 1| := by
      change ‖((cosKernel a x : ℝ) : ℂ) - 1‖ = _
      simpa using norm_ofReal_sub_ofReal (cosKernel a x) 1
    rw [this]; exact hb x hx

lemma growthLtTwo_hurwitzOdd_Λ₀ (a : UnitAddCircle) :
    GrowthLtTwo (hurwitzOddFEPair a).Λ₀ := by
  apply growthLtTwo_Λ₀'
  · obtain ⟨p, hp, hO⟩ := isBigO_atTop_oddKernel a
    obtain ⟨C, hC, hb⟩ := exists_exp_bound (continuousOn_oddKernel a) hp.le hO
    refine ⟨C, p, hC, hp, fun x hx => ?_⟩
    simpa [Complex.norm_real] using hb x hx
  · obtain ⟨p, hp, hO⟩ := isBigO_atTop_sinKernel a
    obtain ⟨C, hC, hb⟩ := exists_exp_bound (continuousOn_sinKernel a) hp.le hO
    refine ⟨C, p, hC, hp, fun x hx => ?_⟩
    simpa [Complex.norm_real] using hb x hx

lemma growthLtTwo_completedHurwitzZetaEven₀ (a : UnitAddCircle) :
    GrowthLtTwo (completedHurwitzZetaEven₀ a) := by
  have h := growthLtTwo_div_const 2
    (growthLtTwo_comp (fun s : ℂ => s / 2) (fun s => by
      rw [norm_div, Complex.norm_two]; linarith [norm_nonneg s])
      (growthLtTwo_hurwitzEven_Λ₀ a))
  exact h

lemma growthLtTwo_completedHurwitzZetaOdd (a : UnitAddCircle) :
    GrowthLtTwo (completedHurwitzZetaOdd a) := by
  have hΛ : ∀ s, (hurwitzOddFEPair a).Λ s = (hurwitzOddFEPair a).Λ₀ s := fun s => by
    simp [WeakFEPair.Λ]
  have h := growthLtTwo_div_const 2
    (growthLtTwo_comp (fun s : ℂ => (s + 1) / 2) (fun s => by
      rw [norm_div, Complex.norm_two]; linarith [norm_add_le s 1, norm_one (α := ℂ), norm_nonneg s])
      (growthLtTwo_hurwitzOdd_Λ₀ a))
  have he : completedHurwitzZetaOdd a = fun s => (hurwitzOddFEPair a).Λ₀ ((s + 1) / 2) / 2 := by
    funext s; rw [completedHurwitzZetaOdd, hΛ]
  rw [he]; exact h

/-! ## Main theorem -/

/-- **Growth of order `< 2`** (in fact `≤ 3/2`, really `1`) of the completed Dirichlet
L-function of any nontrivial character (primitivity not needed). -/
theorem growth_completedLFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) : GrowthLtTwo (completedLFunction χ) := by
  have hq : q ≠ 1 := hχ1 ∘ level_one' χ
  have h0 : χ 0 = 0 := χ.map_zero' hq
  have hsum : ∑ j, χ j = 0 := χ.sum_eq_zero_of_ne_one hχ1
  have hE : completedLFunction χ = ZMod.completedLFunction₀ χ := by
    funext s
    rw [DirichletCharacter.completedLFunction, ZMod.completedLFunction_eq, h0, hsum]
    simp
  rw [hE]
  show GrowthLtTwo (fun s => (q : ℂ) ^ (-s) *
      ∑ j : ZMod q, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s
    + (q : ℂ) ^ (-s) * ∑ j : ZMod q, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s)
  refine growthLtTwo_add (growthLtTwo_mul (growthLtTwo_natCast_cpow_neg q) ?_)
    (growthLtTwo_mul (growthLtTwo_natCast_cpow_neg q) ?_)
  · exact growthLtTwo_finset_sum Finset.univ
      (fun j z => χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z)
      (fun j _ => growthLtTwo_const_mul _ (growthLtTwo_completedHurwitzZetaEven₀ _))
  · exact growthLtTwo_finset_sum Finset.univ
      (fun j z => χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) z)
      (fun j _ => growthLtTwo_const_mul _ (growthLtTwo_completedHurwitzZetaOdd _))

end DetPrimality.Bach
