import DetPrimality.Bach.Growth
import DetPrimality.Bach.HadamardL
import DetPrimality.Bach.ExplicitFormula
import DetPrimality.Bach.LLSDefs

/-!
# The Riemann `ξ`-function and its Hadamard partial fraction (input for LLS Lemma 1)

`llsZeta_xi s = s (s - 1) Λ₀(s) + 1 = s (s - 1) π^{-s/2} Γ(s/2) ζ(s)`.

* `llsZeta_xi_differentiable`, `llsZeta_xi_zero`, `llsZeta_xi_one_sub`, `llsZeta_xi_eq_zeta`;
* `llsZeta_growth : GrowthLtTwo llsZeta_xi`;
* `llsZeta_zeroOrd_eq_order` : zeros of `ξ` = nontrivial zeros of `ζ`, with multiplicity;
* `llsZeta_logDeriv_eq_tsum` : `ξ'/ξ(s) = ξ'(0) + ∑ m_ρ (1/(s-ρ) + 1/ρ)`;
* `llsZeta_deriv_zero_re` : `Re ξ'(0) = -∑ m_ρ Re (1/ρ)` (unconditional);
* `llsZeta_neg_logDeriv_zeta` : the decomposition of `-ζ'/ζ(s)` for `Re s > 1`.
-/

open Complex DirichletCharacter Filter Topology

namespace DetPrimality.Bach

/-- Riemann's `ξ` (normalised so that `ξ(0) = ξ(1) = 1`):
`ξ(s) = s (s - 1) π^{-s/2} Γ(s/2) ζ(s)`. -/
noncomputable def llsZeta_xi : ℂ → ℂ := fun s => s * (s - 1) * completedRiemannZeta₀ s + 1

lemma llsZeta_xi_apply (s : ℂ) : llsZeta_xi s = s * (s - 1) * completedRiemannZeta₀ s + 1 := rfl

theorem llsZeta_xi_differentiable : Differentiable ℂ llsZeta_xi :=
  ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

@[simp] theorem llsZeta_xi_zero : llsZeta_xi 0 = 1 := by simp [llsZeta_xi]

@[simp] theorem llsZeta_xi_one : llsZeta_xi 1 = 1 := by simp [llsZeta_xi]

theorem llsZeta_xi_zero_ne_zero : llsZeta_xi 0 ≠ 0 := by simp

/-- Functional equation. -/
theorem llsZeta_xi_one_sub (s : ℂ) : llsZeta_xi (1 - s) = llsZeta_xi s := by
  rw [llsZeta_xi_apply, llsZeta_xi_apply, completedRiemannZeta₀_one_sub]; ring

theorem llsZeta_xi_eq_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    llsZeta_xi s = s * (s - 1) * completedRiemannZeta s := by
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [llsZeta_xi_apply, completedRiemannZeta_eq]
  field_simp
  ring

/-- `ξ(s) = s (s - 1) Γ_ℝ(s) ζ(s)` for `Re s > 0`, `s ≠ 1`. -/
theorem llsZeta_xi_eq_zeta {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    llsZeta_xi s = s * (s - 1) * Gammaℝ s * riemannZeta s := by
  have h0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  rw [llsZeta_xi_eq_completed h0 h1, riemannZeta_def_of_ne_zero h0]
  have := Gammaℝ_ne_zero_of_re_pos hs
  field_simp

theorem llsZeta_xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : llsZeta_xi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · simp
  · have hs0 : 0 < s.re := by linarith
    have h0 : s ≠ 0 := fun h => by rw [h] at hs0; simp at hs0
    rw [llsZeta_xi_eq_zeta hs0 h1]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
      (Gammaℝ_ne_zero_of_re_pos hs0)) (riemannZeta_ne_zero_of_one_le_re hs)

theorem llsZeta_xi_ne_zero_of_not_strip {s : ℂ} (hs : ¬ (0 < s.re ∧ s.re < 1)) :
    llsZeta_xi s ≠ 0 := by
  by_cases h : 1 ≤ s.re
  · exact llsZeta_xi_ne_zero_of_one_le_re h
  · have h0 : s.re ≤ 0 := by
      by_contra h0
      exact hs ⟨not_le.mp h0, not_le.mp h⟩
    rw [← llsZeta_xi_one_sub]
    exact llsZeta_xi_ne_zero_of_one_le_re (by simp; linarith)

/-! ### Growth -/

private lemma llsZeta_growth_affine (c : ℂ) (hc : ‖c‖ ≤ 1) : GrowthLtTwo (fun s : ℂ => s - c) := by
  refine growthLtTwo_of_bound _ 1 1 (fun s => ?_)
  have h1 : ‖s - c‖ ≤ 1 + ‖s‖ := by linarith [norm_sub_le s c]
  have h2 : 1 + ‖s‖ ≤ (1 + ‖s‖) ^ ((3 : ℝ) / 2) :=
    Real.self_le_rpow_of_one_le (by linarith [norm_nonneg s]) (by norm_num)
  have h3 := Real.add_one_le_exp ((1 + ‖s‖) ^ ((3 : ℝ) / 2))
  rw [one_mul, one_mul]
  linarith

/-- `ξ` has order `< 2`. -/
theorem llsZeta_growth : GrowthLtTwo llsZeta_xi := by
  have h1 : GrowthLtTwo (fun s : ℂ => s) := by simpa using llsZeta_growth_affine 0 (by simp)
  have h2 : GrowthLtTwo (fun s : ℂ => s - 1) := llsZeta_growth_affine 1 (by simp)
  have h3 : GrowthLtTwo completedRiemannZeta₀ :=
    growthLtTwo_completedHurwitzZetaEven₀ 0
  have h4 : GrowthLtTwo (fun _ : ℂ => (1 : ℂ)) := growthLtTwo_of_bound _ 1 0 (fun s => by simp)
  exact growthLtTwo_add (growthLtTwo_mul (growthLtTwo_mul h1 h2) h3) h4

/-! ### Zeros -/

/-- The multiplicity `zeroOrd 1 ρ` of `ρ` as a nontrivial zero of `ζ` is the order of vanishing
of `ξ` at `ρ` (for every `ρ`). -/
theorem llsZeta_zeroOrd_eq_order (ρ : ℂ) :
    zeroOrd (1 : DirichletCharacter ℂ 1) ρ = analyticOrderNatAt llsZeta_xi ρ := by
  have hξ := llsZeta_xi_differentiable
  unfold zeroOrd
  split_ifs with h
  · rw [LFunction_modOne_eq]
    have h0 : ρ ≠ 0 := fun h' => by rw [h'] at h; simp at h
    have h1 : ρ ≠ 1 := fun h' => by rw [h'] at h; simp at h
    set g : ℂ → ℂ := fun s => (Gammaℝ s)⁻¹ * (s * (s - 1))⁻¹ with hg
    have hga : AnalyticAt ℂ g ρ := by
      refine (differentiable_Gammaℝ_inv.analyticAt ρ).mul (AnalyticAt.inv ?_ ?_)
      · exact (differentiable_id.mul (differentiable_id.sub_const 1)).analyticAt ρ
      · exact mul_ne_zero h0 (sub_ne_zero.mpr h1)
    have hg0 : analyticOrderAt g ρ = 0 := by
      rw [hga.analyticOrderAt_eq_zero]
      exact mul_ne_zero (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h.1))
        (inv_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)))
    have hev : riemannZeta =ᶠ[𝓝 ρ] llsZeta_xi * g := by
      have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
        (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
      filter_upwards [hopen.mem_nhds h] with s hs
      have hs0 : s ≠ 0 := fun h' => by rw [h'] at hs; simp at hs
      have hs1 : s ≠ 1 := fun h' => by rw [h'] at hs; simp at hs
      have hΓ := Gammaℝ_ne_zero_of_re_pos hs.1
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      simp only [Pi.mul_apply, hg]
      rw [llsZeta_xi_eq_zeta hs.1 hs1]
      field_simp
    simp only [analyticOrderNatAt]
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul (hξ.analyticAt ρ) hga, hg0, add_zero]
  · exact ((Hadamard.orderNat_eq_zero_iff hξ llsZeta_xi_zero_ne_zero ρ).mpr
      (llsZeta_xi_ne_zero_of_not_strip h)).symm

/-- `∑ m_ρ / |ρ|² < ∞` over the nontrivial zeros of `ζ`. -/
theorem llsZeta_summable :
    Summable fun ρ : ℂ => (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) / ‖ρ‖ ^ 2 := by
  have := Hadamard.summable_order_div_normSq llsZeta_xi_differentiable llsZeta_xi_zero_ne_zero
    llsZeta_growth
  simpa only [llsZeta_zeroOrd_eq_order] using this

/-- **Hadamard partial fraction for `ξ`** (note `ξ(0) = 1`, so `B = ξ'(0)`). -/
theorem llsZeta_logDeriv_eq_tsum {s : ℂ} (hs : llsZeta_xi s ≠ 0) :
    deriv llsZeta_xi s / llsZeta_xi s = deriv llsZeta_xi 0
      + ∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  rw [Hadamard.logDeriv_eq_tsum llsZeta_xi_differentiable llsZeta_xi_zero_ne_zero
    llsZeta_growth hs, llsZeta_xi_zero, div_one]
  congr 1
  exact tsum_congr fun ρ => by rw [llsZeta_zeroOrd_eq_order ρ]

/-! ### Symmetry `ρ ↦ 1 - ρ` -/

lemma llsZeta_order_one_sub {F : ℂ → ℂ} (hF : Differentiable ℂ F) (ρ : ℂ) :
    analyticOrderAt (fun z => F (1 - z)) (1 - ρ) = analyticOrderAt F ρ := by
  have hsub : Differentiable ℂ (fun z : ℂ => 1 - z) := (differentiable_const _).sub differentiable_id
  have hR : Differentiable ℂ (fun z => F (1 - z)) := hF.comp hsub
  by_cases htop : analyticOrderAt F ρ = ⊤
  · have hF0 : F = 0 :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ (fun z => hF.analyticAt z)).mp htop
    rw [htop, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero _ (fun z => hR.analyticAt z)]
    funext z; simp [hF0]
  · obtain ⟨G, hG, hGρ, hFG⟩ := Hadamard.exists_factor_sub hF ρ htop
    rw [← Nat.cast_analyticOrderNatAt htop, (hR.analyticAt _).analyticOrderAt_eq_natCast]
    refine ⟨fun z => (-1) ^ analyticOrderNatAt F ρ * G (1 - z), ?_, ?_,
      Filter.Eventually.of_forall fun z => ?_⟩
    · exact ((hG.comp hsub).const_mul _).analyticAt _
    · simp [hGρ]
    · show F (1 - z) = (z - (1 - ρ)) ^ analyticOrderNatAt F ρ
        * ((-1) ^ analyticOrderNatAt F ρ * G (1 - z))
      rw [hFG, ← mul_assoc, ← mul_pow]
      congr 2
      ring

theorem llsZeta_zeroOrd_one_sub (ρ : ℂ) :
    zeroOrd (1 : DirichletCharacter ℂ 1) (1 - ρ) = zeroOrd (1 : DirichletCharacter ℂ 1) ρ := by
  have h := llsZeta_order_one_sub llsZeta_xi_differentiable ρ
  rw [show (fun z => llsZeta_xi (1 - z)) = llsZeta_xi from funext llsZeta_xi_one_sub] at h
  rw [llsZeta_zeroOrd_eq_order, llsZeta_zeroOrd_eq_order, analyticOrderNatAt, analyticOrderNatAt, h]

lemma llsZeta_zeroOrd_re {ρ : ℂ} (h : zeroOrd (1 : DirichletCharacter ℂ 1) ρ ≠ 0) :
    |ρ.re| ≤ 1 := by
  unfold zeroOrd at h
  split_ifs at h with h1
  · rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
  · exact absurd rfl h

theorem llsZeta_summable_re_inv :
    Summable fun ρ : ℂ => (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) * (1 / ρ).re :=
  summable_re_inv llsZeta_summable (fun _ h => llsZeta_zeroOrd_re h)

/-- `ξ'(0) = -ξ'(1)`. -/
theorem llsZeta_deriv_zero : deriv llsZeta_xi 0 = -deriv llsZeta_xi 1 := by
  have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
  have h2 : HasDerivAt llsZeta_xi (deriv llsZeta_xi 1) (1 - 0) := by
    rw [sub_zero]; exact (llsZeta_xi_differentiable 1).hasDerivAt
  have h3 := h2.comp (0 : ℂ) h1
  have h4 : (llsZeta_xi ∘ fun s : ℂ => 1 - s) = llsZeta_xi := funext llsZeta_xi_one_sub
  rw [h4] at h3
  rw [h3.deriv]; ring

/-- **`Re B = -∑ m_ρ Re (1/ρ)`** (unconditional). -/
theorem llsZeta_deriv_zero_re :
    (deriv llsZeta_xi 0).re
      = -∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) * (1 / ρ).re := by
  have hS := llsZeta_summable
  have hd := llsZeta_summable_re_inv
  obtain ⟨ha, hre⟩ := re_partialFraction hS hd 1
  have e1 := llsZeta_logDeriv_eq_tsum (s := 1) (by simp)
  rw [llsZeta_xi_one, div_one] at e1
  have e2 := llsZeta_deriv_zero
  have hsym : ∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) * (1 / (1 - ρ)).re
      = ∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) * (1 / ρ).re := by
    have hinv : Function.Involutive (fun z : ℂ => 1 - z) := fun z => by simp
    have h := (hinv.toPerm _).tsum_eq
      (fun ρ : ℂ => (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) * (1 / (1 - ρ)).re)
    rw [← h]
    refine tsum_congr fun ρ => ?_
    show (zeroOrd (1 : DirichletCharacter ℂ 1) (1 - ρ) : ℝ) * (1 / (1 - (1 - ρ))).re = _
    rw [llsZeta_zeroOrd_one_sub, sub_sub_cancel]
  have e3 : (deriv llsZeta_xi 1).re = (deriv llsZeta_xi 0).re
      + (∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) * (1 / ρ).re
        + ∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) * (1 / ρ).re) := by
    rw [e1, Complex.add_re, hre, hsym]
  have e4 : (deriv llsZeta_xi 0).re = -(deriv llsZeta_xi 1).re := by
    rw [e2, Complex.neg_re]
  linarith

/-- Under RH, `∑ m_ρ / |ρ|² = -2 Re ξ'(0)`. -/
theorem llsZeta_zeroSumSq_eq (hGRH : DirichletLZerosOnLine) :
    zeroSumSq (1 : DirichletCharacter ℂ 1) = -2 * (deriv llsZeta_xi 0).re := by
  rw [llsZeta_deriv_zero_re, zeroSumSq, neg_mul_neg, ← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  by_cases h : zeroOrd (1 : DirichletCharacter ℂ 1) ρ = 0
  · simp [h]
  · have hre := re_eq_half_of_zeroOrd_ne_zero hGRH _ h
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, hre]
    ring

/-! ### The decomposition of `-ζ'/ζ` -/

/-- `ξ'/ξ(s) = 1/s + 1/(s-1) + Γ_ℝ'/Γ_ℝ(s) + ζ'/ζ(s)` for `Re s > 1`. -/
theorem llsZeta_logDeriv_xi {s : ℂ} (hs : 1 < s.re) :
    deriv llsZeta_xi s / llsZeta_xi s
      = 1 / s + 1 / (s - 1) + deriv Gammaℝ s / Gammaℝ s
        + deriv riemannZeta s / riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have h0 : s ≠ 0 := fun h => by rw [h] at hs0; simp at hs0
  have h1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hΓ0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hΓd := differentiableAt_Gammaℝ_of_re_pos hs0
  have hζ0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hζd := differentiableAt_riemannZeta h1
  have hev : llsZeta_xi =ᶠ[𝓝 s]
      fun z => (fun z => (fun z => z * (z - 1)) z * Gammaℝ z) z * riemannZeta z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < s.re from hs)] with z hz
    have hz1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz
    exact llsZeta_xi_eq_zeta (by linarith) hz1
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s :=
    differentiableAt_id.mul (differentiableAt_id.sub_const 1)
  have hl1 : logDeriv (fun z : ℂ => z * (z - 1)) s = 1 / s + 1 / (s - 1) := by
    have := logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s h0 h1'
      differentiableAt_id (differentiableAt_id.sub_const 1)
    rw [this, logDeriv_apply, logDeriv_apply]
    simp
  have hl2 := logDeriv_mul (f := fun z : ℂ => z * (z - 1)) (g := Gammaℝ) s
    (mul_ne_zero h0 h1') hΓ0 hd1 hΓd
  have hl3 := logDeriv_mul (f := fun z => (fun z : ℂ => z * (z - 1)) z * Gammaℝ z)
    (g := riemannZeta) s (mul_ne_zero (mul_ne_zero h0 h1') hΓ0) hζ0 (hd1.mul hΓd) hζd
  have hl : logDeriv llsZeta_xi s
      = logDeriv (fun z => (fun z => (fun z => z * (z - 1)) z * Gammaℝ z) z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [← logDeriv_apply, hl, hl3, hl2, hl1, logDeriv_apply, logDeriv_apply]

/-- **Decomposition of `-ζ'/ζ`** for `Re s > 1`, with `B = ξ'(0)`. -/
theorem llsZeta_neg_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s)
      = 1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2)
        - deriv llsZeta_xi 0
        - ∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  have h1 := llsZeta_logDeriv_xi hs
  have h2 := llsZeta_logDeriv_eq_tsum (llsZeta_xi_ne_zero_of_one_le_re hs.le)
  rw [← logDeriv_Gammaℝ (by linarith)]
  linear_combination h1 - h2

end DetPrimality.Bach
