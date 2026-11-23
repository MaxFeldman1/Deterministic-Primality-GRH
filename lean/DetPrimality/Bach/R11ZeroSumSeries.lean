import DetPrimality.Bach.R11ZeroSumHad
import DetPrimality.Bach.SharpZeroSum

/-!
# Round 11, zero sums: the two Hadamard sums at `3/2` in terms of Dirichlet series

With `S₁ = ∑ m_ρ Re 1/(3/2-ρ)` and `S₂ = ∑ m_ρ/(3/2-ρ)²`:

* ζ: `S₁ = 8/3 - ½ log π + ½ Re ψ(3/4) - F₀`, `Re S₂ = 40/9 - ¼ Re ψ'(3/4) - F₁`
  (`r11Zs_zeta_S1`, `r11Zs_zeta_S2`), `F₀ = ∑ Λ(n) n^{-3/2}`, `F₁ = ∑ Λ(n) log n · n^{-3/2}`;
* primitive `χ ≠ 1` mod `q`: `S₁ = ½ log q + Re L'/L(3/2) + Re γ'/γ(3/2)`,
  `Re S₂ = -¼ Re ψ'(a) - ∑ Λ(n) log n Re χ(n) n^{-3/2}`, `a ∈ {3/4, 5/4}`
  (`r11Zs_chi_S1`, `r11Zs_chi_S2`).
-/

open Complex DirichletCharacter Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `F₀ = ∑ Λ(n) n^{-3/2} = -ζ'/ζ(3/2)`. -/
noncomputable def r11Zs_F0 : ℝ := ∑' n : ℕ, Λ n / (n : ℝ) ^ (3 / 2 : ℝ)

/-- `F₁ = ∑ Λ(n) log n · n^{-3/2} = (ζ'/ζ)'(3/2)`. -/
noncomputable def r11Zs_F1 : ℝ := ∑' n : ℕ, Λ n * Real.log n / (n : ℝ) ^ (3 / 2 : ℝ)

lemma r11Zs_hasDerivAt_congr {f g : ℂ → ℂ} {f' g' x : ℂ} (h : HasDerivAt f f' x)
    (hfg : ∀ y, g y = f y) (h' : g' = f') : HasDerivAt g g' x := by
  have : g = f := funext hfg
  rw [this, h']; exact h

lemma r11Zs_three_halves : ((3 / 2 : ℝ) : ℂ) = 3 / 2 := by norm_num

lemma r11Zs_re_three_halves : (3 / 2 : ℂ).re = 3 / 2 := by
  rw [← r11Zs_three_halves, Complex.ofReal_re]

lemma r11Zs_one_lt_re : 1 < (3 / 2 : ℂ).re := by
  rw [r11Zs_re_three_halves]; norm_num

lemma r11Zs_eventually_re : ∀ᶠ s : ℂ in 𝓝 (3 / 2), 1 < s.re :=
  (isOpen_lt continuous_const continuous_re).mem_nhds r11Zs_one_lt_re

/-! ## Dirichlet series -/

section series

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma r11Zs_term_re (f : ℕ → ℝ) (n : ℕ) :
    (LSeries.term (fun n : ℕ => χ (n : ZMod N) * (f n : ℂ)) (3 / 2) n).re
      = f n * (χ (n : ZMod N)).re / (n : ℝ) ^ (3 / 2 : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow]
  · rw [LSeries.term_of_ne_zero hn, ← r11Zs_three_halves,
      ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    have e : χ (n : ZMod N) * (f n : ℂ) / (((n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ)
        = χ (n : ZMod N) * ((f n / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.re_mul_ofReal]
    ring

lemma r11Zs_LSeries_re (f : ℕ → ℝ)
    (h : LSeriesSummable (fun n : ℕ => χ (n : ZMod N) * (f n : ℂ)) (3 / 2)) :
    Summable (fun n : ℕ => f n * (χ (n : ZMod N)).re / (n : ℝ) ^ (3 / 2 : ℝ)) ∧
    (LSeries (fun n : ℕ => χ (n : ZMod N) * (f n : ℂ)) (3 / 2)).re
      = ∑' n : ℕ, f n * (χ (n : ZMod N)).re / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have h1 : Summable fun n : ℕ =>
      (LSeries.term (fun n : ℕ => χ (n : ZMod N) * (f n : ℂ)) (3 / 2) n).re :=
    Complex.reCLM.summable h
  simp_rw [r11Zs_term_re] at h1
  refine ⟨h1, ?_⟩
  rw [LSeries, Complex.re_tsum h]
  exact tsum_congr fun n => r11Zs_term_re χ f n

lemma r11Zs_twist_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => χ (n : ZMod N) * ((Λ n : ℝ) : ℂ)) s :=
  LSeriesSummable_twist_vonMangoldt χ hs

lemma r11Zs_twist_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ (n : ZMod N) * ((Λ n : ℝ) : ℂ)) s
      = -deriv (LFunction χ) s / LFunction χ s := by
  have h := LSeries_twist_vonMangoldt_eq χ hs
  rw [← deriv_LFunction_eq_deriv_LSeries χ hs, ← LFunction_eq_LSeries χ hs] at h
  exact h

lemma r11Zs_abscissa :
    LSeries.abscissaOfAbsConv (fun n : ℕ => χ (n : ZMod N) * ((Λ n : ℝ) : ℂ))
      < ((3 / 2 : ℂ).re : EReal) := by
  have h : LSeries.abscissaOfAbsConv (fun n : ℕ => χ (n : ZMod N) * ((Λ n : ℝ) : ℂ))
      ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => r11Zs_twist_summable χ (by simpa using hy))
  refine lt_of_le_of_lt h ?_
  rw [EReal.coe_lt_coe_iff]
  exact r11Zs_one_lt_re

lemma r11Zs_logMul_eq :
    LSeries.logMul (fun n : ℕ => χ (n : ZMod N) * ((Λ n : ℝ) : ℂ))
      = fun n : ℕ => χ (n : ZMod N) * ((Λ n * Real.log n : ℝ) : ℂ) := by
  funext n
  rw [LSeries.logMul, ← Complex.natCast_log]
  push_cast
  ring

/-- `Re L'/L(3/2, χ) = -∑ Λ(n) Re χ(n) n^{-3/2}`. -/
theorem r11Zs_logDeriv_re :
    Summable (fun n : ℕ => Λ n * (χ (n : ZMod N)).re / (n : ℝ) ^ (3 / 2 : ℝ)) ∧
    (deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)).re
      = -∑' n : ℕ, Λ n * (χ (n : ZMod N)).re / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hs := r11Zs_one_lt_re
  obtain ⟨h1, h2⟩ := r11Zs_LSeries_re χ (fun n => Λ n) (r11Zs_twist_summable χ hs)
  refine ⟨h1, ?_⟩
  rw [r11Zs_twist_eq χ hs, neg_div, neg_re] at h2
  linarith

/-- `(L'/L)'(3/2, χ)` exists and has real part `∑ Λ(n) log n Re χ(n) n^{-3/2}`. -/
theorem r11Zs_logDeriv_hasDerivAt :
    Summable (fun n : ℕ => Λ n * Real.log n * (χ (n : ZMod N)).re / (n : ℝ) ^ (3 / 2 : ℝ)) ∧
    ∃ d : ℂ, HasDerivAt (fun s : ℂ => deriv (LFunction χ) s / LFunction χ s) d (3 / 2) ∧
      d.re = ∑' n : ℕ, Λ n * Real.log n * (χ (n : ZMod N)).re / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have habs := r11Zs_abscissa χ
  have hsum := LSeriesSummable_logMul_of_lt_re habs
  rw [r11Zs_logMul_eq] at hsum
  obtain ⟨h1, h2⟩ := r11Zs_LSeries_re χ (fun n => Λ n * Real.log n) hsum
  refine ⟨h1, _, ?_, h2⟩
  have hd := (LSeries_hasDerivAt habs).neg
  rw [r11Zs_logMul_eq, neg_neg] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [r11Zs_eventually_re] with s hs
  show deriv (LFunction χ) s / LFunction χ s
    = -LSeries (fun n : ℕ => χ (n : ZMod N) * ((Λ n : ℝ) : ℂ)) s
  rw [r11Zs_twist_eq χ hs]
  ring

end series

lemma r11Zs_one_apply (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton _)

/-! ## Gamma factors -/

lemma r11Zs_Gammaℝ_hasDerivAt {a : ℂ} (ha : 0 < a.re) :
    HasDerivAt (fun s : ℂ => deriv Gammaℝ s / Gammaℝ s) (deriv digamma (a / 2) / 4) a := by
  have h1 : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) a := (hasDerivAt_id a).div_const 2
  have hmem : (0 : ℝ) < (a / 2).re := by
    have : (a / 2).re = a.re / 2 := by simp
    rw [this]; linarith
  have h2 : HasDerivAt digamma (deriv digamma (a / 2)) (a / 2) :=
    (differentiableOn_digamma.differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hmem)).hasDerivAt
  have h3 : HasDerivAt (fun s : ℂ => digamma (s / 2)) (deriv digamma (a / 2) * (1 / 2)) a :=
    h2.comp a h1
  have h4 : HasDerivAt (fun s : ℂ => -(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2)
      (deriv digamma (a / 2) * (1 / 2) / 2) a := (h3.div_const 2).const_add _
  refine (h4.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds ha] with s hs
  exact logDeriv_Gammaℝ hs

lemma r11Zs_gammaFactor_hasDerivAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ a : ℂ, (a = 3 / 4 ∨ a = 5 / 4) ∧
      HasDerivAt (fun s : ℂ => deriv (gammaFactor χ) s / gammaFactor χ s)
        (deriv digamma a / 4) (3 / 2) := by
  rcases χ.even_or_odd with he | ho
  · have hfun : gammaFactor χ = Gammaℝ := funext fun s => he.gammaFactor_def s
    refine ⟨3 / 4, Or.inl rfl, ?_⟩
    rw [hfun]
    have h := r11Zs_Gammaℝ_hasDerivAt (a := 3 / 2) (by rw [r11Zs_re_three_halves]; norm_num)
    rwa [show (3 / 2 : ℂ) / 2 = 3 / 4 by norm_num] at h
  · have hfun : gammaFactor χ = fun s => Gammaℝ (s + 1) := funext fun s => ho.gammaFactor_def s
    refine ⟨5 / 4, Or.inr rfl, ?_⟩
    rw [hfun]
    have hre : (0 : ℝ) < ((3 / 2 : ℂ) + 1).re := by
      rw [add_re, r11Zs_re_three_halves, one_re]; norm_num
    have h := r11Zs_Gammaℝ_hasDerivAt (a := 3 / 2 + 1) hre
    rw [show ((3 / 2 : ℂ) + 1) / 2 = 5 / 4 by norm_num] at h
    have h2 := h.comp_add_const (3 / 2 : ℂ) 1
    refine r11Zs_hasDerivAt_congr h2 (fun s => ?_) rfl
    rw [deriv_comp_add_const]

/-! ## ζ -/

/-- `∑ m_ρ Re 1/(3/2-ρ) = 8/3 - ½ log π + ½ Re ψ(3/4) - F₀` for ζ (unconditional). -/
theorem r11Zs_zeta_S1 :
    ∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re
      = 8 / 3 - Real.log Real.pi / 2 + (digamma (3 / 4)).re / 2 - r11Zs_F0 := by
  have hs := r11Zs_one_lt_re
  obtain ⟨-, hre⟩ := re_partialFraction llsZeta_summable llsZeta_summable_re_inv (3 / 2)
  have e1 := llsZeta_hadamard (s := 3 / 2) (llsZeta_xi_ne_zero_of_one_le_re hs.le)
  have e2 := llsZeta_logDeriv_xi hs
  have e3 := logDeriv_Gammaℝ (s := 3 / 2) (by linarith)
  have e4 := (r11Zs_logDeriv_re (1 : DirichletCharacter ℂ 1)).2
  rw [LFunction_modOne_eq] at e4
  have e5 : ∑' n : ℕ, Λ n * ((1 : DirichletCharacter ℂ 1) (n : ZMod 1)).re
      / (n : ℝ) ^ (3 / 2 : ℝ) = r11Zs_F0 :=
    tsum_congr fun n => by rw [r11Zs_one_apply, one_re, mul_one]
  rw [e5] at e4
  have hB := llsZeta_B_eq_neg_tsum
  have h1 := congrArg Complex.re e1
  rw [add_re, ofReal_re, hre, e2, e3, show (3 / 2 : ℂ) / 2 = 3 / 4 by norm_num,
    show (1 / (3 / 2 : ℂ) + 1 / ((3 / 2 : ℂ) - 1)) = ((8 / 3 : ℝ) : ℂ) by norm_num,
    add_re, add_re, add_re, ofReal_re, e4] at h1
  have h2 : (-(Real.log Real.pi : ℂ) / 2).re = -Real.log Real.pi / 2 := by
    rw [← Complex.ofReal_neg, show ((-(Real.log Real.pi) : ℝ) : ℂ) / 2
      = (((-(Real.log Real.pi)) / 2 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have h3 : (digamma (3 / 4) / 2).re = (digamma (3 / 4)).re / 2 := by simp
  rw [h2, h3] at h1
  linarith

/-- `Re ∑ m_ρ/(3/2-ρ)² = 40/9 - ¼ Re ψ'(3/4) - F₁` for ζ (unconditional). -/
theorem r11Zs_zeta_S2 :
    (∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (1 / ((3 / 2 : ℂ) - ρ) ^ 2)).re
      = 40 / 9 - (deriv digamma (3 / 4)).re / 4 - r11Zs_F1 := by
  have hT := r11Zs_hasDerivAt_tsum llsZeta_summable
    (fun ρ h => r11Zs_zeroOrd_strip (1 : DirichletCharacter ℂ 1) h)
  have hA : HasDerivAt (fun s : ℂ => deriv llsZeta_xi s / llsZeta_xi s)
      (-∑' ρ : ℂ, (zeroOrd (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (1 / ((3 / 2 : ℂ) - ρ) ^ 2))
      (3 / 2) := by
    refine (hT.const_add (llsZeta_B : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [r11Zs_eventually_re] with s hs
    exact llsZeta_hadamard (llsZeta_xi_ne_zero_of_one_le_re hs.le)
  obtain ⟨-, d, hd, hdre⟩ := r11Zs_logDeriv_hasDerivAt (1 : DirichletCharacter ℂ 1)
  rw [LFunction_modOne_eq] at hd
  have e5 : ∑' n : ℕ, Λ n * Real.log n * ((1 : DirichletCharacter ℂ 1) (n : ZMod 1)).re
      / (n : ℝ) ^ (3 / 2 : ℝ) = r11Zs_F1 :=
    tsum_congr fun n => by rw [r11Zs_one_apply, one_re, mul_one]
  rw [e5] at hdre
  have hΓ := r11Zs_Gammaℝ_hasDerivAt (a := 3 / 2) (by rw [r11Zs_re_three_halves]; norm_num)
  rw [show (3 / 2 : ℂ) / 2 = 3 / 4 by norm_num] at hΓ
  have a1 : HasDerivAt (fun s : ℂ => 1 / s) (-(4 / 9)) (3 / 2) :=
    r11Zs_hasDerivAt_congr (hasDerivAt_inv (𝕜 := ℂ) (x := 3 / 2) (by norm_num))
      (fun y => one_div y) (by norm_num)
  have a2 : HasDerivAt (fun s : ℂ => 1 / (s - 1)) (-4) (3 / 2) :=
    r11Zs_hasDerivAt_congr
      (((hasDerivAt_id (3 / 2 : ℂ)).sub_const 1).inv (by norm_num))
      (fun y => by simp [one_div]) (by norm_num)
  have hB : HasDerivAt (fun s : ℂ => 1 / s + 1 / (s - 1) + deriv Gammaℝ s / Gammaℝ s
      + deriv riemannZeta s / riemannZeta s)
      (-(4 / 9) + -4 + deriv digamma (3 / 4) / 4 + d) (3 / 2) :=
    ((a1.add a2).add hΓ).add hd
  have hB' : HasDerivAt (fun s : ℂ => deriv llsZeta_xi s / llsZeta_xi s)
      (-(4 / 9) + -4 + deriv digamma (3 / 4) / 4 + d) (3 / 2) := by
    refine hB.congr_of_eventuallyEq ?_
    filter_upwards [r11Zs_eventually_re] with s hs
    exact llsZeta_logDeriv_xi hs
  have huniq := congrArg Complex.re (hA.unique hB')
  have h3 : (deriv digamma (3 / 4) / 4).re = (deriv digamma (3 / 4)).re / 4 := by simp
  have h4 : (-(4 / 9 : ℂ) + -4).re = -(40 / 9) := by
    rw [show (-(4 / 9 : ℂ) + -4) = ((-(40 / 9) : ℝ) : ℂ) by norm_num, ofReal_re]
  rw [neg_re, add_re, add_re, h3, h4, hdre] at huniq
  linarith

/-! ## Primitive characters -/

section chi

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

lemma r11Zs_completed_logDeriv (hχ1 : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    deriv (completedLFunction χ) s / completedLFunction χ s
      = deriv (LFunction χ) s / LFunction χ s
        + deriv (gammaFactor χ) s / gammaFactor χ s := by
  have hs0 : 0 < s.re := by linarith
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

/-- `∑ m_ρ Re 1/(3/2-ρ) = ½ log q + Re L'/L(3/2) + Re γ'/γ(3/2)`. -/
theorem r11Zs_chi_S1 (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ((3 / 2 : ℂ) - ρ)).re
      = Real.log q / 2 + (deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)).re
        + (deriv (gammaFactor χ) (3 / 2) / gammaFactor χ (3 / 2)).re := by
  have h := re_logDeriv_eq_tsum_of_growth χ hχ hχ1 (growth_completedLFunction χ hχ1)
    (s := 3 / 2) r11Zs_one_lt_re
  rw [add_re] at h
  linarith

/-- `Re ∑ m_ρ/(3/2-ρ)² = -¼ Re ψ'(a) - ∑ Λ(n) log n Re χ(n) n^{-3/2}`, `a ∈ {3/4, 5/4}`. -/
theorem r11Zs_chi_S2 (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∃ a : ℂ, (a = 3 / 4 ∨ a = 5 / 4) ∧
      (∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / ((3 / 2 : ℂ) - ρ) ^ 2)).re
        = -(deriv digamma a).re / 4
          - ∑' n : ℕ, Λ n * Real.log n * (χ (n : ZMod q)).re / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hG := growth_completedLFunction χ hχ1
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 hG
  obtain ⟨B, hB⟩ := hadamardLogDeriv_of_growth χ hχ hχ1 hG
  have hT := r11Zs_hasDerivAt_tsum hS (fun ρ h => r11Zs_zeroOrd_strip χ h)
  have hA : HasDerivAt (fun s : ℂ => deriv (completedLFunction χ) s / completedLFunction χ s)
      (-∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / ((3 / 2 : ℂ) - ρ) ^ 2)) (3 / 2) := by
    refine (hT.const_add B).congr_of_eventuallyEq ?_
    filter_upwards [r11Zs_eventually_re] with s hs
    exact hB s (completed_ne_zero_of_one_le_re χ hχ1 hs.le)
  obtain ⟨-, d, hd, hdre⟩ := r11Zs_logDeriv_hasDerivAt χ
  obtain ⟨a, ha, hΓ⟩ := r11Zs_gammaFactor_hasDerivAt χ
  refine ⟨a, ha, ?_⟩
  have hB' : HasDerivAt (fun s : ℂ => deriv (completedLFunction χ) s / completedLFunction χ s)
      (d + deriv digamma a / 4) (3 / 2) := by
    refine (hd.add hΓ).congr_of_eventuallyEq ?_
    filter_upwards [r11Zs_eventually_re] with s hs
    exact r11Zs_completed_logDeriv χ hχ1 hs
  have huniq := congrArg Complex.re (hA.unique hB')
  have h3 : (deriv digamma a / 4).re = (deriv digamma a).re / 4 := by simp
  rw [neg_re, add_re, h3, hdre] at huniq
  linarith

end chi

end DetPrimality.Bach
