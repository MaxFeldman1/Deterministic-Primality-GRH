import DetPrimality.Bach.R11ZeroSumGamma
import DetPrimality.Bach.R11ZeroSumNum

/-!
# Round 11: the zero sums `Z₂`, `Z₄` (designB Lemmas 1 and 4)

* `r11Zs_zeta : R11ZetaZ` — under RH, `Z₂(ζ) ≤ 0.047`, `Z₄(ζ) ≤ 0.00012`
  (sharper: `r11Zs_zeta_sharp`, `Z₂ ≤ 0.04615`, `Z₄ ≤ 0.000081`);
* `r11Zs_gain : R11ZeroSumGain` — under GRH, for primitive `χ ≠ 1` mod `q` with `χ(n) = 1` for
  `1 ≤ n < X`: `Z₄(χ) ≤ (log q - 12.4 + 4 T(X))/4` (sharper: `r11Zs_gain_sharp`, `κ = 12.689`).

Proof: `1/(1+γ²)² = ½ [Re (3/2-ρ)⁻¹ + Re (3/2-ρ)⁻²]` (`R11ZeroSumHad`), the Hadamard series and
its termwise derivative at `3/2` (`R11ZeroSumSeries`), certified values of `ψ`, `ψ'`, `log π`
(`R11ZeroSumGamma`) and of `F₀ = -ζ'/ζ(3/2)`, `F₁ = (ζ'/ζ)'(3/2)` (`R11ZeroSumNum`).
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## ζ -/

/-- Under RH: `Z₂(ζ) = 8/3 - ½ log π + ½ ψ(3/4) - F₀`. -/
theorem r11Zs_zeta_Z2_eq (hGRH : DirichletLZerosOnLine) :
    r11Z (1 : DirichletCharacter ℂ 1) 2
      = 8 / 3 - Real.log Real.pi / 2 + (digamma (3 / 4)).re / 2 - r11Zs_F0 := by
  rw [r11Zs_Z2_eq _ hGRH, r11Zs_zeta_S1]

/-- Under RH: `Z₄(ζ) = ½ [Z₂ + 40/9 - ¼ ψ'(3/4) - F₁]`. -/
theorem r11Zs_zeta_Z4_eq (hGRH : DirichletLZerosOnLine) :
    r11Z (1 : DirichletCharacter ℂ 1) 4
      = 1 / 2 * (r11Z (1 : DirichletCharacter ℂ 1) 2
        + (40 / 9 - (deriv digamma (3 / 4)).re / 4 - r11Zs_F1)) := by
  rw [r11Zs_Z4_eq _ hGRH llsZeta_summable, r11Zs_zeta_S2, r11Zs_Z2_eq _ hGRH]

/-- Under RH: `Z₂(ζ) ≤ 0.04615`, `Z₄(ζ) ≤ 0.000081` (true: `0.046136`, `0.0000738`). -/
theorem r11Zs_zeta_sharp (hGRH : DirichletLZerosOnLine) :
    r11Z (1 : DirichletCharacter ℂ 1) 2 ≤ 0.04615 ∧
      r11Z (1 : DirichletCharacter ℂ 1) 4 ≤ 0.000081 := by
  have h2 := r11Zs_zeta_Z2_eq hGRH
  have h4 := r11Zs_zeta_Z4_eq hGRH
  have hπ := r11Zs_log_pi_gt
  have hψ := r11Zs_digamma_three_quarters
  have hψ' := r11Zs_trigamma_three_quarters
  obtain ⟨hF0, -⟩ := r11Zs_F0_bounds
  have hF1 := r11Zs_F1_lower
  have hZ2 : r11Z (1 : DirichletCharacter ℂ 1) 2 ≤ 0.04615 := by
    rw [h2]; norm_num at hπ hψ hF0 ⊢; linarith
  refine ⟨hZ2, ?_⟩
  rw [h4, h2]
  norm_num at hπ hψ hψ' hF0 hF1 ⊢
  linarith

/-- **designB Lemma 1.** -/
theorem r11Zs_zeta : R11ZetaZ := by
  intro hGRH
  obtain ⟨h2, h4⟩ := r11Zs_zeta_sharp hGRH
  constructor
  · exact h2.trans (by norm_num)
  · exact h4.trans (by norm_num)

/-! ## Summability of the two von Mangoldt series -/

theorem r11Zs_F0_summable : Summable fun n : ℕ => Λ n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have h := (r11Zs_logDeriv_re (1 : DirichletCharacter ℂ 1)).1
  simp_rw [r11Zs_one_apply, one_re, mul_one] at h
  exact h

theorem r11Zs_F1_summable :
    Summable fun n : ℕ => Λ n * Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have h := (r11Zs_logDeriv_hasDerivAt (1 : DirichletCharacter ℂ 1)).1
  simp_rw [r11Zs_one_apply, one_re, mul_one] at h
  exact h

/-! ## Primitive characters -/

section chi

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- **designB (4.1)**: under GRH,
`Z₄(χ) = ¼ log q + ½ Re γ'/γ(3/2) - ⅛ Re ψ'(a) - ½ ∑ Λ(n) Re χ(n) (1 + log n) n^{-3/2}`. -/
theorem r11Zs_chi_Z4_eq (hGRH : DirichletLZerosOnLine) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∃ a : ℂ, (a = 3 / 4 ∨ a = 5 / 4) ∧
      r11Z χ 4 = Real.log q / 4
        + (deriv (gammaFactor χ) (3 / 2) / gammaFactor χ (3 / 2)).re / 2
        - (deriv digamma a).re / 8
        - (∑' n : ℕ, Λ n * (χ (n : ZMod q)).re / (n : ℝ) ^ (3 / 2 : ℝ)
          + ∑' n : ℕ, Λ n * Real.log n * (χ (n : ZMod q)).re / (n : ℝ) ^ (3 / 2 : ℝ)) / 2 := by
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 (growth_completedLFunction χ hχ1)
  have hZ4 := r11Zs_Z4_eq χ hGRH hS
  obtain ⟨a, ha, hS2⟩ := r11Zs_chi_S2 χ hχ hχ1
  refine ⟨a, ha, ?_⟩
  rw [r11Zs_chi_S1 χ hχ hχ1, hS2, (r11Zs_logDeriv_re χ).2] at hZ4
  rw [hZ4]
  ring

/-- The Dirichlet series in (4.1) is `≥ F₀ + F₁ - 2 T(X)` when `χ(n) = 1` for `1 ≤ n < X`. -/
theorem r11Zs_series_ge {X : ℝ}
    (hone : ∀ n : ℕ, 1 ≤ n → (n : ℝ) < X → χ (n : ZMod q) = 1) :
    r11Zs_F0 + r11Zs_F1 - 2 * r11T X
      ≤ ∑' n : ℕ, Λ n * (χ (n : ZMod q)).re / (n : ℝ) ^ (3 / 2 : ℝ)
        + ∑' n : ℕ, Λ n * Real.log n * (χ (n : ZMod q)).re / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hs0 := (r11Zs_logDeriv_re χ).1
  have hs1 := (r11Zs_logDeriv_hasDerivAt χ).1
  have hF0 := r11Zs_F0_summable
  have hF1 := r11Zs_F1_summable
  have hw : ∀ n : ℕ, 0 ≤ Λ n / (n : ℝ) ^ (3 / 2 : ℝ) := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hT : Summable fun n : ℕ =>
      if X ≤ n then Λ n * (1 + Real.log n) / (n : ℝ) ^ ((3 : ℝ) / 2) else 0 := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hF0.add hF1)
    · split_ifs
      · exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (by linarith [Real.log_natCast_nonneg n])) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      · exact le_rfl
    · split_ifs
      · exact le_of_eq (by ring)
      · have := hw n
        have h2 : 0 ≤ Λ n * Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) :=
          div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.log_natCast_nonneg n)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        linarith
  rw [r11Zs_F0, r11Zs_F1, r11T, ← hF0.tsum_add hF1, ← tsum_mul_left,
    ← (hF0.add hF1).tsum_sub (hT.mul_left 2), ← hs0.tsum_add hs1]
  refine (((hF0.add hF1).sub (hT.mul_left 2))).tsum_le_tsum (fun n => ?_) (hs0.add hs1)
  have hwn := hw n
  have hL := Real.log_natCast_nonneg n
  set w := Λ n / (n : ℝ) ^ (3 / 2 : ℝ) with hwdef
  have e1 : Λ n * Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) = w * Real.log n := by rw [hwdef]; ring
  have e2 : Λ n * (χ (n : ZMod q)).re / (n : ℝ) ^ (3 / 2 : ℝ) = w * (χ (n : ZMod q)).re := by
    rw [hwdef]; ring
  have e3 : Λ n * Real.log n * (χ (n : ZMod q)).re / (n : ℝ) ^ (3 / 2 : ℝ)
      = w * Real.log n * (χ (n : ZMod q)).re := by rw [hwdef]; ring
  have e4 : Λ n * (1 + Real.log n) / (n : ℝ) ^ ((3 : ℝ) / 2) = w * (1 + Real.log n) := by
    rw [hwdef]; ring
  rw [e1, e2, e3, e4]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : w = 0 := by rw [hwdef]; simp
    rw [this]; simp
  · by_cases hX : X ≤ n
    · rw [if_pos hX]
      have hre : -1 ≤ (χ (n : ZMod q)).re := by
        have h1 := abs_re_le_norm (χ (n : ZMod q))
        have h2 := χ.norm_le_one (n : ZMod q)
        have := abs_le.mp (h1.trans h2)
        exact this.1
      have hp : 0 ≤ w * (1 + Real.log n) := mul_nonneg hwn (by linarith)
      nlinarith
    · rw [if_neg hX, hone n hn (not_le.mp hX), one_re]
      linarith

/-- **designB (4.2)** with `κ = 12.689` (true value `12.69124`). -/
theorem r11Zs_gain_sharp (hGRH : DirichletLZerosOnLine) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {X : ℝ} (hone : ∀ n : ℕ, 1 ≤ n → (n : ℝ) < X → χ (n : ZMod q) = 1) :
    r11Z χ 4 ≤ (Real.log q - 12.689 + 4 * r11T X) / 4 := by
  obtain ⟨a, ha, hZ4⟩ := r11Zs_chi_Z4_eq χ hGRH hχ hχ1
  have hser := r11Zs_series_ge χ hone
  have hγ := re_logDeriv_gammaFactor_three_halves_le_sharp χ
  have hψ : (1.19732 : ℝ) ≤ (deriv digamma a).re := by
    rcases ha with rfl | rfl
    · exact le_trans (by norm_num) r11Zs_trigamma_three_quarters
    · exact r11Zs_trigamma_five_quarters
  obtain ⟨hF0, -⟩ := r11Zs_F0_bounds
  have hF1 := r11Zs_F1_lower
  rw [hZ4]
  norm_num at hγ hψ hF0 hF1 ⊢
  linarith

end chi

/-- **designB Lemma 4, (4.2).** -/
theorem r11Zs_gain : R11ZeroSumGain := by
  intro hGRH q _ χ hχ hχ1 X _ hone
  have h := r11Zs_gain_sharp χ hGRH hχ hχ1 hone
  linarith

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r11Zs_zeta
#print axioms DetPrimality.Bach.r11Zs_gain
#print axioms DetPrimality.Bach.r11Zs_zeta_sharp
#print axioms DetPrimality.Bach.r11Zs_gain_sharp
