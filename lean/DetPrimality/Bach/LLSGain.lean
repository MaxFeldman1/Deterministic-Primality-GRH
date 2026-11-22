import DetPrimality.Bach.LLSGainPerron
import DetPrimality.Bach.SharpZeroSum

/-!
# LLS Lemma 3: the zero sum with the hypothesis gain

`llsGain_main : LLSZeroSumGain`.

With `Ξ = Λ'/Λ` (Mathlib's completed L-function, no conductor factor), `u = 1/x`:
`W(x, χ) = I[G(· + 1)](x) - ∑_ρ m_ρ x^{ρ-1}/(ρ(ρ-1)) - Ξ(1) + u Ξ(0)`
(`llsGain_formula2`), `Re Ξ(0) = -½ log q - ½ Z`, `Re Ξ(1) = -½ log q + ½ Z` under GRH
(`llsGain_re_xi`, `Z = zeroSumSq χ`), and
`Re I[G(· + 1)](x) ≤ -½ (1 - u) log π - 27/100` for `x ≥ 64` (`llsGain_gamma_bound`).
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "γ" => Real.eulerMascheroniConstant

/-! ## The zero terms -/

theorem llsGain_zero_term {ρ : ℂ} (hρ : 0 < ρ.re ∧ ρ.re < 1) {x : ℝ} (hx : 1 ≤ x) :
    perronI (fun s => 1 / (s - (ρ - 1)) - 1 / (2 - (ρ - 1))) x
      = (x : ℂ) ^ (ρ - 1) / ((ρ - 1) * ρ) + (1 / (1 - ρ) + 1 / ρ)
        - (1 - 1 / (x : ℂ)) * (1 / (3 - ρ) + 1 / ρ) := by
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have h0 : ρ ≠ 0 := ne_zero_of_re_pos hρ.1
  have h1' : 1 - ρ ≠ 0 := ne_zero_of_re_pos (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have h1 : ρ - 1 ≠ 0 := by
    intro h; apply h1'; linear_combination -h
  have h3 : 3 - ρ ≠ 0 := ne_zero_of_re_pos (by
    rw [Complex.sub_re, show (3 : ℂ).re = 3 by norm_num]; linarith)
  have hw1 : ρ - 1 + 1 ≠ 0 := by rwa [sub_add_cancel]
  have hw : (ρ - 1).re < 2 := by rw [Complex.sub_re, Complex.one_re]; linarith
  rw [perronI_inv_sub_sub hw h1 hw1 hx, show ρ - 1 + 1 = ρ by ring,
    show (2 : ℂ) - (ρ - 1) = 3 - ρ by ring]
  field_simp
  ring

theorem llsGain_norm_sub_one (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) :
    1 - ρ = (starRingEnd ℂ) ρ := by
  have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h
  refine Complex.ext ?_ ?_
  · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hρ]; norm_num
  · simp

/-- The explicit formula for `W(x, χ)` in terms of `Ξ = Λ'/Λ` at `0` and `1`. -/
theorem llsGain_formula2 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ X : ℂ, ‖X‖ ≤ 1 / √x * zeroSumSq χ ∧
      weightedLogSum χ x
        = perronI (fun s => Gfun χ (s + 1) - Gfun χ 3) x + (1 - 1 / (x : ℂ)) * Gfun χ 3 - X
          - deriv (completedLFunction χ) 1 / completedLFunction χ 1
          + 1 / (x : ℂ) * (deriv (completedLFunction χ) 0 / completedLFunction χ 0) := by
  have hx0 : 0 < x := by linarith
  have hG := growth_completedLFunction χ hχ1
  have hH := hadamardLogDeriv_of_growth χ hχ hχ1 hG
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 hG
  have hF := llsGain_formula χ hχ1 hH hS hx
  obtain ⟨B, hB⟩ := hH
  have hB1 := hB 1 (completed_ne_zero_of_one_le_re χ hχ1 (by simp))
  have hB0 := hB 0 (completed_zero_ne_zero hχ hχ1)
  have hz : ∀ ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (0 - ρ) + 1 / ρ) = 0 := by
    intro ρ
    rw [zero_sub, one_div, one_div, inv_neg, neg_add_cancel, mul_zero]
  simp only [hz, tsum_zero, add_zero] at hB0
  obtain ⟨hc3, hd3⟩ := logDeriv_completed_eq χ hχ1 (s := 3) (by norm_num)
  have hB3 := hB 3 hc3
  have hA : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ) :=
    Hadamard.summable_partialFraction hS 1
  have hC : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℂ) * (1 / (3 - ρ) + 1 / ρ) :=
    Hadamard.summable_partialFraction hS 3
  set Xf : ℂ → ℂ := fun ρ => (zeroOrd χ ρ : ℂ) * ((x : ℂ) ^ (ρ - 1) / ((ρ - 1) * ρ)) with hXf
  have hXn : ∀ ρ, ‖Xf ρ‖ ≤ 1 / √x * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [hXf, h0]
    · have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h0
      have hn1 : ‖ρ - 1‖ = ‖ρ‖ := by
        rw [← norm_neg, neg_sub, llsGain_norm_sub_one hGRH χ h0, Complex.norm_conj]
      have hcpow : ‖(x : ℂ) ^ (ρ - 1)‖ = 1 / √x := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re, hρ,
          show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hx0.le,
          ← Real.sqrt_eq_rpow, one_div]
      simp only [hXf]
      rw [norm_mul, norm_div, norm_mul, hcpow, hn1, Complex.norm_natCast]
      apply le_of_eq
      ring
  have hXs : Summable Xf := Summable.of_norm_bounded (hS.mul_left (1 / √x)) hXn
  have hXle : ‖∑' ρ, Xf ρ‖ ≤ 1 / √x * zeroSumSq χ := by
    calc ‖∑' ρ, Xf ρ‖ ≤ ∑' ρ, ‖Xf ρ‖ := norm_tsum_le_tsum_norm hXs.norm
      _ ≤ ∑' ρ : ℂ, 1 / √x * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) :=
          hXs.norm.tsum_le_tsum hXn (hS.mul_left _)
      _ = 1 / √x * zeroSumSq χ := by rw [tsum_mul_left]; rfl
  refine ⟨∑' ρ, Xf ρ, hXle, ?_⟩
  have hterm : ∀ ρ : ℂ, (zeroOrd χ ρ : ℂ)
      * perronI (fun s => 1 / (s - (ρ - 1)) - 1 / (2 - (ρ - 1))) x
      = Xf ρ + (zeroOrd χ ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)
        - (1 - 1 / (x : ℂ)) * ((zeroOrd χ ρ : ℂ) * (1 / (3 - ρ) + 1 / ρ)) := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [hXf, h0]
    · rw [llsGain_zero_term (zeroOrd_strip h0) hx]
      simp only [hXf]
      ring
  have hsum : HasSum (fun ρ : ℂ => Xf ρ + (zeroOrd χ ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)
        - (1 - 1 / (x : ℂ)) * ((zeroOrd χ ρ : ℂ) * (1 / (3 - ρ) + 1 / ρ)))
      ((∑' ρ, Xf ρ) + ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)
        - (1 - 1 / (x : ℂ)) * ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (3 - ρ) + 1 / ρ)) :=
    (hXs.hasSum.add hA.hasSum).sub (hC.hasSum.mul_left _)
  rw [tsum_congr hterm, hsum.tsum_eq] at hF
  rw [hF]
  linear_combination hB1 - (1 - 1 / (x : ℂ)) * hB3 + (1 - 1 / (x : ℂ)) * hd3
    - 1 / (x : ℂ) * hB0

/-- Under GRH: `Re Ξ(0) = -½ log q - ½ Z` and `Re Ξ(1) = -½ log q + ½ Z`. -/
theorem llsGain_re_xi (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    (deriv (completedLFunction χ) 0 / completedLFunction χ 0).re
        = -Real.log q / 2 - zeroSumSq χ / 2 ∧
    (deriv (completedLFunction χ) 1 / completedLFunction χ 1).re
        = -Real.log q / 2 + zeroSumSq χ / 2 := by
  have hG := growth_completedLFunction χ hχ1
  have hH := hadamardLogDeriv_of_growth χ hχ hχ1 hG
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 hG
  obtain ⟨B, hB⟩ := hH
  have hΛ1 : completedLFunction χ 1 ≠ 0 := completed_ne_zero_of_one_le_re χ hχ1 (by simp)
  have hB1 := hB 1 hΛ1
  have hB0 := hB 0 (completed_zero_ne_zero hχ hχ1)
  have hz : ∀ ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (0 - ρ) + 1 / ρ) = 0 := by
    intro ρ
    rw [zero_sub, one_div, one_div, inv_neg, neg_add_cancel, mul_zero]
  simp only [hz, tsum_zero, add_zero] at hB0
  have hm : ∀ ρ, zeroOrd χ ρ ≠ 0 → |ρ.re| ≤ 1 := by
    intro ρ h
    obtain ⟨h1, h2⟩ := zeroOrd_strip h
    rw [abs_le]; constructor <;> linarith
  have hd := summable_re_inv hS hm
  obtain ⟨ha, hre1⟩ := re_partialFraction hS hd 1
  have hsum0 : ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / ρ).re = zeroSumSq χ / 2 := by
    unfold zeroSumSq
    rw [← tsum_div_const]
    refine tsum_congr fun ρ => ?_
    by_cases h : zeroOrd χ ρ = 0
    · simp [h]
    · have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h
      rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, hρ]
      ring
  have hsum1 : ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (1 - ρ)).re = zeroSumSq χ / 2 := by
    unfold zeroSumSq
    rw [← tsum_div_const]
    refine tsum_congr fun ρ => ?_
    by_cases h : zeroOrd χ ρ = 0
    · simp [h]
    · have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h
      rw [llsGain_norm_sub_one hGRH χ h, one_div, Complex.inv_re, Complex.conj_re,
        Complex.normSq_conj, Complex.normSq_eq_norm_sq, hρ]
      ring
  have hrefl := congrArg Complex.re (logDeriv_completed_reflect hχ hχ1 hΛ1)
  rw [show (1 : ℂ) - (starRingEnd ℂ) 1 = 0 by simp, Complex.sub_re, Complex.neg_re,
    Complex.ofReal_re, Complex.conj_re] at hrefl
  have h1re : (deriv (completedLFunction χ) 1 / completedLFunction χ 1).re
      = B.re + (zeroSumSq χ / 2 + zeroSumSq χ / 2) := by
    rw [hB1, Complex.add_re, hre1, hsum0, hsum1]
  rw [hB0] at hrefl ⊢
  constructor <;> linarith

/-! ## The Γ-part: numerics -/

theorem llsGain_hasSum_tele2 :
    HasSum (fun j : ℕ => 1 / (((j : ℝ) + 2) * ((j : ℝ) + 3))) (1 / 2) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_telescope
  have hv : (1 : ℝ) - ∑ i ∈ Finset.range 1, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = 1 / 2 := by
    norm_num
  rw [hv] at h
  have e : (fun j : ℕ => 1 / (((j : ℝ) + 2) * ((j : ℝ) + 3)))
      = fun n : ℕ => 1 / ((((n + 1 : ℕ) : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) + 2)) := by
    funext j
    congr 1
    push_cast
    ring
  rw [e]
  exact h

theorem llsGain_rterm_le {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx0 : 0 < x) :
    rterm m x ≤ -2 / ((m : ℝ) * ((m : ℝ) + 2)) + 3 / (((m : ℝ) - 1) * ((m : ℝ) + 2)) * (1 / x) := by
  rw [rterm_of_two_le hm]
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 ≤ x ^ (-(m : ℝ)) / ((m : ℝ) * ((m : ℝ) - 1)) :=
    div_nonneg (Real.rpow_pos_of_pos hx0 _).le (mul_nonneg (by linarith) (by linarith))
  have e : 3 / (((m : ℝ) - 1) * ((m : ℝ) + 2) * x)
      = 3 / (((m : ℝ) - 1) * ((m : ℝ) + 2)) * (1 / x) := by rw [mul_one_div, div_div]
  rw [e]
  linarith

theorem llsGain_tail_odd (j : ℕ) {x : ℝ} (hx0 : 0 < x) :
    rterm (2 * (j + 1) + 1 + 1) x
      ≤ (-1 / 2 + 1 / x) * (1 / (((j : ℝ) + 2) * ((j : ℝ) + 3))) := by
  have h := llsGain_rterm_le (m := 2 * (j + 1) + 1 + 1) (by omega) hx0
  have hM : ((2 * (j + 1) + 1 + 1 : ℕ) : ℝ) = 2 * (j : ℝ) + 4 := by push_cast; ring
  rw [hM] at h
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hu0 : 0 ≤ 1 / x := by positivity
  have e1 : (-2 : ℝ) / ((2 * (j : ℝ) + 4) * (2 * (j : ℝ) + 4 + 2))
      = -1 / 2 * (1 / (((j : ℝ) + 2) * ((j : ℝ) + 3))) := by
    field_simp
    ring
  have hpos : (0 : ℝ) < (2 * (j : ℝ) + 4 - 1) * (2 * (j : ℝ) + 4 + 2) := by
    have : (0 : ℝ) < 2 * (j : ℝ) + 4 - 1 := by linarith
    positivity
  have e2 : (3 : ℝ) / ((2 * (j : ℝ) + 4 - 1) * (2 * (j : ℝ) + 4 + 2))
      ≤ 1 / (((j : ℝ) + 2) * ((j : ℝ) + 3)) := by
    rw [div_le_div_iff₀ hpos (by positivity)]
    nlinarith [mul_nonneg hj hj]
  have e3 := mul_le_mul_of_nonneg_right e2 hu0
  rw [e1] at h
  calc rterm (2 * (j + 1) + 1 + 1) x
      ≤ -1 / 2 * (1 / (((j : ℝ) + 2) * ((j : ℝ) + 3)))
        + 1 / (((j : ℝ) + 2) * ((j : ℝ) + 3)) * (1 / x) := by linarith
    _ = (-1 / 2 + 1 / x) * (1 / (((j : ℝ) + 2) * ((j : ℝ) + 3))) := by ring

theorem llsGain_tail_even (j : ℕ) {x : ℝ} (hx0 : 0 < x) :
    rterm (2 * (j + 1) + 0 + 1) x
      ≤ (3 / 4 * (1 / x)) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
  have h := llsGain_rterm_le (m := 2 * (j + 1) + 0 + 1) (by omega) hx0
  have hM : ((2 * (j + 1) + 0 + 1 : ℕ) : ℝ) = 2 * (j : ℝ) + 3 := by push_cast; ring
  rw [hM] at h
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hu0 : 0 ≤ 1 / x := by positivity
  have e1 : (-2 : ℝ) / ((2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 3 + 2)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have hpos : (0 : ℝ) < (2 * (j : ℝ) + 3 - 1) * (2 * (j : ℝ) + 3 + 2) := by
    have : (0 : ℝ) < 2 * (j : ℝ) + 3 - 1 := by linarith
    positivity
  have e2 : (3 : ℝ) / ((2 * (j : ℝ) + 3 - 1) * (2 * (j : ℝ) + 3 + 2))
      ≤ (3 / 4) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    rw [div_le_div_iff₀ hpos (by positivity)]
    nlinarith [mul_nonneg hj hj]
  have e3 := mul_le_mul_of_nonneg_right e2 hu0
  calc rterm (2 * (j + 1) + 0 + 1) x
      ≤ (3 / 4) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * (1 / x) := by linarith
    _ = (3 / 4 * (1 / x)) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by ring

/-- `Re I[G(· + 1)](x) ≤ -½ (1 - 1/x) log π - 27/100` for `x ≥ 64`
(i.e. `E_a(x) ≤ -27/100` in LLS's notation). -/
theorem llsGain_gamma_bound {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 64 ≤ x) :
    (perronI (fun s => Gfun χ (s + 1) - Gfun χ 3) x).re + (1 - 1 / x) * (Gfun χ 3).re
      ≤ -(1 - 1 / x) * Real.log Real.pi / 2 - 27 / 100 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hu0 : 0 ≤ 1 / x := by positivity
  have hu : 1 / x ≤ 1 / 64 := one_div_le_one_div_of_le (by norm_num) hx
  have hS := llsGain_hasSum_perronI_gamma χ hx1
  simp only [perronI_gterm _ hx1] at hS
  have hR := Complex.hasSum_re hS
  simp only [Complex.ofReal_re] at hR
  have hG3 := Gfun_eq χ (s := 3) (by norm_num)
  have hγ1 := szs_gamma_gt
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hdiv2 : ∀ z : ℂ, (z / 2).re = z.re / 2 := fun z => by simp
  rcases gammaShift_cases χ with h0 | h1
  · -- even character: `E₀`
    simp only [h0] at hR
    have hhalf : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -m := fun m h => by
      have h1 := congrArg Complex.re h
      have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      norm_num at h1
      linarith
    have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; norm_num
    have hval : digamma ((3 : ℂ) / 2) = ((-2 * Real.log 2 - γ + 2 : ℝ) : ℂ) := by
      rw [show (3 : ℂ) / 2 = 1 / 2 + 1 by norm_num, digamma_apply_add_one _ hhalf,
        digamma_one_half, hlog]
      norm_num
    rw [h0, Nat.cast_zero, add_zero, hval] at hG3
    have hG3r : (Gfun χ 3).re = -Real.log Real.pi / 2 + (-2 * Real.log 2 - γ + 2) / 2 := by
      rw [hG3, Complex.add_re, hdiv2, hdiv2, Complex.neg_re, Complex.ofReal_re,
        Complex.ofReal_re]
    have hf0 : rterm (2 * 0 + 0 + 1) x = -2 / 3 + Real.log x / x + 2 / (3 * x) := rterm_one x
    have htail : Summable fun j : ℕ => rterm (2 * (j + 1) + 0 + 1) x :=
      (summable_nat_add_iff (f := fun k : ℕ => rterm (2 * k + 0 + 1) x) 1).mpr hR.summable
    have hT := hasSum_telescope
    have hup : ∑' j : ℕ, rterm (2 * (j + 1) + 0 + 1) x ≤ 3 / 4 * (1 / x) := by
      have := htail.tsum_le_tsum (fun j => llsGain_tail_even j hx0) (hT.summable.mul_left _)
      rw [tsum_mul_left, hT.tsum_eq, mul_one] at this
      exact this
    have hsum := hR.tsum_eq
    rw [hR.summable.tsum_eq_zero_add, hf0] at hsum
    have hsq : 8 ≤ √x := (Real.le_sqrt' (by norm_num)).mpr (by norm_num; linarith)
    have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
    have hls := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    rw [Real.log_sqrt hx0.le] at hls
    have hlx : Real.log x / x ≤ 1 / 4 := by
      rw [div_le_iff₀ hx0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (Real.sqrt_nonneg x)]
    have e : 2 / (3 * x) = 2 / 3 * (1 / x) := by ring
    have hc : (-2 * Real.log 2 - γ + 2) / 2 ≤ 2 / 100 := by
      linarith [Real.log_two_gt_d9]
    have hc' := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 - 1 / x by linarith)
    rw [hG3r]
    rw [e] at hsum
    nlinarith
  · -- odd character: `E₁`
    simp only [h1] at hR
    have hone : ∀ m : ℕ, (1 : ℂ) ≠ -m := fun m h => by
      have h1 := congrArg Complex.re h
      have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at h1
      linarith
    have hval : digamma (((3 : ℂ) + 1) / 2) = ((-γ + 1 : ℝ) : ℂ) := by
      rw [show ((3 : ℂ) + 1) / 2 = 1 + 1 by norm_num, digamma_apply_add_one _ hone,
        digamma_one]
      norm_num
    rw [h1, Nat.cast_one, hval] at hG3
    have hG3r : (Gfun χ 3).re = -Real.log Real.pi / 2 + (-γ + 1) / 2 := by
      rw [hG3, Complex.add_re, hdiv2, hdiv2, Complex.neg_re, Complex.ofReal_re,
        Complex.ofReal_re]
    have hf0 : rterm (2 * 0 + 1 + 1) x ≤ -1 / 4 + 3 / 4 * (1 / x) := by
      have h := llsGain_rterm_le (m := 2) le_rfl hx0
      have e1 : (-2 : ℝ) / (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) + 2)) = -1 / 4 := by norm_num
      have e2 : (3 : ℝ) / ((((2 : ℕ) : ℝ) - 1) * (((2 : ℕ) : ℝ) + 2)) = 3 / 4 := by norm_num
      rw [e1, e2] at h
      exact h
    have htail : Summable fun j : ℕ => rterm (2 * (j + 1) + 1 + 1) x :=
      (summable_nat_add_iff (f := fun k : ℕ => rterm (2 * k + 1 + 1) x) 1).mpr hR.summable
    have hT := llsGain_hasSum_tele2
    have hup : ∑' j : ℕ, rterm (2 * (j + 1) + 1 + 1) x ≤ (-1 / 2 + 1 / x) * (1 / 2) := by
      have := htail.tsum_le_tsum (fun j => llsGain_tail_odd j hx0) (hT.summable.mul_left _)
      rw [tsum_mul_left, hT.tsum_eq] at this
      exact this
    have hsum := hR.tsum_eq
    rw [hR.summable.tsum_eq_zero_add] at hsum
    have huγ : 1 / x * γ ≤ 1 / x * (2 / 3) := mul_le_mul_of_nonneg_left hγ2.le hu0
    rw [hG3r]
    nlinarith

/-! ## Main theorem -/

/-- **LLS Lemma 3.** -/
theorem llsGain_main : LLSZeroSumGain := by
  intro hGRH q _ χ hχ hχ1 x hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨X, hXn, hW⟩ := llsGain_formula2 hGRH χ hχ hχ1 hx1
  obtain ⟨h0, h1⟩ := llsGain_re_xi hGRH χ hχ hχ1
  have hγ := llsGain_gamma_bound χ hx
  have hWre := congrArg Complex.re hW
  have e1 : ((1 - 1 / (x : ℂ)) * Gfun χ 3).re = (1 - 1 / x) * (Gfun χ 3).re := by
    rw [show (1 - 1 / (x : ℂ)) = ((1 - 1 / x : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  have e2 : (1 / (x : ℂ) * (deriv (completedLFunction χ) 0 / completedLFunction χ 0)).re
      = 1 / x * (deriv (completedLFunction χ) 0 / completedLFunction χ 0).re := by
    rw [show (1 / (x : ℂ)) = ((1 / x : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  simp only [Complex.add_re, Complex.sub_re] at hWre
  rw [e1, e2, h0, h1] at hWre
  have hXre : -(1 / √x * zeroSumSq χ) ≤ X.re :=
    (abs_le.mp ((Complex.abs_re_le_norm X).trans hXn)).1
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hlog : Real.log (q / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div hq Real.pi_ne_zero
  have e3 : 2 / √x = 2 * (1 / √x) := by ring
  rw [hlog, e3]
  nlinarith

#print axioms llsGain_main

end DetPrimality.Bach
