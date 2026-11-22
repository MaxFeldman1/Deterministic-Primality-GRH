import Mathlib
import DetPrimality.Bach.LLSDefs
import DetPrimality.Bach.LLSElem
import DetPrimality.Bach.SharpZeroSum

/-!
# Assembly of Lamzouri–Li–Soundararajan Theorem 1.1(2): Bach's bound with `c = 1`

From the four inputs of `LLSDefs.lean` (`LLSZetaLower (1/20)`, `LLSChiUpper`, `LLSZeroSumGain`,
`LLSWeightedLower`) we prove: for composite `n ≥ 3000` and `χ ≠ 1` mod `n` there is
`1 ≤ a < log² n` with `χ a ≠ 1` (`llsAsm_bachBound_one`).

With `L = log n ≥ 8`, `X = L²`, `ℓ = log L` (so `log X = 2ℓ`), `p = log π`, `u = log(q̃/π) ≤ L - p`
and `Z = zeroSumSq χ̃`:

* `llsAsm_zeroSum_le`: the gain inequality gives `Z ≤ L - 2ℓ - 8/7`
  (LLS: `|Re B| ≤ ½ log q - ½ log X - 4/7`), using `ℓ ≥ log 8 + 1 - 8/L`;
* `llsAsm_real_contra`: then the upper bound `S ≤ (L + 1 + ℓ) Z + u ℓ` contradicts the lower bound
  `S ≥ L² - (L + 1)/20 - 2 log(2π) ℓ - 1`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-! ## The real-variable contradiction -/

/-- LLS's intermediate bound `2|Re B| ≤ log q - log X - 8/7`, in real variables. -/
theorem llsAsm_zeroSum_le {L ℓ p Z u : ℝ} (hL : 8 ≤ L) (hℓ : 3.079 - 8 / L ≤ ℓ)
    (hp : 1.14396 ≤ p) (hu : u ≤ L - p)
    (hG : (1 + 1 / L ^ 2 - 2 / L) * (Z / 2)
      ≤ (1 - 1 / L ^ 2) * u / 2 - (2 * ℓ - 2) - 27 / 100) :
    Z ≤ L - 2 * ℓ - 8 / 7 := by
  have hL0 : 0 < L := by linarith
  have hL1 : 0 < L - 1 := by linarith
  have h1 : (L - 1) ^ 2 * Z ≤ (L ^ 2 - 1) * u - (4 * ℓ - 3.46) * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ 2 * L ^ 2)
    have e1 : 2 * L ^ 2 * ((1 + 1 / L ^ 2 - 2 / L) * (Z / 2)) = (L - 1) ^ 2 * Z := by
      field_simp; ring
    have e2 : 2 * L ^ 2 * ((1 - 1 / L ^ 2) * u / 2 - (2 * ℓ - 2) - 27 / 100)
        = (L ^ 2 - 1) * u - (4 * ℓ - 3.46) * L ^ 2 := by
      field_simp; ring
    rw [e1, e2] at this
    exact this
  have hsq : 0 ≤ L ^ 2 - 1 := by nlinarith
  have h2 : (L ^ 2 - 1) * u ≤ (L ^ 2 - 1) * (L - p) := mul_le_mul_of_nonneg_left hu hsq
  have h3 : (L ^ 2 - 1) * (L - p) ≤ (L ^ 2 - 1) * (L - 1.14396) :=
    mul_le_mul_of_nonneg_left (by linarith) hsq
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 8 / L := ⟨_, rfl⟩
  have hdL : d * L = 8 := by rw [hd]; field_simp
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  rw [← hd] at hℓ
  have h4 : 0 ≤ (2 * L ^ 2 + 4 * L - 2) * (ℓ - (3.079 - d)) :=
    mul_nonneg (by nlinarith) (by linarith)
  have h5 : 0 ≤ 2 * 3.079 * L ^ 2 + (4 * 3.079 - 16) * L - 2 * 3.079 - 32
      + (L - 1) ^ 2 * (L - 8 / 7) - (L ^ 2 - 1) * (L - 1.14396) - 3.46 * L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hL)]
  have key : (L - 1) ^ 2 * (L - 2 * ℓ - 8 / 7)
      - ((L ^ 2 - 1) * (L - 1.14396) - (4 * ℓ - 3.46) * L ^ 2)
      = (2 * L ^ 2 + 4 * L - 2) * (ℓ - (3.079 - d))
        + (2 * 3.079 * L ^ 2 + (4 * 3.079 - 16) * L - 2 * 3.079 - 32
          + (L - 1) ^ 2 * (L - 8 / 7) - (L ^ 2 - 1) * (L - 1.14396) - 3.46 * L ^ 2)
        + 2 * d := by
    linear_combination (-(2 * L + 4)) * hdL
  have h6 : (L - 1) ^ 2 * Z ≤ (L - 1) ^ 2 * (L - 2 * ℓ - 8 / 7) := by linarith
  exact le_of_mul_le_mul_left h6 (by positivity)

/-- The three LLS inequalities are contradictory for `L = log n ≥ 8` (`X = L² ≥ 64`).
Here `ℓ = log L`, `p = log π`, `l2 = log 2`, `u = log(q̃/π)`, `Z = ∑ 1/|ρ|²`, `S = Re S(X, χ̃)`. -/
theorem llsAsm_real_contra {L ℓ p l2 Z u S : ℝ} (hL : 8 ≤ L) (hℓ : 3.079 - 8 / L ≤ ℓ)
    (hp : 1.14396 ≤ p) (hp' : p ≤ 1.3864) (hl2 : l2 ≤ 0.6932) (hu : u ≤ L - p)
    (hG : (1 + 1 / L ^ 2 - 2 / L) * (Z / 2)
      ≤ (1 - 1 / L ^ 2) * u / 2 - (2 * ℓ - 2) - 27 / 100)
    (hU : S ≤ (L + 1 + ℓ) * Z + u * ℓ)
    (hZ : L ^ 2 - 1 / 20 * (L + 1) - (l2 + p) * (2 * ℓ) - 1 ≤ S) : False := by
  have hL0 : 0 < L := by linarith
  have h8 : 8 / L ≤ 1 := (div_le_one hL0).mpr hL
  have hℓ2 : 2.079 ≤ ℓ := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hZb := llsAsm_zeroSum_le hL hℓ hp hu hG
  have m1 : (L + 1 + ℓ) * Z ≤ (L + 1 + ℓ) * (L - 2 * ℓ - 8 / 7) :=
    mul_le_mul_of_nonneg_left hZb (by linarith)
  have m2 : u * ℓ ≤ (L - p) * ℓ := mul_le_mul_of_nonneg_right hu hℓ0
  have m3 : 0 ≤ (1.3864 - p) * ℓ := mul_nonneg (by linarith) hℓ0
  have m4 : 0 ≤ (0.6932 - l2) * ℓ := mul_nonneg (by linarith) hℓ0
  nlinarith [sq_nonneg ℓ]

/-! ## Numerical facts -/

theorem llsAsm_log_3000 : (8 : ℝ) ≤ Real.log 3000 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 8 = Real.exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  have h2 : Real.exp 1 ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 8
  have h3 : (2.7182818286 : ℝ) ^ 8 ≤ 3000 := by norm_num
  exact h2.trans h3

theorem llsAsm_log_pi_le : Real.log Real.pi ≤ 1.3864 := by
  have h1 : Real.log Real.pi ≤ Real.log ((2 : ℝ) ^ 2) :=
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_d2])
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith [Real.log_two_lt_d9]

theorem llsAsm_loglog_ge {L : ℝ} (hL : 8 ≤ L) : 3.079 - 8 / L ≤ Real.log L := by
  have hL0 : 0 < L := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (x := L / 8) (by positivity)
  rw [Real.log_div hL0.ne' (by norm_num), inv_div] at h1
  have h2 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_gt_d9]

/-! ## Assembly -/

/-- **LLS Theorem 1.1(2), character form**: under GRH (and the four LLS inputs), for composite
`n ≥ 3000` every `χ ≠ 1` mod `n` has a witness `1 ≤ a < log² n` with `χ a ≠ 1`. -/
theorem llsAsm_bachBound_one (hGRH : DirichletLZerosOnLine)
    (hZ : LLSZetaLower (1 / 20)) (hU : LLSChiUpper) (hG : LLSZeroSumGain) (hW : LLSWeightedLower) :
    ∀ n : ℕ, 3000 ≤ n → ¬ n.Prime → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1 := by
  intro n hn _ χ hχ
  by_contra hcon
  have hcon' : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < Real.log n ^ 2 → χ (a : ZMod n) = 1 := by
    intro a ha hax
    by_contra h
    exact hcon ⟨a, ha, hax, h⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 8 ≤ Real.log n :=
    llsAsm_log_3000.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hL0 : 0 ≤ Real.log n := by linarith
  have hX : (64 : ℝ) ≤ Real.log n ^ 2 := by nlinarith
  obtain ⟨-, hprim, hne1, hc0, -, -, hq, -, -, hS, -, hWre⟩ :=
    llsElem_no_witness_facts (by omega) χ hχ hcon'
  have : NeZero χ.conductor := ⟨hc0⟩
  have hsqrt : √(Real.log n ^ 2) = Real.log n := Real.sqrt_sq hL0
  have hlogX : Real.log (Real.log n ^ 2) = 2 * Real.log (Real.log n) := by
    rw [Real.log_pow]; norm_num
  have hcpos : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero hc0
  have hu : Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi :=
    Real.log_div hcpos.ne' Real.pi_ne_zero
  have h2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  have hG' := hG hGRH χ.conductor χ.primitiveCharacter hprim hne1 (Real.log n ^ 2) hX
  have hU' := hU hGRH χ.conductor χ.primitiveCharacter hprim hne1 (Real.log n ^ 2) (by linarith)
  have hZ' := hZ hGRH (Real.log n ^ 2) hX
  have hW' := hW (Real.log n ^ 2) hX
  rw [hsqrt, hWre] at hG'
  rw [hsqrt, hS, hlogX] at hU'
  rw [hsqrt, hlogX, h2pi] at hZ'
  rw [hlogX] at hW'
  refine llsAsm_real_contra (L := Real.log n) (ℓ := Real.log (Real.log n))
    (p := Real.log Real.pi) (l2 := Real.log 2) (Z := zeroSumSq χ.primitiveCharacter)
    (u := Real.log ((χ.conductor : ℝ) / Real.pi)) (S := logPsiZeta (Real.log n ^ 2))
    hL (llsAsm_loglog_ge hL) szs_log_pi_gt.le llsAsm_log_pi_le
    (by linarith [Real.log_two_lt_d9]) (by rw [hu]; linarith) (by linarith) ?_ hZ'
  calc logPsiZeta (Real.log n ^ 2) ≤ _ := hU'
    _ = _ := by ring

end DetPrimality.Bach

#print axioms DetPrimality.Bach.llsAsm_real_contra
#print axioms DetPrimality.Bach.llsAsm_bachBound_one
