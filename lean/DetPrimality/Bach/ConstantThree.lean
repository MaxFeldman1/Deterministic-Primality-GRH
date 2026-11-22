import DetPrimality.CompositeInterface
import DetPrimality.Bach.CompositeReduction
import DetPrimality.Bach.SharpZeroSum
import DetPrimality.Bach.SharpExplicit
import DetPrimality.Bach.ZeroSumGain
import DetPrimality.Bach.ChebyshevThirty

/-!
# GRH ⟹ Bach's Theorem 2 form (composite moduli) with `c = 3`

Main results: `bachBoundCharComposite_of_GRH_c3 : BachBoundCharComposite 3` (under GRH) and
`grh_implies_bach_composite_c3 : GRHImpliesBachComposite 3`.

Let `n > 2` be composite, `χ ≠ 1` mod `n`, `L = log n`, `x = 3 L²`, and assume `χ a = 1` for all
`1 ≤ a < x`.  By `CompositeReduction.lean`: `x² ≤ n`, hence `L ≥ 12.20318`, `x > 446`
(`compred_log_ge_c3`); `χ* m = 1` for `1 ≤ m < x`; and `ψ₁(x) ≤ Re ψ̃(x, χ*)`.

Upper bound (GRH): `re_smoothPsi_le_of_zeroSum_le_of_logDeriv` with the two-point zero-sum bound
with hypothesis gain `zeroSum χ* ≤ 5/9 log q - 2.2016` (`zeroSum_le_gain_240`) and `D = 0.5708`.
Lower bound: the Chebyshev-30 bound `ψ₁(x) ≥ 0.460645 x - 3/2 log x` (`psiOne_lower_cheb30_200`).
The leading terms are `(5/9) √3 L² ≈ 0.962 L²` against `1.382 L²`, so a single case suffices
(margin `≥ 0.41 L² + 2.69 L - 3.1 > 90`).
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- Tangent bound `log x ≤ 9 log 2 + x / 512 - 1` for `x > 0`. -/
theorem cthree_log_le {x : ℝ} (hx : 0 < x) : Real.log x ≤ 9 * Real.log 2 + x / 512 - 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 2 ^ 9 by positivity)
  rw [Real.log_div hx.ne' (by positivity), Real.log_pow] at h1
  norm_num at h1 ⊢
  linarith

/-- The final numerical inequality for `c = 3`: the GRH upper bound (with `A = 5/9`,
`B = -2.2016`, `D = 0.5708`) is below the Chebyshev-30 lower bound for `ψ₁(3L²)`. -/
theorem cthree_final {L lq : ℝ} (hL : 12.2 ≤ L) (hlq : lq ≤ L) :
    (√(3 * L ^ 2) + 2 + 3 / (3 * L ^ 2)) * (5 / 9 * lq + -2.2016) + 0.5708 - 1
        + (Real.log (3 * L ^ 2) + 13 / 6) / (3 * L ^ 2)
      < 0.460645 * (3 * L ^ 2) - 3 / 2 * Real.log (3 * L ^ 2) := by
  have h2u := Real.log_two_lt_d9
  have hL0 : 0 ≤ L := by linarith
  have hx : (446 : ℝ) ≤ 3 * L ^ 2 := by nlinarith
  have hx0 : (0 : ℝ) < 3 * L ^ 2 := by linarith
  have hlog := cthree_log_le hx0
  have hs : √(3 * L ^ 2) ≤ 1.7321 * L :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg L]⟩
  have hs0 : 0 ≤ √(3 * L ^ 2) := Real.sqrt_nonneg _
  have hu0 : 0 ≤ 3 / (3 * L ^ 2) := by positivity
  have hu1 : 3 / (3 * L ^ 2) ≤ 0.01 := by
    rw [div_le_iff₀ hx0]; linarith
  have hR : (Real.log (3 * L ^ 2) + 13 / 6) / (3 * L ^ 2) ≤ 0.03 := by
    rw [div_le_iff₀ hx0]; linarith
  have hT0 : 0 ≤ 5 / 9 * L + -2.2016 := by linarith
  have h1 : (√(3 * L ^ 2) + 2 + 3 / (3 * L ^ 2)) * (5 / 9 * lq + -2.2016)
      ≤ (√(3 * L ^ 2) + 2 + 3 / (3 * L ^ 2)) * (5 / 9 * L + -2.2016) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (√(3 * L ^ 2) + 2 + 3 / (3 * L ^ 2)) * (5 / 9 * L + -2.2016)
      ≤ (1.7321 * L + 2.01) * (5 / 9 * L + -2.2016) :=
    mul_le_mul_of_nonneg_right (by linarith) hT0
  nlinarith [mul_nonneg (sub_nonneg.mpr hL) hL0]

/-- **GRH ⟹ Bach's Theorem 2 form for composite moduli with `c = 3`** (sorry-free). -/
theorem bachBoundCharComposite_of_GRH_c3 (hGRH : DirichletLZerosOnLine) :
    BachBoundCharComposite 3 := by
  intro n hn hnp χ hχ
  by_contra hcon
  push Not at hcon
  have hbig := compred_bootstrap_hyp hn hnp χ (c := 3) (by norm_num) hcon
  obtain ⟨-, hL⟩ := compred_log_ge_c3 hn hbig
  have h2l := Real.log_two_gt_d9
  have hL' : 12.2 ≤ Real.log n := by linarith
  have hx446 : (446 : ℝ) < 3 * Real.log n ^ 2 := by linarith [sq_nonneg (Real.log n - 12.2)]
  have hx0 : (0 : ℝ) < 3 * Real.log n ^ 2 := by linarith
  have hx1 : (1 : ℝ) ≤ 3 * Real.log n ^ 2 := by linarith
  have hlx2 : 2 ≤ Real.log (3 * Real.log n ^ 2) := by
    have h1 : Real.log ((2 : ℝ) ^ 8) ≤ Real.log (3 * Real.log n ^ 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have : NeZero n := ⟨by omega⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨hprim, hne1, -, hq⟩ := compred_primitive_facts (by omega) χ hχ
  have hprim1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < 3 * Real.log n ^ 2 →
      χ.primitiveCharacter (m : ZMod χ.conductor) = 1 :=
    fun m hm hmx => compred_primitive_eq_one χ hcon hm hmx
  have hT0 := zeroSum_le_gain_240 hGRH χ.primitiveCharacter hprim hne1
    (x := 3 * Real.log n ^ 2) (by linarith) hprim1
  have hT : zeroSum χ.primitiveCharacter ≤ 5 / 9 * Real.log χ.conductor + -2.2016 := by
    linarith
  have hD := norm_logDeriv_LFunction_two_le_sharp χ.primitiveCharacter
  have hre := re_smoothPsi_le_of_zeroSum_le_of_logDeriv hGRH χ.primitiveCharacter hprim hne1
    hT hD hx1 hlx2
  have hlow := compred_psiOne_le (by omega) χ hx0 hcon
  have hψ := psiOne_lower_cheb30_200 (x := 3 * Real.log n ^ 2) (by linarith)
  have hfin := cthree_final (L := Real.log n) (lq := Real.log χ.conductor) hL' hq
  linarith

/-- **Main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's Theorem 2 form
for composite moduli with the explicit constant `c = 3`. -/
theorem grh_implies_bach_composite_c3 : GRHImpliesBachComposite 3 :=
  fun hGRH => bachBoundCharComposite_of_GRH_c3 hGRH

end DetPrimality.Bach
