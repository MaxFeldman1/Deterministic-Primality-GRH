import DetPrimality.Bach.Constant22
import DetPrimality.Bach.SharpZeroSum
import DetPrimality.Bach.SharpExplicit
import DetPrimality.Bach.ConstPsiOneGrid

/-!
# Bach's constant `13` (safe assembly of the sharp lemmas)

This file assembles `GRH ⟹ BachBoundChar 13` from already-proved explicit lemmas.  Nothing here
is new analysis.  Compared with `Constant22.lean` three inputs are sharper:

* `zeroSum_le_sharp32` : `∑_ρ 1/(|ρ||ρ+1|) ≤ (2/3) log q + 1.097` (SharpZeroSum);
* `re_smoothPsi_le_of_zeroSum_le_of_logDeriv` (SharpExplicit) with
  `norm_logDeriv_LFunction_two_le_sharp` (`|L'/L(2)| ≤ 0.5708`): the one-sided explicit formula
  `Re ψ̃(x, χ*) ≤ (√x + 2 + 3/x) · zeroSum + 0.5708 - 1 + (log x + 13/6)/x`;
* `psiOne_lower_grid` (ConstPsiOneGrid): `ψ₁(x) ≥ x/2 - 2.6` on `(256, 1536]`.

The `ω(n)` bound for the non-coprime sum is *not* needed at `c = 13`; the old
`log n + A √x` bounds (`A = 1.43` below `2^16`, `A = 1.84` in general) suffice.

Write `L = log n`, `x = 13 L²`, `s = √x`.  Assuming no unit `a < x` has `χ a ≠ 1`:

* (upper, `cmid_upper`) for `x ≥ 256` and `log q ≤ L`:
  `Re ψ̃(x, χ*) ≤ (s + 2.02)((2/3) L + 1.097) + 0.6`
  (using `3/x ≤ 0.02` and `(log x + 13/6)/x ≤ 1.01`);
* (lower) `Re ψ̃(x, χ*) ≥ ψ₁(x) - 2 (L + A s)`.

## Bootstrap (`cmid_log_ge_of_no_small_witness_13`)

`n > 13 (log n)² ⟹ log n ≥ 6.1516` through the chain
`n ≥ 2^3, 2^5, 2^7, 2^8`, `n² ≥ 2^17`, `n⁴ ≥ 2^35`, `n⁸ ≥ 2^71`
(the true fixed point of `e^L = 13 L²` is `L ≈ 6.2`).  Hence `x ≥ 491.9 > 256`.

## The two cases (Lean-form margin = minimum over the range of RHS - LHS)

| range of `x = 13 L²` | `ψ₁` lower bound                    | `ψ - θ` constant `A` | margin |
|----------------------|-------------------------------------|----------------------|--------|
| `(491, 1536]`        | `x/2 - 2.6` (`psiOne_lower_grid`)   | `1.43` (`x < 2^16`)  | ≈ 41   |
| `(1536, ∞)`          | `psiOne_lower_integral`, `k = 11`   | `1.84` (all `x`)     | ≈ 13.5 |

Both margins are attained at the left end of the range and grow with `L`.  (The same two-case
scheme has model margins `24.5 / 0.4` at `c = 12` and fails at `c = 11` in the second case, so
`13` is a deliberately comfortable choice; lower constants need the finer inputs.)
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- (§7.1, `c = 13`) If no unit `a < 13 (log n)²` has `χ a ≠ 1`, then `log n ≥ 6.1516`. -/
theorem cmid_log_ge_of_no_small_witness_13 {n : ℕ} (hn : 2 < n) (χ : DirichletCharacter ℂ n)
    (hχ : χ ≠ 1)
    (h : ∀ a : ℕ, (a : ℝ) < 13 * (Real.log n) ^ 2 → IsUnit (a : ZMod n) → χ (a : ZMod n) = 1) :
    6.1516 ≤ Real.log n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod n)ˣ, χ u ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hχ (MulChar.ext fun a => by rw [hc a, MulChar.one_apply_coe])
  have hval : ¬ (((u : ZMod n).val : ℝ) < 13 * Real.log n ^ 2) := fun hlt => hu (by
    have h1 := h (u : ZMod n).val hlt (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    rwa [ZMod.natCast_zmod_val] at h1)
  have hlt : ((u : ZMod n).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
  have hbig : 13 * Real.log n ^ 2 < n := by linarith [not_lt.mp hval]
  have h2 := Real.log_two_gt_d9
  have hn0 : (0 : ℝ) < n := by positivity
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  -- `n ≥ 2^3`
  have hn1 : (2 : ℝ) ^ 3 ≤ (n : ℝ) ^ 1 := by nlinarith
  have hL2 := nat_mul_log_two_le_mul_log 3 1 hn1
  push_cast at hL2
  have hL2' : 2.0794 ≤ Real.log n := by linarith
  -- `n ≥ 2^5`
  have hn2 : (2 : ℝ) ^ 5 ≤ (n : ℝ) ^ 1 := by nlinarith
  have hL3 := nat_mul_log_two_le_mul_log 5 1 hn2
  push_cast at hL3
  have hL3' : 3.4657 ≤ Real.log n := by linarith
  -- `n ≥ 2^7`
  have hn3 : (2 : ℝ) ^ 7 ≤ (n : ℝ) ^ 1 := by nlinarith
  have hL4 := nat_mul_log_two_le_mul_log 7 1 hn3
  push_cast at hL4
  have hL4' : 4.852 ≤ Real.log n := by linarith
  -- `n ≥ 2^8`
  have hn4 : (2 : ℝ) ^ 8 ≤ (n : ℝ) ^ 1 := by nlinarith
  have hL5 := nat_mul_log_two_le_mul_log 8 1 hn4
  push_cast at hL5
  have hL5' : 5.5451 ≤ Real.log n := by linarith
  -- `n ≥ 363`, `n² ≥ 2^17`
  have hn5 : (363 : ℝ) ≤ n := by nlinarith
  have hn5' : (2 : ℝ) ^ 17 ≤ (n : ℝ) ^ 2 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn5 2)
  have hL6 := nat_mul_log_two_le_mul_log 17 2 hn5'
  push_cast at hL6
  have hL6' : 5.8917 ≤ Real.log n := by linarith
  -- `n ≥ 431`, `n⁴ ≥ 2^35`
  have hn6 : (431 : ℝ) ≤ n := by nlinarith
  have hn6' : (2 : ℝ) ^ 35 ≤ (n : ℝ) ^ 4 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn6 4)
  have hL7 := nat_mul_log_two_le_mul_log 35 4 hn6'
  push_cast at hL7
  have hL7' : 6.065 ≤ Real.log n := by linarith
  -- `n ≥ 470`, `n⁸ ≥ 2^71`
  have hn7 : (470 : ℝ) ≤ n := by nlinarith
  have hn7' : (2 : ℝ) ^ 71 ≤ (n : ℝ) ^ 8 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn7 8)
  have hL8 := nat_mul_log_two_le_mul_log 71 8 hn7'
  push_cast at hL8
  linarith

/-- Simplified upper bound: for `x ≥ 256` and `lq ≤ L`, the right-hand side of
`re_smoothPsi_le_of_zeroSum_le_of_logDeriv` (with `A = 2/3`, `B = 1.097`, `D = 0.5708`) is at most
`(s + 2.02)((2/3) L + 1.097) + 0.6`. -/
theorem cmid_upper {x s L lq : ℝ} (hx : 256 ≤ x) (hs : 0 ≤ s) (hlq : lq ≤ L) (hL : 0 ≤ L) :
    (s + 2 + 3 / x) * (2 / 3 * lq + 1.097) + 0.5708 - 1 + (Real.log x + 13 / 6) / x
      ≤ (s + 2.02) * (2 / 3 * L + 1.097) + 0.6 := by
  have hx0 : 0 < x := by linarith
  have h3 : 3 / x ≤ 0.02 := by
    rw [div_le_iff₀ hx0]; linarith
  have h30 : 0 ≤ 3 / x := by positivity
  have hlog : (Real.log x + 13 / 6) / x ≤ 1.01 := by
    rw [div_le_iff₀ hx0]
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have m1 : (s + 2 + 3 / x) * (2 / 3 * lq + 1.097) ≤ (s + 2 + 3 / x) * (2 / 3 * L + 1.097) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have m2 : (s + 2 + 3 / x) * (2 / 3 * L + 1.097) ≤ (s + 2.02) * (2 / 3 * L + 1.097) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- `s ≤ 3.6056 L` when `s² = 13 L²` and `L ≥ 0`. -/
theorem cmid_sqrt_le {L s : ℝ} (hL : 0 ≤ L) (hs : s ^ 2 = 13 * L ^ 2) : s ≤ 3.6056 * L := by
  by_contra hc
  push Not at hc
  have hp : 0 < (s - 3.6056 * L) * (s + 3.6056 * L) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- (§7.2, case `x ≤ 1536`) grid bound `ψ₁ ≥ x/2 - 2.6`, `A = 1.43`. -/
theorem cmid_final_numeric_13_a {L s : ℝ} (hL : 6.1516 ≤ L) (hs : s ^ 2 = 13 * L ^ 2) :
    (s + 2.02) * (2 / 3 * L + 1.097) + 0.6
      < 13 * L ^ 2 / 2 - 2.6 - 2 * (L + 1.43 * s) := by
  have hsL := cmid_sqrt_le (by linarith) hs
  have m : (s + 2.02) * (2 / 3 * L + 1.097) ≤ (3.6056 * L + 2.02) * (2 / 3 * L + 1.097) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ L - 6.1516 by linarith) (show (0 : ℝ) ≤ L by linarith)]

/-- (§7.2, case `x > 1536`) `psiOne_lower_integral`, `A = 1.84`. -/
theorem cmid_final_numeric_13_b {L s : ℝ} (hx : 1536 < 13 * L ^ 2) (hL : 0 ≤ L)
    (hs : s ^ 2 = 13 * L ^ 2) :
    (s + 2.02) * (2 / 3 * L + 1.097) + 0.6
      < (13 * L ^ 2 - 3) * Real.log 2 / 2 - Real.log (13 * L ^ 2) - 2 * (L + 1.84 * s) := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have hL' : 10.869 ≤ L := by nlinarith
  have hsL := cmid_sqrt_le hL hs
  have m : (s + 2.02) * (2 / 3 * L + 1.097) ≤ (3.6056 * L + 2.02) * (2 / 3 * L + 1.097) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hy := log_le_of_two_pow (x := 13 * L ^ 2) (by positivity) 11
  push_cast at hy
  have a1 : (13 * L ^ 2 - 3) * 0.6931471803 ≤ (13 * L ^ 2 - 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2l.le (by nlinarith)
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ L - 10.869 by linarith) (show (0 : ℝ) ≤ L by linarith)]

/-- (§7.3) **GRH ⟹ character form of Bach's bound with `c = 13`** (sorry-free). -/
theorem bachBoundChar_of_GRH_c13 (hGRH : DirichletLZerosOnLine) : BachBoundChar 13 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  have hL := cmid_log_ge_of_no_small_witness_13 hn χ hχ hcon
  have h2l := Real.log_two_gt_d9
  have hx491 : (491 : ℝ) < 13 * Real.log n ^ 2 := by nlinarith
  have hx1 : (1 : ℝ) ≤ 13 * Real.log n ^ 2 := by linarith
  have hlx : 2 ≤ Real.log (13 * Real.log n ^ 2) := by
    have h8 := nat_mul_log_two_le_mul_log (n := 13 * Real.log n ^ 2) 8 1 (by norm_num; linarith)
    push_cast at h8
    linarith
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hne1 : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, changeLevel_one]
  have hq : Real.log χ.conductor ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level)
  have hT := zeroSum_le_sharp32 hGRH χ.primitiveCharacter hprim hne1
  have hD := norm_logDeriv_LFunction_two_le_sharp χ.primitiveCharacter
  have hU := re_smoothPsi_le_of_zeroSum_le_of_logDeriv hGRH χ.primitiveCharacter hprim hne1
    hT hD hx1 hlx
  have hlow := re_smoothPsi_primitive_lower χ (x := 13 * Real.log n ^ 2) (by linarith) hcon
  have hs0 := Real.sqrt_nonneg (13 * Real.log n ^ 2)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 13 * Real.log n ^ 2 by linarith)
  have hup := cmid_upper (x := 13 * Real.log n ^ 2) (s := √(13 * Real.log n ^ 2))
    (L := Real.log n) (lq := Real.log χ.conductor) (by linarith) hs0 hq (by linarith)
  have hn0 : 0 < n := by omega
  rcases le_or_gt (13 * Real.log n ^ 2) 1536 with h1536 | h1536
  · -- `491 < x ≤ 1536`
    have hE := noncoprimeSum_le_of_lt_65536 (n := n) hn0
      (x := 13 * Real.log n ^ 2) (by linarith) (by linarith)
    have hψ := psiOne_lower_grid (x := 13 * Real.log n ^ 2) (by linarith) h1536
    have hfin := cmid_final_numeric_13_a hL hsq
    linarith
  · -- `x > 1536`
    have hE := noncoprimeSum_le_small (n := n) hn0 (13 * Real.log n ^ 2)
    have hψ := psiOne_lower_integral (x := 13 * Real.log n ^ 2) hx1
    have hfin := cmid_final_numeric_13_b h1536 (by linarith) hsq
    linarith

/-- **Main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's bound with the
explicit constant `c = 13`. -/
theorem grh_implies_bach_c13 : GRHImpliesBach 13 :=
  fun hGRH => bachBound_of_bachBoundChar (bachBoundChar_of_GRH_c13 hGRH)


end DetPrimality.Bach
