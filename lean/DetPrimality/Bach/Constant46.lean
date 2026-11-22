import DetPrimality.Bach.Assembly
import DetPrimality.Bach.ConstPsiOne
import DetPrimality.Bach.ConstPsiTheta

/-!
# Round 4: lowering Bach's constant from `64` to `46`

The analytic part (`BachInputs`, `bachInputs`, `norm_smoothPsi_le_of_inputs`) is reused verbatim
from `Assembly.lean`, exactly as in `Constant.lean`.  Compared with round 3 (`c = 64`):

* §6.1: unchanged, `psiOne_lower_integral` (`ConstPsiOne.lean`):
  `ψ₁(x) ≥ (x - 3) log 2 / 2 - log x`;
* §6.2: `noncoprimeSum_le_small` (`ConstPsiTheta.lean`):
  `∑_{m<x,(m,n)>1} Λ(m) ≤ log n + 1.84 √x` for **all** `x` (instead of `3.36 √x`, `x ≥ 4096`);
* §7.1: the bootstrap `n > 46 (log n)² ⟹ log n ≥ 11 log 2 > 7.62`, through `n > 2^5, 2^9, 2^10, 2^11`
  (no bound on `exp` needed);
* §7.2: the final inequality, with `s = √x`, `s² = 46 L²`, `s ≤ 6.7824 L` (`6.7824² ≥ 46`) and
  `log x ≤ 12 log 2 + x / 4096 - 1`.  It reduces to `9.13 L² - 45.6 L - 30.7 > 0`, whose value at
  `L = 7.62` is about `153`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- `k log 2 ≤ log n` as soon as `2 ^ k ≤ n`. -/
theorem nat_mul_log_two_le_log {n : ℝ} (k : ℕ) (h : (2 : ℝ) ^ k ≤ n) :
    (k : ℝ) * Real.log 2 ≤ Real.log n := by
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log n := Real.log_le_log (by positivity) h
  rwa [Real.log_pow] at h1

/-- (§7.1, `c = 46`) If no unit `a < 46 (log n)²` has `χ a ≠ 1`, then `log n ≥ 7.62`. -/
theorem log_ge_of_no_small_witness_46 {n : ℕ} (hn : 2 < n) (χ : DirichletCharacter ℂ n)
    (hχ : χ ≠ 1)
    (h : ∀ a : ℕ, (a : ℝ) < 46 * (Real.log n) ^ 2 → IsUnit (a : ZMod n) → χ (a : ZMod n) = 1) :
    7.62 ≤ Real.log n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod n)ˣ, χ u ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hχ (MulChar.ext fun a => by rw [hc a, MulChar.one_apply_coe])
  have hval : ¬ (((u : ZMod n).val : ℝ) < 46 * Real.log n ^ 2) := fun hlt => hu (by
    have h1 := h (u : ZMod n).val hlt (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    rwa [ZMod.natCast_zmod_val] at h1)
  have hlt : ((u : ZMod n).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
  have hbig : 46 * Real.log n ^ 2 < n := by linarith [not_lt.mp hval]
  have h2 := Real.log_two_gt_d9
  have hn0 : (0 : ℝ) < n := by positivity
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  have hn1 : (2 : ℝ) ^ 5 ≤ n := by nlinarith
  have hL2 := nat_mul_log_two_le_log 5 hn1
  push_cast at hL2
  have hL2' : 3.4657 ≤ Real.log n := by linarith
  have hn2 : (2 : ℝ) ^ 9 ≤ n := by nlinarith
  have hL3 := nat_mul_log_two_le_log 9 hn2
  push_cast at hL3
  have hL3' : 6.2383 ≤ Real.log n := by linarith
  have hn3 : (2 : ℝ) ^ 10 ≤ n := by nlinarith
  have hL4 := nat_mul_log_two_le_log 10 hn3
  push_cast at hL4
  have hL4' : 6.9314 ≤ Real.log n := by linarith
  have hn4 : (2 : ℝ) ^ 11 ≤ n := by nlinarith
  have hL5 := nat_mul_log_two_le_log 11 hn4
  push_cast at hL5
  linarith

/-- `log x ≤ 12 log 2 + x / 4096 - 1` for `x > 0`. -/
theorem log_le_of_4096 {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 12 * Real.log 2 + x / 4096 - 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 4096 by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h1
  have h2 : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
  linarith

/-- (§7.2, `c = 46`) The final numerical inequality, in `L = log n ≥ 7.62` and `s = √x`,
`s² = x = 46 L²`. -/
theorem final_numeric_46 {L s : ℝ} (hL : 7.62 ≤ L) (hs : s ^ 2 = 46 * L ^ 2) :
    (s + 5) * (L + 2) + Real.log (46 * L ^ 2) + 5
      < (46 * L ^ 2 - 3) * Real.log 2 / 2 - Real.log (46 * L ^ 2)
        - 2 * (L + 1.84 * s) := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have hsL : s ≤ 6.7824 * L := by
    by_contra hc
    push Not at hc
    have hp : 0 < (s - 6.7824 * L) * (s + 6.7824 * L) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hy := log_le_of_4096 (x := 46 * L ^ 2) (by positivity)
  have a1 : (46 * L ^ 2 - 3) * 0.6931471803 ≤ (46 * L ^ 2 - 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2l.le (by nlinarith)
  have p1 : s * L ≤ 6.7824 * L * L := mul_le_mul_of_nonneg_right hsL (by linarith)
  have hq : 0 ≤ L * (L - 7.62) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- (§7.3, round 4) **GRH ⟹ character form of Bach's bound with `c = 46`** (sorry-free, from
`bachInputs`). -/
theorem bachBoundChar_of_GRH_c46 (hGRH : DirichletLZerosOnLine) : BachBoundChar 46 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  have hL := log_ge_of_no_small_witness_46 hn χ hχ hcon
  have hx1 : (1 : ℝ) ≤ 46 * Real.log n ^ 2 := by nlinarith
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hne1 : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, changeLevel_one]
  have hq : Real.log χ.conductor ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level)
  have hA := norm_smoothPsi_le_of_inputs bachInputs hGRH χ.primitiveCharacter hprim hne1 hx1
  have hlow := re_smoothPsi_primitive_lower χ (x := 46 * Real.log n ^ 2) (by linarith) hcon
  have hE := noncoprimeSum_le_small (n := n) (by omega) (46 * Real.log n ^ 2)
  have hψ := psiOne_lower_integral (x := 46 * Real.log n ^ 2) hx1
  have hre := Complex.re_le_norm (smoothPsi χ.primitiveCharacter (46 * Real.log n ^ 2))
  have hfin := final_numeric_46 hL
    (Real.sq_sqrt (show (0 : ℝ) ≤ 46 * Real.log n ^ 2 by linarith))
  have hs0 := Real.sqrt_nonneg (46 * Real.log n ^ 2)
  have hmul : (√(46 * Real.log n ^ 2) + 5) * (Real.log χ.conductor + 2)
      ≤ (√(46 * Real.log n ^ 2) + 5) * (Real.log n + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- **Round 4 main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's bound
with the explicit constant `c = 46`. -/
theorem grh_implies_bach_c46 : GRHImpliesBach 46 :=
  fun hGRH => bachBound_of_bachBoundChar (bachBoundChar_of_GRH_c46 hGRH)

end DetPrimality.Bach
