import DetPrimality.Bach.Assembly
import DetPrimality.Bach.ConstPsiOne
import DetPrimality.Bach.ConstNoncoprime

/-!
# Round 3: lowering Bach's constant from `1024` to `64`

The analytic part (`BachInputs`, `bachInputs`, `norm_smoothPsi_le_of_inputs`) is reused verbatim
from `Assembly.lean`.  Only the elementary §6–§7 inputs are sharpened:

* §6.1: `psiOne_lower_integral` (`ConstPsiOne.lean`): `ψ₁(x) ≥ (x - 3) log 2 / 2 - log x`
  (slope `log 2 / 2` instead of `log 2 / 4`);
* §6.2: `noncoprimeSum_le_of_ge_4096` (`ConstNoncoprime.lean`):
  `∑_{m<x,(m,n)>1} Λ(m) ≤ log n + 3.36 √x` for `x ≥ 4096` (instead of `16.16 √x`);
* §7.1: the bootstrap `n > 64 (log n)² ⟹ log n ≥ 8` (so `x = 64 (log n)² ≥ 4096`);
* §7.2: the final inequality with `√x = 8 L`, `L ≥ 8`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- `exp 8 < 2981`. -/
theorem exp_eight_lt : Real.exp 8 < 2981 := by
  have h : Real.exp 8 = Real.exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h1 := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  calc Real.exp 1 ^ 8 < 2.7182818286 ^ 8 := by gcongr
    _ < 2981 := by norm_num

/-- (§7.1, `c = 64`) If no unit `a < 64 (log n)²` has `χ a ≠ 1`, then `log n ≥ 8`. -/
theorem eight_le_log_of_no_small_witness {n : ℕ} (hn : 2 < n) (χ : DirichletCharacter ℂ n)
    (hχ : χ ≠ 1)
    (h : ∀ a : ℕ, (a : ℝ) < 64 * (Real.log n) ^ 2 → IsUnit (a : ZMod n) → χ (a : ZMod n) = 1) :
    8 ≤ Real.log n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod n)ˣ, χ u ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hχ (MulChar.ext fun a => by rw [hc a, MulChar.one_apply_coe])
  have hval : ¬ (((u : ZMod n).val : ℝ) < 64 * Real.log n ^ 2) := fun hlt => hu (by
    have h1 := h (u : ZMod n).val hlt (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    rwa [ZMod.natCast_zmod_val] at h1)
  have hlt : ((u : ZMod n).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
  have hbig : 64 * Real.log n ^ 2 < n := by linarith [not_lt.mp hval]
  have h2 := Real.log_two_gt_d9
  have hn0 : (0 : ℝ) < n := by positivity
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  have hn1 : (64 : ℝ) < n := by nlinarith
  have hL2 : 6 * Real.log 2 ≤ Real.log n := by
    have h3 : Real.log ((2 : ℝ) ^ (6 : ℕ)) ≤ Real.log n :=
      Real.log_le_log (by positivity) (by norm_num; exact_mod_cast hn1.le)
    rw [Real.log_pow] at h3
    push_cast at h3
    exact h3
  have hn2 : (1024 : ℝ) < n := by nlinarith
  have hL3 : 10 * Real.log 2 ≤ Real.log n := by
    have h3 : Real.log ((2 : ℝ) ^ (10 : ℕ)) ≤ Real.log n :=
      Real.log_le_log (by positivity) (by norm_num; exact_mod_cast hn2.le)
    rw [Real.log_pow] at h3
    push_cast at h3
    exact h3
  have hn3 : (2981 : ℝ) < n := by nlinarith
  have : Real.exp 8 < n := lt_trans exp_eight_lt hn3
  exact ((Real.lt_log_iff_exp_lt hn0).mpr this).le

/-- (§7.2, `c = 64`) The final numerical inequality, in `L = log n ≥ 8`, `√x = 8 L`. -/
theorem final_numeric_64 {L : ℝ} (hL : 8 ≤ L) :
    (8 * L + 5) * (L + 2) + Real.log (64 * L ^ 2) + 5
      < (64 * L ^ 2 - 3) * Real.log 2 / 2 - Real.log (64 * L ^ 2)
        - 2 * (L + 3.36 * (8 * L)) := by
  have h2l := Real.log_two_gt_d9
  have hy : Real.log (64 * L ^ 2) ≤ 2 * (8 * L) - 2 := by
    have h1 : Real.log (8 * L) ≤ 8 * L - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [show 64 * L ^ 2 = (8 * L) ^ (2 : ℕ) by ring, Real.log_pow]
    push_cast; linarith
  have a1 : (64 * L ^ 2 - 3) * 0.6931471803 ≤ (64 * L ^ 2 - 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2l.le (by nlinarith)
  have hq : 0 ≤ L * (L - 8) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- (§7.3, round 3) **GRH ⟹ character form of Bach's bound with `c = 64`** (sorry-free, from
`bachInputs`). -/
theorem bachBoundChar_of_GRH_c (hGRH : DirichletLZerosOnLine) : BachBoundChar 64 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  have hL := eight_le_log_of_no_small_witness hn χ hχ hcon
  have hx1 : (1 : ℝ) ≤ 64 * Real.log n ^ 2 := by nlinarith
  have hx4096 : (4096 : ℝ) ≤ 64 * Real.log n ^ 2 := by nlinarith
  have hsqrt : √(64 * Real.log n ^ 2) = 8 * Real.log n := by
    rw [show 64 * Real.log n ^ 2 = (8 * Real.log n) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
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
  have hlow := re_smoothPsi_primitive_lower χ (x := 64 * Real.log n ^ 2) (by linarith) hcon
  have hE := noncoprimeSum_le_of_ge_4096 (n := n) (by omega) hx4096
  have hψ := psiOne_lower_integral (x := 64 * Real.log n ^ 2) hx1
  have hre := Complex.re_le_norm (smoothPsi χ.primitiveCharacter (64 * Real.log n ^ 2))
  have hfin := final_numeric_64 hL
  rw [hsqrt] at hA hE
  have hmul : (8 * Real.log n + 5) * (Real.log χ.conductor + 2)
      ≤ (8 * Real.log n + 5) * (Real.log n + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- **Round 3 main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's bound
with the explicit constant `c = 64`. -/
theorem grh_implies_bach_c : GRHImpliesBach 64 :=
  fun hGRH => bachBound_of_bachBoundChar (bachBoundChar_of_GRH_c hGRH)

end DetPrimality.Bach
