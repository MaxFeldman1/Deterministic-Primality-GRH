import DetPrimality.Bach.Constant46
import DetPrimality.Bach.ConstPsiOneSharp

/-!
# Round 5: lowering Bach's constant from `46` to `28`

The analytic part (`BachInputs`, `bachInputs`, `norm_smoothPsi_le_of_inputs`,
`re_smoothPsi_primitive_lower`) is reused verbatim, exactly as in `Constant46.lean`.  Compared
with round 4 (`c = 46`):

* §6.1: `psiOne_lower_1024` (`ConstPsiOneSharp.lean`), valid for `x > 1024`:
  `ψ₁(x) ≥ (x - 3) log 2 / 2 - log x + 239571 · log 2 / x`
  (the gain `239571 · log 2 ≈ 166058` comes from the exact values of `ψ(k)`, `k < 1024`);
* §6.2: unchanged, `noncoprimeSum_le_small`: `∑_{m<x,(m,n)>1} Λ(m) ≤ log n + 1.84 √x` for all `x`;
* §7.1: the bootstrap `n > 28 (log n)² ⟹ log n ≥ 10 log 2 > 6.9314`, through
  `n ≥ 2^4, 2^7, 2^9, 2^10` (no bound on `exp` needed).  Then `x = 28 L² > 1024`, so the
  `K = 1024` form of §6.1 applies;
* §7.2: the final inequality, in `L = log n` and `s = √x`, `s² = x = 28 L²`, `s ≤ 5.2916 L`.
  Two cases:
  - `L ≤ 10` (`x ≤ 2800`): `log x ≤ 11 log 2 + x / 2048 - 1`, and the gain term is bounded below
    via the tangent line of `1/x` at `1600`: `1/x ≥ 2/1600 - x/1600²` (`inv_ge_tangent_c28`),
    which is non-negative for `x ≤ 3200`.  The inequality reduces to a quadratic in `L` with
    leading coefficient `≈ 2.57` and minimum `≈ 44.6` (at `L ≈ 7.21`).
  - `L ≥ 10`: drop the gain, `log x ≤ 12 log 2 + x / 4096 - 1`; the quadratic
    (`≈ 4.40 L² - 37.06 L - 30.7`) is `≈ 38.6` at `L = 10` and increasing.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- (§7.1, `c = 28`) If no unit `a < 28 (log n)²` has `χ a ≠ 1`, then `log n ≥ 6.9314`. -/
theorem log_ge_of_no_small_witness_28 {n : ℕ} (hn : 2 < n) (χ : DirichletCharacter ℂ n)
    (hχ : χ ≠ 1)
    (h : ∀ a : ℕ, (a : ℝ) < 28 * (Real.log n) ^ 2 → IsUnit (a : ZMod n) → χ (a : ZMod n) = 1) :
    6.9314 ≤ Real.log n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod n)ˣ, χ u ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hχ (MulChar.ext fun a => by rw [hc a, MulChar.one_apply_coe])
  have hval : ¬ (((u : ZMod n).val : ℝ) < 28 * Real.log n ^ 2) := fun hlt => hu (by
    have h1 := h (u : ZMod n).val hlt (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    rwa [ZMod.natCast_zmod_val] at h1)
  have hlt : ((u : ZMod n).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
  have hbig : 28 * Real.log n ^ 2 < n := by linarith [not_lt.mp hval]
  have h2 := Real.log_two_gt_d9
  have hn0 : (0 : ℝ) < n := by positivity
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  have hn1 : (2 : ℝ) ^ 4 ≤ n := by nlinarith
  have hL2 := nat_mul_log_two_le_log 4 hn1
  push_cast at hL2
  have hL2' : 2.7725 ≤ Real.log n := by linarith
  have hn2 : (2 : ℝ) ^ 7 ≤ n := by nlinarith
  have hL3 := nat_mul_log_two_le_log 7 hn2
  push_cast at hL3
  have hL3' : 4.852 ≤ Real.log n := by linarith
  have hn3 : (2 : ℝ) ^ 9 ≤ n := by nlinarith
  have hL4 := nat_mul_log_two_le_log 9 hn3
  push_cast at hL4
  have hL4' : 6.2383 ≤ Real.log n := by linarith
  have hn4 : (2 : ℝ) ^ 10 ≤ n := by nlinarith
  have hL5 := nat_mul_log_two_le_log 10 hn4
  push_cast at hL5
  linarith

/-- `log x ≤ 11 log 2 + x / 2048 - 1` for `x > 0`. -/
theorem log_le_of_2048_c28 {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 11 * Real.log 2 + x / 2048 - 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 2048 by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h1
  have h2 : Real.log (2048 : ℝ) = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]; norm_num
  linarith

/-- Tangent-line lower bound for `1/x`: `2/X - x/X² ≤ 1/x` for `x, X > 0`. -/
theorem inv_ge_tangent_c28 {x X : ℝ} (hx : 0 < x) (hX : 0 < X) :
    2 / X - x / X ^ 2 ≤ 1 / x := by
  have h : 1 / x - (2 / X - x / X ^ 2) = (x - X) ^ 2 / (x * X ^ 2) := by
    field_simp
    ring
  have h0 : 0 ≤ (x - X) ^ 2 / (x * X ^ 2) := by positivity
  linarith

/-- (§7.2, `c = 28`) The final numerical inequality, in `L = log n ≥ 6.9314` and `s = √x`,
`s² = x = 28 L²`, with the `K = 1024` gain of §6.1. -/
theorem final_numeric_28 {L s : ℝ} (hL : 6.9314 ≤ L) (hs : s ^ 2 = 28 * L ^ 2) :
    (s + 5) * (L + 2) + Real.log (28 * L ^ 2) + 5
      < (28 * L ^ 2 - 3) * Real.log 2 / 2 - Real.log (28 * L ^ 2)
        + 239571 * Real.log 2 / (28 * L ^ 2) - 2 * (L + 1.84 * s) := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have hsL : s ≤ 5.2916 * L := by
    by_contra hc
    push Not at hc
    have hp : 0 < (s - 5.2916 * L) * (s + 5.2916 * L) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hx0 : 0 < 28 * L ^ 2 := by positivity
  have a1 : (28 * L ^ 2 - 3) * 0.6931471803 ≤ (28 * L ^ 2 - 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2l.le (by nlinarith)
  have p1 : s * L ≤ 5.2916 * L * L := mul_le_mul_of_nonneg_right hsL (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases le_or_gt L 10 with h10 | h10
  · -- `x ≤ 2800`: tangent-line bound for the gain
    have hy := log_le_of_2048_c28 hx0
    have ht := inv_ge_tangent_c28 hx0 (show (0 : ℝ) < 1600 by norm_num)
    have hL2 : L ^ 2 ≤ 100 := by nlinarith
    have ht0 : 0 ≤ 2 / 1600 - 28 * L ^ 2 / 1600 ^ 2 := by
      have : 28 * L ^ 2 / 1600 ^ 2 ≤ 2800 / 1600 ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num); linarith
      have h' : (2800 : ℝ) / 1600 ^ 2 ≤ 2 / 1600 := by norm_num
      linarith
    have hg : 239571 * 0.6931471803 * (2 / 1600 - 28 * L ^ 2 / 1600 ^ 2)
        ≤ 239571 * Real.log 2 / (28 * L ^ 2) := by
      calc 239571 * 0.6931471803 * (2 / 1600 - 28 * L ^ 2 / 1600 ^ 2)
          ≤ 239571 * Real.log 2 * (2 / 1600 - 28 * L ^ 2 / 1600 ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) ht0
        _ ≤ 239571 * Real.log 2 * (1 / (28 * L ^ 2)) :=
            mul_le_mul_of_nonneg_left ht (by positivity)
        _ = 239571 * Real.log 2 / (28 * L ^ 2) := by ring
    have hq : 0 ≤ (L - 7.2126) ^ 2 := sq_nonneg _
    nlinarith
  · -- `L ≥ 10`: no gain needed
    have hy := log_le_of_4096 hx0
    have hg : 0 ≤ 239571 * Real.log 2 / (28 * L ^ 2) := by positivity
    have hq : 0 ≤ (L - 10) ^ 2 := sq_nonneg _
    nlinarith

/-- (§7.3, round 5) **GRH ⟹ character form of Bach's bound with `c = 28`** (sorry-free, from
`bachInputs`). -/
theorem bachBoundChar_of_GRH_c28 (hGRH : DirichletLZerosOnLine) : BachBoundChar 28 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  have hL := log_ge_of_no_small_witness_28 hn χ hχ hcon
  have hx1 : (1 : ℝ) ≤ 28 * Real.log n ^ 2 := by nlinarith
  have hx1024 : (1024 : ℝ) < 28 * Real.log n ^ 2 := by nlinarith
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
  have hlow := re_smoothPsi_primitive_lower χ (x := 28 * Real.log n ^ 2) (by linarith) hcon
  have hE := noncoprimeSum_le_small (n := n) (by omega) (28 * Real.log n ^ 2)
  have hψ := psiOne_lower_1024 hx1024
  have hre := Complex.re_le_norm (smoothPsi χ.primitiveCharacter (28 * Real.log n ^ 2))
  have hs0 := Real.sqrt_nonneg (28 * Real.log n ^ 2)
  have hfin := final_numeric_28 hL
    (Real.sq_sqrt (show (0 : ℝ) ≤ 28 * Real.log n ^ 2 by linarith))
  have hmul : (√(28 * Real.log n ^ 2) + 5) * (Real.log χ.conductor + 2)
      ≤ (√(28 * Real.log n ^ 2) + 5) * (Real.log n + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- **Round 5 main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's bound
with the explicit constant `c = 28`. -/
theorem grh_implies_bach_c28 : GRHImpliesBach 28 :=
  fun hGRH => bachBound_of_bachBoundChar (bachBoundChar_of_GRH_c28 hGRH)

end DetPrimality.Bach
