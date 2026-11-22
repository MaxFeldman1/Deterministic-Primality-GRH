import DetPrimality.Bach.Assembly
import DetPrimality.Bach.ConstPsiOne
import DetPrimality.Bach.ConstPsiOneSharp
import DetPrimality.Bach.ConstPsiTheta

/-!
# Lowering Bach's constant to `22`

The analytic part (`BachInputs`, `bachInputs`, `norm_smoothPsi_le_of_inputs`,
`re_smoothPsi_primitive_lower`) is reused verbatim, exactly as in `Constant46.lean`.  Nothing here
is new analysis: the file is an assembly of already-proved explicit lemmas, with a sharper
bootstrap and a case split of the final inequality.

Write `L = log n`, `x = 22 L²`, `s = √x`.  Assuming that no unit `a < x` has `χ a ≠ 1`, we have

* (upper bound, GRH) `‖ψ̃(x, χ*)‖ ≤ (s + 5)(log q + 2) + log x + 5` with `q ∣ n`;
* (lower bound) `Re ψ̃(x, χ*) ≥ ψ₁(x) - 2 ∑_{m<x,(m,n)>1} Λ(m)`,

and the contradiction is the *final inequality*

`(s + 5)(L + 2) + log x + 5 < (x - 3) log 2 / 2 - log x + g - 2 (L + A s)`,

where `A √x` bounds `ψ(x) - θ(x)` and `g` is a gain in the lower bound for `ψ₁`.

## Ingredients

* §7.1 bootstrap (`log_ge_of_no_small_witness_22`): `n > 22 (log n)² ⟹ n ≥ 2^10`, hence
  `L ≥ 10 log 2 > 6.9314` and `x > 1056.9 > 1024`.  The chain is
  `n ≥ 2^4, 2^7, 2^9`, then `n² ≥ 2^19`, `n⁴ ≥ 2^39`, `n⁸ ≥ 2^79`, `n ≥ 2^10`
  (fractional powers of two, through `nat_mul_log_two_le_mul_log`; no bound on `exp` is needed).
  The true fixed point of `e^L = 22 L²` is `L ≈ 6.976`.
* `final_of_quad`: with `s ≤ 4.6905 L` (`4.6905² ≥ 22`), `log 2 ∈ [0.6931471803, 0.6931471808]`
  and the tangent bound `log x ≤ k log 2 + x / 2^k - 1`, the final inequality follows from the
  positivity of an explicit quadratic in `L`.
* `gain_tangent`: the `ψ₁` gain `N log 2 / x` of `psiOne_lower_1024` is bounded below by its
  tangent at `x₀` (convexity of `1/x`), `N log 2 / x ≥ N · 0.6931471803 · (2/x₀ - x/x₀²)`,
  which is linear in `x = 22 L²` and so keeps the final inequality quadratic in `L`.

## The four cases (Lean-form margin = minimum of the quadratic on the range)

| range of `x = 22 L²`  | `ψ - θ` constant `A`           | `ψ₁` gain                               | `k` | margin |
|-----------------------|--------------------------------|-----------------------------------------|-----|--------|
| `(1024, 1450]`        | `1.35` (`[420, 2^16)`)         | `psiOne_lower_1024`, tangent at `1230`  | 10  | ≈ 37.7 |
| `(1450, 2048]`        | `1.35`                         | `psiOne_lower_1024`, tangent at `1720`  | 11  | ≈ 38.1 |
| `(2048, 4096]`        | `1.34` (`[2000, 2^16)`)        | `psiOne_lower_2048_of_le`, `X = 4096`   | 11  | ≈ 122  |
| `(4096, ∞)`           | `1.84` (all `x`)               | none (`psiOne_lower_integral`)          | 12  | ≈ 54   |

The binding region is `x ≈ 1700` (exact-model margin `≈ 38`).  For `c ≤ 21` the bootstrap only
gives `x₀ < 1024`, where the available `ψ₁` certificates (`K = 1024`, `K = 2048`) do not apply.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- `k log 2 ≤ j log n` as soon as `2 ^ k ≤ n ^ j` (fractional powers of two). -/
theorem nat_mul_log_two_le_mul_log {n : ℝ} (k j : ℕ) (h : (2 : ℝ) ^ k ≤ n ^ j) :
    (k : ℝ) * Real.log 2 ≤ (j : ℝ) * Real.log n := by
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log (n ^ j) := Real.log_le_log (by positivity) h
  rwa [Real.log_pow, Real.log_pow] at h1

/-- (§7.1, `c = 22`) If no unit `a < 22 (log n)²` has `χ a ≠ 1`, then `log n ≥ 6.9314`
(indeed `n ≥ 2^10`). -/
theorem log_ge_of_no_small_witness_22 {n : ℕ} (hn : 2 < n) (χ : DirichletCharacter ℂ n)
    (hχ : χ ≠ 1)
    (h : ∀ a : ℕ, (a : ℝ) < 22 * (Real.log n) ^ 2 → IsUnit (a : ZMod n) → χ (a : ZMod n) = 1) :
    6.9314 ≤ Real.log n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod n)ˣ, χ u ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hχ (MulChar.ext fun a => by rw [hc a, MulChar.one_apply_coe])
  have hval : ¬ (((u : ZMod n).val : ℝ) < 22 * Real.log n ^ 2) := fun hlt => hu (by
    have h1 := h (u : ZMod n).val hlt (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    rwa [ZMod.natCast_zmod_val] at h1)
  have hlt : ((u : ZMod n).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
  have hbig : 22 * Real.log n ^ 2 < n := by linarith [not_lt.mp hval]
  have h2 := Real.log_two_gt_d9
  have hn0 : (0 : ℝ) < n := by positivity
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  -- `n ≥ 2^4`
  have hn1 : (2 : ℝ) ^ 4 ≤ (n : ℝ) ^ 1 := by nlinarith
  have hL2 := nat_mul_log_two_le_mul_log 4 1 hn1
  push_cast at hL2
  have hL2' : 2.7725 ≤ Real.log n := by linarith
  -- `n ≥ 2^7`
  have hn2 : (2 : ℝ) ^ 7 ≤ (n : ℝ) ^ 1 := by nlinarith
  have hL3 := nat_mul_log_two_le_mul_log 7 1 hn2
  push_cast at hL3
  have hL3' : 4.852 ≤ Real.log n := by linarith
  -- `n ≥ 2^9`
  have hn3 : (2 : ℝ) ^ 9 ≤ (n : ℝ) ^ 1 := by nlinarith
  have hL4 := nat_mul_log_two_le_mul_log 9 1 hn3
  push_cast at hL4
  have hL4' : 6.2383 ≤ Real.log n := by linarith
  -- `n ≥ 856`, `n² ≥ 2^19`
  have hn4 : (856 : ℝ) ≤ n := by nlinarith
  have hn4' : (2 : ℝ) ^ 19 ≤ (n : ℝ) ^ 2 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn4 2)
  have hL5 := nat_mul_log_two_le_mul_log 19 2 hn4'
  push_cast at hL5
  have hL5' : 6.5848 ≤ Real.log n := by linarith
  -- `n ≥ 953`, `n⁴ ≥ 2^39`
  have hn5 : (953 : ℝ) ≤ n := by nlinarith
  have hn5' : (2 : ℝ) ^ 39 ≤ (n : ℝ) ^ 4 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn5 4)
  have hL6 := nat_mul_log_two_le_mul_log 39 4 hn5'
  push_cast at hL6
  have hL6' : 6.7581 ≤ Real.log n := by linarith
  -- `n ≥ 1004`, `n⁸ ≥ 2^79`
  have hn6 : (1004 : ℝ) ≤ n := by nlinarith
  have hn6' : (2 : ℝ) ^ 79 ≤ (n : ℝ) ^ 8 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn6 8)
  have hL7 := nat_mul_log_two_le_mul_log 79 8 hn6'
  push_cast at hL7
  have hL7' : 6.8448 ≤ Real.log n := by linarith
  -- `n ≥ 2^10`
  have hn7 : (2 : ℝ) ^ 10 ≤ (n : ℝ) ^ 1 := by nlinarith
  have hL8 := nat_mul_log_two_le_mul_log 10 1 hn7
  push_cast at hL8
  linarith

/-- Tangent bound `log x ≤ k log 2 + x / 2^k - 1` for `x > 0`. -/
theorem log_le_of_two_pow {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.log x ≤ k * Real.log 2 + x / 2 ^ k - 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 2 ^ k by positivity)
  rw [Real.log_div hx.ne' (by positivity), Real.log_pow] at h1
  linarith

/-- Tangent lower bound for the `ψ₁` gain `N log 2 / x` at `x₀` (convexity of `1/x`). -/
theorem gain_tangent {N x x0 : ℝ} (hN : 0 ≤ N) (hx : 0 < x) (hx0 : 0 < x0) (h2 : x ≤ 2 * x0) :
    N * 0.6931471803 * (2 / x0 - x / x0 ^ 2) ≤ N * Real.log 2 / x := by
  have h2l := Real.log_two_gt_d9
  have ht0 : 0 ≤ 2 / x0 - x / x0 ^ 2 := by
    have : 2 / x0 - x / x0 ^ 2 = (2 * x0 - x) / x0 ^ 2 := by field_simp
    rw [this]
    exact div_nonneg (by linarith) (by positivity)
  have ht1 : 2 / x0 - x / x0 ^ 2 ≤ 1 / x := by
    have : 1 / x - (2 / x0 - x / x0 ^ 2) = (x - x0) ^ 2 / (x * x0 ^ 2) := by
      field_simp
      ring
    have h3 : 0 ≤ (x - x0) ^ 2 / (x * x0 ^ 2) := by positivity
    linarith
  calc N * 0.6931471803 * (2 / x0 - x / x0 ^ 2)
      ≤ N * Real.log 2 * (2 / x0 - x / x0 ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2l.le hN) ht0
    _ ≤ N * Real.log 2 * (1 / x) :=
        mul_le_mul_of_nonneg_left ht1 (mul_nonneg hN (by linarith))
    _ = N * Real.log 2 / x := by ring

/-- (§7.2, generic) The final inequality with `ψ - θ` constant `A` and `ψ₁` gain `g` follows from
the positivity of an explicit quadratic in `L`, using `s ≤ 4.6905 L` and
`log x ≤ k log 2 + x / 2^k - 1`. -/
theorem final_of_quad {L s A g : ℝ} (k : ℕ) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hs : s ^ 2 = 22 * L ^ 2)
    (hq : 0 < (22 * L ^ 2 - 3) * 0.6931471803 / 2
        - 2 * (k * 0.6931471808 + 22 * L ^ 2 / 2 ^ k - 1) + g
        - 2 * L - 2 * (A * (4.6905 * L)) - (4.6905 * L + 5) * (L + 2) - 5) :
    (s + 5) * (L + 2) + Real.log (22 * L ^ 2) + 5
      < (22 * L ^ 2 - 3) * Real.log 2 / 2 - Real.log (22 * L ^ 2) + g
        - 2 * (L + A * s) := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have hsL : s ≤ 4.6905 * L := by
    by_contra hc
    push Not at hc
    have hp : 0 < (s - 4.6905 * L) * (s + 4.6905 * L) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hy := log_le_of_two_pow (x := 22 * L ^ 2) (by positivity) k
  have hk : (k : ℝ) * Real.log 2 ≤ k * 0.6931471808 :=
    mul_le_mul_of_nonneg_left h2u.le (Nat.cast_nonneg k)
  have a1 : (22 * L ^ 2 - 3) * 0.6931471803 ≤ (22 * L ^ 2 - 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2l.le (by nlinarith)
  have p1 : s * L ≤ 4.6905 * L * L := mul_le_mul_of_nonneg_right hsL (by linarith)
  have pA : A * s ≤ A * (4.6905 * L) := mul_le_mul_of_nonneg_left hsL hA
  linarith

/-- (§7.2, case `1024 < x ≤ 1450`) `A = 1.35`, gain of `psiOne_lower_1024` (tangent at `1230`). -/
theorem final_numeric_22_a {L s : ℝ} (hL : 6.9314 ≤ L) (hx : 22 * L ^ 2 ≤ 1450)
    (hs : s ^ 2 = 22 * L ^ 2) :
    (s + 5) * (L + 2) + Real.log (22 * L ^ 2) + 5
      < (22 * L ^ 2 - 3) * Real.log 2 / 2 - Real.log (22 * L ^ 2)
        + 239571 * 0.6931471803 * (2 / 1230 - 22 * L ^ 2 / 1230 ^ 2)
        - 2 * (L + 1.35 * s) := by
  have hU : L ≤ 8.1185 := by nlinarith
  refine final_of_quad 10 (by linarith) (by norm_num) hs ?_
  push_cast
  nlinarith [sq_nonneg (L - 8.1185)]

/-- (§7.2, case `1450 < x ≤ 2048`) `A = 1.35`, gain of `psiOne_lower_1024` (tangent at `1720`). -/
theorem final_numeric_22_b {L s : ℝ} (hL : 6.9314 ≤ L) (hx : 22 * L ^ 2 ≤ 2048)
    (hs : s ^ 2 = 22 * L ^ 2) :
    (s + 5) * (L + 2) + Real.log (22 * L ^ 2) + 5
      < (22 * L ^ 2 - 3) * Real.log 2 / 2 - Real.log (22 * L ^ 2)
        + 239571 * 0.6931471803 * (2 / 1720 - 22 * L ^ 2 / 1720 ^ 2)
        - 2 * (L + 1.35 * s) := by
  refine final_of_quad 11 (by linarith) (by norm_num) hs ?_
  push_cast
  nlinarith [sq_nonneg (L - 8.656)]

/-- (§7.2, case `2048 < x ≤ 4096`) `A = 1.34`, gain of `psiOne_lower_2048_of_le` at `X = 4096`. -/
theorem final_numeric_22_c {L s : ℝ} (hx : 2048 < 22 * L ^ 2) (hL : 0 ≤ L)
    (hs : s ^ 2 = 22 * L ^ 2) :
    (s + 5) * (L + 2) + Real.log (22 * L ^ 2) + 5
      < (22 * L ^ 2 - 3) * Real.log 2 / 2 - Real.log (22 * L ^ 2)
        + 946453 * 0.6931471803 / 4096
        - 2 * (L + 1.34 * s) := by
  have hL' : 9.648 ≤ L := by nlinarith
  refine final_of_quad 11 (by linarith) (by norm_num) hs ?_
  push_cast
  nlinarith [sq_nonneg (L - 9.648)]

/-- (§7.2, case `x > 4096`) `A = 1.84`, no gain. -/
theorem final_numeric_22_d {L s : ℝ} (hx : 4096 < 22 * L ^ 2) (hL : 0 ≤ L)
    (hs : s ^ 2 = 22 * L ^ 2) :
    (s + 5) * (L + 2) + Real.log (22 * L ^ 2) + 5
      < (22 * L ^ 2 - 3) * Real.log 2 / 2 - Real.log (22 * L ^ 2) + 0
        - 2 * (L + 1.84 * s) := by
  have hL' : 13.644 ≤ L := by nlinarith
  refine final_of_quad 12 (by linarith) (by norm_num) hs ?_
  push_cast
  nlinarith [sq_nonneg (L - 13.644)]

/-- (§7.3) **GRH ⟹ character form of Bach's bound with `c = 22`** (sorry-free, from
`bachInputs`). -/
theorem bachBoundChar_of_GRH_c22 (hGRH : DirichletLZerosOnLine) : BachBoundChar 22 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  have hL := log_ge_of_no_small_witness_22 hn χ hχ hcon
  have h2l := Real.log_two_gt_d9
  have hx1056 : (1056 : ℝ) < 22 * Real.log n ^ 2 := by nlinarith
  have hx1 : (1 : ℝ) ≤ 22 * Real.log n ^ 2 := by linarith
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
  have hlow := re_smoothPsi_primitive_lower χ (x := 22 * Real.log n ^ 2) (by linarith) hcon
  have hre := Complex.re_le_norm (smoothPsi χ.primitiveCharacter (22 * Real.log n ^ 2))
  have hs0 := Real.sqrt_nonneg (22 * Real.log n ^ 2)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 22 * Real.log n ^ 2 by linarith)
  have hmul : (√(22 * Real.log n ^ 2) + 5) * (Real.log χ.conductor + 2)
      ≤ (√(22 * Real.log n ^ 2) + 5) * (Real.log n + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hn0 : 0 < n := by omega
  rcases le_or_gt (22 * Real.log n ^ 2) 2048 with h2048 | h2048
  · -- `1024 < x ≤ 2048`
    have hE := noncoprimeSum_le_of_ge_420_of_lt_65536 (n := n) hn0
      (x := 22 * Real.log n ^ 2) (by linarith) (by linarith)
    have hψ := psiOne_lower_1024 (x := 22 * Real.log n ^ 2) (by linarith)
    rcases le_or_gt (22 * Real.log n ^ 2) 1450 with h1450 | h1450
    · have hg := gain_tangent (N := 239571) (x := 22 * Real.log n ^ 2) (x0 := 1230)
        (by norm_num) (by linarith) (by norm_num) (by linarith)
      have hfin := final_numeric_22_a hL h1450 hsq
      linarith
    · have hg := gain_tangent (N := 239571) (x := 22 * Real.log n ^ 2) (x0 := 1720)
        (by norm_num) (by linarith) (by norm_num) (by linarith)
      have hfin := final_numeric_22_b hL h2048 hsq
      linarith
  · rcases le_or_gt (22 * Real.log n ^ 2) 4096 with h4096 | h4096
    · -- `2048 < x ≤ 4096`
      have hE := noncoprimeSum_le_of_ge_2000_of_lt_65536 (n := n) hn0
        (x := 22 * Real.log n ^ 2) (by linarith) (by linarith)
      have hψ := psiOne_lower_2048_of_le (x := 22 * Real.log n ^ 2) (X := 4096) h2048 h4096
      have hg : 946453 * 0.6931471803 / 4096 ≤ 946453 * Real.log 2 / 4096 := by linarith
      have hfin := final_numeric_22_c h2048 (by linarith) hsq
      linarith
    · -- `x > 4096`
      have hE := noncoprimeSum_le_small (n := n) hn0 (22 * Real.log n ^ 2)
      have hψ := psiOne_lower_integral (x := 22 * Real.log n ^ 2) hx1
      have hfin := final_numeric_22_d h4096 (by linarith) hsq
      linarith

/-- **Main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's bound with the
explicit constant `c = 22`. -/
theorem grh_implies_bach_c22 : GRHImpliesBach 22 :=
  fun hGRH => bachBound_of_bachBoundChar (bachBoundChar_of_GRH_c22 hGRH)

end DetPrimality.Bach
