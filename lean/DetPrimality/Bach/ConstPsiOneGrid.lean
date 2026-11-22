import Mathlib
import DetPrimality.Bach.ConstPsiOneSharp

/-!
# Near-exact lower bounds for `ψ₁(x)` on a grid, `256 < x ≤ 1536`

`x ψ₁(x) = ∑_{m<x} Λ(m)(x - m) = ∫₀ˣ ψ`.  For a natural `K < x`, dropping the terms `m > K`,

  `x ψ₁(x) ≥ ∑_{m ≤ K} Λ(m)(x - m) = ∑_{k<K} ψ(k) + (x - K) ψ(K)`   (`psiOneGrid_mul_ge`).

Both `∑_{k<K} ψ(k) = log ∏_{k<K} lcm(1..k)` and `ψ(K) = log lcm(1..K)` are certified from below by
kernel computations `2^A ≤ ∏_{k<K} lcm(1..k)`, `2^B ≤ lcm(1..K)^8` (`decide +kernel`), giving

  `ψ₁(x) ≥ a_K - c_K / x`  for all `x > K`   (`psiOne_lower_grid_K`),

with `a_K ≈ ψ(K)`, `c_K ≈ K ψ(K) - ∑_{k<K} ψ(k)`; the loss on `(K, K+16]` is `≤ ∫_K^x (ψ - ψ(K)) / x`,
i.e. `≲ 128/x`.  Grid: `K = 256, 272, …, 1520`.  Combined: `psiOne_lower_grid`
(`ψ₁(x) ≥ x/2 - 2.6` on `(256, 1536]`).  (This file is generated; the generic lemmas are at the top.)
-/

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `x ψ₁(x) ≥ ∑_{k<K} ψ(k) + (x - K) ψ(K)` for `K < x`. -/
theorem psiOneGrid_mul_ge (K : ℕ) {x : ℝ} (hKx : (K : ℝ) < x) :
    ∑ k ∈ Finset.range K, Chebyshev.psi (k : ℝ) + (x - K) * Chebyshev.psi (K : ℝ)
      ≤ x * psiOne x := by
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg K) hKx
  have hle : K + 1 ≤ ⌈x⌉₊ := Nat.lt_ceil.mpr hKx
  rw [sum_psi_eq, psi_natCast_eq_sum_range, Finset.mul_sum, ← Finset.sum_add_distrib, psiOne,
    Finset.mul_sum]
  calc ∑ m ∈ Finset.range (K + 1), (Λ m * ((K : ℝ) - m) + (x - K) * Λ m)
      = ∑ m ∈ Finset.range (K + 1), x * (Λ m * (1 - (m : ℝ) / x)) :=
        Finset.sum_congr rfl fun m _ => by field_simp; ring
    _ ≤ ∑ m ∈ Finset.range ⌈x⌉₊, x * (Λ m * (1 - (m : ℝ) / x)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle) fun m hm _ => ?_
        have hmx : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
        have h0 : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
        have h1 : (m : ℝ) / x ≤ 1 := (div_le_one hx0).mpr hmx.le
        exact mul_nonneg hx0.le (mul_nonneg h0 (by linarith))

/-- **Certificate form.** If `2^A ≤ ∏_{k<K} lcm(1..k)` and `2^B ≤ lcm(1..K)^8` then for `x > K`,
`x ψ₁(x) ≥ log 2 · (A + (x - K) B / 8)`. -/
theorem psiOneGrid_of_cert {K A B : ℕ} (hA : 2 ^ A ≤ (lcmProd K).2)
    (hB : 2 ^ B ≤ (lcmProd K).1 ^ 8) {x : ℝ} (hKx : (K : ℝ) < x) :
    Real.log 2 * (A + (x - K) * (B / 8)) ≤ x * psiOne x := by
  have key := psiOneGrid_mul_ge K hKx
  have hSK : (A : ℝ) * Real.log 2 ≤ ∑ k ∈ Finset.range K, Chebyshev.psi (k : ℝ) := by
    rw [sum_psi_eq_log_lcmProd, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hA)
  have hpsi : (B : ℝ) * Real.log 2 ≤ 8 * Chebyshev.psi (K : ℝ) := by
    have h1 : (lcmProd K).1 = Nat.lcmUpto K := congrArg Prod.fst (lcmProd_eq K)
    rw [Chebyshev.psi_eq_log_lcmUpto, ← h1, ← Real.log_pow,
      show (8 : ℝ) * Real.log ((lcmProd K).1 : ℝ) = Real.log (((lcmProd K).1 : ℝ) ^ 8) by
        rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hB)
  have hxK : 0 ≤ x - K := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hpsi hxK]

/-- Rational form: `a x - c ≤ x ψ₁(x)` given `a ≤ 0.6931471803 · B/8` and
`0.6931471803 · (K B / 8 - A) ≤ c`. -/
theorem psiOneGrid_mul {K A B : ℕ} (hA : 2 ^ A ≤ (lcmProd K).2)
    (hB : 2 ^ B ≤ (lcmProd K).1 ^ 8) {a c : ℝ}
    (ha : a ≤ 0.6931471803 * ((B : ℝ) / 8))
    (hc : 0.6931471803 * ((K : ℝ) * B / 8 - A) ≤ c) {x : ℝ} (hKx : (K : ℝ) < x) :
    a * x - c ≤ x * psiOne x := by
  have h := psiOneGrid_of_cert hA hB hKx
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg K) hKx
  have hl := Real.log_two_gt_d9
  have hnn : (0 : ℝ) ≤ A + (x - K) * (B / 8) :=
    add_nonneg (Nat.cast_nonneg A) (mul_nonneg (by linarith) (by positivity))
  nlinarith [mul_le_mul_of_nonneg_right hl.le hnn, mul_le_mul_of_nonneg_right ha hx0.le]

/-- Rational form: `a - c / x ≤ ψ₁(x)`. -/
theorem psiOneGrid_div {K A B : ℕ} (hA : 2 ^ A ≤ (lcmProd K).2)
    (hB : 2 ^ B ≤ (lcmProd K).1 ^ 8) {a c : ℝ}
    (ha : a ≤ 0.6931471803 * ((B : ℝ) / 8))
    (hc : 0.6931471803 * ((K : ℝ) * B / 8 - A) ≤ c) {x : ℝ} (hKx : (K : ℝ) < x) :
    a - c / x ≤ psiOne x := by
  have h := psiOneGrid_mul hA hB ha hc hKx
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg K) hKx
  refine le_of_mul_le_mul_left ?_ hx0
  have : x * (a - c / x) = a * x - c := by field_simp
  rw [this]; exact h

/-! ## Grid certificates (generated) -/

theorem psiOneGrid_cert_256 : 2 ^ 46551 ≤ (lcmProd 256).2 ∧ 2 ^ 2902 ≤ (lcmProd 256).1 ^ 8 := by
  decide +kernel

/-- For `x > 256`: `ψ₁(x) ≥ 251.439 - 32102/x` (sharp on `(256, 272]`). -/
theorem psiOne_lower_grid_256 {x : ℝ} (hx : 256 < x) : 251.439 - 32102 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_256.1 psiOneGrid_cert_256.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_256 {x : ℝ} (hx : 256 < x) : 251.439 * x - 32102 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_256.1 psiOneGrid_cert_256.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_272 : 2 ^ 52581 ≤ (lcmProd 272).2 ∧ 2 ^ 3160 ≤ (lcmProd 272).1 ^ 8 := by
  decide +kernel

/-- For `x > 272`: `ψ₁(x) ≥ 273.793 - 38026/x` (sharp on `(272, 288]`). -/
theorem psiOne_lower_grid_272 {x : ℝ} (hx : 272 < x) : 273.793 - 38026 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_272.1 psiOneGrid_cert_272.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_272 {x : ℝ} (hx : 272 < x) : 273.793 * x - 38026 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_272.1 psiOneGrid_cert_272.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_288 : 2 ^ 59089 ≤ (lcmProd 288).2 ∧ 2 ^ 3355 ≤ (lcmProd 288).1 ^ 8 := by
  decide +kernel

/-- For `x > 288`: `ψ₁(x) ≥ 290.688 - 42761/x` (sharp on `(288, 304]`). -/
theorem psiOne_lower_grid_288 {x : ℝ} (hx : 288 < x) : 290.688 - 42761 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_288.1 psiOneGrid_cert_288.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_288 {x : ℝ} (hx : 288 < x) : 290.688 * x - 42761 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_288.1 psiOneGrid_cert_288.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_304 : 2 ^ 65951 ≤ (lcmProd 304).2 ∧ 2 ^ 3453 ≤ (lcmProd 304).1 ^ 8 := by
  decide +kernel

/-- For `x > 304`: `ψ₁(x) ≥ 299.179 - 45237/x` (sharp on `(304, 320]`). -/
theorem psiOne_lower_grid_304 {x : ℝ} (hx : 304 < x) : 299.179 - 45237 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_304.1 psiOneGrid_cert_304.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_304 {x : ℝ} (hx : 304 < x) : 299.179 * x - 45237 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_304.1 psiOneGrid_cert_304.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_320 : 2 ^ 73123 ≤ (lcmProd 320).2 ∧ 2 ^ 3718 ≤ (lcmProd 320).1 ^ 8 := by
  decide +kernel

/-- For `x > 320`: `ψ₁(x) ≥ 322.140 - 52400/x` (sharp on `(320, 336]`). -/
theorem psiOne_lower_grid_320 {x : ℝ} (hx : 320 < x) : 322.140 - 52400 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_320.1 psiOneGrid_cert_320.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_320 {x : ℝ} (hx : 320 < x) : 322.140 * x - 52400 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_320.1 psiOneGrid_cert_320.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_336 : 2 ^ 80602 ≤ (lcmProd 336).2 ∧ 2 ^ 3785 ≤ (lcmProd 336).1 ^ 8 := by
  decide +kernel

/-- For `x > 336`: `ψ₁(x) ≥ 327.945 - 54321/x` (sharp on `(336, 352]`). -/
theorem psiOne_lower_grid_336 {x : ℝ} (hx : 336 < x) : 327.945 - 54321 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_336.1 psiOneGrid_cert_336.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_336 {x : ℝ} (hx : 336 < x) : 327.945 * x - 54321 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_336.1 psiOneGrid_cert_336.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_352 : 2 ^ 88392 ≤ (lcmProd 352).2 ∧ 2 ^ 4010 ≤ (lcmProd 352).1 ^ 8 := by
  decide +kernel

/-- For `x > 352`: `ψ₁(x) ≥ 347.440 - 61031/x` (sharp on `(352, 368]`). -/
theorem psiOne_lower_grid_352 {x : ℝ} (hx : 352 < x) : 347.440 - 61031 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_352.1 psiOneGrid_cert_352.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_352 {x : ℝ} (hx : 352 < x) : 347.440 * x - 61031 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_352.1 psiOneGrid_cert_352.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_368 : 2 ^ 96655 ≤ (lcmProd 368).2 ∧ 2 ^ 4248 ≤ (lcmProd 368).1 ^ 8 := by
  decide +kernel

/-- For `x > 368`: `ψ₁(x) ≥ 368.061 - 68451/x` (sharp on `(368, 384]`). -/
theorem psiOne_lower_grid_368 {x : ℝ} (hx : 368 < x) : 368.061 - 68451 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_368.1 psiOneGrid_cert_368.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_368 {x : ℝ} (hx : 368 < x) : 368.061 * x - 68451 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_368.1 psiOneGrid_cert_368.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_384 : 2 ^ 105297 ≤ (lcmProd 384).2 ∧ 2 ^ 4453 ≤ (lcmProd 384).1 ^ 8 := by
  decide +kernel

/-- For `x > 384`: `ψ₁(x) ≥ 385.823 - 75170/x` (sharp on `(384, 400]`). -/
theorem psiOne_lower_grid_384 {x : ℝ} (hx : 384 < x) : 385.823 - 75170 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_384.1 psiOneGrid_cert_384.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_384 {x : ℝ} (hx : 384 < x) : 385.823 * x - 75170 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_384.1 psiOneGrid_cert_384.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_400 : 2 ^ 114325 ≤ (lcmProd 400).2 ∧ 2 ^ 4591 ≤ (lcmProd 400).1 ^ 8 := by
  decide +kernel

/-- For `x > 400`: `ψ₁(x) ≥ 397.779 - 79868/x` (sharp on `(400, 416]`). -/
theorem psiOne_lower_grid_400 {x : ℝ} (hx : 400 < x) : 397.779 - 79868 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_400.1 psiOneGrid_cert_400.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_400 {x : ℝ} (hx : 400 < x) : 397.779 * x - 79868 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_400.1 psiOneGrid_cert_400.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_416 : 2 ^ 123698 ≤ (lcmProd 416).2 ∧ 2 ^ 4730 ≤ (lcmProd 416).1 ^ 8 := by
  decide +kernel

/-- For `x > 416`: `ψ₁(x) ≥ 409.823 - 84746/x` (sharp on `(416, 432]`). -/
theorem psiOne_lower_grid_416 {x : ℝ} (hx : 416 < x) : 409.823 - 84746 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_416.1 psiOneGrid_cert_416.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_416 {x : ℝ} (hx : 416 < x) : 409.823 * x - 84746 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_416.1 psiOneGrid_cert_416.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_432 : 2 ^ 133376 ≤ (lcmProd 432).2 ∧ 2 ^ 4939 ≤ (lcmProd 432).1 ^ 8 := by
  decide +kernel

/-- For `x > 432`: `ψ₁(x) ≥ 427.931 - 92418/x` (sharp on `(432, 448]`). -/
theorem psiOne_lower_grid_432 {x : ℝ} (hx : 432 < x) : 427.931 - 92418 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_432.1 psiOneGrid_cert_432.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_432 {x : ℝ} (hx : 432 < x) : 427.931 * x - 92418 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_432.1 psiOneGrid_cert_432.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_448 : 2 ^ 143510 ≤ (lcmProd 448).2 ∧ 2 ^ 5150 ≤ (lcmProd 448).1 ^ 8 := by
  decide +kernel

/-- For `x > 448`: `ψ₁(x) ≥ 446.213 - 100431/x` (sharp on `(448, 464]`). -/
theorem psiOne_lower_grid_448 {x : ℝ} (hx : 448 < x) : 446.213 - 100431 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_448.1 psiOneGrid_cert_448.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_448 {x : ℝ} (hx : 448 < x) : 446.213 * x - 100431 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_448.1 psiOneGrid_cert_448.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_464 : 2 ^ 154040 ≤ (lcmProd 464).2 ∧ 2 ^ 5433 ≤ (lcmProd 464).1 ^ 8 := by
  decide +kernel

/-- For `x > 464`: `ψ₁(x) ≥ 470.733 - 111648/x` (sharp on `(464, 480]`). -/
theorem psiOne_lower_grid_464 {x : ℝ} (hx : 464 < x) : 470.733 - 111648 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_464.1 psiOneGrid_cert_464.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_464 {x : ℝ} (hx : 464 < x) : 470.733 * x - 111648 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_464.1 psiOneGrid_cert_464.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_480 : 2 ^ 165030 ≤ (lcmProd 480).2 ∧ 2 ^ 5575 ≤ (lcmProd 480).1 ^ 8 := by
  decide +kernel

/-- For `x > 480`: `ψ₁(x) ≥ 483.036 - 117468/x` (sharp on `(480, 496]`). -/
theorem psiOne_lower_grid_480 {x : ℝ} (hx : 480 < x) : 483.036 - 117468 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_480.1 psiOneGrid_cert_480.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_480 {x : ℝ} (hx : 480 < x) : 483.036 * x - 117468 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_480.1 psiOneGrid_cert_480.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_496 : 2 ^ 176306 ≤ (lcmProd 496).2 ∧ 2 ^ 5718 ≤ (lcmProd 496).1 ^ 8 := by
  decide +kernel

/-- For `x > 496`: `ψ₁(x) ≥ 495.426 - 123526/x` (sharp on `(496, 512]`). -/
theorem psiOne_lower_grid_496 {x : ℝ} (hx : 496 < x) : 495.426 - 123526 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_496.1 psiOneGrid_cert_496.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_496 {x : ℝ} (hx : 496 < x) : 495.426 * x - 123526 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_496.1 psiOneGrid_cert_496.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_512 : 2 ^ 187966 ≤ (lcmProd 512).2 ∧ 2 ^ 5941 ≤ (lcmProd 512).1 ^ 8 := by
  decide +kernel

/-- For `x > 512`: `ψ₁(x) ≥ 514.748 - 133264/x` (sharp on `(512, 528]`). -/
theorem psiOne_lower_grid_512 {x : ℝ} (hx : 512 < x) : 514.748 - 133264 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_512.1 psiOneGrid_cert_512.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_512 {x : ℝ} (hx : 512 < x) : 514.748 * x - 133264 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_512.1 psiOneGrid_cert_512.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_528 : 2 ^ 199958 ≤ (lcmProd 528).2 ∧ 2 ^ 6086 ≤ (lcmProd 528).1 ^ 8 := by
  decide +kernel

/-- For `x > 528`: `ψ₁(x) ≥ 527.311 - 139821/x` (sharp on `(528, 544]`). -/
theorem psiOne_lower_grid_528 {x : ℝ} (hx : 528 < x) : 527.311 - 139821 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_528.1 psiOneGrid_cert_528.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_528 {x : ℝ} (hx : 528 < x) : 527.311 * x - 139821 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_528.1 psiOneGrid_cert_528.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_544 : 2 ^ 212225 ≤ (lcmProd 544).2 ∧ 2 ^ 6194 ≤ (lcmProd 544).1 ^ 8 := by
  decide +kernel

/-- For `x > 544`: `ψ₁(x) ≥ 536.669 - 144845/x` (sharp on `(544, 560]`). -/
theorem psiOne_lower_grid_544 {x : ℝ} (hx : 544 < x) : 536.669 - 144845 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_544.1 psiOneGrid_cert_544.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_544 {x : ℝ} (hx : 544 < x) : 536.669 * x - 144845 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_544.1 psiOneGrid_cert_544.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_560 : 2 ^ 224760 ≤ (lcmProd 560).2 ∧ 2 ^ 6340 ≤ (lcmProd 560).1 ^ 8 := by
  decide +kernel

/-- For `x > 560`: `ψ₁(x) ≥ 549.319 - 151827/x` (sharp on `(560, 576]`). -/
theorem psiOne_lower_grid_560 {x : ℝ} (hx : 560 < x) : 549.319 - 151827 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_560.1 psiOneGrid_cert_560.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_560 {x : ℝ} (hx : 560 < x) : 549.319 * x - 151827 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_560.1 psiOneGrid_cert_560.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_576 : 2 ^ 237670 ≤ (lcmProd 576).2 ∧ 2 ^ 6560 ≤ (lcmProd 576).1 ^ 8 := by
  decide +kernel

/-- For `x > 576`: `ψ₁(x) ≥ 568.380 - 162647/x` (sharp on `(576, 592]`). -/
theorem psiOne_lower_grid_576 {x : ℝ} (hx : 576 < x) : 568.380 - 162647 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_576.1 psiOneGrid_cert_576.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_576 {x : ℝ} (hx : 576 < x) : 568.380 * x - 162647 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_576.1 psiOneGrid_cert_576.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_592 : 2 ^ 250974 ≤ (lcmProd 592).2 ∧ 2 ^ 6707 ≤ (lcmProd 592).1 ^ 8 := by
  decide +kernel

/-- For `x > 592`: `ψ₁(x) ≥ 581.117 - 170060/x` (sharp on `(592, 608]`). -/
theorem psiOne_lower_grid_592 {x : ℝ} (hx : 592 < x) : 581.117 - 170060 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_592.1 psiOneGrid_cert_592.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_592 {x : ℝ} (hx : 592 < x) : 581.117 * x - 170060 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_592.1 psiOneGrid_cert_592.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_608 : 2 ^ 264683 ≤ (lcmProd 608).2 ∧ 2 ^ 7002 ≤ (lcmProd 608).1 ^ 8 := by
  decide +kernel

/-- For `x > 608`: `ψ₁(x) ≥ 606.677 - 185396/x` (sharp on `(608, 624]`). -/
theorem psiOne_lower_grid_608 {x : ℝ} (hx : 608 < x) : 606.677 - 185396 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_608.1 psiOneGrid_cert_608.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_608 {x : ℝ} (hx : 608 < x) : 606.677 * x - 185396 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_608.1 psiOneGrid_cert_608.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_624 : 2 ^ 278901 ≤ (lcmProd 624).2 ∧ 2 ^ 7224 ≤ (lcmProd 624).1 ^ 8 := by
  decide +kernel

/-- For `x > 624`: `ψ₁(x) ≥ 625.911 - 197250/x` (sharp on `(624, 640]`). -/
theorem psiOne_lower_grid_624 {x : ℝ} (hx : 624 < x) : 625.911 - 197250 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_624.1 psiOneGrid_cert_624.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_624 {x : ℝ} (hx : 624 < x) : 625.911 * x - 197250 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_624.1 psiOneGrid_cert_624.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_640 : 2 ^ 293469 ≤ (lcmProd 640).2 ∧ 2 ^ 7317 ≤ (lcmProd 640).1 ^ 8 := by
  decide +kernel

/-- For `x > 640`: `ψ₁(x) ≥ 633.969 - 202324/x` (sharp on `(640, 656]`). -/
theorem psiOne_lower_grid_640 {x : ℝ} (hx : 640 < x) : 633.969 - 202324 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_640.1 psiOneGrid_cert_640.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_640 {x : ℝ} (hx : 640 < x) : 633.969 * x - 202324 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_640.1 psiOneGrid_cert_640.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_656 : 2 ^ 308478 ≤ (lcmProd 656).2 ∧ 2 ^ 7616 ≤ (lcmProd 656).1 ^ 8 := by
  decide +kernel

/-- For `x > 656`: `ψ₁(x) ≥ 659.876 - 219059/x` (sharp on `(656, 672]`). -/
theorem psiOne_lower_grid_656 {x : ℝ} (hx : 656 < x) : 659.876 - 219059 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_656.1 psiOneGrid_cert_656.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_656 {x : ℝ} (hx : 656 < x) : 659.876 * x - 219059 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_656.1 psiOneGrid_cert_656.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_672 : 2 ^ 323936 ≤ (lcmProd 672).2 ∧ 2 ^ 7766 ≤ (lcmProd 672).1 ^ 8 := by
  decide +kernel

/-- For `x > 672`: `ψ₁(x) ≥ 672.872 - 227636/x` (sharp on `(672, 688]`). -/
theorem psiOne_lower_grid_672 {x : ℝ} (hx : 672 < x) : 672.872 - 227636 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_672.1 psiOneGrid_cert_672.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_672 {x : ℝ} (hx : 672 < x) : 672.872 * x - 227636 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_672.1 psiOneGrid_cert_672.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_688 : 2 ^ 339760 ≤ (lcmProd 688).2 ∧ 2 ^ 7992 ≤ (lcmProd 688).1 ^ 8 := by
  decide +kernel

/-- For `x > 688`: `ψ₁(x) ≥ 692.454 - 240905/x` (sharp on `(688, 704]`). -/
theorem psiOne_lower_grid_688 {x : ℝ} (hx : 688 < x) : 692.454 - 240905 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_688.1 psiOneGrid_cert_688.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_688 {x : ℝ} (hx : 688 < x) : 692.454 * x - 240905 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_688.1 psiOneGrid_cert_688.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_704 : 2 ^ 355896 ≤ (lcmProd 704).2 ∧ 2 ^ 8143 ≤ (lcmProd 704).1 ^ 8 := by
  decide +kernel

/-- For `x > 704`: `ψ₁(x) ≥ 705.537 - 250010/x` (sharp on `(704, 720]`). -/
theorem psiOne_lower_grid_704 {x : ℝ} (hx : 704 < x) : 705.537 - 250010 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_704.1 psiOneGrid_cert_704.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_704 {x : ℝ} (hx : 704 < x) : 705.537 * x - 250010 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_704.1 psiOneGrid_cert_704.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_720 : 2 ^ 372296 ≤ (lcmProd 720).2 ∧ 2 ^ 8294 ≤ (lcmProd 720).1 ^ 8 := by
  decide +kernel

/-- For `x > 720`: `ψ₁(x) ≥ 718.620 - 259351/x` (sharp on `(720, 736]`). -/
theorem psiOne_lower_grid_720 {x : ℝ} (hx : 720 < x) : 718.620 - 259351 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_720.1 psiOneGrid_cert_720.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_720 {x : ℝ} (hx : 720 < x) : 718.620 * x - 259351 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_720.1 psiOneGrid_cert_720.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_736 : 2 ^ 389011 ≤ (lcmProd 736).2 ∧ 2 ^ 8459 ≤ (lcmProd 736).1 ^ 8 := by
  decide +kernel

/-- For `x > 736`: `ψ₁(x) ≥ 732.916 - 269785/x` (sharp on `(736, 752]`). -/
theorem psiOne_lower_grid_736 {x : ℝ} (hx : 736 < x) : 732.916 - 269785 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_736.1 psiOneGrid_cert_736.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_736 {x : ℝ} (hx : 736 < x) : 732.916 * x - 269785 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_736.1 psiOneGrid_cert_736.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_752 : 2 ^ 406150 ≤ (lcmProd 752).2 ∧ 2 ^ 8688 ≤ (lcmProd 752).1 ^ 8 := by
  decide +kernel

/-- For `x > 752`: `ψ₁(x) ≥ 752.757 - 284553/x` (sharp on `(752, 768]`). -/
theorem psiOne_lower_grid_752 {x : ℝ} (hx : 752 < x) : 752.757 - 284553 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_752.1 psiOneGrid_cert_752.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_752 {x : ℝ} (hx : 752 < x) : 752.757 * x - 284553 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_752.1 psiOneGrid_cert_752.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_768 : 2 ^ 423699 ≤ (lcmProd 768).2 ∧ 2 ^ 8841 ≤ (lcmProd 768).1 ^ 8 := by
  decide +kernel

/-- For `x > 768`: `ψ₁(x) ≥ 766.014 - 294614/x` (sharp on `(768, 784]`). -/
theorem psiOne_lower_grid_768 {x : ℝ} (hx : 768 < x) : 766.014 - 294614 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_768.1 psiOneGrid_cert_768.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_768 {x : ℝ} (hx : 768 < x) : 766.014 * x - 294614 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_768.1 psiOneGrid_cert_768.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_784 : 2 ^ 441632 ≤ (lcmProd 784).2 ∧ 2 ^ 8995 ≤ (lcmProd 784).1 ^ 8 := by
  decide +kernel

/-- For `x > 784`: `ψ₁(x) ≥ 779.357 - 304901/x` (sharp on `(784, 800]`). -/
theorem psiOne_lower_grid_784 {x : ℝ} (hx : 784 < x) : 779.357 - 304901 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_784.1 psiOneGrid_cert_784.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_784 {x : ℝ} (hx : 784 < x) : 779.357 * x - 304901 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_784.1 psiOneGrid_cert_784.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_800 : 2 ^ 459777 ≤ (lcmProd 800).2 ∧ 2 ^ 9149 ≤ (lcmProd 800).1 ^ 8 := by
  decide +kernel

/-- For `x > 800`: `ψ₁(x) ≥ 792.700 - 315468/x` (sharp on `(800, 816]`). -/
theorem psiOne_lower_grid_800 {x : ℝ} (hx : 800 < x) : 792.700 - 315468 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_800.1 psiOneGrid_cert_800.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_800 {x : ℝ} (hx : 800 < x) : 792.700 * x - 315468 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_800.1 psiOneGrid_cert_800.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_816 : 2 ^ 478191 ≤ (lcmProd 816).2 ∧ 2 ^ 9303 ≤ (lcmProd 816).1 ^ 8 := by
  decide +kernel

/-- For `x > 816`: `ψ₁(x) ≥ 806.043 - 326275/x` (sharp on `(816, 832]`). -/
theorem psiOne_lower_grid_816 {x : ℝ} (hx : 816 < x) : 806.043 - 326275 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_816.1 psiOneGrid_cert_816.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_816 {x : ℝ} (hx : 816 < x) : 806.043 * x - 326275 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_816.1 psiOneGrid_cert_816.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_832 : 2 ^ 497070 ≤ (lcmProd 832).2 ∧ 2 ^ 9613 ≤ (lcmProd 832).1 ^ 8 := by
  decide +kernel

/-- For `x > 832`: `ψ₁(x) ≥ 832.902 - 348433/x` (sharp on `(832, 848]`). -/
theorem psiOne_lower_grid_832 {x : ℝ} (hx : 832 < x) : 832.902 - 348433 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_832.1 psiOneGrid_cert_832.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_832 {x : ℝ} (hx : 832 < x) : 832.902 * x - 348433 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_832.1 psiOneGrid_cert_832.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_848 : 2 ^ 516420 ≤ (lcmProd 848).2 ∧ 2 ^ 9730 ≤ (lcmProd 848).1 ^ 8 := by
  decide +kernel

/-- For `x > 848`: `ψ₁(x) ≥ 843.040 - 356944/x` (sharp on `(848, 864]`). -/
theorem psiOne_lower_grid_848 {x : ℝ} (hx : 848 < x) : 843.040 - 356944 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_848.1 psiOneGrid_cert_848.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_848 {x : ℝ} (hx : 848 < x) : 843.040 * x - 356944 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_848.1 psiOneGrid_cert_848.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_864 : 2 ^ 536114 ≤ (lcmProd 864).2 ∧ 2 ^ 10042 ≤ (lcmProd 864).1 ^ 8 := by
  decide +kernel

/-- For `x > 864`: `ψ₁(x) ≥ 870.072 - 380138/x` (sharp on `(864, 880]`). -/
theorem psiOne_lower_grid_864 {x : ℝ} (hx : 864 < x) : 870.072 - 380138 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_864.1 psiOneGrid_cert_864.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_864 {x : ℝ} (hx : 864 < x) : 870.072 * x - 380138 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_864.1 psiOneGrid_cert_864.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_880 : 2 ^ 556228 ≤ (lcmProd 880).2 ∧ 2 ^ 10120 ≤ (lcmProd 880).1 ^ 8 := by
  decide +kernel

/-- For `x > 880`: `ψ₁(x) ≥ 876.831 - 386064/x` (sharp on `(880, 896]`). -/
theorem psiOne_lower_grid_880 {x : ℝ} (hx : 880 < x) : 876.831 - 386064 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_880.1 psiOneGrid_cert_880.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_880 {x : ℝ} (hx : 880 < x) : 876.831 * x - 386064 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_880.1 psiOneGrid_cert_880.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_896 : 2 ^ 576832 ≤ (lcmProd 896).2 ∧ 2 ^ 10355 ≤ (lcmProd 896).1 ^ 8 := by
  decide +kernel

/-- For `x > 896`: `ψ₁(x) ≥ 897.192 - 404055/x` (sharp on `(896, 912]`). -/
theorem psiOne_lower_grid_896 {x : ℝ} (hx : 896 < x) : 897.192 - 404055 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_896.1 psiOneGrid_cert_896.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_896 {x : ℝ} (hx : 896 < x) : 897.192 * x - 404055 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_896.1 psiOneGrid_cert_896.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_912 : 2 ^ 597602 ≤ (lcmProd 912).2 ∧ 2 ^ 10512 ≤ (lcmProd 912).1 ^ 8 := by
  decide +kernel

/-- For `x > 912`: `ψ₁(x) ≥ 910.795 - 416420/x` (sharp on `(912, 928]`). -/
theorem psiOne_lower_grid_912 {x : ℝ} (hx : 912 < x) : 910.795 - 416420 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_912.1 psiOneGrid_cert_912.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_912 {x : ℝ} (hx : 912 < x) : 910.795 * x - 416420 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_912.1 psiOneGrid_cert_912.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_928 : 2 ^ 618716 ≤ (lcmProd 928).2 ∧ 2 ^ 10591 ≤ (lcmProd 928).1 ^ 8 := by
  decide +kernel

/-- For `x > 928`: `ψ₁(x) ≥ 917.640 - 422709/x` (sharp on `(928, 944]`). -/
theorem psiOne_lower_grid_928 {x : ℝ} (hx : 928 < x) : 917.640 - 422709 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_928.1 psiOneGrid_cert_928.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_928 {x : ℝ} (hx : 928 < x) : 917.640 * x - 422709 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_928.1 psiOneGrid_cert_928.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_944 : 2 ^ 640145 ≤ (lcmProd 944).2 ∧ 2 ^ 10828 ≤ (lcmProd 944).1 ^ 8 := by
  decide +kernel

/-- For `x > 944`: `ψ₁(x) ≥ 938.174 - 441923/x` (sharp on `(944, 960]`). -/
theorem psiOne_lower_grid_944 {x : ℝ} (hx : 944 < x) : 938.174 - 441923 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_944.1 psiOneGrid_cert_944.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_944 {x : ℝ} (hx : 944 < x) : 938.174 * x - 441923 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_944.1 psiOneGrid_cert_944.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_960 : 2 ^ 662000 ≤ (lcmProd 960).2 ∧ 2 ^ 10986 ≤ (lcmProd 960).1 ^ 8 := by
  decide +kernel

/-- For `x > 960`: `ψ₁(x) ≥ 951.864 - 454927/x` (sharp on `(960, 976]`). -/
theorem psiOne_lower_grid_960 {x : ℝ} (hx : 960 < x) : 951.864 - 454927 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_960.1 psiOneGrid_cert_960.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_960 {x : ℝ} (hx : 960 < x) : 951.864 * x - 454927 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_960.1 psiOneGrid_cert_960.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_976 : 2 ^ 684186 ≤ (lcmProd 976).2 ∧ 2 ^ 11184 ≤ (lcmProd 976).1 ^ 8 := by
  decide +kernel

/-- For `x > 976`: `ψ₁(x) ≥ 969.019 - 471522/x` (sharp on `(976, 992]`). -/
theorem psiOne_lower_grid_976 {x : ℝ} (hx : 976 < x) : 969.019 - 471522 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_976.1 psiOneGrid_cert_976.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_976 {x : ℝ} (hx : 976 < x) : 969.019 * x - 471522 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_976.1 psiOneGrid_cert_976.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_992 : 2 ^ 706804 ≤ (lcmProd 992).2 ∧ 2 ^ 11423 ≤ (lcmProd 992).1 ^ 8 := by
  decide +kernel

/-- For `x > 992`: `ψ₁(x) ≥ 989.727 - 491891/x` (sharp on `(992, 1008]`). -/
theorem psiOne_lower_grid_992 {x : ℝ} (hx : 992 < x) : 989.727 - 491891 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_992.1 psiOneGrid_cert_992.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_992 {x : ℝ} (hx : 992 < x) : 989.727 * x - 491891 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_992.1 psiOneGrid_cert_992.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1008 : 2 ^ 729761 ≤ (lcmProd 1008).2 ∧ 2 ^ 11503 ≤ (lcmProd 1008).1 ^ 8 := by
  decide +kernel

/-- For `x > 1008`: `ψ₁(x) ≥ 996.659 - 498801/x` (sharp on `(1008, 1024]`). -/
theorem psiOne_lower_grid_1008 {x : ℝ} (hx : 1008 < x) : 996.659 - 498801 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1008.1 psiOneGrid_cert_1008.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1008 {x : ℝ} (hx : 1008 < x) : 996.659 * x - 498801 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1008.1 psiOneGrid_cert_1008.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1024 : 2 ^ 753107 ≤ (lcmProd 1024).2 ∧ 2 ^ 11830 ≤ (lcmProd 1024).1 ^ 8 := by
  decide +kernel

/-- For `x > 1024`: `ψ₁(x) ≥ 1024.991 - 527578/x` (sharp on `(1024, 1040]`). -/
theorem psiOne_lower_grid_1024 {x : ℝ} (hx : 1024 < x) : 1024.991 - 527578 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1024.1 psiOneGrid_cert_1024.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1024 {x : ℝ} (hx : 1024 < x) : 1024.991 * x - 527578 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1024.1 psiOneGrid_cert_1024.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1040 : 2 ^ 776939 ≤ (lcmProd 1040).2 ∧ 2 ^ 12071 ≤ (lcmProd 1040).1 ^ 8 := by
  decide +kernel

/-- For `x > 1040`: `ψ₁(x) ≥ 1045.872 - 549175/x` (sharp on `(1040, 1056]`). -/
theorem psiOne_lower_grid_1040 {x : ℝ} (hx : 1040 < x) : 1045.872 - 549175 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1040.1 psiOneGrid_cert_1040.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1040 {x : ℝ} (hx : 1040 < x) : 1045.872 * x - 549175 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1040.1 psiOneGrid_cert_1040.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1056 : 2 ^ 801202 ≤ (lcmProd 1056).2 ∧ 2 ^ 12231 ≤ (lcmProd 1056).1 ^ 8 := by
  decide +kernel

/-- For `x > 1056`: `ψ₁(x) ≥ 1059.735 - 563730/x` (sharp on `(1056, 1072]`). -/
theorem psiOne_lower_grid_1056 {x : ℝ} (hx : 1056 < x) : 1059.735 - 563730 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1056.1 psiOneGrid_cert_1056.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1056 {x : ℝ} (hx : 1056 < x) : 1059.735 * x - 563730 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1056.1 psiOneGrid_cert_1056.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1072 : 2 ^ 825896 ≤ (lcmProd 1072).2 ∧ 2 ^ 12473 ≤ (lcmProd 1072).1 ^ 8 := by
  decide +kernel

/-- For `x > 1072`: `ψ₁(x) ≥ 1080.703 - 586047/x` (sharp on `(1072, 1088]`). -/
theorem psiOne_lower_grid_1072 {x : ℝ} (hx : 1072 < x) : 1080.703 - 586047 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1072.1 psiOneGrid_cert_1072.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1072 {x : ℝ} (hx : 1072 < x) : 1080.703 * x - 586047 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1072.1 psiOneGrid_cert_1072.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1088 : 2 ^ 850853 ≤ (lcmProd 1088).2 ∧ 2 ^ 12553 ≤ (lcmProd 1088).1 ^ 8 := by
  decide +kernel

/-- For `x > 1088`: `ψ₁(x) ≥ 1087.634 - 593581/x` (sharp on `(1088, 1104]`). -/
theorem psiOne_lower_grid_1088 {x : ℝ} (hx : 1088 < x) : 1087.634 - 593581 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1088.1 psiOneGrid_cert_1088.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1088 {x : ℝ} (hx : 1088 < x) : 1087.634 * x - 593581 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1088.1 psiOneGrid_cert_1088.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1104 : 2 ^ 876284 ≤ (lcmProd 1104).2 ∧ 2 ^ 12876 ≤ (lcmProd 1104).1 ^ 8 := by
  decide +kernel

/-- For `x > 1104`: `ψ₁(x) ≥ 1115.620 - 624252/x` (sharp on `(1104, 1120]`). -/
theorem psiOne_lower_grid_1104 {x : ℝ} (hx : 1104 < x) : 1115.620 - 624252 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1104.1 psiOneGrid_cert_1104.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1104 {x : ℝ} (hx : 1104 < x) : 1115.620 * x - 624252 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1104.1 psiOneGrid_cert_1104.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1120 : 2 ^ 902179 ≤ (lcmProd 1120).2 ∧ 2 ^ 13038 ≤ (lcmProd 1120).1 ^ 8 := by
  decide +kernel

/-- For `x > 1120`: `ψ₁(x) ≥ 1129.656 - 639873/x` (sharp on `(1120, 1136]`). -/
theorem psiOne_lower_grid_1120 {x : ℝ} (hx : 1120 < x) : 1129.656 - 639873 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1120.1 psiOneGrid_cert_1120.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1120 {x : ℝ} (hx : 1120 < x) : 1129.656 * x - 639873 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1120.1 psiOneGrid_cert_1120.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1136 : 2 ^ 928460 ≤ (lcmProd 1136).2 ∧ 2 ^ 13201 ≤ (lcmProd 1136).1 ^ 8 := by
  decide +kernel

/-- For `x > 1136`: `ψ₁(x) ≥ 1143.779 - 655775/x` (sharp on `(1136, 1152]`). -/
theorem psiOne_lower_grid_1136 {x : ℝ} (hx : 1136 < x) : 1143.779 - 655775 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1136.1 psiOneGrid_cert_1136.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1136 {x : ℝ} (hx : 1136 < x) : 1143.779 * x - 655775 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1136.1 psiOneGrid_cert_1136.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1152 : 2 ^ 954872 ≤ (lcmProd 1152).2 ∧ 2 ^ 13282 ≤ (lcmProd 1152).1 ^ 8 := by
  decide +kernel

/-- For `x > 1152`: `ψ₁(x) ≥ 1150.797 - 663853/x` (sharp on `(1152, 1168]`). -/
theorem psiOne_lower_grid_1152 {x : ℝ} (hx : 1152 < x) : 1150.797 - 663853 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1152.1 psiOneGrid_cert_1152.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1152 {x : ℝ} (hx : 1152 < x) : 1150.797 * x - 663853 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1152.1 psiOneGrid_cert_1152.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1168 : 2 ^ 981640 ≤ (lcmProd 1168).2 ∧ 2 ^ 13445 ≤ (lcmProd 1168).1 ^ 8 := by
  decide +kernel

/-- For `x > 1168`: `ψ₁(x) ≥ 1164.920 - 680207/x` (sharp on `(1168, 1184]`). -/
theorem psiOne_lower_grid_1168 {x : ℝ} (hx : 1168 < x) : 1164.920 - 680207 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1168.1 psiOneGrid_cert_1168.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1168 {x : ℝ} (hx : 1168 < x) : 1164.920 * x - 680207 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1168.1 psiOneGrid_cert_1168.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1184 : 2 ^ 1008694 ≤ (lcmProd 1184).2 ∧ 2 ^ 13608 ≤ (lcmProd 1184).1 ^ 8 := by
  decide +kernel

/-- For `x > 1184`: `ψ₁(x) ≥ 1179.043 - 696814/x` (sharp on `(1184, 1200]`). -/
theorem psiOne_lower_grid_1184 {x : ℝ} (hx : 1184 < x) : 1179.043 - 696814 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1184.1 psiOneGrid_cert_1184.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1184 {x : ℝ} (hx : 1184 < x) : 1179.043 * x - 696814 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1184.1 psiOneGrid_cert_1184.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1200 : 2 ^ 1036115 ≤ (lcmProd 1200).2 ∧ 2 ^ 13771 ≤ (lcmProd 1200).1 ^ 8 := by
  decide +kernel

/-- For `x > 1200`: `ψ₁(x) ≥ 1193.166 - 713620/x` (sharp on `(1200, 1216]`). -/
theorem psiOne_lower_grid_1200 {x : ℝ} (hx : 1200 < x) : 1193.166 - 713620 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1200.1 psiOneGrid_cert_1200.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1200 {x : ℝ} (hx : 1200 < x) : 1193.166 * x - 713620 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1200.1 psiOneGrid_cert_1200.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1216 : 2 ^ 1063843 ≤ (lcmProd 1216).2 ∧ 2 ^ 13935 ≤ (lcmProd 1216).1 ^ 8 := by
  decide +kernel

/-- For `x > 1216`: `ψ₁(x) ≥ 1207.375 - 730770/x` (sharp on `(1216, 1232]`). -/
theorem psiOne_lower_grid_1216 {x : ℝ} (hx : 1216 < x) : 1207.375 - 730770 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1216.1 psiOneGrid_cert_1216.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1216 {x : ℝ} (hx : 1216 < x) : 1207.375 * x - 730770 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1216.1 psiOneGrid_cert_1216.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1232 : 2 ^ 1092002 ≤ (lcmProd 1232).2 ∧ 2 ^ 14263 ≤ (lcmProd 1232).1 ^ 8 := by
  decide +kernel

/-- For `x > 1232`: `ψ₁(x) ≥ 1235.794 - 765582/x` (sharp on `(1232, 1248]`). -/
theorem psiOne_lower_grid_1232 {x : ℝ} (hx : 1232 < x) : 1235.794 - 765582 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1232.1 psiOneGrid_cert_1232.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1232 {x : ℝ} (hx : 1232 < x) : 1235.794 * x - 765582 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1232.1 psiOneGrid_cert_1232.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1248 : 2 ^ 1120643 ≤ (lcmProd 1248).2 ∧ 2 ^ 14346 ≤ (lcmProd 1248).1 ^ 8 := by
  decide +kernel

/-- For `x > 1248`: `ψ₁(x) ≥ 1242.986 - 774477/x` (sharp on `(1248, 1264]`). -/
theorem psiOne_lower_grid_1248 {x : ℝ} (hx : 1248 < x) : 1242.986 - 774477 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1248.1 psiOneGrid_cert_1248.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1248 {x : ℝ} (hx : 1248 < x) : 1242.986 * x - 774477 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1248.1 psiOneGrid_cert_1248.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1264 : 2 ^ 1149541 ≤ (lcmProd 1264).2 ∧ 2 ^ 14510 ≤ (lcmProd 1264).1 ^ 8 := by
  decide +kernel

/-- For `x > 1264`: `ψ₁(x) ≥ 1257.195 - 792295/x` (sharp on `(1264, 1280]`). -/
theorem psiOne_lower_grid_1264 {x : ℝ} (hx : 1264 < x) : 1257.195 - 792295 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1264.1 psiOneGrid_cert_1264.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1264 {x : ℝ} (hx : 1264 < x) : 1257.195 * x - 792295 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1264.1 psiOneGrid_cert_1264.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1280 : 2 ^ 1178604 ≤ (lcmProd 1280).2 ∧ 2 ^ 14675 ≤ (lcmProd 1280).1 ^ 8 := by
  decide +kernel

/-- For `x > 1280`: `ψ₁(x) ≥ 1271.491 - 810564/x` (sharp on `(1280, 1296]`). -/
theorem psiOne_lower_grid_1280 {x : ℝ} (hx : 1280 < x) : 1271.491 - 810564 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1280.1 psiOneGrid_cert_1280.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1280 {x : ℝ} (hx : 1280 < x) : 1271.491 * x - 810564 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1280.1 psiOneGrid_cert_1280.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1296 : 2 ^ 1208214 ≤ (lcmProd 1296).2 ∧ 2 ^ 14923 ≤ (lcmProd 1296).1 ^ 8 := by
  decide +kernel

/-- For `x > 1296`: `ψ₁(x) ≥ 1292.979 - 838232/x` (sharp on `(1296, 1312]`). -/
theorem psiOne_lower_grid_1296 {x : ℝ} (hx : 1296 < x) : 1292.979 - 838232 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1296.1 psiOneGrid_cert_1296.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1296 {x : ℝ} (hx : 1296 < x) : 1292.979 * x - 838232 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1296.1 psiOneGrid_cert_1296.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1312 : 2 ^ 1238475 ≤ (lcmProd 1312).2 ∧ 2 ^ 15254 ≤ (lcmProd 1312).1 ^ 8 := by
  decide +kernel

/-- For `x > 1312`: `ψ₁(x) ≥ 1321.658 - 875571/x` (sharp on `(1312, 1328]`). -/
theorem psiOne_lower_grid_1312 {x : ℝ} (hx : 1312 < x) : 1321.658 - 875571 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1312.1 psiOneGrid_cert_1312.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1312 {x : ℝ} (hx : 1312 < x) : 1321.658 * x - 875571 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1312.1 psiOneGrid_cert_1312.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1328 : 2 ^ 1269162 ≤ (lcmProd 1328).2 ∧ 2 ^ 15503 ≤ (lcmProd 1328).1 ^ 8 := by
  decide +kernel

/-- For `x > 1328`: `ψ₁(x) ≥ 1343.232 - 904097/x` (sharp on `(1328, 1344]`). -/
theorem psiOne_lower_grid_1328 {x : ℝ} (hx : 1328 < x) : 1343.232 - 904097 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1328.1 psiOneGrid_cert_1328.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1328 {x : ℝ} (hx : 1328 < x) : 1343.232 * x - 904097 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1328.1 psiOneGrid_cert_1328.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1344 : 2 ^ 1300214 ≤ (lcmProd 1344).2 ∧ 2 ^ 15531 ≤ (lcmProd 1344).1 ^ 8 := by
  decide +kernel

/-- For `x > 1344`: `ψ₁(x) ≥ 1345.658 - 907326/x` (sharp on `(1344, 1360]`). -/
theorem psiOne_lower_grid_1344 {x : ℝ} (hx : 1344 < x) : 1345.658 - 907326 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1344.1 psiOneGrid_cert_1344.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1344 {x : ℝ} (hx : 1344 < x) : 1345.658 * x - 907326 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1344.1 psiOneGrid_cert_1344.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1360 : 2 ^ 1331277 ≤ (lcmProd 1360).2 ∧ 2 ^ 15531 ≤ (lcmProd 1360).1 ^ 8 := by
  decide +kernel

/-- For `x > 1360`: `ψ₁(x) ≥ 1345.658 - 907325/x` (sharp on `(1360, 1376]`). -/
theorem psiOne_lower_grid_1360 {x : ℝ} (hx : 1360 < x) : 1345.658 - 907325 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1360.1 psiOneGrid_cert_1360.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1360 {x : ℝ} (hx : 1360 < x) : 1345.658 * x - 907325 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1360.1 psiOneGrid_cert_1360.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1376 : 2 ^ 1362658 ≤ (lcmProd 1376).2 ∧ 2 ^ 15823 ≤ (lcmProd 1376).1 ^ 8 := by
  decide +kernel

/-- For `x > 1376`: `ψ₁(x) ≥ 1370.958 - 941917/x` (sharp on `(1376, 1392]`). -/
theorem psiOne_lower_grid_1376 {x : ℝ} (hx : 1376 < x) : 1370.958 - 941917 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1376.1 psiOneGrid_cert_1376.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1376 {x : ℝ} (hx : 1376 < x) : 1370.958 * x - 941917 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1376.1 psiOneGrid_cert_1376.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1392 : 2 ^ 1394419 ≤ (lcmProd 1392).2 ∧ 2 ^ 15906 ≤ (lcmProd 1392).1 ^ 8 := by
  decide +kernel

/-- For `x > 1392`: `ψ₁(x) ≥ 1378.149 - 951848/x` (sharp on `(1392, 1408]`). -/
theorem psiOne_lower_grid_1392 {x : ℝ} (hx : 1392 < x) : 1378.149 - 951848 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1392.1 psiOneGrid_cert_1392.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1392 {x : ℝ} (hx : 1392 < x) : 1378.149 * x - 951848 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1392.1 psiOneGrid_cert_1392.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1408 : 2 ^ 1426326 ≤ (lcmProd 1408).2 ∧ 2 ^ 15990 ≤ (lcmProd 1408).1 ^ 8 := by
  decide +kernel

/-- For `x > 1408`: `ψ₁(x) ≥ 1385.427 - 962029/x` (sharp on `(1408, 1424]`). -/
theorem psiOne_lower_grid_1408 {x : ℝ} (hx : 1408 < x) : 1385.427 - 962029 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1408.1 psiOneGrid_cert_1408.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1408 {x : ℝ} (hx : 1408 < x) : 1385.427 * x - 962029 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1408.1 psiOneGrid_cert_1408.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1424 : 2 ^ 1458474 ≤ (lcmProd 1424).2 ∧ 2 ^ 16157 ≤ (lcmProd 1424).1 ^ 8 := by
  decide +kernel

/-- For `x > 1424`: `ψ₁(x) ≥ 1399.897 - 982517/x` (sharp on `(1424, 1440]`). -/
theorem psiOne_lower_grid_1424 {x : ℝ} (hx : 1424 < x) : 1399.897 - 982517 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1424.1 psiOneGrid_cert_1424.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1424 {x : ℝ} (hx : 1424 < x) : 1399.897 * x - 982517 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1424.1 psiOneGrid_cert_1424.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1440 : 2 ^ 1491125 ≤ (lcmProd 1440).2 ∧ 2 ^ 16493 ≤ (lcmProd 1440).1 ^ 8 := by
  decide +kernel

/-- For `x > 1440`: `ψ₁(x) ≥ 1429.009 - 1024205/x` (sharp on `(1440, 1456]`). -/
theorem psiOne_lower_grid_1440 {x : ℝ} (hx : 1440 < x) : 1429.009 - 1024205 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1440.1 psiOneGrid_cert_1440.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1440 {x : ℝ} (hx : 1440 < x) : 1429.009 * x - 1024205 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1440.1 psiOneGrid_cert_1440.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1456 : 2 ^ 1524290 ≤ (lcmProd 1456).2 ∧ 2 ^ 16745 ≤ (lcmProd 1456).1 ^ 8 := by
  decide +kernel

/-- For `x > 1456`: `ψ₁(x) ≥ 1450.843 - 1055872/x` (sharp on `(1456, 1472]`). -/
theorem psiOne_lower_grid_1456 {x : ℝ} (hx : 1456 < x) : 1450.843 - 1055872 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1456.1 psiOneGrid_cert_1456.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1456 {x : ℝ} (hx : 1456 < x) : 1450.843 * x - 1055872 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1456.1 psiOneGrid_cert_1456.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1472 : 2 ^ 1557928 ≤ (lcmProd 1472).2 ∧ 2 ^ 16913 ≤ (lcmProd 1472).1 ^ 8 := by
  decide +kernel

/-- For `x > 1472`: `ψ₁(x) ≥ 1465.399 - 1077196/x` (sharp on `(1472, 1488]`). -/
theorem psiOne_lower_grid_1472 {x : ℝ} (hx : 1472 < x) : 1465.399 - 1077196 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1472.1 psiOneGrid_cert_1472.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1472 {x : ℝ} (hx : 1472 < x) : 1465.399 * x - 1077196 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1472.1 psiOneGrid_cert_1472.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1488 : 2 ^ 1591892 ≤ (lcmProd 1488).2 ∧ 2 ^ 17166 ≤ (lcmProd 1488).1 ^ 8 := by
  decide +kernel

/-- For `x > 1488`: `ψ₁(x) ≥ 1487.320 - 1109718/x` (sharp on `(1488, 1504]`). -/
theorem psiOne_lower_grid_1488 {x : ℝ} (hx : 1488 < x) : 1487.320 - 1109718 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1488.1 psiOneGrid_cert_1488.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1488 {x : ℝ} (hx : 1488 < x) : 1487.320 * x - 1109718 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1488.1 psiOneGrid_cert_1488.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1504 : 2 ^ 1626551 ≤ (lcmProd 1504).2 ∧ 2 ^ 17419 ≤ (lcmProd 1504).1 ^ 8 := by
  decide +kernel

/-- For `x > 1504`: `ψ₁(x) ≥ 1509.241 - 1142460/x` (sharp on `(1504, 1520]`). -/
theorem psiOne_lower_grid_1504 {x : ℝ} (hx : 1504 < x) : 1509.241 - 1142460 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1504.1 psiOneGrid_cert_1504.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1504 {x : ℝ} (hx : 1504 < x) : 1509.241 * x - 1142460 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1504.1 psiOneGrid_cert_1504.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOneGrid_cert_1520 : 2 ^ 1661485 ≤ (lcmProd 1520).2 ∧ 2 ^ 17503 ≤ (lcmProd 1520).1 ^ 8 := by
  decide +kernel

/-- For `x > 1520`: `ψ₁(x) ≥ 1516.519 - 1153456/x` (sharp on `(1520, 1536]`). -/
theorem psiOne_lower_grid_1520 {x : ℝ} (hx : 1520 < x) : 1516.519 - 1153456 / x ≤ psiOne x :=
  psiOneGrid_div psiOneGrid_cert_1520.1 psiOneGrid_cert_1520.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

theorem psiOne_lower_grid_mul_1520 {x : ℝ} (hx : 1520 < x) : 1516.519 * x - 1153456 ≤ x * psiOne x :=
  psiOneGrid_mul psiOneGrid_cert_1520.1 psiOneGrid_cert_1520.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

private theorem psiOneGrid_cell_256 {x : ℝ} (hx : 256 < x) (hx' : x ≤ 272) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_256 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_272 {x : ℝ} (hx : 272 < x) (hx' : x ≤ 288) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_272 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_288 {x : ℝ} (hx : 288 < x) (hx' : x ≤ 304) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_288 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_304 {x : ℝ} (hx : 304 < x) (hx' : x ≤ 320) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_304 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_320 {x : ℝ} (hx : 320 < x) (hx' : x ≤ 336) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_320 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_336 {x : ℝ} (hx : 336 < x) (hx' : x ≤ 352) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_336 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_352 {x : ℝ} (hx : 352 < x) (hx' : x ≤ 368) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_352 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_368 {x : ℝ} (hx : 368 < x) (hx' : x ≤ 384) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_368 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_384 {x : ℝ} (hx : 384 < x) (hx' : x ≤ 400) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_384 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_400 {x : ℝ} (hx : 400 < x) (hx' : x ≤ 416) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_400 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_416 {x : ℝ} (hx : 416 < x) (hx' : x ≤ 432) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_416 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_432 {x : ℝ} (hx : 432 < x) (hx' : x ≤ 448) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_432 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_448 {x : ℝ} (hx : 448 < x) (hx' : x ≤ 464) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_448 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_464 {x : ℝ} (hx : 464 < x) (hx' : x ≤ 480) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_464 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_480 {x : ℝ} (hx : 480 < x) (hx' : x ≤ 496) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_480 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_496 {x : ℝ} (hx : 496 < x) (hx' : x ≤ 512) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_496 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_512 {x : ℝ} (hx : 512 < x) (hx' : x ≤ 528) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_512 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_528 {x : ℝ} (hx : 528 < x) (hx' : x ≤ 544) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_528 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_544 {x : ℝ} (hx : 544 < x) (hx' : x ≤ 560) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_544 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_560 {x : ℝ} (hx : 560 < x) (hx' : x ≤ 576) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_560 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_576 {x : ℝ} (hx : 576 < x) (hx' : x ≤ 592) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_576 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_592 {x : ℝ} (hx : 592 < x) (hx' : x ≤ 608) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_592 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_608 {x : ℝ} (hx : 608 < x) (hx' : x ≤ 624) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_608 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_624 {x : ℝ} (hx : 624 < x) (hx' : x ≤ 640) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_624 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_640 {x : ℝ} (hx : 640 < x) (hx' : x ≤ 656) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_640 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_656 {x : ℝ} (hx : 656 < x) (hx' : x ≤ 672) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_656 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_672 {x : ℝ} (hx : 672 < x) (hx' : x ≤ 688) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_672 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_688 {x : ℝ} (hx : 688 < x) (hx' : x ≤ 704) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_688 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_704 {x : ℝ} (hx : 704 < x) (hx' : x ≤ 720) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_704 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_720 {x : ℝ} (hx : 720 < x) (hx' : x ≤ 736) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_720 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_736 {x : ℝ} (hx : 736 < x) (hx' : x ≤ 752) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_736 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_752 {x : ℝ} (hx : 752 < x) (hx' : x ≤ 768) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_752 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_768 {x : ℝ} (hx : 768 < x) (hx' : x ≤ 784) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_768 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_784 {x : ℝ} (hx : 784 < x) (hx' : x ≤ 800) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_784 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_800 {x : ℝ} (hx : 800 < x) (hx' : x ≤ 816) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_800 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_816 {x : ℝ} (hx : 816 < x) (hx' : x ≤ 832) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_816 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_832 {x : ℝ} (hx : 832 < x) (hx' : x ≤ 848) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_832 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_848 {x : ℝ} (hx : 848 < x) (hx' : x ≤ 864) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_848 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_864 {x : ℝ} (hx : 864 < x) (hx' : x ≤ 880) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_864 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_880 {x : ℝ} (hx : 880 < x) (hx' : x ≤ 896) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_880 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_896 {x : ℝ} (hx : 896 < x) (hx' : x ≤ 912) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_896 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_912 {x : ℝ} (hx : 912 < x) (hx' : x ≤ 928) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_912 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_928 {x : ℝ} (hx : 928 < x) (hx' : x ≤ 944) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_928 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_944 {x : ℝ} (hx : 944 < x) (hx' : x ≤ 960) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_944 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_960 {x : ℝ} (hx : 960 < x) (hx' : x ≤ 976) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_960 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_976 {x : ℝ} (hx : 976 < x) (hx' : x ≤ 992) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_976 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_992 {x : ℝ} (hx : 992 < x) (hx' : x ≤ 1008) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_992 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1008 {x : ℝ} (hx : 1008 < x) (hx' : x ≤ 1024) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1008 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1024 {x : ℝ} (hx : 1024 < x) (hx' : x ≤ 1040) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1024 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1040 {x : ℝ} (hx : 1040 < x) (hx' : x ≤ 1056) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1040 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1056 {x : ℝ} (hx : 1056 < x) (hx' : x ≤ 1072) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1056 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1072 {x : ℝ} (hx : 1072 < x) (hx' : x ≤ 1088) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1072 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1088 {x : ℝ} (hx : 1088 < x) (hx' : x ≤ 1104) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1088 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1104 {x : ℝ} (hx : 1104 < x) (hx' : x ≤ 1120) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1104 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1120 {x : ℝ} (hx : 1120 < x) (hx' : x ≤ 1136) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1120 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1136 {x : ℝ} (hx : 1136 < x) (hx' : x ≤ 1152) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1136 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1152 {x : ℝ} (hx : 1152 < x) (hx' : x ≤ 1168) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1152 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1168 {x : ℝ} (hx : 1168 < x) (hx' : x ≤ 1184) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1168 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1184 {x : ℝ} (hx : 1184 < x) (hx' : x ≤ 1200) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1184 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1200 {x : ℝ} (hx : 1200 < x) (hx' : x ≤ 1216) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1200 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1216 {x : ℝ} (hx : 1216 < x) (hx' : x ≤ 1232) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1216 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1232 {x : ℝ} (hx : 1232 < x) (hx' : x ≤ 1248) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1232 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1248 {x : ℝ} (hx : 1248 < x) (hx' : x ≤ 1264) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1248 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1264 {x : ℝ} (hx : 1264 < x) (hx' : x ≤ 1280) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1264 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1280 {x : ℝ} (hx : 1280 < x) (hx' : x ≤ 1296) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1280 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1296 {x : ℝ} (hx : 1296 < x) (hx' : x ≤ 1312) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1296 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1312 {x : ℝ} (hx : 1312 < x) (hx' : x ≤ 1328) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1312 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1328 {x : ℝ} (hx : 1328 < x) (hx' : x ≤ 1344) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1328 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1344 {x : ℝ} (hx : 1344 < x) (hx' : x ≤ 1360) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1344 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1360 {x : ℝ} (hx : 1360 < x) (hx' : x ≤ 1376) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1360 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1376 {x : ℝ} (hx : 1376 < x) (hx' : x ≤ 1392) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1376 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1392 {x : ℝ} (hx : 1392 < x) (hx' : x ≤ 1408) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1392 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1408 {x : ℝ} (hx : 1408 < x) (hx' : x ≤ 1424) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1408 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1424 {x : ℝ} (hx : 1424 < x) (hx' : x ≤ 1440) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1424 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1440 {x : ℝ} (hx : 1440 < x) (hx' : x ≤ 1456) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1440 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1456 {x : ℝ} (hx : 1456 < x) (hx' : x ≤ 1472) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1456 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1472 {x : ℝ} (hx : 1472 < x) (hx' : x ≤ 1488) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1472 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1488 {x : ℝ} (hx : 1488 < x) (hx' : x ≤ 1504) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1488 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1504 {x : ℝ} (hx : 1504 < x) (hx' : x ≤ 1520) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1504 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

private theorem psiOneGrid_cell_1520 {x : ℝ} (hx : 1520 < x) (hx' : x ≤ 1536) :
    x / 2 - 2.6 ≤ psiOne x := by
  have h := psiOne_lower_grid_mul_1520 hx
  have hx0 : (0 : ℝ) < x := by linarith
  refine le_of_mul_le_mul_left ?_ hx0
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hx')]

/-- **Combined grid bound.** For `256 < x ≤ 1536`: `ψ₁(x) ≥ x/2 - 2.6`. -/
theorem psiOne_lower_grid {x : ℝ} (hx : 256 < x) (hx' : x ≤ 1536) : x / 2 - 2.6 ≤ psiOne x := by
  rcases le_or_gt x 272 with h | h
  · exact psiOneGrid_cell_256 (by assumption) h
  rcases le_or_gt x 288 with h | h
  · exact psiOneGrid_cell_272 (by assumption) h
  rcases le_or_gt x 304 with h | h
  · exact psiOneGrid_cell_288 (by assumption) h
  rcases le_or_gt x 320 with h | h
  · exact psiOneGrid_cell_304 (by assumption) h
  rcases le_or_gt x 336 with h | h
  · exact psiOneGrid_cell_320 (by assumption) h
  rcases le_or_gt x 352 with h | h
  · exact psiOneGrid_cell_336 (by assumption) h
  rcases le_or_gt x 368 with h | h
  · exact psiOneGrid_cell_352 (by assumption) h
  rcases le_or_gt x 384 with h | h
  · exact psiOneGrid_cell_368 (by assumption) h
  rcases le_or_gt x 400 with h | h
  · exact psiOneGrid_cell_384 (by assumption) h
  rcases le_or_gt x 416 with h | h
  · exact psiOneGrid_cell_400 (by assumption) h
  rcases le_or_gt x 432 with h | h
  · exact psiOneGrid_cell_416 (by assumption) h
  rcases le_or_gt x 448 with h | h
  · exact psiOneGrid_cell_432 (by assumption) h
  rcases le_or_gt x 464 with h | h
  · exact psiOneGrid_cell_448 (by assumption) h
  rcases le_or_gt x 480 with h | h
  · exact psiOneGrid_cell_464 (by assumption) h
  rcases le_or_gt x 496 with h | h
  · exact psiOneGrid_cell_480 (by assumption) h
  rcases le_or_gt x 512 with h | h
  · exact psiOneGrid_cell_496 (by assumption) h
  rcases le_or_gt x 528 with h | h
  · exact psiOneGrid_cell_512 (by assumption) h
  rcases le_or_gt x 544 with h | h
  · exact psiOneGrid_cell_528 (by assumption) h
  rcases le_or_gt x 560 with h | h
  · exact psiOneGrid_cell_544 (by assumption) h
  rcases le_or_gt x 576 with h | h
  · exact psiOneGrid_cell_560 (by assumption) h
  rcases le_or_gt x 592 with h | h
  · exact psiOneGrid_cell_576 (by assumption) h
  rcases le_or_gt x 608 with h | h
  · exact psiOneGrid_cell_592 (by assumption) h
  rcases le_or_gt x 624 with h | h
  · exact psiOneGrid_cell_608 (by assumption) h
  rcases le_or_gt x 640 with h | h
  · exact psiOneGrid_cell_624 (by assumption) h
  rcases le_or_gt x 656 with h | h
  · exact psiOneGrid_cell_640 (by assumption) h
  rcases le_or_gt x 672 with h | h
  · exact psiOneGrid_cell_656 (by assumption) h
  rcases le_or_gt x 688 with h | h
  · exact psiOneGrid_cell_672 (by assumption) h
  rcases le_or_gt x 704 with h | h
  · exact psiOneGrid_cell_688 (by assumption) h
  rcases le_or_gt x 720 with h | h
  · exact psiOneGrid_cell_704 (by assumption) h
  rcases le_or_gt x 736 with h | h
  · exact psiOneGrid_cell_720 (by assumption) h
  rcases le_or_gt x 752 with h | h
  · exact psiOneGrid_cell_736 (by assumption) h
  rcases le_or_gt x 768 with h | h
  · exact psiOneGrid_cell_752 (by assumption) h
  rcases le_or_gt x 784 with h | h
  · exact psiOneGrid_cell_768 (by assumption) h
  rcases le_or_gt x 800 with h | h
  · exact psiOneGrid_cell_784 (by assumption) h
  rcases le_or_gt x 816 with h | h
  · exact psiOneGrid_cell_800 (by assumption) h
  rcases le_or_gt x 832 with h | h
  · exact psiOneGrid_cell_816 (by assumption) h
  rcases le_or_gt x 848 with h | h
  · exact psiOneGrid_cell_832 (by assumption) h
  rcases le_or_gt x 864 with h | h
  · exact psiOneGrid_cell_848 (by assumption) h
  rcases le_or_gt x 880 with h | h
  · exact psiOneGrid_cell_864 (by assumption) h
  rcases le_or_gt x 896 with h | h
  · exact psiOneGrid_cell_880 (by assumption) h
  rcases le_or_gt x 912 with h | h
  · exact psiOneGrid_cell_896 (by assumption) h
  rcases le_or_gt x 928 with h | h
  · exact psiOneGrid_cell_912 (by assumption) h
  rcases le_or_gt x 944 with h | h
  · exact psiOneGrid_cell_928 (by assumption) h
  rcases le_or_gt x 960 with h | h
  · exact psiOneGrid_cell_944 (by assumption) h
  rcases le_or_gt x 976 with h | h
  · exact psiOneGrid_cell_960 (by assumption) h
  rcases le_or_gt x 992 with h | h
  · exact psiOneGrid_cell_976 (by assumption) h
  rcases le_or_gt x 1008 with h | h
  · exact psiOneGrid_cell_992 (by assumption) h
  rcases le_or_gt x 1024 with h | h
  · exact psiOneGrid_cell_1008 (by assumption) h
  rcases le_or_gt x 1040 with h | h
  · exact psiOneGrid_cell_1024 (by assumption) h
  rcases le_or_gt x 1056 with h | h
  · exact psiOneGrid_cell_1040 (by assumption) h
  rcases le_or_gt x 1072 with h | h
  · exact psiOneGrid_cell_1056 (by assumption) h
  rcases le_or_gt x 1088 with h | h
  · exact psiOneGrid_cell_1072 (by assumption) h
  rcases le_or_gt x 1104 with h | h
  · exact psiOneGrid_cell_1088 (by assumption) h
  rcases le_or_gt x 1120 with h | h
  · exact psiOneGrid_cell_1104 (by assumption) h
  rcases le_or_gt x 1136 with h | h
  · exact psiOneGrid_cell_1120 (by assumption) h
  rcases le_or_gt x 1152 with h | h
  · exact psiOneGrid_cell_1136 (by assumption) h
  rcases le_or_gt x 1168 with h | h
  · exact psiOneGrid_cell_1152 (by assumption) h
  rcases le_or_gt x 1184 with h | h
  · exact psiOneGrid_cell_1168 (by assumption) h
  rcases le_or_gt x 1200 with h | h
  · exact psiOneGrid_cell_1184 (by assumption) h
  rcases le_or_gt x 1216 with h | h
  · exact psiOneGrid_cell_1200 (by assumption) h
  rcases le_or_gt x 1232 with h | h
  · exact psiOneGrid_cell_1216 (by assumption) h
  rcases le_or_gt x 1248 with h | h
  · exact psiOneGrid_cell_1232 (by assumption) h
  rcases le_or_gt x 1264 with h | h
  · exact psiOneGrid_cell_1248 (by assumption) h
  rcases le_or_gt x 1280 with h | h
  · exact psiOneGrid_cell_1264 (by assumption) h
  rcases le_or_gt x 1296 with h | h
  · exact psiOneGrid_cell_1280 (by assumption) h
  rcases le_or_gt x 1312 with h | h
  · exact psiOneGrid_cell_1296 (by assumption) h
  rcases le_or_gt x 1328 with h | h
  · exact psiOneGrid_cell_1312 (by assumption) h
  rcases le_or_gt x 1344 with h | h
  · exact psiOneGrid_cell_1328 (by assumption) h
  rcases le_or_gt x 1360 with h | h
  · exact psiOneGrid_cell_1344 (by assumption) h
  rcases le_or_gt x 1376 with h | h
  · exact psiOneGrid_cell_1360 (by assumption) h
  rcases le_or_gt x 1392 with h | h
  · exact psiOneGrid_cell_1376 (by assumption) h
  rcases le_or_gt x 1408 with h | h
  · exact psiOneGrid_cell_1392 (by assumption) h
  rcases le_or_gt x 1424 with h | h
  · exact psiOneGrid_cell_1408 (by assumption) h
  rcases le_or_gt x 1440 with h | h
  · exact psiOneGrid_cell_1424 (by assumption) h
  rcases le_or_gt x 1456 with h | h
  · exact psiOneGrid_cell_1440 (by assumption) h
  rcases le_or_gt x 1472 with h | h
  · exact psiOneGrid_cell_1456 (by assumption) h
  rcases le_or_gt x 1488 with h | h
  · exact psiOneGrid_cell_1472 (by assumption) h
  rcases le_or_gt x 1504 with h | h
  · exact psiOneGrid_cell_1488 (by assumption) h
  rcases le_or_gt x 1520 with h | h
  · exact psiOneGrid_cell_1504 (by assumption) h
  exact psiOneGrid_cell_1520 h hx'


end DetPrimality.Bach
