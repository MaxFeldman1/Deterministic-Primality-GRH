import Mathlib
import DetPrimality.Bach.Blueprint

/-!
# Sharper Chebyshev-type lower bound for `ψ₁` (constant-lowering, plan step 2)

`x ψ₁(x) = ∑_{m<x} Λ(m)(x-m) ≥ ∑_{k<N} ψ(k)` with `N = ⌈x⌉₊ - 1`, then Mathlib's
`Chebyshev.psi_ge` and `log N! ≤ N log N`.  Result (`psiOne_lower_integral`):
`ψ₁(x) ≥ (x-3) log 2 / 2 - log x` for `x ≥ 1`.
-/

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `ψ(N) = ∑_{m ≤ N} Λ(m)` as a sum over `range (N+1)`. -/
theorem psi_natCast_eq_sum_range (N : ℕ) :
    Chebyshev.psi (N : ℝ) = ∑ m ∈ Finset.range (N + 1), Λ m := by
  unfold Chebyshev.psi
  rw [Nat.floor_natCast, Finset.sum_range_succ', ArithmeticFunction.map_zero, add_zero]
  refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
  · intro m hm; rw [Finset.mem_Ioc] at hm; rw [Finset.mem_range]; omega
  · intro a ha b hb h; rw [Finset.mem_Ioc] at ha hb; omega
  · intro b hb; rw [Finset.mem_range] at hb
    exact ⟨b + 1, by rw [Finset.mem_Ioc]; omega, by simp⟩
  · intro m hm; rw [Finset.mem_Ioc] at hm
    rw [Nat.sub_add_cancel (by omega)]

/-- Summation by parts: `∑_{k<N} ψ(k) = ∑_{m ≤ N} Λ(m) (N - m)`. -/
theorem sum_psi_eq (N : ℕ) :
    ∑ k ∈ Finset.range N, Chebyshev.psi (k : ℝ)
      = ∑ m ∈ Finset.range (N + 1), Λ m * ((N : ℝ) - m) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, psi_natCast_eq_sum_range,
      Finset.sum_range_succ (fun m => Λ m * (((N + 1 : ℕ) : ℝ) - m)) (N + 1), sub_self, mul_zero,
      add_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast; ring

/-- `∑_{k<N} ψ(k) ≥ log 2 · N(N-1)/2 - N log N`. -/
theorem sum_psi_ge (N : ℕ) :
    Real.log 2 * ((N : ℝ) * (N - 1) / 2) - N * Real.log N
      ≤ ∑ k ∈ Finset.range N, Chebyshev.psi (k : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h1 := Chebyshev.psi_ge N
    have h2 : (N : ℝ) * Real.log N ≤ N * Real.log ((N : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos N with h | h
      · simp [h]
      · have hN : (0 : ℝ) < N := by exact_mod_cast h
        exact mul_le_mul_of_nonneg_left (Real.log_le_log hN (by linarith)) hN.le
    push_cast
    nlinarith

/-- Exact-shape intermediate bound: with `N = ⌈x⌉₊ - 1`,
`x ψ₁(x) ≥ log 2 · N(N-1)/2 - N log N`. -/
theorem mul_psiOne_ge {x : ℝ} (hx : 0 < x) :
    Real.log 2 * (((⌈x⌉₊ - 1 : ℕ) : ℝ) * (((⌈x⌉₊ - 1 : ℕ) : ℝ) - 1) / 2)
        - ((⌈x⌉₊ - 1 : ℕ) : ℝ) * Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ)
      ≤ x * psiOne x := by
  have hM : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
  obtain ⟨N, hN⟩ : ∃ N, ⌈x⌉₊ = N + 1 := ⟨⌈x⌉₊ - 1, by omega⟩
  have hNx : (N : ℝ) < x := Nat.lt_ceil.mp (by omega)
  rw [hN, Nat.add_sub_cancel]
  refine (sum_psi_ge N).trans ?_
  rw [sum_psi_eq, psiOne, hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have h0 : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  have : x * (Λ m * (1 - (m : ℝ) / x)) = Λ m * (x - m) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) h0

/-- (§6.1, integral form) `ψ₁(x) ≥ (x - 3) log 2 / 2 - log x` for `x ≥ 1`. -/
theorem psiOne_lower_integral {x : ℝ} (hx : 1 ≤ x) :
    (x - 3) * Real.log 2 / 2 - Real.log x ≤ psiOne x := by
  have hx0 : 0 < x := by linarith
  have hM : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx0
  have key := mul_psiOne_ge hx0
  obtain ⟨N, hN⟩ : ∃ N, ⌈x⌉₊ = N + 1 := ⟨⌈x⌉₊ - 1, by omega⟩
  rw [hN, Nat.add_sub_cancel] at key
  have hNx : (N : ℝ) < x := Nat.lt_ceil.mp (by omega)
  have hxN : x ≤ (N : ℝ) + 1 := by
    have := Nat.le_ceil x; rw [hN] at this; exact_mod_cast this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogN : Real.log (N : ℝ) ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h, hlogx]
    · exact Real.log_le_log (by exact_mod_cast h) hNx.le
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hA : (N : ℝ) * Real.log N ≤ x * Real.log x :=
    mul_le_mul hNx.le hlogN hlogN0 hx0.le
  have hB : x * (x - 3) ≤ (N : ℝ) * (N - 1) := by
    nlinarith [mul_nonneg hN0 (by linarith : (0 : ℝ) ≤ 1 - (x - N)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ x - N) (by linarith : (0 : ℝ) ≤ 3 - (x - N))]
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hC : x * ((x - 3) * Real.log 2 / 2 - Real.log x) ≤ x * psiOne x := by
    have := mul_le_mul_of_nonneg_left hB hl2.le
    nlinarith
  exact le_of_mul_le_mul_left hC hx0

end DetPrimality.Bach
