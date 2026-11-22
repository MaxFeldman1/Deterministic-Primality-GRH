import Mathlib
import DetPrimality.Bach.ConstPsiOne

/-!
# Sharper §6.1 main term: exact `ψ` up to `K`, then Chebyshev

`psiOne_lower_integral` (`ConstPsiOne.lean`) bounds `x ψ₁(x) ≥ ∑_{k<N} ψ(k)` (`N = ⌈x⌉₊ - 1`)
from below by `F(N) = log 2 · N(N-1)/2 - N log N`, using Mathlib's `Chebyshev.psi_ge`
(`ψ(k) ≥ k log 2 - log (k+1)`) for *every* `k`.  For small `k` this throws away a lot:
`ψ(k) ≈ k`, not `k log 2`.

Here we keep the exact value of `∑_{k<K} ψ(k) = log ∏_{k<K} lcm(1..k)` for a fixed `K`,
certified by a single kernel computation (`decide +kernel`, no `native_decide`), and use
`Chebyshev.psi_ge` only for `K ≤ k < N`.  The "gap" `∑_{k<N} ψ(k) - F(N)` is non-decreasing in
`N` (`sum_psi_gap_mono`), so for `x > K`

  `ψ₁(x) ≥ (x - 3) log 2 / 2 - log x + D_K / x`,   `D_K = ∑_{k<K} ψ(k) - F(K)`.

Instances: `K = 2048` (`psiOne_lower_2048`, `D ≥ 946453 · log 2 ≈ 656031`) and
`K = 1024` (`psiOne_lower_1024`, `D ≥ 239571 · log 2 ≈ 166058`).
-/

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `lcmProd n = (lcm(1..n), ∏_{k<n} lcm(1..k))`, computed in one pass (kernel-friendly). -/
def lcmProd : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => (Nat.lcm (lcmProd n).1 (n + 1), (lcmProd n).2 * (lcmProd n).1)

theorem lcmUpto_zero' : Nat.lcmUpto 0 = 1 := by
  simp [Nat.lcmUpto]

theorem lcmUpto_succ' (n : ℕ) :
    Nat.lcmUpto (n + 1) = Nat.lcm (Nat.lcmUpto n) (n + 1) := by
  unfold Nat.lcmUpto
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (show 1 ≤ n + 1 by omega), Finset.lcm_insert, lcm_eq_nat_lcm]
  exact Nat.lcm_comm _ _

theorem lcmProd_eq (n : ℕ) :
    lcmProd n = (Nat.lcmUpto n, ∏ k ∈ Finset.range n, Nat.lcmUpto k) := by
  induction n with
  | zero => simp [lcmProd, lcmUpto_zero']
  | succ n ih =>
    refine Prod.ext ?_ ?_
    · simp only [lcmProd, ih, lcmUpto_succ']
    · simp only [lcmProd, ih, Finset.prod_range_succ]

theorem lcmProd_snd (n : ℕ) :
    (lcmProd n).2 = ∏ k ∈ Finset.range n, Nat.lcmUpto k :=
  congrArg Prod.snd (lcmProd_eq n)

/-- `∑_{k<K} ψ(k) = log ∏_{k<K} lcm(1..k)`. -/
theorem sum_psi_eq_log_lcmProd (K : ℕ) :
    ∑ k ∈ Finset.range K, Chebyshev.psi (k : ℝ) = Real.log ((lcmProd K).2 : ℝ) := by
  rw [lcmProd_snd, Nat.cast_prod,
    Real.log_prod (fun k _ => by exact_mod_cast (Nat.lcmUpto_pos k).ne')]
  exact Finset.sum_congr rfl fun k _ => Chebyshev.psi_eq_log_lcmUpto k

/-- The gap `∑_{k<N} ψ(k) - (log 2 · N(N-1)/2 - N log N)` is non-decreasing in `N`. -/
theorem sum_psi_gap_mono {K N : ℕ} (h : K ≤ N) :
    ∑ k ∈ Finset.range K, Chebyshev.psi (k : ℝ)
        - (Real.log 2 * ((K : ℝ) * (K - 1) / 2) - K * Real.log K)
      ≤ ∑ k ∈ Finset.range N, Chebyshev.psi (k : ℝ)
        - (Real.log 2 * ((N : ℝ) * (N - 1) / 2) - N * Real.log N) := by
  induction N, h using Nat.le_induction with
  | base => exact le_rfl
  | succ N _ ih =>
    rw [Finset.sum_range_succ]
    have h1 := Chebyshev.psi_ge N
    have h2 : (N : ℝ) * Real.log N ≤ N * Real.log ((N : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos N with h | h
      · simp [h]
      · have hN : (0 : ℝ) < N := by exact_mod_cast h
        exact mul_le_mul_of_nonneg_left (Real.log_le_log hN (by linarith)) hN.le
    push_cast
    nlinarith

/-- `x ψ₁(x) ≥ ∑_{k < ⌈x⌉₊ - 1} ψ(k)`. -/
theorem mul_psiOne_ge_sum {x : ℝ} (hx : 0 < x) :
    ∑ k ∈ Finset.range (⌈x⌉₊ - 1), Chebyshev.psi (k : ℝ) ≤ x * psiOne x := by
  have hM : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
  obtain ⟨N, hN⟩ : ∃ N, ⌈x⌉₊ = N + 1 := ⟨⌈x⌉₊ - 1, by omega⟩
  have hNx : (N : ℝ) < x := Nat.lt_ceil.mp (by omega)
  rw [hN, Nat.add_sub_cancel, sum_psi_eq, psiOne, hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have h0 : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  have : x * (Λ m * (1 - (m : ℝ) / x)) = Λ m * (x - m) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) h0

/-- **Certificate form.** If `2^B ≤ ∏_{k<K} lcm(1..k)` then for `x > K`, `x ≥ 1`,
`ψ₁(x) ≥ (x - 3) log 2 / 2 - log x + (B log 2 - log 2 · K(K-1)/2 + K log K) / x`. -/
theorem psiOne_lower_of_cert {K B : ℕ} (hcert : 2 ^ B ≤ (lcmProd K).2) {x : ℝ}
    (hKx : (K : ℝ) < x) (hx1 : 1 ≤ x) :
    (x - 3) * Real.log 2 / 2 - Real.log x
        + (B * Real.log 2 - Real.log 2 * ((K : ℝ) * (K - 1) / 2) + K * Real.log K) / x
      ≤ psiOne x := by
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg K) hKx
  have hM : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx0
  obtain ⟨N, hN⟩ : ∃ N, ⌈x⌉₊ = N + 1 := ⟨⌈x⌉₊ - 1, by omega⟩
  have hNx : (N : ℝ) < x := Nat.lt_ceil.mp (by omega)
  have hxN : x ≤ (N : ℝ) + 1 := by
    have := Nat.le_ceil x; rw [hN] at this; exact_mod_cast this
  have hKN : K ≤ N := by
    have : K < ⌈x⌉₊ := Nat.lt_ceil.mpr hKx
    omega
  have key := mul_psiOne_ge_sum hx0
  rw [hN, Nat.add_sub_cancel] at key
  have hgap := sum_psi_gap_mono hKN
  have hSK : (B : ℝ) * Real.log 2 ≤ ∑ k ∈ Finset.range K, Chebyshev.psi (k : ℝ) := by
    rw [sum_psi_eq_log_lcmProd, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hcert)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
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
  have hB2 := mul_le_mul_of_nonneg_left hB hl2.le
  set D := (B * Real.log 2 - Real.log 2 * ((K : ℝ) * (K - 1) / 2) + K * Real.log K) with hDdef
  have hD : x * (D / x) = D := by field_simp [hx0.ne']
  have hC : x * ((x - 3) * Real.log 2 / 2 - Real.log x + D / x) ≤ x * psiOne x := by
    rw [mul_add, hD]
    linarith
  exact le_of_mul_le_mul_left hC hx0

/-! ## Kernel certificates -/

/-- `∑_{k<1024} ψ(k) ≥ 753107 · log 2` (kernel computation, GMP-accelerated `Nat` ops). -/
theorem lcmProd_1024_cert : 2 ^ 753107 ≤ (lcmProd 1024).2 := by decide +kernel

/-- `∑_{k<2048} ψ(k) ≥ 3020053 · log 2` (kernel computation, GMP-accelerated `Nat` ops). -/
theorem lcmProd_2048_cert : 2 ^ 3020053 ≤ (lcmProd 2048).2 := by decide +kernel

theorem log_two_pow_nat (k : ℕ) : Real.log ((2 : ℝ) ^ k) = k * Real.log 2 := Real.log_pow 2 k

/-- **(§6.1, sharp, `K = 1024`)** For `x > 1024`:
`ψ₁(x) ≥ (x - 3) log 2 / 2 - log x + 239571 · log 2 / x`  (`239571 log 2 ≈ 166058`). -/
theorem psiOne_lower_1024 {x : ℝ} (hx : 1024 < x) :
    (x - 3) * Real.log 2 / 2 - Real.log x + 239571 * Real.log 2 / x ≤ psiOne x := by
  have h := psiOne_lower_of_cert lcmProd_1024_cert (x := x) (by exact_mod_cast hx) (by linarith)
  have hlog : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, log_two_pow_nat]; norm_num
  refine le_trans (le_of_eq ?_) h
  simp only [Nat.cast_ofNat]
  rw [hlog]
  ring

/-- **(§6.1, sharp, `K = 2048`)** For `x > 2048`:
`ψ₁(x) ≥ (x - 3) log 2 / 2 - log x + 946453 · log 2 / x`  (`946453 log 2 ≈ 656031`). -/
theorem psiOne_lower_2048 {x : ℝ} (hx : 2048 < x) :
    (x - 3) * Real.log 2 / 2 - Real.log x + 946453 * Real.log 2 / x ≤ psiOne x := by
  have h := psiOne_lower_of_cert lcmProd_2048_cert (x := x) (by exact_mod_cast hx) (by linarith)
  have hlog : Real.log (2048 : ℝ) = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ (11 : ℕ) by norm_num, log_two_pow_nat]; norm_num
  refine le_trans (le_of_eq ?_) h
  simp only [Nat.cast_ofNat]
  rw [hlog]
  ring

/-- Window form (constant gain): for `2048 < x ≤ X`,
`ψ₁(x) ≥ (x - 3) log 2 / 2 - log x + 946453 · log 2 / X`. -/
theorem psiOne_lower_2048_of_le {x X : ℝ} (hx : 2048 < x) (hX : x ≤ X) :
    (x - 3) * Real.log 2 / 2 - Real.log x + 946453 * Real.log 2 / X ≤ psiOne x := by
  have h := psiOne_lower_2048 hx
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have : 946453 * Real.log 2 / X ≤ 946453 * Real.log 2 / x :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hl2.le) (by linarith) hX
  linarith

end DetPrimality.Bach
