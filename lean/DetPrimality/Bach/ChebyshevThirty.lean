import Mathlib
import DetPrimality.Bach.ConstPsiOneGrid

/-!
# Chebyshev's elementary lower bound with the "30" identity

With `log N! = ∑_{d ≤ N} Λ(d) ⌊N/d⌋` and `f(k) = k - ⌊k/2⌋ - ⌊k/3⌋ - ⌊k/5⌋ + ⌊k/30⌋ ≤ 1`,

  `ψ(N) ≥ log N! - log ⌊N/2⌋! - log ⌊N/3⌋! - log ⌊N/5⌋! + log ⌊N/30⌋!`  (`cheb30_factorials_le_psi`).

Two-sided Stirling bounds (Mathlib's `le_log_factorial_stirling` and the antitonicity of the
Stirling sequence) give, for `N ≥ 30` (`cheb30_psi_ge`),

  `ψ(N) ≥ 0.92129 N - (3/2) log N + 2.2337 - 30/N`,

where `0.92129 < A = log(2^(1/2) 3^(1/3) 5^(1/5) / 30^(1/30)) = 0.921292…`.  Summing
(`cheb30_sum_psi_ge`) and using `x ψ₁(x) ≥ ∑_{k<N} ψ(k) + (x-N) ψ(N)`:

  `ψ₁(x) ≥ 0.460645 x - (3/2) log x + 3.273 - (30 log x + 265)/x`  for `x > 30`
  (`psiOne_lower_cheb30_sharp`), hence `ψ₁(x) ≥ 0.46 x - (3/2) log x` for `x ≥ 200`
  (`psiOne_lower_cheb30`).
-/

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `log M! = ∑_{m ≤ M} log m`. -/
theorem cheb30_log_factorial_sum (M : ℕ) :
    Real.log (M.factorial : ℝ) = ∑ m ∈ Finset.Ioc 0 M, Real.log (m : ℝ) := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), add_comm]

/-- Legendre/Chebyshev: `log M! = ∑_{d ≤ N} Λ(d) ⌊M/d⌋` for any `N ≥ M`. -/
theorem cheb30_log_factorial_eq {M N : ℕ} (h : M ≤ N) :
    Real.log (M.factorial : ℝ) = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((M / d : ℕ) : ℝ) := by
  rw [cheb30_log_factorial_sum]
  have h1 : ∀ m ∈ Finset.Ioc 0 M, Real.log (m : ℝ)
      = ∑ d ∈ Finset.Ioc 0 N, if d ∣ m then Λ d else 0 := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [← ArithmeticFunction.vonMangoldt_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hm.1, (Nat.le_of_dvd hm.1 hd).trans (by omega)⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div,
    mul_comm]

/-- **Chebyshev's "30" inequality.**
`log N! - log ⌊N/2⌋! - log ⌊N/3⌋! - log ⌊N/5⌋! + log ⌊N/30⌋! ≤ ψ(N)`. -/
theorem cheb30_factorials_le_psi (N : ℕ) :
    Real.log (N.factorial : ℝ) - Real.log ((N / 2).factorial : ℝ)
        - Real.log ((N / 3).factorial : ℝ) - Real.log ((N / 5).factorial : ℝ)
        + Real.log ((N / 30).factorial : ℝ) ≤ Chebyshev.psi (N : ℝ) := by
  rw [cheb30_log_factorial_eq (le_refl N), cheb30_log_factorial_eq (Nat.div_le_self N 2),
    cheb30_log_factorial_eq (Nat.div_le_self N 3), cheb30_log_factorial_eq (Nat.div_le_self N 5),
    cheb30_log_factorial_eq (Nat.div_le_self N 30)]
  unfold Chebyshev.psi
  rw [Nat.floor_natCast, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d _ => ?_
  have e2 : N / 2 / d = N / d / 2 := Nat.div_right_comm N 2 d
  have e3 : N / 3 / d = N / d / 3 := Nat.div_right_comm N 3 d
  have e5 : N / 5 / d = N / d / 5 := Nat.div_right_comm N 5 d
  have e30 : N / 30 / d = N / d / 30 := Nat.div_right_comm N 30 d
  rw [e2, e3, e5, e30]
  have hk : N / d + N / d / 30 ≤ 1 + N / d / 2 + N / d / 3 + N / d / 5 := by omega
  have hk' : ((N / d + N / d / 30 : ℕ) : ℝ) ≤ ((1 + N / d / 2 + N / d / 3 + N / d / 5 : ℕ) : ℝ) :=
    by exact_mod_cast hk
  simp only [Nat.cast_add, Nat.cast_one] at hk'
  have h0 : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  calc Λ d * ((N / d : ℕ) : ℝ) - Λ d * ((N / d / 2 : ℕ) : ℝ) - Λ d * ((N / d / 3 : ℕ) : ℝ)
        - Λ d * ((N / d / 5 : ℕ) : ℝ) + Λ d * ((N / d / 30 : ℕ) : ℝ)
      = Λ d * (((N / d : ℕ) : ℝ) - ((N / d / 2 : ℕ) : ℝ) - ((N / d / 3 : ℕ) : ℝ)
        - ((N / d / 5 : ℕ) : ℝ) + ((N / d / 30 : ℕ) : ℝ)) := by ring
    _ ≤ Λ d * 1 := mul_le_mul_of_nonneg_left (by linarith) h0
    _ = Λ d := mul_one _

/-- Stirling upper bound: `log n! ≤ n log n - n + (log n)/2 + 1` for `n ≥ 1`. -/
theorem cheb30_log_factorial_le {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h : Real.log (Stirling.stirlingSeq (m + 1)) ≤ Real.log (Stirling.stirlingSeq 1) :=
    Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  have h0 : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one, Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
      Real.log_sqrt (by norm_num)]
  have hx : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [Stirling.log_stirlingSeq_formula, h0, Real.log_mul (by norm_num) hx.ne',
    Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- `t ↦ t log t - t + (log t)/2` is monotone on `[1, ∞)`. -/
theorem cheb30_g_mono {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    s * Real.log s - s + Real.log s / 2 ≤ t * Real.log t - t + Real.log t / 2 := by
  have hs0 : 0 < s := by linarith
  have ht : 0 < t := by linarith
  have h1 : Real.log (s / t) ≤ s / t - 1 := Real.log_le_sub_one_of_pos (div_pos hs0 ht)
  rw [Real.log_div hs0.ne' ht.ne'] at h1
  have h2 : t * (Real.log s - Real.log t) ≤ s - t := by
    have := mul_le_mul_of_nonneg_left h1 ht.le
    have e : t * (s / t - 1) = s - t := by field_simp
    rwa [e] at this
  have h3 : 0 ≤ Real.log s := Real.log_nonneg hs
  have h4 : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
  linarith [mul_nonneg (sub_nonneg.mpr hst) h3]

/-- Upper bound for `log ⌊N/j⌋!` in terms of the real quotient `N/j`. -/
theorem cheb30_upper {N j : ℕ} (hj : 0 < j) (h : j ≤ N) :
    Real.log ((N / j).factorial : ℝ)
      ≤ (N : ℝ) / j * Real.log ((N : ℝ) / j) - (N : ℝ) / j + Real.log ((N : ℝ) / j) / 2 + 1 := by
  have h1 : 1 ≤ N / j := (Nat.one_le_div_iff hj).mpr h
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have h2 : ((N / j : ℕ) : ℝ) ≤ (N : ℝ) / j := by
    rw [le_div_iff₀ hj0]; exact_mod_cast Nat.div_mul_le_self N j
  have h3 := cheb30_log_factorial_le (n := N / j) (by omega)
  have h4 := cheb30_g_mono (s := ((N / j : ℕ) : ℝ)) (t := (N : ℝ) / j) (by exact_mod_cast h1) h2
  linarith

/-- Lower bound for `log ⌊N/30⌋!` in terms of the real quotient `N/30`. -/
theorem cheb30_lower {N : ℕ} (h : 30 ≤ N) :
    (N : ℝ) / 30 * Real.log ((N : ℝ) / 30) - (N : ℝ) / 30 + Real.log ((N : ℝ) / 30) / 2
        + Real.log (2 * Real.pi) / 2 - Real.log ((N : ℝ) / 30 + 1)
      ≤ Real.log ((N / 30).factorial : ℝ) := by
  have hN : (30 : ℝ) ≤ N := by exact_mod_cast h
  have h1 : (1 : ℝ) ≤ (N : ℝ) / 30 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have h2 : (N : ℝ) / 30 ≤ ((N / 30 + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]; exact_mod_cast (by omega : N ≤ (N / 30 + 1) * 30)
  have h3 : ((N / 30 : ℕ) : ℝ) ≤ (N : ℝ) / 30 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self N 30
  have hS := Stirling.le_log_factorial_stirling (n := N / 30 + 1) (Nat.succ_ne_zero _)
  have hm := cheb30_g_mono h1 h2
  have hf : Real.log ((N / 30 + 1).factorial : ℝ)
      = Real.log (((N / 30 : ℕ) : ℝ) + 1) + Real.log ((N / 30).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast; ring
  have hl : Real.log (((N / 30 : ℕ) : ℝ) + 1) ≤ Real.log ((N : ℝ) / 30 + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

theorem cheb30_log_thirty : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
  rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

/-- `log(2π) ≥ log(25/4) = 2 log 5 - 2 log 2`. -/
theorem cheb30_log_two_pi : 2 * Real.log 5 - 2 * Real.log 2 ≤ Real.log (2 * Real.pi) := by
  have h : Real.log ((5 : ℝ) ^ 2 / 2 ^ 2) = 2 * Real.log 5 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  rw [← h]
  refine Real.log_le_log (by norm_num) ?_
  have := Real.pi_gt_d2
  linarith

/-- **Chebyshev-30 lower bound for `ψ`.** For `N ≥ 30`,
`ψ(N) ≥ 0.92129 N - (3/2) log N + 2.2337 - 30/N`. -/
theorem cheb30_psi_ge {N : ℕ} (hN : 30 ≤ N) :
    0.92129 * (N : ℝ) - 3 / 2 * Real.log N + 2.2337 - 30 / (N : ℝ) ≤ Chebyshev.psi (N : ℝ) := by
  have hn : (30 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hψ := cheb30_factorials_le_psi N
  have hS := Stirling.le_log_factorial_stirling (n := N) (by omega)
  have h2 := cheb30_upper (N := N) (j := 2) (by norm_num) (by omega)
  have h3 := cheb30_upper (N := N) (j := 3) (by norm_num) (by omega)
  have h5 := cheb30_upper (N := N) (j := 5) (by norm_num) (by omega)
  have h30 := cheb30_lower hN
  have e1 : Real.log ((N : ℝ) / 30 + 1) ≤ Real.log ((N : ℝ) / 30) + 30 / (N : ℝ) := by
    have e : (N : ℝ) / 30 + 1 = (N : ℝ) / 30 * (1 + 30 / (N : ℝ)) := by field_simp
    have hp : (0 : ℝ) < 1 + 30 / (N : ℝ) := by positivity
    rw [e, Real.log_mul (by positivity) hp.ne']
    have := Real.log_le_sub_one_of_pos hp
    linarith
  simp only [Nat.cast_ofNat] at h2 h3 h5
  rw [Real.log_div hn0.ne' (by norm_num)] at h2 h3 h5 h30 e1
  rw [cheb30_log_thirty] at h30 e1
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := Real.log_three_gt_d9
  have l5 := Real.log_five_gt_d9
  have hpi := cheb30_log_two_pi
  have hA : 0.92129 * (N : ℝ)
      ≤ (14 / 30 * Real.log 2 + 9 / 30 * Real.log 3 + 5 / 30 * Real.log 5) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hn0.le
  linarith

/-- Summed form: for `N ≥ 30`,
`∑_{k<N} ψ(k) ≥ 0.92129 N(N-1)/2 - (3/2)(N log N - N) + 2.2337 N - 30 log(N-1) - 262`. -/
theorem cheb30_sum_psi_ge {N : ℕ} (hN : 30 ≤ N) :
    0.92129 * ((N : ℝ) * ((N : ℝ) - 1) / 2) - 3 / 2 * ((N : ℝ) * Real.log N - N) + 2.2337 * (N : ℝ)
        - 30 * Real.log ((N : ℝ) - 1) - 262
      ≤ ∑ k ∈ Finset.range N, Chebyshev.psi (k : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h0 : 0 ≤ ∑ k ∈ Finset.range 30, Chebyshev.psi (k : ℝ) :=
      Finset.sum_nonneg fun k _ => Chebyshev.psi_nonneg _
    have l2 := Real.log_two_gt_d9
    have l3 := Real.log_three_gt_d9
    have l5 := Real.log_five_gt_d9
    have h29 : 3 * Real.log 3 ≤ Real.log 29 := by
      have h : Real.log ((3 : ℝ) ^ 3) = 3 * Real.log 3 := by rw [Real.log_pow]; push_cast; ring
      rw [← h]
      exact Real.log_le_log (by norm_num) (by norm_num)
    simp only [Nat.cast_ofNat]
    rw [show ((30 : ℝ) - 1) = 29 by norm_num, cheb30_log_thirty]
    linarith
  | succ N hN ih =>
    have hn : (30 : ℝ) ≤ N := by exact_mod_cast hN
    have hn0 : (0 : ℝ) < N := by linarith
    have hn1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    have hm : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have hψ := cheb30_psi_ge hN
    have hi : 1 ≤ ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - Real.log N) := by
      have h := Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
      rw [Real.log_div hn0.ne' hn1.ne'] at h
      have h' := mul_le_mul_of_nonneg_left h hn1.le
      have e : ((N : ℝ) + 1) * ((N : ℝ) / ((N : ℝ) + 1) - 1) = -1 := by field_simp; ring
      rw [e] at h'
      linarith
    have hii : 1 / (N : ℝ) ≤ Real.log N - Real.log ((N : ℝ) - 1) := by
      have h := Real.log_le_sub_one_of_pos (div_pos hm hn0)
      rw [Real.log_div hm.ne' hn0.ne'] at h
      have e : ((N : ℝ) - 1) / (N : ℝ) - 1 = -(1 / (N : ℝ)) := by field_simp; ring
      rw [e] at h
      linarith
    have hiii : 30 / (N : ℝ) ≤ 30 * (Real.log N - Real.log ((N : ℝ) - 1)) := by
      have e : 30 / (N : ℝ) = 30 * (1 / (N : ℝ)) := by ring
      rw [e]; linarith
    rw [Finset.sum_range_succ, show ((N + 1 : ℕ) : ℝ) - 1 = (N : ℝ) by push_cast; ring]
    push_cast
    linarith

/-- **Chebyshev-30 lower bound for `ψ₁`, sharp form.** For `x > 30`,
`ψ₁(x) ≥ 0.460645 x - (3/2) log x + 3.273 - (30 log x + 265)/x`. -/
theorem psiOne_lower_cheb30_sharp {x : ℝ} (hx : 30 < x) :
    0.460645 * x - 3 / 2 * Real.log x + 3.273 - (30 * Real.log x + 265) / x ≤ psiOne x := by
  have hx0 : 0 < x := by linarith
  have hM : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx0
  obtain ⟨N, hN⟩ : ∃ N, ⌈x⌉₊ = N + 1 := ⟨⌈x⌉₊ - 1, by omega⟩
  have hNx : (N : ℝ) < x := Nat.lt_ceil.mp (by omega)
  have hxN : x ≤ (N : ℝ) + 1 := by
    have := Nat.le_ceil x; rw [hN] at this; exact_mod_cast this
  have hN30 : 30 ≤ N := by
    by_contra h
    have : (N : ℝ) + 1 ≤ 30 := by exact_mod_cast (by omega : N + 1 ≤ 30)
    linarith
  have hn : (30 : ℝ) ≤ N := by exact_mod_cast hN30
  have hn0 : (0 : ℝ) < N := by linarith
  have key := psiOneGrid_mul_ge N hNx
  have hS := cheb30_sum_psi_ge hN30
  have hψ := cheb30_psi_ge hN30
  have hd0 : 0 ≤ x - N := by linarith
  have hd1 : x - N ≤ 1 := by linarith
  have hL : Real.log (N : ℝ) ≤ Real.log x := Real.log_le_log hn0 hNx.le
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hL1 : Real.log ((N : ℝ) - 1) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
  -- `(x - N) ψ(N) ≥ (x - N)(0.92129 N - 1.5 log N + 2.2337) - 1`
  have hr : 30 / (N : ℝ) ≤ 1 := by rw [div_le_one hn0]; exact hn
  have hr0 : 0 ≤ 30 / (N : ℝ) := by positivity
  have hψ' : (x - N) * (0.92129 * (N : ℝ) - 3 / 2 * Real.log N + 2.2337) - 1
      ≤ (x - N) * Chebyshev.psi (N : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hψ hd0
    have h2 : (x - N) * (30 / (N : ℝ)) ≤ 1 := by
      calc (x - N) * (30 / (N : ℝ)) ≤ 1 * 1 := mul_le_mul hd1 hr hr0 zero_le_one
        _ = 1 := one_mul 1
    linarith
  have h1 : (x ^ 2 - x) / 2 ≤ (N : ℝ) * ((N : ℝ) - 1) / 2 + (x - N) * N := by
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd1)]
  have h2 : x * Real.log (N : ℝ) ≤ x * Real.log x := mul_le_mul_of_nonneg_left hL hx0.le
  have e : x * ((30 * Real.log x + 265) / x) = 30 * Real.log x + 265 := by field_simp
  have hC : x * (0.460645 * x - 3 / 2 * Real.log x + 3.273 - (30 * Real.log x + 265) / x)
      ≤ x * psiOne x := by
    rw [mul_sub, e]
    linarith
  exact le_of_mul_le_mul_left hC hx0

/-- `log x ≤ log X + x/X - 1` (tangent line at `X`). -/
theorem cheb30_log_le_tangent {X x : ℝ} (hX : 0 < X) (hx : 0 < x) :
    Real.log x ≤ Real.log X + x / X - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hX)
  rw [Real.log_div hx.ne' hX.ne'] at h
  linarith

/-- For `x ≥ 200`: `ψ₁(x) ≥ 0.460645 x - (3/2) log x`. -/
theorem psiOne_lower_cheb30_200 {x : ℝ} (hx : 200 ≤ x) :
    0.460645 * x - 3 / 2 * Real.log x ≤ psiOne x := by
  have hx0 : 0 < x := by linarith
  have h := psiOne_lower_cheb30_sharp (x := x) (by linarith)
  have ht := cheb30_log_le_tangent (X := 200) (by norm_num) hx0
  have h200 : Real.log 200 = 3 * Real.log 2 + 2 * Real.log 5 := by
    rw [show (200 : ℝ) = 2 ^ 3 * 5 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]; push_cast; ring
  have l2 := Real.log_two_lt_d9
  have l5 := Real.log_five_lt_d9
  have hq : (30 * Real.log x + 265) / x ≤ 3.273 := by
    rw [div_le_iff₀ hx0]; linarith
  linarith

/-- **Chebyshev-30 lower bound for `ψ₁`.** For `x ≥ 200`: `ψ₁(x) ≥ 0.46 x - (3/2) log x`. -/
theorem psiOne_lower_cheb30 {x : ℝ} (hx : 200 ≤ x) :
    0.46 * x - 3 / 2 * Real.log x ≤ psiOne x := by
  have h := psiOne_lower_cheb30_200 hx
  linarith

/-- For `x ≥ 6000`: `ψ₁(x) ≥ 0.460645 x - (3/2) log x + 3.18`. -/
theorem psiOne_lower_cheb30_6000 {x : ℝ} (hx : 6000 ≤ x) :
    0.460645 * x - 3 / 2 * Real.log x + 3.18 ≤ psiOne x := by
  have hx0 : 0 < x := by linarith
  have h := psiOne_lower_cheb30_sharp (x := x) (by linarith)
  have ht := cheb30_log_le_tangent (X := 6000) (by norm_num) hx0
  have h6000 : Real.log 6000 = 4 * Real.log 2 + Real.log 3 + 3 * Real.log 5 := by
    rw [show (6000 : ℝ) = 2 ^ 4 * 3 * 5 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have l2 := Real.log_two_lt_d9
  have l3 := Real.log_three_lt_d9
  have l5 := Real.log_five_lt_d9
  have hq : (30 * Real.log x + 265) / x ≤ 0.093 := by
    rw [div_le_iff₀ hx0]; linarith
  linarith

end DetPrimality.Bach
