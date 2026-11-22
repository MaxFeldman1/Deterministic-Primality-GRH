import Mathlib
import DetPrimality.Bach.Blueprint

/-!
# Sharpened §6.2: prime powers not coprime to `n`

Plan step 1 for lowering the constant `c` (see `STATUS.md`, "Plan for lowering c = 1024").

`Blueprint.noncoprimeSum_le` bounds `∑_{m<x, (m,n)>1} Λ(m)` by `log n + 3 (log 4 + 4) √x`
(≈ `16.16 √x`).  Here we keep the Costa-Pereira decomposition
`ψ(x) - θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})` and replace `psi_le_const_mul_self` by
Mathlib's sharper `Chebyshev.psi_le : ψ y ≤ log 4 · y + 2 √y log y` (for `y ≥ 1`).  This gives

`noncoprimeSum n x ≤ log n + sharpE x`, where
`sharpE x = log 4 · (√x + x^{1/3} + x^{1/5}) + log x · (x^{1/4} + ⅔ x^{1/6} + ⅖ x^{1/10})`.

`sharpE x / √x` is non-increasing for `log x ≥ 4` (`sharpE_le_of_le`), which yields the
concrete corollaries `sharpE x ≤ 3.36 √x` (`x ≥ 2^12`), `≤ 2.6 √x` (`x ≥ 2^16`) and
`≤ 2 √x` (`x ≥ 2^22`).  Asymptotically `sharpE x / √x → log 4 ≈ 1.386`.
-/

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## The explicit error term -/

/-- The explicit bound for `ψ(x) - θ(x)` obtained from `Chebyshev.psi_le` at
`x^{1/2}, x^{1/3}, x^{1/5}`. -/
noncomputable def sharpE (x : ℝ) : ℝ :=
  Real.log 4 * (√x + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ))
    + Real.log x * (x ^ (1 / 4 : ℝ) + 2 / 3 * x ^ (1 / 6 : ℝ) + 2 / 5 * x ^ (1 / 10 : ℝ))

/-! ## Reduction to `ψ - θ` -/

/-- `∑_{m<x, (m,n)>1} Λ(m) ≤ log n + (ψ(x) - θ(x))`. -/
theorem noncoprimeSum_le_log_add_psi_sub_theta {n : ℕ} (hn : 0 < n) (x : ℝ) :
    noncoprimeSum n x ≤ Real.log n + (Chebyshev.psi x - Chebyshev.theta x) := by
  unfold noncoprimeSum
  rw [← Finset.sum_filter_add_sum_filter_not _ Nat.Prime]
  -- primes dividing `n`
  have hP : ∑ m ∈ ((Finset.range ⌈x⌉₊).filter (fun m => ¬ Nat.Coprime m n)).filter Nat.Prime, Λ m
      ≤ Real.log n := by
    calc _ = ∑ m ∈ ((Finset.range ⌈x⌉₊).filter (fun m => ¬ Nat.Coprime m n)).filter Nat.Prime,
            Real.log m := Finset.sum_congr rfl fun m hm =>
              ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hm).2
      _ ≤ ∑ p ∈ n.primeFactors, Real.log p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_)
            (fun p _ _ => Real.log_natCast_nonneg p)
          obtain ⟨hm1, hmp⟩ := Finset.mem_filter.mp hm
          exact Nat.mem_primeFactors.mpr
            ⟨hmp, (Nat.Prime.dvd_iff_not_coprime hmp).mpr (Finset.mem_filter.mp hm1).2, hn.ne'⟩
      _ = Real.log ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by
          rw [Nat.cast_prod, Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
      _ ≤ Real.log n := by
          apply Real.log_le_log
          · exact_mod_cast Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp
          · exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  -- proper prime powers
  have hQ : ∑ m ∈ ((Finset.range ⌈x⌉₊).filter (fun m => ¬ Nat.Coprime m n)).filter
        (fun m => ¬ Nat.Prime m), Λ m ≤ Chebyshev.psi x - Chebyshev.theta x := by
    have h0 : (0 : ℕ) ∉ (Finset.Ioc 0 ⌊x⌋₊).filter (fun m => ¬ Nat.Prime m) := by simp
    calc _ ≤ ∑ m ∈ insert 0 ((Finset.Ioc 0 ⌊x⌋₊).filter (fun m => ¬ Nat.Prime m)), Λ m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_)
            (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
          obtain ⟨hm1, hmp⟩ := Finset.mem_filter.mp hm
          have hmx : (m : ℝ) < x :=
            Nat.lt_ceil.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm1).1)
          rcases Nat.eq_zero_or_pos m with rfl | hpos
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
              ⟨Finset.mem_Ioc.mpr ⟨hpos, Nat.le_floor hmx.le⟩, hmp⟩)
      _ = Chebyshev.psi x - Chebyshev.theta x := by
          rw [Finset.sum_insert h0, Chebyshev.psi_sub_theta_eq_sum_not_prime]
          simp
  linarith

/-! ## `ψ - θ ≤ sharpE` -/

/-- `Chebyshev.psi_le` at `y = x^a`: `ψ(x^a) ≤ log 4 · x^a + 2a · x^{a/2} log x`. -/
theorem psi_rpow_le {x : ℝ} (hx : 1 ≤ x) {a b : ℝ} (ha : 0 ≤ a) (hb : a / 2 = b) :
    Chebyshev.psi (x ^ a) ≤ Real.log 4 * x ^ a + 2 * a * (x ^ b * Real.log x) := by
  have hx0 : 0 ≤ x := by linarith
  have h := Chebyshev.psi_le (Real.one_le_rpow hx ha)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0, Real.log_rpow (by linarith),
    show a * (1 / 2) = b by rw [← hb]; ring] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- Sharpened `ψ - θ` bound. -/
theorem psi_sub_theta_le_sharpE {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ sharpE x := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, show (3 : ℝ)⁻¹ = 1 / 3 by norm_num,
    show (5 : ℝ)⁻¹ = 1 / 5 by norm_num] at h
  have h2 := psi_rpow_le hx (a := 1 / 2) (b := 1 / 4) (by norm_num) (by norm_num)
  have h3 := psi_rpow_le hx (a := 1 / 3) (b := 1 / 6) (by norm_num) (by norm_num)
  have h5 := psi_rpow_le hx (a := 1 / 5) (b := 1 / 10) (by norm_num) (by norm_num)
  have e : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm
  rw [e] at h h2
  unfold sharpE
  linear_combination h + h2 + h3 + h5

/-- **§6.2, sharpened.**  `∑_{m<x, (m,n)>1} Λ(m) ≤ log n + sharpE x`. -/
theorem noncoprimeSum_le_sharp {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 1 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + sharpE x := by
  have h1 := noncoprimeSum_le_log_add_psi_sub_theta hn x
  have h2 := psi_sub_theta_le_sharpE hx
  linarith

/-! ## `sharpE x / √x` is non-increasing for `log x ≥ 4` -/

theorem log_mul_le_log_mul_rpow {a x0 t : ℝ} (ha : 0 < a) (hx0 : 0 < x0) (ht : 1 ≤ t)
    (hl : 1 ≤ a * Real.log x0) : Real.log (x0 * t) ≤ Real.log x0 * t ^ a := by
  have ht0 : 0 < t := by linarith
  rw [Real.log_mul hx0.ne' ht0.ne']
  have h1 : a * Real.log t ≤ t ^ a - 1 := by
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 a)
    rwa [Real.log_rpow ht0] at this
  have hT : 1 ≤ t ^ a := Real.one_le_rpow ht ha.le
  have h2 : t ^ a - 1 ≤ a * Real.log x0 * (t ^ a - 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hT)]
  nlinarith

theorem rpow_mul_le_sqrt {x0 t b : ℝ} (hx0 : 0 ≤ x0) (ht : 1 ≤ t) (hb : b ≤ 1 / 2) :
    (x0 * t) ^ b ≤ x0 ^ b * √t := by
  rw [Real.mul_rpow hx0 (by linarith), Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht hb)
    (Real.rpow_nonneg hx0 _)

theorem rpow_mul_log_le_sqrt {x0 t b : ℝ} (hx0 : 0 < x0) (ht : 1 ≤ t) (hb : b < 1 / 2)
    (hl : 1 ≤ (1 / 2 - b) * Real.log x0) :
    (x0 * t) ^ b * Real.log (x0 * t) ≤ x0 ^ b * Real.log x0 * √t := by
  have ht0 : 0 < t := by linarith
  have hlog := log_mul_le_log_mul_rpow (a := 1 / 2 - b) (by linarith) hx0 ht hl
  calc (x0 * t) ^ b * Real.log (x0 * t)
      ≤ (x0 * t) ^ b * (Real.log x0 * t ^ (1 / 2 - b)) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (by positivity) _)
    _ = x0 ^ b * Real.log x0 * (t ^ b * t ^ (1 / 2 - b)) := by
        rw [Real.mul_rpow hx0.le ht0.le]; ring
    _ = x0 ^ b * Real.log x0 * √t := by
        rw [← Real.rpow_add ht0, show b + (1 / 2 - b) = (1 / 2 : ℝ) by ring, Real.sqrt_eq_rpow]

/-- `sharpE x / √x ≤ sharpE x₀ / √x₀` for `x ≥ x₀ > 0` with `log x₀ ≥ 4`. -/
theorem sharpE_le_of_le {x0 x : ℝ} (hx0 : 0 < x0) (hl : 4 ≤ Real.log x0) (hle : x0 ≤ x) :
    sharpE x ≤ sharpE x0 / √x0 * √x := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ x = x0 * t :=
    ⟨x / x0, (le_div_iff₀ hx0).mpr (by linarith), by field_simp⟩
  have hs0 : 0 < √x0 := Real.sqrt_pos.mpr hx0
  have e1 : sharpE x0 / √x0 * √(x0 * t) = sharpE x0 * √t := by
    rw [Real.sqrt_mul hx0.le t]; field_simp
  rw [e1]
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have p3 := mul_le_mul_of_nonneg_left
    (rpow_mul_le_sqrt (b := 1 / 3) hx0.le ht (by norm_num)) hl4
  have p5 := mul_le_mul_of_nonneg_left
    (rpow_mul_le_sqrt (b := 1 / 5) hx0.le ht (by norm_num)) hl4
  have q4 := rpow_mul_log_le_sqrt (b := 1 / 4) hx0 ht (by norm_num) (by linarith)
  have q6 := rpow_mul_log_le_sqrt (b := 1 / 6) hx0 ht (by norm_num) (by linarith)
  have q10 := rpow_mul_log_le_sqrt (b := 1 / 10) hx0 ht (by norm_num) (by linarith)
  unfold sharpE
  rw [Real.sqrt_mul hx0.le t]
  linear_combination p3 + p5 + q4 + (2 / 3 : ℝ) * q6 + (2 / 5 : ℝ) * q10

/-! ## Concrete corollaries -/

theorem rpow_inv_le_of_le_pow {y b : ℝ} {k : ℕ} (hk : k ≠ 0) (hy : 0 ≤ y) (hb : 0 ≤ b)
    (h : y ≤ b ^ k) : y ^ ((k : ℝ)⁻¹) ≤ b :=
  calc y ^ ((k : ℝ)⁻¹) ≤ (b ^ k) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow hy h (by positivity)
    _ = b := Real.pow_rpow_inv_natCast hb hk

theorem rpow_one_div_le {y b : ℝ} (k : ℕ) (hk : k ≠ 0) (hy : 0 ≤ y) (hb : 0 ≤ b)
    (h : y ≤ b ^ k) : y ^ ((1 : ℝ) / k) ≤ b := by
  rw [one_div]; exact rpow_inv_le_of_le_pow hk hy hb h

theorem log_two_pow (k : ℕ) : Real.log ((2 : ℝ) ^ k) = k * Real.log 2 := by simp [Real.log_pow]

theorem sharpE_4096_le : sharpE 4096 ≤ 3.36 * 64 := by
  have hs : √(4096 : ℝ) = 64 := by
    rw [show (4096 : ℝ) = 64 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have hlog : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, log_two_pow]; norm_num
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_two_pow]; norm_num
  have r3 : (4096 : ℝ) ^ (1 / 3 : ℝ) ≤ 16 := by
    have := rpow_one_div_le (y := 4096) (b := 16) 3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num); simpa using this
  have r4 : (4096 : ℝ) ^ (1 / 4 : ℝ) ≤ 8 := by
    have := rpow_one_div_le (y := 4096) (b := 8) 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num); simpa using this
  have r5 : (4096 : ℝ) ^ (1 / 5 : ℝ) ≤ 5.28 := by
    have := rpow_one_div_le (y := 4096) (b := 5.28) 5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num); simpa using this
  have r6 : (4096 : ℝ) ^ (1 / 6 : ℝ) ≤ 4 := by
    have := rpow_one_div_le (y := 4096) (b := 4) 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num); simpa using this
  have r10 : (4096 : ℝ) ^ (1 / 10 : ℝ) ≤ 2.3 := by
    have := rpow_one_div_le (y := 4096) (b := 2.3) 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num); simpa using this
  have n3 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4096 by norm_num) (1 / 3 : ℝ)
  have n4 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4096 by norm_num) (1 / 4 : ℝ)
  have n5 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4096 by norm_num) (1 / 5 : ℝ)
  have n6 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4096 by norm_num) (1 / 6 : ℝ)
  have n10 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4096 by norm_num) (1 / 10 : ℝ)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  unfold sharpE
  rw [hs, hlog, h4]
  have e1 := mul_le_mul_of_nonneg_left
    (show 64 + (4096 : ℝ) ^ (1 / 3 : ℝ) + (4096 : ℝ) ^ (1 / 5 : ℝ) ≤ 85.28 by linarith)
    (show (0 : ℝ) ≤ Real.log 2 by linarith)
  have e2 := mul_le_mul_of_nonneg_left
    (show (4096 : ℝ) ^ (1 / 4 : ℝ) + 2 / 3 * (4096 : ℝ) ^ (1 / 6 : ℝ)
      + 2 / 5 * (4096 : ℝ) ^ (1 / 10 : ℝ) ≤ 11.587 by linarith)
    (show (0 : ℝ) ≤ Real.log 2 by linarith)
  nlinarith

theorem sharpE_65536_le : sharpE 65536 ≤ 2.6 * 256 := by
  have hs : √(65536 : ℝ) = 256 := by
    rw [show (65536 : ℝ) = 256 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have hlog : Real.log (65536 : ℝ) = 16 * Real.log 2 := by
    rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, log_two_pow]; norm_num
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_two_pow]; norm_num
  have r3 : (65536 : ℝ) ^ (1 / 3 : ℝ) ≤ 40.33 := by
    have := rpow_one_div_le (y := 65536) (b := 40.33) 3 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have r4 : (65536 : ℝ) ^ (1 / 4 : ℝ) ≤ 16 := by
    have := rpow_one_div_le (y := 65536) (b := 16) 4 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have r5 : (65536 : ℝ) ^ (1 / 5 : ℝ) ≤ 9.19 := by
    have := rpow_one_div_le (y := 65536) (b := 9.19) 5 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have r6 : (65536 : ℝ) ^ (1 / 6 : ℝ) ≤ 6.35 := by
    have := rpow_one_div_le (y := 65536) (b := 6.35) 6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have r10 : (65536 : ℝ) ^ (1 / 10 : ℝ) ≤ 3.04 := by
    have := rpow_one_div_le (y := 65536) (b := 3.04) 10 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have n3 := Real.rpow_nonneg (show (0 : ℝ) ≤ 65536 by norm_num) (1 / 3 : ℝ)
  have n4 := Real.rpow_nonneg (show (0 : ℝ) ≤ 65536 by norm_num) (1 / 4 : ℝ)
  have n5 := Real.rpow_nonneg (show (0 : ℝ) ≤ 65536 by norm_num) (1 / 5 : ℝ)
  have n6 := Real.rpow_nonneg (show (0 : ℝ) ≤ 65536 by norm_num) (1 / 6 : ℝ)
  have n10 := Real.rpow_nonneg (show (0 : ℝ) ≤ 65536 by norm_num) (1 / 10 : ℝ)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  unfold sharpE
  rw [hs, hlog, h4]
  have e1 := mul_le_mul_of_nonneg_left
    (show 256 + (65536 : ℝ) ^ (1 / 3 : ℝ) + (65536 : ℝ) ^ (1 / 5 : ℝ) ≤ 305.52 by linarith)
    (show (0 : ℝ) ≤ Real.log 2 by linarith)
  have e2 := mul_le_mul_of_nonneg_left
    (show (65536 : ℝ) ^ (1 / 4 : ℝ) + 2 / 3 * (65536 : ℝ) ^ (1 / 6 : ℝ)
      + 2 / 5 * (65536 : ℝ) ^ (1 / 10 : ℝ) ≤ 21.45 by linarith)
    (show (0 : ℝ) ≤ Real.log 2 by linarith)
  nlinarith

theorem sharpE_4194304_le : sharpE 4194304 ≤ 2 * 2048 := by
  have hs : √(4194304 : ℝ) = 2048 := by
    rw [show (4194304 : ℝ) = 2048 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have hlog : Real.log (4194304 : ℝ) = 22 * Real.log 2 := by
    rw [show (4194304 : ℝ) = 2 ^ 22 by norm_num, log_two_pow]; norm_num
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_two_pow]; norm_num
  have r3 : (4194304 : ℝ) ^ (1 / 3 : ℝ) ≤ 161.3 := by
    have := rpow_one_div_le (y := 4194304) (b := 161.3) 3 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have r4 : (4194304 : ℝ) ^ (1 / 4 : ℝ) ≤ 45.26 := by
    have := rpow_one_div_le (y := 4194304) (b := 45.26) 4 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have r5 : (4194304 : ℝ) ^ (1 / 5 : ℝ) ≤ 21.12 := by
    have := rpow_one_div_le (y := 4194304) (b := 21.12) 5 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have r6 : (4194304 : ℝ) ^ (1 / 6 : ℝ) ≤ 12.7 := by
    have := rpow_one_div_le (y := 4194304) (b := 12.7) 6 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have r10 : (4194304 : ℝ) ^ (1 / 10 : ℝ) ≤ 4.6 := by
    have := rpow_one_div_le (y := 4194304) (b := 4.6) 10 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num); simpa using this
  have n3 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4194304 by norm_num) (1 / 3 : ℝ)
  have n4 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4194304 by norm_num) (1 / 4 : ℝ)
  have n5 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4194304 by norm_num) (1 / 5 : ℝ)
  have n6 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4194304 by norm_num) (1 / 6 : ℝ)
  have n10 := Real.rpow_nonneg (show (0 : ℝ) ≤ 4194304 by norm_num) (1 / 10 : ℝ)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  unfold sharpE
  rw [hs, hlog, h4]
  have e1 := mul_le_mul_of_nonneg_left
    (show 2048 + (4194304 : ℝ) ^ (1 / 3 : ℝ) + (4194304 : ℝ) ^ (1 / 5 : ℝ) ≤ 2230.42 by linarith)
    (show (0 : ℝ) ≤ Real.log 2 by linarith)
  have e2 := mul_le_mul_of_nonneg_left
    (show (4194304 : ℝ) ^ (1 / 4 : ℝ) + 2 / 3 * (4194304 : ℝ) ^ (1 / 6 : ℝ)
      + 2 / 5 * (4194304 : ℝ) ^ (1 / 10 : ℝ) ≤ 55.567 by linarith)
    (show (0 : ℝ) ≤ Real.log 2 by linarith)
  nlinarith

/-- Generic transfer: from a value bound at `x₀` to all `x ≥ x₀`. -/
theorem sharpE_le_mul_sqrt_of {x0 a x : ℝ} (hx0 : 0 < x0) (hl : 4 ≤ Real.log x0)
    (h0 : sharpE x0 ≤ a * √x0) (hle : x0 ≤ x) : sharpE x ≤ a * √x := by
  have h := sharpE_le_of_le hx0 hl hle
  have hs0 : 0 < √x0 := Real.sqrt_pos.mpr hx0
  have : sharpE x0 / √x0 ≤ a := by rwa [div_le_iff₀ hs0]
  exact h.trans (mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg x))

theorem log_ge_four_of_ge_4096 {x0 : ℝ} (h : 4096 ≤ x0) : 4 ≤ Real.log x0 := by
  have h1 : Real.log (4096 : ℝ) ≤ Real.log x0 := Real.log_le_log (by norm_num) h
  have : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, log_two_pow]; norm_num
  linarith [Real.log_two_gt_d9]

/-- `sharpE x ≤ 3.36 √x` for `x ≥ 2^12` (e.g. `x = 64 L²`, `L ≥ 8`). -/
theorem sharpE_le_of_ge_4096 {x : ℝ} (hx : 4096 ≤ x) : sharpE x ≤ 3.36 * √x := by
  refine sharpE_le_mul_sqrt_of (x0 := 4096) (by norm_num) (log_ge_four_of_ge_4096 le_rfl) ?_ hx
  have hs : √(4096 : ℝ) = 64 := by
    rw [show (4096 : ℝ) = 64 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [hs]; exact sharpE_4096_le

/-- `sharpE x ≤ 2.6 √x` for `x ≥ 2^16`. -/
theorem sharpE_le_of_ge_65536 {x : ℝ} (hx : 65536 ≤ x) : sharpE x ≤ 2.6 * √x := by
  refine sharpE_le_mul_sqrt_of (x0 := 65536) (by norm_num)
    (log_ge_four_of_ge_4096 (by norm_num)) ?_ hx
  have hs : √(65536 : ℝ) = 256 := by
    rw [show (65536 : ℝ) = 256 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [hs]; exact sharpE_65536_le

/-- `sharpE x ≤ 2 √x` for `x ≥ 2^22`. -/
theorem sharpE_le_of_ge_4194304 {x : ℝ} (hx : 4194304 ≤ x) : sharpE x ≤ 2 * √x := by
  refine sharpE_le_mul_sqrt_of (x0 := 4194304) (by norm_num)
    (log_ge_four_of_ge_4096 (by norm_num)) ?_ hx
  have hs : √(4194304 : ℝ) = 2048 := by
    rw [show (4194304 : ℝ) = 2048 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [hs]; exact sharpE_4194304_le

/-- §6.2 in the linear form used by `final_numeric`, for `x ≥ 2^12`. -/
theorem noncoprimeSum_le_of_ge_4096 {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 4096 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + 3.36 * √x := by
  have h1 := noncoprimeSum_le_sharp hn (x := x) (by linarith)
  have h2 := sharpE_le_of_ge_4096 hx
  linarith

/-- §6.2 in linear form, for `x ≥ 2^16`. -/
theorem noncoprimeSum_le_of_ge_65536 {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 65536 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + 2.6 * √x := by
  have h1 := noncoprimeSum_le_sharp hn (x := x) (by linarith)
  have h2 := sharpE_le_of_ge_65536 hx
  linarith

/-- §6.2 in linear form, for `x ≥ 2^22`. -/
theorem noncoprimeSum_le_of_ge_4194304 {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 4194304 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + 2 * √x := by
  have h1 := noncoprimeSum_le_sharp hn (x := x) (by linarith)
  have h2 := sharpE_le_of_ge_4194304 hx
  linarith

end DetPrimality.Bach
