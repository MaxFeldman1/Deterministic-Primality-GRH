import Mathlib
import DetPrimality.Bach.ConstNoncoprime

/-!
# A sharper `ψ - θ` bound at small `x` (and a uniform one)

Round 4 of lowering the Bach constant (see `STATUS.md`, "Round 3: lowering c").

For `x < 2^16` we use the exact identity `ψ x - θ x = ∑_{k=2}^{15} θ(x^{1/k})`
(`Chebyshev.psi_eq_theta_add_sum_theta'`) and, on each cell `A ≤ x < B` between consecutive
proper prime powers, `θ(x^{1/k}) ≤ log (primorial m_k)` where `B ≤ (m_k+1)^k`.  The product of
these primorials is an explicit natural number `P`, and `P^16 ≤ 2^e` gives
`ψ x - θ x ≤ (e/16) log 2`.  This yields (the constants are essentially the true suprema)

* `ψ x - θ x ≤ 1.43 √x` for `0 ≤ x < 2^16`,
* `ψ x - θ x ≤ 1.35 √x` for `420 ≤ x < 2^16`,
* `ψ x - θ x ≤ 1.34 √x` for `2000 ≤ x < 2^16`,
* `ψ x - θ x ≤ 1.30 √x` for `2500 ≤ x < 2^16`.

For `x ≥ 2^16` an induction on the Costa-Pereira inequality
`ψ x - θ x ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})` with `ψ y = θ y + (ψ y - θ y)` and
`θ y ≤ log 4 · y` gives `ψ x - θ x ≤ 1.84 √x` for **all** real `x`.

The tables (`prim_*`, `pst_lt_*`, `pst_cell_*` and the range theorems) are machine generated;
every step is checked by `norm_num` (no `native_decide`).
-/

set_option exponentiation.threshold 8000

namespace DetPrimality.Bach

/-! ## Primorial steps -/

theorem primorial_of_prime {n m : ℕ} (h : m = n + 1) (hp : m.Prime) :
    primorial m = m * primorial n := by
  subst h
  unfold primorial
  rw [show Finset.range (n + 1 + 1) = insert (n + 1) (Finset.range (n + 1)) from
    Finset.range_add_one, Finset.filter_insert, if_pos hp, Finset.prod_insert]
  simp

theorem primorial_of_not_prime {n m : ℕ} (h : m = n + 1) (hp : ¬ m.Prime) :
    primorial m = primorial n := by
  subst h
  unfold primorial
  rw [show Finset.range (n + 1 + 1) = insert (n + 1) (Finset.range (n + 1)) from
    Finset.range_add_one, Finset.filter_insert, if_neg hp]

/-! ## `θ` at a root, bounded by a primorial -/

theorem theta_le_log_primorial_of_lt {y : ℝ} {m : ℕ} (h : y < m + 1) :
    Chebyshev.theta y ≤ Real.log (primorial m) := by
  have hfl : ⌊y⌋₊ ≤ m := by
    have : ⌊y⌋₊ < m + 1 := (Nat.floor_lt' (Nat.succ_ne_zero m)).mpr (by push_cast; exact h)
    omega
  have h1 : Chebyshev.theta y = Chebyshev.theta (⌊y⌋₊ : ℝ) := Chebyshev.theta_eq_theta_coe_floor y
  have h2 : Chebyshev.theta (⌊y⌋₊ : ℝ) ≤ Chebyshev.theta (m : ℝ) :=
    Chebyshev.theta_mono (by exact_mod_cast hfl)
  have h3 : Chebyshev.theta (m : ℝ) = Real.log (primorial m) := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  linarith

theorem rpow_one_div_lt {x : ℝ} {k m : ℕ} (hx : 0 ≤ x) (hk : k ≠ 0)
    (h : x < ((m : ℝ) + 1) ^ k) : x ^ ((1 : ℝ) / k) < (m : ℝ) + 1 := by
  have hk' : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hk)
  calc x ^ ((1 : ℝ) / k) = x ^ ((k : ℝ)⁻¹) := by rw [one_div]
    _ < (((m : ℝ) + 1) ^ k) ^ ((k : ℝ)⁻¹) := Real.rpow_lt_rpow hx h hk'
    _ = (m : ℝ) + 1 := Real.pow_rpow_inv_natCast (by positivity) hk

/-- Generic step bound: if `x < B ≤ 2^16` and `B ≤ (m k + 1)^k` for `2 ≤ k ≤ 15`, then
`ψ x - θ x ≤ log ∏_k primorial (m k)`. -/
theorem psi_sub_theta_le_log_prod (m : ℕ → ℕ) (B : ℕ) {x : ℝ} (hx : x < B) (hB : B ≤ 65536)
    (hm : ∀ k ∈ Finset.Icc 2 15, B ≤ (m k + 1) ^ k) :
    Chebyshev.psi x - Chebyshev.theta x
      ≤ Real.log ((∏ k ∈ Finset.Icc 2 15, primorial (m k) : ℕ) : ℝ) := by
  have hpos : (0 : ℝ) ≤ Real.log ((∏ k ∈ Finset.Icc 2 15, primorial (m k) : ℕ) : ℝ) :=
    Real.log_natCast_nonneg _
  rcases lt_or_ge x 2 with h2 | h2
  · rw [Chebyshev.psi_eq_zero_of_lt_two h2]
    linarith [Chebyshev.theta_nonneg x]
  · have hx0 : 0 ≤ x := by linarith
    have hB' : (B : ℝ) ≤ 65536 := by exact_mod_cast hB
    have hN : ⌊Real.log x / Real.log 2⌋₊ ≤ 15 := by
      have hlt : Real.log x / Real.log 2 < 16 := by
        rw [div_lt_iff₀ (Real.log_pos one_lt_two)]
        have h16 : Real.log x < Real.log ((2 : ℝ) ^ 16) :=
          Real.log_lt_log (by linarith) (by norm_num; linarith)
        rw [Real.log_pow] at h16
        push_cast at h16
        linarith
      have : ⌊Real.log x / Real.log 2⌋₊ < 16 :=
        (Nat.floor_lt' (by norm_num)).mpr (by exact_mod_cast hlt)
      omega
    rw [Chebyshev.psi_eq_theta_add_sum_theta' h2 hN, Nat.cast_prod, Real.log_prod]
    · have hk : ∀ k : ℕ, k ∈ Finset.Icc 2 15 →
          Chebyshev.theta (x ^ ((1 : ℝ) / k)) ≤ Real.log (primorial (m k)) := by
        intro k hk
        apply theta_le_log_primorial_of_lt
        have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
        have hlt : x < ((m k : ℝ) + 1) ^ k := lt_of_lt_of_le hx (by exact_mod_cast hm k hk)
        exact rpow_one_div_lt hx0 hk0 hlt
      linarith [Finset.sum_le_sum hk]
    · intro k _
      exact_mod_cast (primorial_pos _).ne'

/-- Table of the `m k`, `2 ≤ k ≤ 15`. -/
def mtab (a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : ℕ) : ℕ → ℕ
  | 2 => a2 | 3 => a3 | 4 => a4 | 5 => a5 | 6 => a6 | 7 => a7 | 8 => a8 | 9 => a9
  | 10 => a10 | 11 => a11 | 12 => a12 | 13 => a13 | 14 => a14 | 15 => a15 | _ => 0

theorem prod_Icc_two_fifteen (f : ℕ → ℕ) :
    ∏ k ∈ Finset.Icc 2 15, f k
      = f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10 * f 11 * f 12 * f 13 * f 14 * f 15 := by
  have e : Finset.Icc 2 15 = Finset.Ico 2 16 := by ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e, Finset.prod_Ico_eq_prod_range]
  simp [Finset.prod_range_succ]

/-- The step bound with the fourteen roots as explicit arguments. -/
theorem psi_sub_theta_le_log14 (B a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : ℕ) {x : ℝ}
    (hx : x < B) (hB : B ≤ 65536)
    (h2 : B ≤ (a2 + 1) ^ 2) (h3 : B ≤ (a3 + 1) ^ 3) (h4 : B ≤ (a4 + 1) ^ 4)
    (h5 : B ≤ (a5 + 1) ^ 5) (h6 : B ≤ (a6 + 1) ^ 6) (h7 : B ≤ (a7 + 1) ^ 7)
    (h8 : B ≤ (a8 + 1) ^ 8) (h9 : B ≤ (a9 + 1) ^ 9) (h10 : B ≤ (a10 + 1) ^ 10)
    (h11 : B ≤ (a11 + 1) ^ 11) (h12 : B ≤ (a12 + 1) ^ 12) (h13 : B ≤ (a13 + 1) ^ 13)
    (h14 : B ≤ (a14 + 1) ^ 14) (h15 : B ≤ (a15 + 1) ^ 15) :
    Chebyshev.psi x - Chebyshev.theta x
      ≤ Real.log ((primorial a2 * primorial a3 * primorial a4 * primorial a5 * primorial a6
          * primorial a7 * primorial a8 * primorial a9 * primorial a10 * primorial a11
          * primorial a12 * primorial a13 * primorial a14 * primorial a15 : ℕ) : ℝ) := by
  have h := psi_sub_theta_le_log_prod (mtab a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) B
    hx hB (by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      interval_cases k
      exacts [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15])
  rw [prod_Icc_two_fifteen] at h
  exact h

theorem log_natCast_le_of_pow_le {P e : ℕ} (h : P ^ 16 ≤ 2 ^ e) :
    Real.log (P : ℝ) ≤ (e : ℝ) / 16 * Real.log 2 := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · rw [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (by positivity) (Real.log_pos one_lt_two).le
  · have hP' : (0 : ℝ) < P := by exact_mod_cast hP
    have h1 : Real.log ((P : ℝ) ^ 16) ≤ Real.log ((2 : ℝ) ^ e) :=
      Real.log_le_log (pow_pos hP' 16) (by exact_mod_cast h)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith

theorem le_mul_sqrt_of_log {D x A s r v : ℝ} (hD : D ≤ v * Real.log 2) (hv : 0 ≤ v)
    (hA : A ≤ x) (hsA : s ^ 2 ≤ A) (hr : 0 ≤ r) (hnum : v * 0.6931471808 ≤ r * s) :
    D ≤ r * √x := by
  have h1 : s ≤ √x := (le_abs_self s).trans (Real.abs_le_sqrt (hsA.trans hA))
  have h2 : v * Real.log 2 ≤ v * 0.6931471808 :=
    mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hv
  have h3 : r * s ≤ r * √x := mul_le_mul_of_nonneg_left h1 hr
  linarith


/-! ## Literal values of `primorial n`, `n ≤ 255` (generated) -/

theorem prim_0 : primorial 0 = 1 := primorial_zero

theorem prim_1 : primorial 1 = 1 := 
  (primorial_of_not_prime (n := 0) (m := 1) (by norm_num) (by norm_num)).trans prim_0

theorem prim_2 : primorial 2 = 2 := 
  (primorial_of_prime (n := 1) (m := 2) (by norm_num) (by norm_num)).trans (by norm_num [prim_1])

theorem prim_3 : primorial 3 = 6 := 
  (primorial_of_prime (n := 2) (m := 3) (by norm_num) (by norm_num)).trans (by norm_num [prim_2])

theorem prim_4 : primorial 4 = 6 := 
  (primorial_of_not_prime (n := 3) (m := 4) (by norm_num) (by norm_num)).trans prim_3

theorem prim_5 : primorial 5 = 30 := 
  (primorial_of_prime (n := 4) (m := 5) (by norm_num) (by norm_num)).trans (by norm_num [prim_4])

theorem prim_6 : primorial 6 = 30 := 
  (primorial_of_not_prime (n := 5) (m := 6) (by norm_num) (by norm_num)).trans prim_5

theorem prim_7 : primorial 7 = 210 := 
  (primorial_of_prime (n := 6) (m := 7) (by norm_num) (by norm_num)).trans (by norm_num [prim_6])

theorem prim_8 : primorial 8 = 210 := 
  (primorial_of_not_prime (n := 7) (m := 8) (by norm_num) (by norm_num)).trans prim_7

theorem prim_9 : primorial 9 = 210 := 
  (primorial_of_not_prime (n := 8) (m := 9) (by norm_num) (by norm_num)).trans prim_8

theorem prim_10 : primorial 10 = 210 := 
  (primorial_of_not_prime (n := 9) (m := 10) (by norm_num) (by norm_num)).trans prim_9

theorem prim_11 : primorial 11 = 2310 := 
  (primorial_of_prime (n := 10) (m := 11) (by norm_num) (by norm_num)).trans (by norm_num [prim_10])

theorem prim_12 : primorial 12 = 2310 := 
  (primorial_of_not_prime (n := 11) (m := 12) (by norm_num) (by norm_num)).trans prim_11

theorem prim_13 : primorial 13 = 30030 := 
  (primorial_of_prime (n := 12) (m := 13) (by norm_num) (by norm_num)).trans (by norm_num [prim_12])

theorem prim_14 : primorial 14 = 30030 := 
  (primorial_of_not_prime (n := 13) (m := 14) (by norm_num) (by norm_num)).trans prim_13

theorem prim_15 : primorial 15 = 30030 := 
  (primorial_of_not_prime (n := 14) (m := 15) (by norm_num) (by norm_num)).trans prim_14

theorem prim_16 : primorial 16 = 30030 := 
  (primorial_of_not_prime (n := 15) (m := 16) (by norm_num) (by norm_num)).trans prim_15

theorem prim_17 : primorial 17 = 510510 := 
  (primorial_of_prime (n := 16) (m := 17) (by norm_num) (by norm_num)).trans (by norm_num [prim_16])

theorem prim_18 : primorial 18 = 510510 := 
  (primorial_of_not_prime (n := 17) (m := 18) (by norm_num) (by norm_num)).trans prim_17

theorem prim_19 : primorial 19 = 9699690 := 
  (primorial_of_prime (n := 18) (m := 19) (by norm_num) (by norm_num)).trans (by norm_num [prim_18])

theorem prim_20 : primorial 20 = 9699690 := 
  (primorial_of_not_prime (n := 19) (m := 20) (by norm_num) (by norm_num)).trans prim_19

theorem prim_21 : primorial 21 = 9699690 := 
  (primorial_of_not_prime (n := 20) (m := 21) (by norm_num) (by norm_num)).trans prim_20

theorem prim_22 : primorial 22 = 9699690 := 
  (primorial_of_not_prime (n := 21) (m := 22) (by norm_num) (by norm_num)).trans prim_21

theorem prim_23 : primorial 23 = 223092870 := 
  (primorial_of_prime (n := 22) (m := 23) (by norm_num) (by norm_num)).trans (by norm_num [prim_22])

theorem prim_24 : primorial 24 = 223092870 := 
  (primorial_of_not_prime (n := 23) (m := 24) (by norm_num) (by norm_num)).trans prim_23

theorem prim_25 : primorial 25 = 223092870 := 
  (primorial_of_not_prime (n := 24) (m := 25) (by norm_num) (by norm_num)).trans prim_24

theorem prim_26 : primorial 26 = 223092870 := 
  (primorial_of_not_prime (n := 25) (m := 26) (by norm_num) (by norm_num)).trans prim_25

theorem prim_27 : primorial 27 = 223092870 := 
  (primorial_of_not_prime (n := 26) (m := 27) (by norm_num) (by norm_num)).trans prim_26

theorem prim_28 : primorial 28 = 223092870 := 
  (primorial_of_not_prime (n := 27) (m := 28) (by norm_num) (by norm_num)).trans prim_27

theorem prim_29 : primorial 29 = 6469693230 := 
  (primorial_of_prime (n := 28) (m := 29) (by norm_num) (by norm_num)).trans (by norm_num [prim_28])

theorem prim_30 : primorial 30 = 6469693230 := 
  (primorial_of_not_prime (n := 29) (m := 30) (by norm_num) (by norm_num)).trans prim_29

theorem prim_31 : primorial 31 = 200560490130 := 
  (primorial_of_prime (n := 30) (m := 31) (by norm_num) (by norm_num)).trans (by norm_num [prim_30])

theorem prim_32 : primorial 32 = 200560490130 := 
  (primorial_of_not_prime (n := 31) (m := 32) (by norm_num) (by norm_num)).trans prim_31

theorem prim_33 : primorial 33 = 200560490130 := 
  (primorial_of_not_prime (n := 32) (m := 33) (by norm_num) (by norm_num)).trans prim_32

theorem prim_34 : primorial 34 = 200560490130 := 
  (primorial_of_not_prime (n := 33) (m := 34) (by norm_num) (by norm_num)).trans prim_33

theorem prim_35 : primorial 35 = 200560490130 := 
  (primorial_of_not_prime (n := 34) (m := 35) (by norm_num) (by norm_num)).trans prim_34

theorem prim_36 : primorial 36 = 200560490130 := 
  (primorial_of_not_prime (n := 35) (m := 36) (by norm_num) (by norm_num)).trans prim_35

theorem prim_37 : primorial 37 = 7420738134810 := 
  (primorial_of_prime (n := 36) (m := 37) (by norm_num) (by norm_num)).trans (by norm_num [prim_36])

theorem prim_38 : primorial 38 = 7420738134810 := 
  (primorial_of_not_prime (n := 37) (m := 38) (by norm_num) (by norm_num)).trans prim_37

theorem prim_39 : primorial 39 = 7420738134810 := 
  (primorial_of_not_prime (n := 38) (m := 39) (by norm_num) (by norm_num)).trans prim_38

theorem prim_40 : primorial 40 = 7420738134810 := 
  (primorial_of_not_prime (n := 39) (m := 40) (by norm_num) (by norm_num)).trans prim_39

theorem prim_41 : primorial 41 = 304250263527210 := 
  (primorial_of_prime (n := 40) (m := 41) (by norm_num) (by norm_num)).trans (by norm_num [prim_40])

theorem prim_42 : primorial 42 = 304250263527210 := 
  (primorial_of_not_prime (n := 41) (m := 42) (by norm_num) (by norm_num)).trans prim_41

theorem prim_43 : primorial 43 = 13082761331670030 := 
  (primorial_of_prime (n := 42) (m := 43) (by norm_num) (by norm_num)).trans (by norm_num [prim_42])

theorem prim_44 : primorial 44 = 13082761331670030 := 
  (primorial_of_not_prime (n := 43) (m := 44) (by norm_num) (by norm_num)).trans prim_43

theorem prim_45 : primorial 45 = 13082761331670030 := 
  (primorial_of_not_prime (n := 44) (m := 45) (by norm_num) (by norm_num)).trans prim_44

theorem prim_46 : primorial 46 = 13082761331670030 := 
  (primorial_of_not_prime (n := 45) (m := 46) (by norm_num) (by norm_num)).trans prim_45

theorem prim_47 : primorial 47 = 614889782588491410 := 
  (primorial_of_prime (n := 46) (m := 47) (by norm_num) (by norm_num)).trans (by norm_num [prim_46])

theorem prim_48 : primorial 48 = 614889782588491410 := 
  (primorial_of_not_prime (n := 47) (m := 48) (by norm_num) (by norm_num)).trans prim_47

theorem prim_49 : primorial 49 = 614889782588491410 := 
  (primorial_of_not_prime (n := 48) (m := 49) (by norm_num) (by norm_num)).trans prim_48

theorem prim_50 : primorial 50 = 614889782588491410 := 
  (primorial_of_not_prime (n := 49) (m := 50) (by norm_num) (by norm_num)).trans prim_49

theorem prim_51 : primorial 51 = 614889782588491410 := 
  (primorial_of_not_prime (n := 50) (m := 51) (by norm_num) (by norm_num)).trans prim_50

theorem prim_52 : primorial 52 = 614889782588491410 := 
  (primorial_of_not_prime (n := 51) (m := 52) (by norm_num) (by norm_num)).trans prim_51

theorem prim_53 : primorial 53 = 32589158477190044730 := 
  (primorial_of_prime (n := 52) (m := 53) (by norm_num) (by norm_num)).trans (by norm_num [prim_52])

theorem prim_54 : primorial 54 = 32589158477190044730 := 
  (primorial_of_not_prime (n := 53) (m := 54) (by norm_num) (by norm_num)).trans prim_53

theorem prim_55 : primorial 55 = 32589158477190044730 := 
  (primorial_of_not_prime (n := 54) (m := 55) (by norm_num) (by norm_num)).trans prim_54

theorem prim_56 : primorial 56 = 32589158477190044730 := 
  (primorial_of_not_prime (n := 55) (m := 56) (by norm_num) (by norm_num)).trans prim_55

theorem prim_57 : primorial 57 = 32589158477190044730 := 
  (primorial_of_not_prime (n := 56) (m := 57) (by norm_num) (by norm_num)).trans prim_56

theorem prim_58 : primorial 58 = 32589158477190044730 := 
  (primorial_of_not_prime (n := 57) (m := 58) (by norm_num) (by norm_num)).trans prim_57

theorem prim_59 : primorial 59 = 1922760350154212639070 := 
  (primorial_of_prime (n := 58) (m := 59) (by norm_num) (by norm_num)).trans (by norm_num [prim_58])

theorem prim_60 : primorial 60 = 1922760350154212639070 := 
  (primorial_of_not_prime (n := 59) (m := 60) (by norm_num) (by norm_num)).trans prim_59

theorem prim_61 : primorial 61 = 117288381359406970983270 := 
  (primorial_of_prime (n := 60) (m := 61) (by norm_num) (by norm_num)).trans (by norm_num [prim_60])

theorem prim_62 : primorial 62 = 117288381359406970983270 := 
  (primorial_of_not_prime (n := 61) (m := 62) (by norm_num) (by norm_num)).trans prim_61

theorem prim_63 : primorial 63 = 117288381359406970983270 := 
  (primorial_of_not_prime (n := 62) (m := 63) (by norm_num) (by norm_num)).trans prim_62

theorem prim_64 : primorial 64 = 117288381359406970983270 := 
  (primorial_of_not_prime (n := 63) (m := 64) (by norm_num) (by norm_num)).trans prim_63

theorem prim_65 : primorial 65 = 117288381359406970983270 := 
  (primorial_of_not_prime (n := 64) (m := 65) (by norm_num) (by norm_num)).trans prim_64

theorem prim_66 : primorial 66 = 117288381359406970983270 := 
  (primorial_of_not_prime (n := 65) (m := 66) (by norm_num) (by norm_num)).trans prim_65

theorem prim_67 : primorial 67 = 7858321551080267055879090 := 
  (primorial_of_prime (n := 66) (m := 67) (by norm_num) (by norm_num)).trans (by norm_num [prim_66])

theorem prim_68 : primorial 68 = 7858321551080267055879090 := 
  (primorial_of_not_prime (n := 67) (m := 68) (by norm_num) (by norm_num)).trans prim_67

theorem prim_69 : primorial 69 = 7858321551080267055879090 := 
  (primorial_of_not_prime (n := 68) (m := 69) (by norm_num) (by norm_num)).trans prim_68

theorem prim_70 : primorial 70 = 7858321551080267055879090 := 
  (primorial_of_not_prime (n := 69) (m := 70) (by norm_num) (by norm_num)).trans prim_69

theorem prim_71 : primorial 71 = 557940830126698960967415390 := 
  (primorial_of_prime (n := 70) (m := 71) (by norm_num) (by norm_num)).trans (by norm_num [prim_70])

theorem prim_72 : primorial 72 = 557940830126698960967415390 := 
  (primorial_of_not_prime (n := 71) (m := 72) (by norm_num) (by norm_num)).trans prim_71

theorem prim_73 : primorial 73 = 40729680599249024150621323470 := 
  (primorial_of_prime (n := 72) (m := 73) (by norm_num) (by norm_num)).trans (by norm_num [prim_72])

theorem prim_74 : primorial 74 = 40729680599249024150621323470 := 
  (primorial_of_not_prime (n := 73) (m := 74) (by norm_num) (by norm_num)).trans prim_73

theorem prim_75 : primorial 75 = 40729680599249024150621323470 := 
  (primorial_of_not_prime (n := 74) (m := 75) (by norm_num) (by norm_num)).trans prim_74

theorem prim_76 : primorial 76 = 40729680599249024150621323470 := 
  (primorial_of_not_prime (n := 75) (m := 76) (by norm_num) (by norm_num)).trans prim_75

theorem prim_77 : primorial 77 = 40729680599249024150621323470 := 
  (primorial_of_not_prime (n := 76) (m := 77) (by norm_num) (by norm_num)).trans prim_76

theorem prim_78 : primorial 78 = 40729680599249024150621323470 := 
  (primorial_of_not_prime (n := 77) (m := 78) (by norm_num) (by norm_num)).trans prim_77

theorem prim_79 : primorial 79 = 3217644767340672907899084554130 := 
  (primorial_of_prime (n := 78) (m := 79) (by norm_num) (by norm_num)).trans (by norm_num [prim_78])

theorem prim_80 : primorial 80 = 3217644767340672907899084554130 := 
  (primorial_of_not_prime (n := 79) (m := 80) (by norm_num) (by norm_num)).trans prim_79

theorem prim_81 : primorial 81 = 3217644767340672907899084554130 := 
  (primorial_of_not_prime (n := 80) (m := 81) (by norm_num) (by norm_num)).trans prim_80

theorem prim_82 : primorial 82 = 3217644767340672907899084554130 := 
  (primorial_of_not_prime (n := 81) (m := 82) (by norm_num) (by norm_num)).trans prim_81

theorem prim_83 : primorial 83 = 267064515689275851355624017992790 := 
  (primorial_of_prime (n := 82) (m := 83) (by norm_num) (by norm_num)).trans (by norm_num [prim_82])

theorem prim_84 : primorial 84 = 267064515689275851355624017992790 := 
  (primorial_of_not_prime (n := 83) (m := 84) (by norm_num) (by norm_num)).trans prim_83

theorem prim_85 : primorial 85 = 267064515689275851355624017992790 := 
  (primorial_of_not_prime (n := 84) (m := 85) (by norm_num) (by norm_num)).trans prim_84

theorem prim_86 : primorial 86 = 267064515689275851355624017992790 := 
  (primorial_of_not_prime (n := 85) (m := 86) (by norm_num) (by norm_num)).trans prim_85

theorem prim_87 : primorial 87 = 267064515689275851355624017992790 := 
  (primorial_of_not_prime (n := 86) (m := 87) (by norm_num) (by norm_num)).trans prim_86

theorem prim_88 : primorial 88 = 267064515689275851355624017992790 := 
  (primorial_of_not_prime (n := 87) (m := 88) (by norm_num) (by norm_num)).trans prim_87

theorem prim_89 : primorial 89 = 23768741896345550770650537601358310 := 
  (primorial_of_prime (n := 88) (m := 89) (by norm_num) (by norm_num)).trans (by norm_num [prim_88])

theorem prim_90 : primorial 90 = 23768741896345550770650537601358310 := 
  (primorial_of_not_prime (n := 89) (m := 90) (by norm_num) (by norm_num)).trans prim_89

theorem prim_91 : primorial 91 = 23768741896345550770650537601358310 := 
  (primorial_of_not_prime (n := 90) (m := 91) (by norm_num) (by norm_num)).trans prim_90

theorem prim_92 : primorial 92 = 23768741896345550770650537601358310 := 
  (primorial_of_not_prime (n := 91) (m := 92) (by norm_num) (by norm_num)).trans prim_91

theorem prim_93 : primorial 93 = 23768741896345550770650537601358310 := 
  (primorial_of_not_prime (n := 92) (m := 93) (by norm_num) (by norm_num)).trans prim_92

theorem prim_94 : primorial 94 = 23768741896345550770650537601358310 := 
  (primorial_of_not_prime (n := 93) (m := 94) (by norm_num) (by norm_num)).trans prim_93

theorem prim_95 : primorial 95 = 23768741896345550770650537601358310 := 
  (primorial_of_not_prime (n := 94) (m := 95) (by norm_num) (by norm_num)).trans prim_94

theorem prim_96 : primorial 96 = 23768741896345550770650537601358310 := 
  (primorial_of_not_prime (n := 95) (m := 96) (by norm_num) (by norm_num)).trans prim_95

theorem prim_97 : primorial 97 = 2305567963945518424753102147331756070 := 
  (primorial_of_prime (n := 96) (m := 97) (by norm_num) (by norm_num)).trans (by norm_num [prim_96])

theorem prim_98 : primorial 98 = 2305567963945518424753102147331756070 := 
  (primorial_of_not_prime (n := 97) (m := 98) (by norm_num) (by norm_num)).trans prim_97

theorem prim_99 : primorial 99 = 2305567963945518424753102147331756070 := 
  (primorial_of_not_prime (n := 98) (m := 99) (by norm_num) (by norm_num)).trans prim_98

theorem prim_100 : primorial 100 = 2305567963945518424753102147331756070 := 
  (primorial_of_not_prime (n := 99) (m := 100) (by norm_num) (by norm_num)).trans prim_99

theorem prim_101 : primorial 101 = 232862364358497360900063316880507363070 := 
  (primorial_of_prime (n := 100) (m := 101) (by norm_num) (by norm_num)).trans (by norm_num [prim_100])

theorem prim_102 : primorial 102 = 232862364358497360900063316880507363070 := 
  (primorial_of_not_prime (n := 101) (m := 102) (by norm_num) (by norm_num)).trans prim_101

theorem prim_103 : primorial 103 = 23984823528925228172706521638692258396210 := 
  (primorial_of_prime (n := 102) (m := 103) (by norm_num) (by norm_num)).trans (by norm_num [prim_102])

theorem prim_104 : primorial 104 = 23984823528925228172706521638692258396210 := 
  (primorial_of_not_prime (n := 103) (m := 104) (by norm_num) (by norm_num)).trans prim_103

theorem prim_105 : primorial 105 = 23984823528925228172706521638692258396210 := 
  (primorial_of_not_prime (n := 104) (m := 105) (by norm_num) (by norm_num)).trans prim_104

theorem prim_106 : primorial 106 = 23984823528925228172706521638692258396210 := 
  (primorial_of_not_prime (n := 105) (m := 106) (by norm_num) (by norm_num)).trans prim_105

theorem prim_107 : primorial 107 = 2566376117594999414479597815340071648394470 := 
  (primorial_of_prime (n := 106) (m := 107) (by norm_num) (by norm_num)).trans (by norm_num [prim_106])

theorem prim_108 : primorial 108 = 2566376117594999414479597815340071648394470 := 
  (primorial_of_not_prime (n := 107) (m := 108) (by norm_num) (by norm_num)).trans prim_107

theorem prim_109 : primorial 109 = 279734996817854936178276161872067809674997230 := 
  (primorial_of_prime (n := 108) (m := 109) (by norm_num) (by norm_num)).trans (by norm_num [prim_108])

theorem prim_110 : primorial 110 = 279734996817854936178276161872067809674997230 := 
  (primorial_of_not_prime (n := 109) (m := 110) (by norm_num) (by norm_num)).trans prim_109

theorem prim_111 : primorial 111 = 279734996817854936178276161872067809674997230 := 
  (primorial_of_not_prime (n := 110) (m := 111) (by norm_num) (by norm_num)).trans prim_110

theorem prim_112 : primorial 112 = 279734996817854936178276161872067809674997230 := 
  (primorial_of_not_prime (n := 111) (m := 112) (by norm_num) (by norm_num)).trans prim_111

theorem prim_113 : primorial 113 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_prime (n := 112) (m := 113) (by norm_num) (by norm_num)).trans (by norm_num [prim_112])

theorem prim_114 : primorial 114 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 113) (m := 114) (by norm_num) (by norm_num)).trans prim_113

theorem prim_115 : primorial 115 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 114) (m := 115) (by norm_num) (by norm_num)).trans prim_114

theorem prim_116 : primorial 116 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 115) (m := 116) (by norm_num) (by norm_num)).trans prim_115

theorem prim_117 : primorial 117 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 116) (m := 117) (by norm_num) (by norm_num)).trans prim_116

theorem prim_118 : primorial 118 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 117) (m := 118) (by norm_num) (by norm_num)).trans prim_117

theorem prim_119 : primorial 119 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 118) (m := 119) (by norm_num) (by norm_num)).trans prim_118

theorem prim_120 : primorial 120 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 119) (m := 120) (by norm_num) (by norm_num)).trans prim_119

theorem prim_121 : primorial 121 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 120) (m := 121) (by norm_num) (by norm_num)).trans prim_120

theorem prim_122 : primorial 122 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 121) (m := 122) (by norm_num) (by norm_num)).trans prim_121

theorem prim_123 : primorial 123 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 122) (m := 123) (by norm_num) (by norm_num)).trans prim_122

theorem prim_124 : primorial 124 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 123) (m := 124) (by norm_num) (by norm_num)).trans prim_123

theorem prim_125 : primorial 125 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 124) (m := 125) (by norm_num) (by norm_num)).trans prim_124

theorem prim_126 : primorial 126 = 31610054640417607788145206291543662493274686990 := 
  (primorial_of_not_prime (n := 125) (m := 126) (by norm_num) (by norm_num)).trans prim_125

theorem prim_127 : primorial 127 = 4014476939333036189094441199026045136645885247730 := 
  (primorial_of_prime (n := 126) (m := 127) (by norm_num) (by norm_num)).trans (by norm_num [prim_126])

theorem prim_128 : primorial 128 = 4014476939333036189094441199026045136645885247730 := 
  (primorial_of_not_prime (n := 127) (m := 128) (by norm_num) (by norm_num)).trans prim_127

theorem prim_129 : primorial 129 = 4014476939333036189094441199026045136645885247730 := 
  (primorial_of_not_prime (n := 128) (m := 129) (by norm_num) (by norm_num)).trans prim_128

theorem prim_130 : primorial 130 = 4014476939333036189094441199026045136645885247730 := 
  (primorial_of_not_prime (n := 129) (m := 130) (by norm_num) (by norm_num)).trans prim_129

theorem prim_131 : primorial 131 = 525896479052627740771371797072411912900610967452630 := 
  (primorial_of_prime (n := 130) (m := 131) (by norm_num) (by norm_num)).trans (by norm_num [prim_130])

theorem prim_132 : primorial 132 = 525896479052627740771371797072411912900610967452630 := 
  (primorial_of_not_prime (n := 131) (m := 132) (by norm_num) (by norm_num)).trans prim_131

theorem prim_133 : primorial 133 = 525896479052627740771371797072411912900610967452630 := 
  (primorial_of_not_prime (n := 132) (m := 133) (by norm_num) (by norm_num)).trans prim_132

theorem prim_134 : primorial 134 = 525896479052627740771371797072411912900610967452630 := 
  (primorial_of_not_prime (n := 133) (m := 134) (by norm_num) (by norm_num)).trans prim_133

theorem prim_135 : primorial 135 = 525896479052627740771371797072411912900610967452630 := 
  (primorial_of_not_prime (n := 134) (m := 135) (by norm_num) (by norm_num)).trans prim_134

theorem prim_136 : primorial 136 = 525896479052627740771371797072411912900610967452630 := 
  (primorial_of_not_prime (n := 135) (m := 136) (by norm_num) (by norm_num)).trans prim_135

theorem prim_137 : primorial 137 = 72047817630210000485677936198920432067383702541010310 := 
  (primorial_of_prime (n := 136) (m := 137) (by norm_num) (by norm_num)).trans (by norm_num [prim_136])

theorem prim_138 : primorial 138 = 72047817630210000485677936198920432067383702541010310 := 
  (primorial_of_not_prime (n := 137) (m := 138) (by norm_num) (by norm_num)).trans prim_137

theorem prim_139 : primorial 139 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_prime (n := 138) (m := 139) (by norm_num) (by norm_num)).trans (by norm_num [prim_138])

theorem prim_140 : primorial 140 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_not_prime (n := 139) (m := 140) (by norm_num) (by norm_num)).trans prim_139

theorem prim_141 : primorial 141 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_not_prime (n := 140) (m := 141) (by norm_num) (by norm_num)).trans prim_140

theorem prim_142 : primorial 142 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_not_prime (n := 141) (m := 142) (by norm_num) (by norm_num)).trans prim_141

theorem prim_143 : primorial 143 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_not_prime (n := 142) (m := 143) (by norm_num) (by norm_num)).trans prim_142

theorem prim_144 : primorial 144 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_not_prime (n := 143) (m := 144) (by norm_num) (by norm_num)).trans prim_143

theorem prim_145 : primorial 145 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_not_prime (n := 144) (m := 145) (by norm_num) (by norm_num)).trans prim_144

theorem prim_146 : primorial 146 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_not_prime (n := 145) (m := 146) (by norm_num) (by norm_num)).trans prim_145

theorem prim_147 : primorial 147 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_not_prime (n := 146) (m := 147) (by norm_num) (by norm_num)).trans prim_146

theorem prim_148 : primorial 148 = 10014646650599190067509233131649940057366334653200433090 := 
  (primorial_of_not_prime (n := 147) (m := 148) (by norm_num) (by norm_num)).trans prim_147

theorem prim_149 : primorial 149 = 1492182350939279320058875736615841068547583863326864530410 := 
  (primorial_of_prime (n := 148) (m := 149) (by norm_num) (by norm_num)).trans (by norm_num [prim_148])

theorem prim_150 : primorial 150 = 1492182350939279320058875736615841068547583863326864530410 := 
  (primorial_of_not_prime (n := 149) (m := 150) (by norm_num) (by norm_num)).trans prim_149

theorem prim_151 : primorial 151 = 225319534991831177328890236228992001350685163362356544091910 := 
  (primorial_of_prime (n := 150) (m := 151) (by norm_num) (by norm_num)).trans (by norm_num [prim_150])

theorem prim_152 : primorial 152 = 225319534991831177328890236228992001350685163362356544091910 := 
  (primorial_of_not_prime (n := 151) (m := 152) (by norm_num) (by norm_num)).trans prim_151

theorem prim_153 : primorial 153 = 225319534991831177328890236228992001350685163362356544091910 := 
  (primorial_of_not_prime (n := 152) (m := 153) (by norm_num) (by norm_num)).trans prim_152

theorem prim_154 : primorial 154 = 225319534991831177328890236228992001350685163362356544091910 := 
  (primorial_of_not_prime (n := 153) (m := 154) (by norm_num) (by norm_num)).trans prim_153

theorem prim_155 : primorial 155 = 225319534991831177328890236228992001350685163362356544091910 := 
  (primorial_of_not_prime (n := 154) (m := 155) (by norm_num) (by norm_num)).trans prim_154

theorem prim_156 : primorial 156 = 225319534991831177328890236228992001350685163362356544091910 := 
  (primorial_of_not_prime (n := 155) (m := 156) (by norm_num) (by norm_num)).trans prim_155

theorem prim_157 : primorial 157 = 35375166993717494840635767087951744212057570647889977422429870 := 
  (primorial_of_prime (n := 156) (m := 157) (by norm_num) (by norm_num)).trans (by norm_num [prim_156])

theorem prim_158 : primorial 158 = 35375166993717494840635767087951744212057570647889977422429870 := 
  (primorial_of_not_prime (n := 157) (m := 158) (by norm_num) (by norm_num)).trans prim_157

theorem prim_159 : primorial 159 = 35375166993717494840635767087951744212057570647889977422429870 := 
  (primorial_of_not_prime (n := 158) (m := 159) (by norm_num) (by norm_num)).trans prim_158

theorem prim_160 : primorial 160 = 35375166993717494840635767087951744212057570647889977422429870 := 
  (primorial_of_not_prime (n := 159) (m := 160) (by norm_num) (by norm_num)).trans prim_159

theorem prim_161 : primorial 161 = 35375166993717494840635767087951744212057570647889977422429870 := 
  (primorial_of_not_prime (n := 160) (m := 161) (by norm_num) (by norm_num)).trans prim_160

theorem prim_162 : primorial 162 = 35375166993717494840635767087951744212057570647889977422429870 := 
  (primorial_of_not_prime (n := 161) (m := 162) (by norm_num) (by norm_num)).trans prim_161

theorem prim_163 : primorial 163 = 5766152219975951659023630035336134306565384015606066319856068810 := 
  (primorial_of_prime (n := 162) (m := 163) (by norm_num) (by norm_num)).trans (by norm_num [prim_162])

theorem prim_164 : primorial 164 = 5766152219975951659023630035336134306565384015606066319856068810 := 
  (primorial_of_not_prime (n := 163) (m := 164) (by norm_num) (by norm_num)).trans prim_163

theorem prim_165 : primorial 165 = 5766152219975951659023630035336134306565384015606066319856068810 := 
  (primorial_of_not_prime (n := 164) (m := 165) (by norm_num) (by norm_num)).trans prim_164

theorem prim_166 : primorial 166 = 5766152219975951659023630035336134306565384015606066319856068810 := 
  (primorial_of_not_prime (n := 165) (m := 166) (by norm_num) (by norm_num)).trans prim_165

theorem prim_167 : primorial 167 = 962947420735983927056946215901134429196419130606213075415963491270 := 
  (primorial_of_prime (n := 166) (m := 167) (by norm_num) (by norm_num)).trans (by norm_num [prim_166])

theorem prim_168 : primorial 168 = 962947420735983927056946215901134429196419130606213075415963491270 := 
  (primorial_of_not_prime (n := 167) (m := 168) (by norm_num) (by norm_num)).trans prim_167

theorem prim_169 : primorial 169 = 962947420735983927056946215901134429196419130606213075415963491270 := 
  (primorial_of_not_prime (n := 168) (m := 169) (by norm_num) (by norm_num)).trans prim_168

theorem prim_170 : primorial 170 = 962947420735983927056946215901134429196419130606213075415963491270 := 
  (primorial_of_not_prime (n := 169) (m := 170) (by norm_num) (by norm_num)).trans prim_169

theorem prim_171 : primorial 171 = 962947420735983927056946215901134429196419130606213075415963491270 := 
  (primorial_of_not_prime (n := 170) (m := 171) (by norm_num) (by norm_num)).trans prim_170

theorem prim_172 : primorial 172 = 962947420735983927056946215901134429196419130606213075415963491270 := 
  (primorial_of_not_prime (n := 171) (m := 172) (by norm_num) (by norm_num)).trans prim_171

theorem prim_173 : primorial 173 = 166589903787325219380851695350896256250980509594874862046961683989710 := 
  (primorial_of_prime (n := 172) (m := 173) (by norm_num) (by norm_num)).trans (by norm_num [prim_172])

theorem prim_174 : primorial 174 = 166589903787325219380851695350896256250980509594874862046961683989710 := 
  (primorial_of_not_prime (n := 173) (m := 174) (by norm_num) (by norm_num)).trans prim_173

theorem prim_175 : primorial 175 = 166589903787325219380851695350896256250980509594874862046961683989710 := 
  (primorial_of_not_prime (n := 174) (m := 175) (by norm_num) (by norm_num)).trans prim_174

theorem prim_176 : primorial 176 = 166589903787325219380851695350896256250980509594874862046961683989710 := 
  (primorial_of_not_prime (n := 175) (m := 176) (by norm_num) (by norm_num)).trans prim_175

theorem prim_177 : primorial 177 = 166589903787325219380851695350896256250980509594874862046961683989710 := 
  (primorial_of_not_prime (n := 176) (m := 177) (by norm_num) (by norm_num)).trans prim_176

theorem prim_178 : primorial 178 = 166589903787325219380851695350896256250980509594874862046961683989710 := 
  (primorial_of_not_prime (n := 177) (m := 178) (by norm_num) (by norm_num)).trans prim_177

theorem prim_179 : primorial 179 = 29819592777931214269172453467810429868925511217482600306406141434158090 := 
  (primorial_of_prime (n := 178) (m := 179) (by norm_num) (by norm_num)).trans (by norm_num [prim_178])

theorem prim_180 : primorial 180 = 29819592777931214269172453467810429868925511217482600306406141434158090 := 
  (primorial_of_not_prime (n := 179) (m := 180) (by norm_num) (by norm_num)).trans prim_179

theorem prim_181 : primorial 181 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_prime (n := 180) (m := 181) (by norm_num) (by norm_num)).trans (by norm_num [prim_180])

theorem prim_182 : primorial 182 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_not_prime (n := 181) (m := 182) (by norm_num) (by norm_num)).trans prim_181

theorem prim_183 : primorial 183 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_not_prime (n := 182) (m := 183) (by norm_num) (by norm_num)).trans prim_182

theorem prim_184 : primorial 184 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_not_prime (n := 183) (m := 184) (by norm_num) (by norm_num)).trans prim_183

theorem prim_185 : primorial 185 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_not_prime (n := 184) (m := 185) (by norm_num) (by norm_num)).trans prim_184

theorem prim_186 : primorial 186 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_not_prime (n := 185) (m := 186) (by norm_num) (by norm_num)).trans prim_185

theorem prim_187 : primorial 187 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_not_prime (n := 186) (m := 187) (by norm_num) (by norm_num)).trans prim_186

theorem prim_188 : primorial 188 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_not_prime (n := 187) (m := 188) (by norm_num) (by norm_num)).trans prim_187

theorem prim_189 : primorial 189 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_not_prime (n := 188) (m := 189) (by norm_num) (by norm_num)).trans prim_188

theorem prim_190 : primorial 190 = 5397346292805549782720214077673687806275517530364350655459511599582614290 := 
  (primorial_of_not_prime (n := 189) (m := 190) (by norm_num) (by norm_num)).trans prim_189

theorem prim_191 : primorial 191 = 1030893141925860008499560888835674370998623848299590975192766715520279329390 := 
  (primorial_of_prime (n := 190) (m := 191) (by norm_num) (by norm_num)).trans (by norm_num [prim_190])

theorem prim_192 : primorial 192 = 1030893141925860008499560888835674370998623848299590975192766715520279329390 := 
  (primorial_of_not_prime (n := 191) (m := 192) (by norm_num) (by norm_num)).trans prim_191

theorem prim_193 : primorial 193 = 198962376391690981640415251545285153602734402721821058212203976095413910572270 := 
  (primorial_of_prime (n := 192) (m := 193) (by norm_num) (by norm_num)).trans (by norm_num [prim_192])

theorem prim_194 : primorial 194 = 198962376391690981640415251545285153602734402721821058212203976095413910572270 := 
  (primorial_of_not_prime (n := 193) (m := 194) (by norm_num) (by norm_num)).trans prim_193

theorem prim_195 : primorial 195 = 198962376391690981640415251545285153602734402721821058212203976095413910572270 := 
  (primorial_of_not_prime (n := 194) (m := 195) (by norm_num) (by norm_num)).trans prim_194

theorem prim_196 : primorial 196 = 198962376391690981640415251545285153602734402721821058212203976095413910572270 := 
  (primorial_of_not_prime (n := 195) (m := 196) (by norm_num) (by norm_num)).trans prim_195

theorem prim_197 : primorial 197 = 39195588149163123383161804554421175259738677336198748467804183290796540382737190 := 
  (primorial_of_prime (n := 196) (m := 197) (by norm_num) (by norm_num)).trans (by norm_num [prim_196])

theorem prim_198 : primorial 198 = 39195588149163123383161804554421175259738677336198748467804183290796540382737190 := 
  (primorial_of_not_prime (n := 197) (m := 198) (by norm_num) (by norm_num)).trans prim_197

theorem prim_199 : primorial 199 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_prime (n := 198) (m := 199) (by norm_num) (by norm_num)).trans (by norm_num [prim_198])

theorem prim_200 : primorial 200 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 199) (m := 200) (by norm_num) (by norm_num)).trans prim_199

theorem prim_201 : primorial 201 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 200) (m := 201) (by norm_num) (by norm_num)).trans prim_200

theorem prim_202 : primorial 202 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 201) (m := 202) (by norm_num) (by norm_num)).trans prim_201

theorem prim_203 : primorial 203 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 202) (m := 203) (by norm_num) (by norm_num)).trans prim_202

theorem prim_204 : primorial 204 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 203) (m := 204) (by norm_num) (by norm_num)).trans prim_203

theorem prim_205 : primorial 205 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 204) (m := 205) (by norm_num) (by norm_num)).trans prim_204

theorem prim_206 : primorial 206 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 205) (m := 206) (by norm_num) (by norm_num)).trans prim_205

theorem prim_207 : primorial 207 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 206) (m := 207) (by norm_num) (by norm_num)).trans prim_206

theorem prim_208 : primorial 208 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 207) (m := 208) (by norm_num) (by norm_num)).trans prim_207

theorem prim_209 : primorial 209 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 208) (m := 209) (by norm_num) (by norm_num)).trans prim_208

theorem prim_210 : primorial 210 = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := 
  (primorial_of_not_prime (n := 209) (m := 210) (by norm_num) (by norm_num)).trans prim_209

theorem prim_211 : primorial 211 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_prime (n := 210) (m := 211) (by norm_num) (by norm_num)).trans (by norm_num [prim_210])

theorem prim_212 : primorial 212 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 211) (m := 212) (by norm_num) (by norm_num)).trans prim_211

theorem prim_213 : primorial 213 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 212) (m := 213) (by norm_num) (by norm_num)).trans prim_212

theorem prim_214 : primorial 214 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 213) (m := 214) (by norm_num) (by norm_num)).trans prim_213

theorem prim_215 : primorial 215 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 214) (m := 215) (by norm_num) (by norm_num)).trans prim_214

theorem prim_216 : primorial 216 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 215) (m := 216) (by norm_num) (by norm_num)).trans prim_215

theorem prim_217 : primorial 217 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 216) (m := 217) (by norm_num) (by norm_num)).trans prim_216

theorem prim_218 : primorial 218 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 217) (m := 218) (by norm_num) (by norm_num)).trans prim_217

theorem prim_219 : primorial 219 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 218) (m := 219) (by norm_num) (by norm_num)).trans prim_218

theorem prim_220 : primorial 220 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 219) (m := 220) (by norm_num) (by norm_num)).trans prim_219

theorem prim_221 : primorial 221 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 220) (m := 221) (by norm_num) (by norm_num)).trans prim_220

theorem prim_222 : primorial 222 = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := 
  (primorial_of_not_prime (n := 221) (m := 222) (by norm_num) (by norm_num)).trans prim_221

theorem prim_223 : primorial 223 = 367009731827331916465034565550136732339800312955331782619462457039988073311157667212930 := 
  (primorial_of_prime (n := 222) (m := 223) (by norm_num) (by norm_num)).trans (by norm_num [prim_222])

theorem prim_224 : primorial 224 = 367009731827331916465034565550136732339800312955331782619462457039988073311157667212930 := 
  (primorial_of_not_prime (n := 223) (m := 224) (by norm_num) (by norm_num)).trans prim_223

theorem prim_225 : primorial 225 = 367009731827331916465034565550136732339800312955331782619462457039988073311157667212930 := 
  (primorial_of_not_prime (n := 224) (m := 225) (by norm_num) (by norm_num)).trans prim_224

theorem prim_226 : primorial 226 = 367009731827331916465034565550136732339800312955331782619462457039988073311157667212930 := 
  (primorial_of_not_prime (n := 225) (m := 226) (by norm_num) (by norm_num)).trans prim_225

theorem prim_227 : primorial 227 = 83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110 := 
  (primorial_of_prime (n := 226) (m := 227) (by norm_num) (by norm_num)).trans (by norm_num [prim_226])

theorem prim_228 : primorial 228 = 83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110 := 
  (primorial_of_not_prime (n := 227) (m := 228) (by norm_num) (by norm_num)).trans prim_227

theorem prim_229 : primorial 229 = 19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190 := 
  (primorial_of_prime (n := 228) (m := 229) (by norm_num) (by norm_num)).trans (by norm_num [prim_228])

theorem prim_230 : primorial 230 = 19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190 := 
  (primorial_of_not_prime (n := 229) (m := 230) (by norm_num) (by norm_num)).trans prim_229

theorem prim_231 : primorial 231 = 19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190 := 
  (primorial_of_not_prime (n := 230) (m := 231) (by norm_num) (by norm_num)).trans prim_230

theorem prim_232 : primorial 232 = 19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190 := 
  (primorial_of_not_prime (n := 231) (m := 232) (by norm_num) (by norm_num)).trans prim_231

theorem prim_233 : primorial 233 = 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270 := 
  (primorial_of_prime (n := 232) (m := 233) (by norm_num) (by norm_num)).trans (by norm_num [prim_232])

theorem prim_234 : primorial 234 = 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270 := 
  (primorial_of_not_prime (n := 233) (m := 234) (by norm_num) (by norm_num)).trans prim_233

theorem prim_235 : primorial 235 = 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270 := 
  (primorial_of_not_prime (n := 234) (m := 235) (by norm_num) (by norm_num)).trans prim_234

theorem prim_236 : primorial 236 = 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270 := 
  (primorial_of_not_prime (n := 235) (m := 236) (by norm_num) (by norm_num)).trans prim_235

theorem prim_237 : primorial 237 = 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270 := 
  (primorial_of_not_prime (n := 236) (m := 237) (by norm_num) (by norm_num)).trans prim_236

theorem prim_238 : primorial 238 = 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270 := 
  (primorial_of_not_prime (n := 237) (m := 238) (by norm_num) (by norm_num)).trans prim_237

theorem prim_239 : primorial 239 = 1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530 := 
  (primorial_of_prime (n := 238) (m := 239) (by norm_num) (by norm_num)).trans (by norm_num [prim_238])

theorem prim_240 : primorial 240 = 1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530 := 
  (primorial_of_not_prime (n := 239) (m := 240) (by norm_num) (by norm_num)).trans prim_239

theorem prim_241 : primorial 241 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_prime (n := 240) (m := 241) (by norm_num) (by norm_num)).trans (by norm_num [prim_240])

theorem prim_242 : primorial 242 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_not_prime (n := 241) (m := 242) (by norm_num) (by norm_num)).trans prim_241

theorem prim_243 : primorial 243 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_not_prime (n := 242) (m := 243) (by norm_num) (by norm_num)).trans prim_242

theorem prim_244 : primorial 244 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_not_prime (n := 243) (m := 244) (by norm_num) (by norm_num)).trans prim_243

theorem prim_245 : primorial 245 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_not_prime (n := 244) (m := 245) (by norm_num) (by norm_num)).trans prim_244

theorem prim_246 : primorial 246 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_not_prime (n := 245) (m := 246) (by norm_num) (by norm_num)).trans prim_245

theorem prim_247 : primorial 247 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_not_prime (n := 246) (m := 247) (by norm_num) (by norm_num)).trans prim_246

theorem prim_248 : primorial 248 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_not_prime (n := 247) (m := 248) (by norm_num) (by norm_num)).trans prim_247

theorem prim_249 : primorial 249 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_not_prime (n := 248) (m := 249) (by norm_num) (by norm_num)).trans prim_248

theorem prim_250 : primorial 250 = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := 
  (primorial_of_not_prime (n := 249) (m := 250) (by norm_num) (by norm_num)).trans prim_249

theorem prim_251 : primorial 251 = 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230 := 
  (primorial_of_prime (n := 250) (m := 251) (by norm_num) (by norm_num)).trans (by norm_num [prim_250])

theorem prim_252 : primorial 252 = 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230 := 
  (primorial_of_not_prime (n := 251) (m := 252) (by norm_num) (by norm_num)).trans prim_251

theorem prim_253 : primorial 253 = 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230 := 
  (primorial_of_not_prime (n := 252) (m := 253) (by norm_num) (by norm_num)).trans prim_252

theorem prim_254 : primorial 254 = 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230 := 
  (primorial_of_not_prime (n := 253) (m := 254) (by norm_num) (by norm_num)).trans prim_253

theorem prim_255 : primorial 255 = 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230 := 
  (primorial_of_not_prime (n := 254) (m := 255) (by norm_num) (by norm_num)).trans prim_254


/-! ## Step bounds: `ψ x - θ x ≤ (e/16) log 2` for `x < B` (generated) -/

theorem pst_lt_4 {x : ℝ} (hx : x < 4) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (0 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 4 1 1 1 1 1 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 0)
    (by norm_num [prim_1])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_8 {x : ℝ} (hx : x < 8) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (16 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 8 2 1 1 1 1 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 16)
    (by norm_num [prim_1, prim_2])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_9 {x : ℝ} (hx : x < 9) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (32 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 9 2 2 1 1 1 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 32)
    (by norm_num [prim_1, prim_2])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_16 {x : ℝ} (hx : x < 16) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (58 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 16 3 2 1 1 1 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 3 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 58)
    (by norm_num [prim_1, prim_2, prim_3])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_25 {x : ℝ} (hx : x < 25) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (74 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 25 4 2 2 1 1 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 4 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 74)
    (by norm_num [prim_1, prim_2, prim_4])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_27 {x : ℝ} (hx : x < 27) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (111 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 27 5 2 2 1 1 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 5 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 111)
    (by norm_num [prim_1, prim_2, prim_5])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_32 {x : ℝ} (hx : x < 32) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (136 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 32 5 3 2 1 1 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 5 * primorial 3 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 136)
    (by norm_num [prim_1, prim_2, prim_3, prim_5])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_49 {x : ℝ} (hx : x < 49) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (152 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 49 6 3 2 2 1 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 6 * primorial 3 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 152)
    (by norm_num [prim_1, prim_2, prim_3, prim_6])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_64 {x : ℝ} (hx : x < 64) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (197 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 64 7 3 2 2 1 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 7 * primorial 3 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 197)
    (by norm_num [prim_1, prim_2, prim_3, prim_7])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_81 {x : ℝ} (hx : x < 81) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (213 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 81 8 4 2 2 2 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 8 * primorial 4 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 213)
    (by norm_num [prim_1, prim_2, prim_4, prim_8])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_121 {x : ℝ} (hx : x < 121) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (239 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 121 10 4 3 2 2 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 10 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 239)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_10])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_125 {x : ℝ} (hx : x < 125) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (294 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 125 11 4 3 2 2 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 11 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 294)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_11])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_128 {x : ℝ} (hx : x < 128) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (331 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 128 11 5 3 2 2 1 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 11 * primorial 5 * primorial 3 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 331)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_11])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_169 {x : ℝ} (hx : x < 169) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (347 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 169 12 5 3 2 2 2 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 12 * primorial 5 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 347)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_12])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_243 {x : ℝ} (hx : x < 243) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (406 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 243 15 6 3 2 2 2 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 15 * primorial 6 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 406)
    (by norm_num [prim_1, prim_2, prim_3, prim_6, prim_15])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_256 {x : ℝ} (hx : x < 256) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (432 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 256 15 6 3 3 2 2 1 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 15 * primorial 6 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 432)
    (by norm_num [prim_1, prim_2, prim_3, prim_6, prim_15])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_289 {x : ℝ} (hx : x < 289) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (448 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 289 16 6 4 3 2 2 2 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 16 * primorial 6 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 448)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_16])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_343 {x : ℝ} (hx : x < 343) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (513 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 343 18 6 4 3 2 2 2 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 18 * primorial 6 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 513)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_18])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_361 {x : ℝ} (hx : x < 361) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (558 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 361 18 7 4 3 2 2 2 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 18 * primorial 7 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 558)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_7, prim_18])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_420 {x : ℝ} (hx : x < 420) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (626 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 420 20 7 4 3 2 2 2 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 20 * primorial 7 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 626)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_7, prim_20])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_512 {x : ℝ} (hx : x < 512) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (626 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 512 22 7 4 3 2 2 2 1 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 22 * primorial 7 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 626)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_7, prim_22])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_529 {x : ℝ} (hx : x < 529) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (642 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 529 22 8 4 3 2 2 2 2 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 22 * primorial 8 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 642)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_8, prim_22])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_625 {x : ℝ} (hx : x < 625) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (714 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 625 24 8 4 3 2 2 2 2 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 24 * primorial 8 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 714)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_8, prim_24])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_729 {x : ℝ} (hx : x < 729) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (752 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 729 26 8 5 3 2 2 2 2 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 26 * primorial 8 * primorial 5 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 752)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_8, prim_26])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_841 {x : ℝ} (hx : x < 841) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (777 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 841 28 9 5 3 3 2 2 2 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 28 * primorial 9 * primorial 5 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 777)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_9, prim_28])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_961 {x : ℝ} (hx : x < 961) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (855 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 961 30 9 5 3 3 2 2 2 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 30 * primorial 9 * primorial 5 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 855)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_9, prim_30])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_1024 {x : ℝ} (hx : x < 1024) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (934 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 1024 31 10 5 3 3 2 2 2 1 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 31 * primorial 10 * primorial 5 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 934)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_10, prim_31])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_1331 {x : ℝ} (hx : x < 1331) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (950 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 1331 36 10 6 4 3 2 2 2 2 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 36 * primorial 10 * primorial 6 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 950)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_10, prim_36])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_1369 {x : ℝ} (hx : x < 1369) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1005 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 1369 36 11 6 4 3 2 2 2 2 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 36 * primorial 11 * primorial 6 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1005)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_11, prim_36])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_1681 {x : ℝ} (hx : x < 1681) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1089 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 1681 40 11 6 4 3 2 2 2 2 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 40 * primorial 11 * primorial 6 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1089)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_11, prim_40])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_1849 {x : ℝ} (hx : x < 1849) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1174 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 1849 42 12 6 4 3 2 2 2 2 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 42 * primorial 12 * primorial 6 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1174)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_12, prim_42])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_2000 {x : ℝ} (hx : x < 2000) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1261 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 2000 44 12 6 4 3 2 2 2 2 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 44 * primorial 12 * primorial 6 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1261)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_12, prim_44])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_2048 {x : ℝ} (hx : x < 2048) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1261 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 2048 45 12 6 4 3 2 2 2 2 1 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 45 * primorial 12 * primorial 6 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1261)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_12, prim_45])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_2187 {x : ℝ} (hx : x < 2187) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1277 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 2187 46 12 6 4 3 2 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 46 * primorial 12 * primorial 6 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1277)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_12, prim_46])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_2197 {x : ℝ} (hx : x < 2197) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1302 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 2197 46 12 6 4 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 46 * primorial 12 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1302)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_12, prim_46])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_2209 {x : ℝ} (hx : x < 2209) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1362 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 2209 46 13 6 4 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 46 * primorial 13 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1362)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_13, prim_46])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_2401 {x : ℝ} (hx : x < 2401) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1451 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 2401 48 13 6 4 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 48 * primorial 13 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1451)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_13, prim_48])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_2500 {x : ℝ} (hx : x < 2500) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1495 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 2500 49 13 7 4 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 49 * primorial 13 * primorial 7 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1495)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_7, prim_13, prim_49])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_2809 {x : ℝ} (hx : x < 2809) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1495 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 2809 52 14 7 4 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 52 * primorial 14 * primorial 7 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1495)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_7, prim_14, prim_52])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_3000 {x : ℝ} (hx : x < 3000) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1587 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 3000 54 14 7 4 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 54 * primorial 14 * primorial 7 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1587)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_7, prim_14, prim_54])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_3125 {x : ℝ} (hx : x < 3125) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1587 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 3125 55 14 7 4 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 55 * primorial 14 * primorial 7 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1587)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_7, prim_14, prim_55])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_3481 {x : ℝ} (hx : x < 3481) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1624 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 3481 58 15 7 5 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 58 * primorial 15 * primorial 7 * primorial 5 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1624)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_7, prim_15, prim_58])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_3721 {x : ℝ} (hx : x < 3721) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1718 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 3721 60 15 7 5 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 60 * primorial 15 * primorial 7 * primorial 5 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1718)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_7, prim_15, prim_60])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_4096 {x : ℝ} (hx : x < 4096) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1813 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 4096 63 15 7 5 3 3 2 2 2 2 1 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 63 * primorial 15 * primorial 7 * primorial 5 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1 * primorial 1) (e := 1813)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_7, prim_15, prim_63])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_4489 {x : ℝ} (hx : x < 4489) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1829 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 4489 66 16 8 5 4 3 2 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 66 * primorial 16 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 1829)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_8, prim_16, prim_66])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_4913 {x : ℝ} (hx : x < 4913) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1926 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 4913 70 16 8 5 4 3 2 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 70 * primorial 16 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 1926)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_8, prim_16, prim_70])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_5041 {x : ℝ} (hx : x < 5041) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (1992 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 5041 70 17 8 5 4 3 2 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 70 * primorial 17 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 1992)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_8, prim_17, prim_70])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_5329 {x : ℝ} (hx : x < 5329) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2090 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 5329 72 17 8 5 4 3 2 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 72 * primorial 17 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 2090)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_8, prim_17, prim_72])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_6241 {x : ℝ} (hx : x < 6241) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2189 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 6241 78 18 8 5 4 3 2 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 78 * primorial 18 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 2189)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_8, prim_18, prim_78])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_6561 {x : ℝ} (hx : x < 6561) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2290 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 6561 80 18 8 5 4 3 2 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 80 * primorial 18 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 2290)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_8, prim_18, prim_80])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_6859 {x : ℝ} (hx : x < 6859) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2315 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 6859 82 18 9 5 4 3 3 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 82 * primorial 18 * primorial 9 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 2315)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_9, prim_18, prim_82])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_6889 {x : ℝ} (hx : x < 6889) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2383 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 6889 82 19 9 5 4 3 3 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 82 * primorial 19 * primorial 9 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 2383)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_9, prim_19, prim_82])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_7921 {x : ℝ} (hx : x < 7921) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2485 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 7921 88 19 9 6 4 3 3 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 88 * primorial 19 * primorial 9 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 2485)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_9, prim_19, prim_88])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_8192 {x : ℝ} (hx : x < 8192) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2589 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 8192 90 20 9 6 4 3 3 2 2 2 2 1 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 90 * primorial 20 * primorial 9 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1 * primorial 1) (e := 2589)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_9, prim_20, prim_90])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_9409 {x : ℝ} (hx : x < 9409) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2605 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 9409 96 21 9 6 4 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 96 * primorial 21 * primorial 9 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 2605)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_9, prim_21, prim_96])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_10201 {x : ℝ} (hx : x < 10201) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2711 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 10201 100 21 10 6 4 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 100 * primorial 21 * primorial 10 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 2711)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_10, prim_21, prim_100])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_10609 {x : ℝ} (hx : x < 10609) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2817 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 10609 102 21 10 6 4 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 102 * primorial 21 * primorial 10 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 2817)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_10, prim_21, prim_102])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_11449 {x : ℝ} (hx : x < 11449) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (2924 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 11449 106 22 10 6 4 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 106 * primorial 22 * primorial 10 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 2924)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_10, prim_22, prim_106])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_11881 {x : ℝ} (hx : x < 11881) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3032 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 11881 108 22 10 6 4 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 108 * primorial 22 * primorial 10 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 3032)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_10, prim_22, prim_108])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_12167 {x : ℝ} (hx : x < 12167) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3140 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 12167 110 22 10 6 4 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 110 * primorial 22 * primorial 10 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 3140)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_10, prim_22, prim_110])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_12769 {x : ℝ} (hx : x < 12769) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3213 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 12769 112 23 10 6 4 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 112 * primorial 23 * primorial 10 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 3213)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_10, prim_23, prim_112])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_14641 {x : ℝ} (hx : x < 14641) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3322 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 14641 120 24 10 6 4 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 120 * primorial 24 * primorial 10 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 3322)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_10, prim_24, prim_120])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_15625 {x : ℝ} (hx : x < 15625) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3377 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 15625 124 24 11 6 4 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 124 * primorial 24 * primorial 11 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 3377)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_6, prim_11, prim_24, prim_124])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_16129 {x : ℝ} (hx : x < 16129) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3414 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 16129 126 25 11 6 5 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 126 * primorial 25 * primorial 11 * primorial 6 * primorial 5 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 3414)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_6, prim_11, prim_25, prim_126])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_16384 {x : ℝ} (hx : x < 16384) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3526 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 16384 127 25 11 6 5 3 3 2 2 2 2 2 1 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 127 * primorial 25 * primorial 11 * primorial 6 * primorial 5 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1 * primorial 1) (e := 3526)
    (by norm_num [prim_1, prim_2, prim_3, prim_5, prim_6, prim_11, prim_25, prim_127])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_16807 {x : ℝ} (hx : x < 16807) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3542 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 16807 129 25 11 6 5 4 3 2 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 129 * primorial 25 * primorial 11 * primorial 6 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 3542)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_6, prim_11, prim_25, prim_129])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_17161 {x : ℝ} (hx : x < 17161) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3587 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 17161 130 25 11 7 5 4 3 2 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 130 * primorial 25 * primorial 11 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 3587)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_11, prim_25, prim_130])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_18769 {x : ℝ} (hx : x < 18769) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3700 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 18769 136 26 11 7 5 4 3 2 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 136 * primorial 26 * primorial 11 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 3700)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_11, prim_26, prim_136])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_19321 {x : ℝ} (hx : x < 19321) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3813 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 19321 138 26 11 7 5 4 3 2 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 138 * primorial 26 * primorial 11 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 3813)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_11, prim_26, prim_138])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_19683 {x : ℝ} (hx : x < 19683) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3927 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 19683 140 26 11 7 5 4 3 2 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 140 * primorial 26 * primorial 11 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 3927)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_11, prim_26, prim_140])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_22201 {x : ℝ} (hx : x < 22201) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3952 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 22201 148 28 12 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 148 * primorial 28 * primorial 12 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 3952)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_12, prim_28, prim_148])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_22801 {x : ℝ} (hx : x < 22801) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4068 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 22801 150 28 12 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 150 * primorial 28 * primorial 12 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4068)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_12, prim_28, prim_150])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_24389 {x : ℝ} (hx : x < 24389) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4184 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 24389 156 28 12 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 156 * primorial 28 * primorial 12 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4184)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_12, prim_28, prim_156])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_24649 {x : ℝ} (hx : x < 24649) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4261 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 24649 156 29 12 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 156 * primorial 29 * primorial 12 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4261)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_12, prim_29, prim_156])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_26569 {x : ℝ} (hx : x < 26569) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4378 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 26569 162 29 12 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 162 * primorial 29 * primorial 12 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4378)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_12, prim_29, prim_162])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_27889 {x : ℝ} (hx : x < 27889) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4496 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 27889 166 30 12 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 166 * primorial 30 * primorial 12 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4496)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_12, prim_30, prim_166])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_28561 {x : ℝ} (hx : x < 28561) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4614 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 28561 168 30 12 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 168 * primorial 30 * primorial 12 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4614)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_12, prim_30, prim_168])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_29791 {x : ℝ} (hx : x < 29791) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4673 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 29791 172 30 13 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 172 * primorial 30 * primorial 13 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4673)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_13, prim_30, prim_172])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_29929 {x : ℝ} (hx : x < 29929) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4752 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 29929 172 31 13 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 172 * primorial 31 * primorial 13 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4752)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_13, prim_31, prim_172])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_32041 {x : ℝ} (hx : x < 32041) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4871 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 32041 178 31 13 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 178 * primorial 31 * primorial 13 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4871)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_13, prim_31, prim_178])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_32761 {x : ℝ} (hx : x < 32761) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4991 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 32761 180 31 13 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 180 * primorial 31 * primorial 13 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 4991)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_13, prim_31, prim_180])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_32768 {x : ℝ} (hx : x < 32768) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (5111 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 32768 181 31 13 7 5 4 3 3 2 2 2 2 2 1 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 181 * primorial 31 * primorial 13 * primorial 7 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 1) (e := 5111)
    (by norm_num [prim_1, prim_2, prim_3, prim_4, prim_5, prim_7, prim_13, prim_31, prim_181])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_36481 {x : ℝ} (hx : x < 36481) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (5127 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 36481 190 33 13 8 5 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 190 * primorial 33 * primorial 13 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 5127)
    (by norm_num [prim_2, prim_3, prim_4, prim_5, prim_8, prim_13, prim_33, prim_190])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_37249 {x : ℝ} (hx : x < 37249) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (5248 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 37249 192 33 13 8 5 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 192 * primorial 33 * primorial 13 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 5248)
    (by norm_num [prim_2, prim_3, prim_4, prim_5, prim_8, prim_13, prim_33, prim_192])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_38809 {x : ℝ} (hx : x < 38809) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (5370 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 38809 196 33 14 8 5 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 196 * primorial 33 * primorial 14 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 5370)
    (by norm_num [prim_2, prim_3, prim_4, prim_5, prim_8, prim_14, prim_33, prim_196])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_39601 {x : ℝ} (hx : x < 39601) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (5492 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 39601 198 34 14 8 5 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 198 * primorial 34 * primorial 14 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 5492)
    (by norm_num [prim_2, prim_3, prim_4, prim_5, prim_8, prim_14, prim_34, prim_198])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_44521 {x : ℝ} (hx : x < 44521) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (5614 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 44521 210 35 14 8 5 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 210 * primorial 35 * primorial 14 * primorial 8 * primorial 5 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 5614)
    (by norm_num [prim_2, prim_3, prim_4, prim_5, prim_8, prim_14, prim_35, prim_210])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_49729 {x : ℝ} (hx : x < 49729) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (5737 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 49729 222 36 14 8 6 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 222 * primorial 36 * primorial 14 * primorial 8 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 5737)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_8, prim_14, prim_36, prim_222])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_50653 {x : ℝ} (hx : x < 50653) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (5862 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 50653 225 36 15 8 6 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 225 * primorial 36 * primorial 15 * primorial 8 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 5862)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_8, prim_15, prim_36, prim_225])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_51529 {x : ℝ} (hx : x < 51529) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (5946 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 51529 226 37 15 8 6 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 226 * primorial 37 * primorial 15 * primorial 8 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 5946)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_8, prim_15, prim_37, prim_226])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_52441 {x : ℝ} (hx : x < 52441) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (6071 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 52441 228 37 15 8 6 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 228 * primorial 37 * primorial 15 * primorial 8 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 6071)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_8, prim_15, prim_37, prim_228])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_54289 {x : ℝ} (hx : x < 54289) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (6196 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 54289 232 37 15 8 6 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 232 * primorial 37 * primorial 15 * primorial 8 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 6196)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_8, prim_15, prim_37, prim_232])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_57121 {x : ℝ} (hx : x < 57121) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (6322 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 57121 238 38 15 8 6 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 238 * primorial 38 * primorial 15 * primorial 8 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 6322)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_8, prim_15, prim_38, prim_238])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_58081 {x : ℝ} (hx : x < 58081) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (6448 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 58081 240 38 15 8 6 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 240 * primorial 38 * primorial 15 * primorial 8 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 6448)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_8, prim_15, prim_38, prim_240])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_59049 {x : ℝ} (hx : x < 59049) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (6575 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 59049 242 38 15 8 6 4 3 3 2 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 242 * primorial 38 * primorial 15 * primorial 8 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 6575)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_8, prim_15, prim_38, prim_242])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_63001 {x : ℝ} (hx : x < 63001) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (6600 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 63001 250 39 15 9 6 4 3 3 3 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 250 * primorial 39 * primorial 15 * primorial 9 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 6600)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_9, prim_15, prim_39, prim_250])
  exact h.trans (by exact_mod_cast h2)

theorem pst_lt_65536 {x : ℝ} (hx : x < 65536) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (6728 : ℝ) / 16 * Real.log 2 := by
  have h := psi_sub_theta_le_log14 65536 255 40 15 9 6 4 3 3 3 2 2 2 2 2 (x := x) (by exact_mod_cast hx)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := log_natCast_le_of_pow_le (P := primorial 255 * primorial 40 * primorial 15 * primorial 9 * primorial 6 * primorial 4 * primorial 3 * primorial 3 * primorial 3 * primorial 2 * primorial 2 * primorial 2 * primorial 2 * primorial 2) (e := 6728)
    (by norm_num [prim_2, prim_3, prim_4, prim_6, prim_9, prim_15, prim_40, prim_255])
  exact h.trans (by exact_mod_cast h2)


/-! ## Cells `A ≤ x < B` (generated) -/

theorem pst_cell_0 {x : ℝ} (hA : 0 ≤ x) (hB : x < 4) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 0.0 * √x :=
  le_mul_sqrt_of_log (pst_lt_4 hB) (by norm_num) hA (s := 0.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_4 {x : ℝ} (hA : 4 ≤ x) (hB : x < 8) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 0.3466 * √x :=
  le_mul_sqrt_of_log (pst_lt_8 hB) (by norm_num) hA (s := 2.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_8 {x : ℝ} (hA : 8 ≤ x) (hB : x < 9) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 0.4902 * √x :=
  le_mul_sqrt_of_log (pst_lt_9 hB) (by norm_num) hA (s := 2.8284) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_9 {x : ℝ} (hA : 9 ≤ x) (hB : x < 16) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 0.8376 * √x :=
  le_mul_sqrt_of_log (pst_lt_16 hB) (by norm_num) hA (s := 3.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_16 {x : ℝ} (hA : 16 ≤ x) (hB : x < 25) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 0.8015 * √x :=
  le_mul_sqrt_of_log (pst_lt_25 hB) (by norm_num) hA (s := 4.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_25 {x : ℝ} (hA : 25 ≤ x) (hB : x < 27) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 0.9618 * √x :=
  le_mul_sqrt_of_log (pst_lt_27 hB) (by norm_num) hA (s := 5.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_27 {x : ℝ} (hA : 27 ≤ x) (hB : x < 32) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1339 * √x :=
  le_mul_sqrt_of_log (pst_lt_32 hB) (by norm_num) hA (s := 5.1961) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_32 {x : ℝ} (hA : 32 ≤ x) (hB : x < 49) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1641 * √x :=
  le_mul_sqrt_of_log (pst_lt_49 hB) (by norm_num) hA (s := 5.6568) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_49 {x : ℝ} (hA : 49 ≤ x) (hB : x < 64) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2192 * √x :=
  le_mul_sqrt_of_log (pst_lt_64 hB) (by norm_num) hA (s := 7.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_64 {x : ℝ} (hA : 64 ≤ x) (hB : x < 81) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1535 * √x :=
  le_mul_sqrt_of_log (pst_lt_81 hB) (by norm_num) hA (s := 8.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_81 {x : ℝ} (hA : 81 ≤ x) (hB : x < 121) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1505 * √x :=
  le_mul_sqrt_of_log (pst_lt_121 hB) (by norm_num) hA (s := 9.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_121 {x : ℝ} (hA : 121 ≤ x) (hB : x < 125) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1579 * √x :=
  le_mul_sqrt_of_log (pst_lt_125 hB) (by norm_num) hA (s := 11.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_125 {x : ℝ} (hA : 125 ≤ x) (hB : x < 128) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2826 * √x :=
  le_mul_sqrt_of_log (pst_lt_128 hB) (by norm_num) hA (s := 11.1803) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_128 {x : ℝ} (hA : 128 ≤ x) (hB : x < 169) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3288 * √x :=
  le_mul_sqrt_of_log (pst_lt_169 hB) (by norm_num) hA (s := 11.3137) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_169 {x : ℝ} (hA : 169 ≤ x) (hB : x < 243) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.353 * √x :=
  le_mul_sqrt_of_log (pst_lt_243 hB) (by norm_num) hA (s := 13.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_243 {x : ℝ} (hA : 243 ≤ x) (hB : x < 256) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2006 * √x :=
  le_mul_sqrt_of_log (pst_lt_256 hB) (by norm_num) hA (s := 15.5884) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_256 {x : ℝ} (hA : 256 ≤ x) (hB : x < 289) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2131 * √x :=
  le_mul_sqrt_of_log (pst_lt_289 hB) (by norm_num) hA (s := 16.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_289 {x : ℝ} (hA : 289 ≤ x) (hB : x < 343) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3073 * √x :=
  le_mul_sqrt_of_log (pst_lt_343 hB) (by norm_num) hA (s := 17.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_343 {x : ℝ} (hA : 343 ≤ x) (hB : x < 361) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3053 * √x :=
  le_mul_sqrt_of_log (pst_lt_361 hB) (by norm_num) hA (s := 18.5202) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_361 {x : ℝ} (hA : 361 ≤ x) (hB : x < 420) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.4274 * √x :=
  le_mul_sqrt_of_log (pst_lt_420 hB) (by norm_num) hA (s := 19.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_420 {x : ℝ} (hA : 420 ≤ x) (hB : x < 512) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3233 * √x :=
  le_mul_sqrt_of_log (pst_lt_512 hB) (by norm_num) hA (s := 20.4939) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_512 {x : ℝ} (hA : 512 ≤ x) (hB : x < 529) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2292 * √x :=
  le_mul_sqrt_of_log (pst_lt_529 hB) (by norm_num) hA (s := 22.6274) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_529 {x : ℝ} (hA : 529 ≤ x) (hB : x < 625) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3449 * √x :=
  le_mul_sqrt_of_log (pst_lt_625 hB) (by norm_num) hA (s := 23.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_625 {x : ℝ} (hA : 625 ≤ x) (hB : x < 729) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3032 * √x :=
  le_mul_sqrt_of_log (pst_lt_729 hB) (by norm_num) hA (s := 25.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_729 {x : ℝ} (hA : 729 ≤ x) (hB : x < 841) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2468 * √x :=
  le_mul_sqrt_of_log (pst_lt_841 hB) (by norm_num) hA (s := 27.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_841 {x : ℝ} (hA : 841 ≤ x) (hB : x < 961) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2773 * √x :=
  le_mul_sqrt_of_log (pst_lt_961 hB) (by norm_num) hA (s := 29.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_961 {x : ℝ} (hA : 961 ≤ x) (hB : x < 1024) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3053 * √x :=
  le_mul_sqrt_of_log (pst_lt_1024 hB) (by norm_num) hA (s := 31.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_1024 {x : ℝ} (hA : 1024 ≤ x) (hB : x < 1331) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2862 * √x :=
  le_mul_sqrt_of_log (pst_lt_1331 hB) (by norm_num) hA (s := 32.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_1331 {x : ℝ} (hA : 1331 ≤ x) (hB : x < 1369) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1934 * √x :=
  le_mul_sqrt_of_log (pst_lt_1369 hB) (by norm_num) hA (s := 36.4828) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_1369 {x : ℝ} (hA : 1369 ≤ x) (hB : x < 1681) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2751 * √x :=
  le_mul_sqrt_of_log (pst_lt_1681 hB) (by norm_num) hA (s := 37.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_1681 {x : ℝ} (hA : 1681 ≤ x) (hB : x < 1849) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2405 * √x :=
  le_mul_sqrt_of_log (pst_lt_1849 hB) (by norm_num) hA (s := 41.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_1849 {x : ℝ} (hA : 1849 ≤ x) (hB : x < 2000) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2705 * √x :=
  le_mul_sqrt_of_log (pst_lt_2000 hB) (by norm_num) hA (s := 43.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_2000 {x : ℝ} (hA : 2000 ≤ x) (hB : x < 2048) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2216 * √x :=
  le_mul_sqrt_of_log (pst_lt_2048 hB) (by norm_num) hA (s := 44.7213) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_2048 {x : ℝ} (hA : 2048 ≤ x) (hB : x < 2187) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2225 * √x :=
  le_mul_sqrt_of_log (pst_lt_2187 hB) (by norm_num) hA (s := 45.2548) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_2187 {x : ℝ} (hA : 2187 ≤ x) (hB : x < 2197) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2062 * √x :=
  le_mul_sqrt_of_log (pst_lt_2197 hB) (by norm_num) hA (s := 46.7653) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_2197 {x : ℝ} (hA : 2197 ≤ x) (hB : x < 2209) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2589 * √x :=
  le_mul_sqrt_of_log (pst_lt_2209 hB) (by norm_num) hA (s := 46.8721) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_2209 {x : ℝ} (hA : 2209 ≤ x) (hB : x < 2401) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3375 * √x :=
  le_mul_sqrt_of_log (pst_lt_2401 hB) (by norm_num) hA (s := 47.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_2401 {x : ℝ} (hA : 2401 ≤ x) (hB : x < 2500) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3218 * √x :=
  le_mul_sqrt_of_log (pst_lt_2500 hB) (by norm_num) hA (s := 49.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_2500 {x : ℝ} (hA : 2500 ≤ x) (hB : x < 2809) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2954 * √x :=
  le_mul_sqrt_of_log (pst_lt_2809 hB) (by norm_num) hA (s := 50.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_2809 {x : ℝ} (hA : 2809 ≤ x) (hB : x < 3000) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2972 * √x :=
  le_mul_sqrt_of_log (pst_lt_3000 hB) (by norm_num) hA (s := 53.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_3000 {x : ℝ} (hA : 3000 ≤ x) (hB : x < 3125) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2553 * √x :=
  le_mul_sqrt_of_log (pst_lt_3125 hB) (by norm_num) hA (s := 54.7722) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_3125 {x : ℝ} (hA : 3125 ≤ x) (hB : x < 3481) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2586 * √x :=
  le_mul_sqrt_of_log (pst_lt_3481 hB) (by norm_num) hA (s := 55.9016) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_3481 {x : ℝ} (hA : 3481 ≤ x) (hB : x < 3721) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2615 * √x :=
  le_mul_sqrt_of_log (pst_lt_3721 hB) (by norm_num) hA (s := 59.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_3721 {x : ℝ} (hA : 3721 ≤ x) (hB : x < 4096) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2876 * √x :=
  le_mul_sqrt_of_log (pst_lt_4096 hB) (by norm_num) hA (s := 61.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_4096 {x : ℝ} (hA : 4096 ≤ x) (hB : x < 4489) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2381 * √x :=
  le_mul_sqrt_of_log (pst_lt_4489 hB) (by norm_num) hA (s := 64.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_4489 {x : ℝ} (hA : 4489 ≤ x) (hB : x < 4913) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2454 * √x :=
  le_mul_sqrt_of_log (pst_lt_4913 hB) (by norm_num) hA (s := 67.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_4913 {x : ℝ} (hA : 4913 ≤ x) (hB : x < 5041) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2312 * √x :=
  le_mul_sqrt_of_log (pst_lt_5041 hB) (by norm_num) hA (s := 70.0927) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_5041 {x : ℝ} (hA : 5041 ≤ x) (hB : x < 5329) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2753 * √x :=
  le_mul_sqrt_of_log (pst_lt_5329 hB) (by norm_num) hA (s := 71.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_5329 {x : ℝ} (hA : 5329 ≤ x) (hB : x < 6241) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2991 * √x :=
  le_mul_sqrt_of_log (pst_lt_6241 hB) (by norm_num) hA (s := 73.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_6241 {x : ℝ} (hA : 6241 ≤ x) (hB : x < 6561) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2558 * √x :=
  le_mul_sqrt_of_log (pst_lt_6561 hB) (by norm_num) hA (s := 79.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_6561 {x : ℝ} (hA : 6561 ≤ x) (hB : x < 6859) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2382 * √x :=
  le_mul_sqrt_of_log (pst_lt_6859 hB) (by norm_num) hA (s := 81.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_6859 {x : ℝ} (hA : 6859 ≤ x) (hB : x < 6889) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2466 * √x :=
  le_mul_sqrt_of_log (pst_lt_6889 hB) (by norm_num) hA (s := 82.819) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_6889 {x : ℝ} (hA : 6889 ≤ x) (hB : x < 7921) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2971 * √x :=
  le_mul_sqrt_of_log (pst_lt_7921 hB) (by norm_num) hA (s := 83.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_7921 {x : ℝ} (hA : 7921 ≤ x) (hB : x < 8192) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2603 * √x :=
  le_mul_sqrt_of_log (pst_lt_8192 hB) (by norm_num) hA (s := 89.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_8192 {x : ℝ} (hA : 8192 ≤ x) (hB : x < 9409) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2469 * √x :=
  le_mul_sqrt_of_log (pst_lt_9409 hB) (by norm_num) hA (s := 90.5096) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_9409 {x : ℝ} (hA : 9409 ≤ x) (hB : x < 10201) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2108 * √x :=
  le_mul_sqrt_of_log (pst_lt_10201 hB) (by norm_num) hA (s := 97.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_10201 {x : ℝ} (hA : 10201 ≤ x) (hB : x < 10609) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2083 * √x :=
  le_mul_sqrt_of_log (pst_lt_10609 hB) (by norm_num) hA (s := 101.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_10609 {x : ℝ} (hA : 10609 ≤ x) (hB : x < 11449) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2299 * √x :=
  le_mul_sqrt_of_log (pst_lt_11449 hB) (by norm_num) hA (s := 103.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_11449 {x : ℝ} (hA : 11449 ≤ x) (hB : x < 11881) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2276 * √x :=
  le_mul_sqrt_of_log (pst_lt_11881 hB) (by norm_num) hA (s := 107.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_11881 {x : ℝ} (hA : 11881 ≤ x) (hB : x < 12167) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.248 * √x :=
  le_mul_sqrt_of_log (pst_lt_12167 hB) (by norm_num) hA (s := 109.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_12167 {x : ℝ} (hA : 12167 ≤ x) (hB : x < 12769) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2619 * √x :=
  le_mul_sqrt_of_log (pst_lt_12769 hB) (by norm_num) hA (s := 110.3041) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_12769 {x : ℝ} (hA : 12769 ≤ x) (hB : x < 14641) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2736 * √x :=
  le_mul_sqrt_of_log (pst_lt_14641 hB) (by norm_num) hA (s := 113.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_14641 {x : ℝ} (hA : 14641 ≤ x) (hB : x < 15625) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2091 * √x :=
  le_mul_sqrt_of_log (pst_lt_15625 hB) (by norm_num) hA (s := 121.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_15625 {x : ℝ} (hA : 15625 ≤ x) (hB : x < 16129) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1833 * √x :=
  le_mul_sqrt_of_log (pst_lt_16129 hB) (by norm_num) hA (s := 125.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_16129 {x : ℝ} (hA : 16129 ≤ x) (hB : x < 16384) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2028 * √x :=
  le_mul_sqrt_of_log (pst_lt_16384 hB) (by norm_num) hA (s := 127.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_16384 {x : ℝ} (hA : 16384 ≤ x) (hB : x < 16807) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1988 * √x :=
  le_mul_sqrt_of_log (pst_lt_16807 hB) (by norm_num) hA (s := 128.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_16807 {x : ℝ} (hA : 16807 ≤ x) (hB : x < 17161) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1987 * √x :=
  le_mul_sqrt_of_log (pst_lt_17161 hB) (by norm_num) hA (s := 129.6418) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_17161 {x : ℝ} (hA : 17161 ≤ x) (hB : x < 18769) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2236 * √x :=
  le_mul_sqrt_of_log (pst_lt_18769 hB) (by norm_num) hA (s := 131.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_18769 {x : ℝ} (hA : 18769 ≤ x) (hB : x < 19321) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2058 * √x :=
  le_mul_sqrt_of_log (pst_lt_19321 hB) (by norm_num) hA (s := 137.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_19321 {x : ℝ} (hA : 19321 ≤ x) (hB : x < 19683) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.224 * √x :=
  le_mul_sqrt_of_log (pst_lt_19683 hB) (by norm_num) hA (s := 139.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_19683 {x : ℝ} (hA : 19683 ≤ x) (hB : x < 22201) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2204 * √x :=
  le_mul_sqrt_of_log (pst_lt_22201 hB) (by norm_num) hA (s := 140.2961) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_22201 {x : ℝ} (hA : 22201 ≤ x) (hB : x < 22801) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1828 * √x :=
  le_mul_sqrt_of_log (pst_lt_22801 hB) (by norm_num) hA (s := 149.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_22801 {x : ℝ} (hA : 22801 ≤ x) (hB : x < 24389) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2004 * √x :=
  le_mul_sqrt_of_log (pst_lt_24389 hB) (by norm_num) hA (s := 151.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_24389 {x : ℝ} (hA : 24389 ≤ x) (hB : x < 24649) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1821 * √x :=
  le_mul_sqrt_of_log (pst_lt_24649 hB) (by norm_num) hA (s := 156.1697) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_24649 {x : ℝ} (hA : 24649 ≤ x) (hB : x < 26569) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2081 * √x :=
  le_mul_sqrt_of_log (pst_lt_26569 hB) (by norm_num) hA (s := 157.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_26569 {x : ℝ} (hA : 26569 ≤ x) (hB : x < 27889) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.195 * √x :=
  le_mul_sqrt_of_log (pst_lt_27889 hB) (by norm_num) hA (s := 163.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_27889 {x : ℝ} (hA : 27889 ≤ x) (hB : x < 28561) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.197 * √x :=
  le_mul_sqrt_of_log (pst_lt_28561 hB) (by norm_num) hA (s := 167.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_28561 {x : ℝ} (hA : 28561 ≤ x) (hB : x < 29791) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1979 * √x :=
  le_mul_sqrt_of_log (pst_lt_29791 hB) (by norm_num) hA (s := 169.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_29791 {x : ℝ} (hA : 29791 ≤ x) (hB : x < 29929) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1928 * √x :=
  le_mul_sqrt_of_log (pst_lt_29929 hB) (by norm_num) hA (s := 172.6006) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_29929 {x : ℝ} (hA : 29929 ≤ x) (hB : x < 32041) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2198 * √x :=
  le_mul_sqrt_of_log (pst_lt_32041 hB) (by norm_num) hA (s := 173.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_32041 {x : ℝ} (hA : 32041 ≤ x) (hB : x < 32761) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.208 * √x :=
  le_mul_sqrt_of_log (pst_lt_32761 hB) (by norm_num) hA (s := 179.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_32761 {x : ℝ} (hA : 32761 ≤ x) (hB : x < 32768) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2233 * √x :=
  le_mul_sqrt_of_log (pst_lt_32768 hB) (by norm_num) hA (s := 181.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_32768 {x : ℝ} (hA : 32768 ≤ x) (hB : x < 36481) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.227 * √x :=
  le_mul_sqrt_of_log (pst_lt_36481 hB) (by norm_num) hA (s := 181.0193) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_36481 {x : ℝ} (hA : 36481 ≤ x) (hB : x < 37249) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1904 * √x :=
  le_mul_sqrt_of_log (pst_lt_37249 hB) (by norm_num) hA (s := 191.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_37249 {x : ℝ} (hA : 37249 ≤ x) (hB : x < 38809) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2054 * √x :=
  le_mul_sqrt_of_log (pst_lt_38809 hB) (by norm_num) hA (s := 193.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_38809 {x : ℝ} (hA : 38809 ≤ x) (hB : x < 39601) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2078 * √x :=
  le_mul_sqrt_of_log (pst_lt_39601 hB) (by norm_num) hA (s := 197.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_39601 {x : ℝ} (hA : 39601 ≤ x) (hB : x < 44521) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.2222 * √x :=
  le_mul_sqrt_of_log (pst_lt_44521 hB) (by norm_num) hA (s := 199.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_44521 {x : ℝ} (hA : 44521 ≤ x) (hB : x < 49729) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1779 * √x :=
  le_mul_sqrt_of_log (pst_lt_49729 hB) (by norm_num) hA (s := 211.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_49729 {x : ℝ} (hA : 49729 ≤ x) (hB : x < 50653) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1388 * √x :=
  le_mul_sqrt_of_log (pst_lt_50653 hB) (by norm_num) hA (s := 223.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_50653 {x : ℝ} (hA : 50653 ≤ x) (hB : x < 51529) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1446 * √x :=
  le_mul_sqrt_of_log (pst_lt_51529 hB) (by norm_num) hA (s := 225.0622) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_51529 {x : ℝ} (hA : 51529 ≤ x) (hB : x < 52441) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1587 * √x :=
  le_mul_sqrt_of_log (pst_lt_52441 hB) (by norm_num) hA (s := 227.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_52441 {x : ℝ} (hA : 52441 ≤ x) (hB : x < 54289) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1722 * √x :=
  le_mul_sqrt_of_log (pst_lt_54289 hB) (by norm_num) hA (s := 229.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_54289 {x : ℝ} (hA : 54289 ≤ x) (hB : x < 57121) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1755 * √x :=
  le_mul_sqrt_of_log (pst_lt_57121 hB) (by norm_num) hA (s := 233.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_57121 {x : ℝ} (hA : 57121 ≤ x) (hB : x < 58081) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1688 * √x :=
  le_mul_sqrt_of_log (pst_lt_58081 hB) (by norm_num) hA (s := 239.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_58081 {x : ℝ} (hA : 58081 ≤ x) (hB : x < 59049) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.182 * √x :=
  le_mul_sqrt_of_log (pst_lt_59049 hB) (by norm_num) hA (s := 241.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_59049 {x : ℝ} (hA : 59049 ≤ x) (hB : x < 63001) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1767 * √x :=
  le_mul_sqrt_of_log (pst_lt_63001 hB) (by norm_num) hA (s := 243.0) (by norm_num) (by norm_num) (by norm_num)

theorem pst_cell_63001 {x : ℝ} (hA : 63001 ≤ x) (hB : x < 65536) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.1613 * √x :=
  le_mul_sqrt_of_log (pst_lt_65536 hB) (by norm_num) hA (s := 251.0) (by norm_num) (by norm_num) (by norm_num)


/-! ## Range bounds below `2^16` (generated) -/

/-- `ψ x - θ x ≤ a √x` on `[0, 2^16)` (true sup ≈ 1.4274). -/
theorem psi_sub_theta_le_of_lt_65536 {x : ℝ} (hA : 0 ≤ x) (hB : x < 65536) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.43 * √x := by
  have hs := Real.sqrt_nonneg x
  rcases lt_or_ge x 4 with h4 | h4
  · exact (pst_cell_0 hA h4).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 8 with h8 | h8
  · exact (pst_cell_4 h4 h8).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 9 with h9 | h9
  · exact (pst_cell_8 h8 h9).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16 with h16 | h16
  · exact (pst_cell_9 h9 h16).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 25 with h25 | h25
  · exact (pst_cell_16 h16 h25).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 27 with h27 | h27
  · exact (pst_cell_25 h25 h27).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32 with h32 | h32
  · exact (pst_cell_27 h27 h32).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 49 with h49 | h49
  · exact (pst_cell_32 h32 h49).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 64 with h64 | h64
  · exact (pst_cell_49 h49 h64).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 81 with h81 | h81
  · exact (pst_cell_64 h64 h81).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 121 with h121 | h121
  · exact (pst_cell_81 h81 h121).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 125 with h125 | h125
  · exact (pst_cell_121 h121 h125).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 128 with h128 | h128
  · exact (pst_cell_125 h125 h128).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 169 with h169 | h169
  · exact (pst_cell_128 h128 h169).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 243 with h243 | h243
  · exact (pst_cell_169 h169 h243).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 256 with h256 | h256
  · exact (pst_cell_243 h243 h256).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 289 with h289 | h289
  · exact (pst_cell_256 h256 h289).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 343 with h343 | h343
  · exact (pst_cell_289 h289 h343).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 361 with h361 | h361
  · exact (pst_cell_343 h343 h361).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 420 with h420 | h420
  · exact (pst_cell_361 h361 h420).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 512 with h512 | h512
  · exact (pst_cell_420 h420 h512).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 529 with h529 | h529
  · exact (pst_cell_512 h512 h529).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 625 with h625 | h625
  · exact (pst_cell_529 h529 h625).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 729 with h729 | h729
  · exact (pst_cell_625 h625 h729).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 841 with h841 | h841
  · exact (pst_cell_729 h729 h841).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 961 with h961 | h961
  · exact (pst_cell_841 h841 h961).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1024 with h1024 | h1024
  · exact (pst_cell_961 h961 h1024).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1331 with h1331 | h1331
  · exact (pst_cell_1024 h1024 h1331).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1369 with h1369 | h1369
  · exact (pst_cell_1331 h1331 h1369).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1681 with h1681 | h1681
  · exact (pst_cell_1369 h1369 h1681).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1849 with h1849 | h1849
  · exact (pst_cell_1681 h1681 h1849).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2000 with h2000 | h2000
  · exact (pst_cell_1849 h1849 h2000).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2048 with h2048 | h2048
  · exact (pst_cell_2000 h2000 h2048).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2187 with h2187 | h2187
  · exact (pst_cell_2048 h2048 h2187).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2197 with h2197 | h2197
  · exact (pst_cell_2187 h2187 h2197).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2209 with h2209 | h2209
  · exact (pst_cell_2197 h2197 h2209).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2401 with h2401 | h2401
  · exact (pst_cell_2209 h2209 h2401).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2500 with h2500 | h2500
  · exact (pst_cell_2401 h2401 h2500).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2809 with h2809 | h2809
  · exact (pst_cell_2500 h2500 h2809).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3000 with h3000 | h3000
  · exact (pst_cell_2809 h2809 h3000).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3125 with h3125 | h3125
  · exact (pst_cell_3000 h3000 h3125).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3481 with h3481 | h3481
  · exact (pst_cell_3125 h3125 h3481).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3721 with h3721 | h3721
  · exact (pst_cell_3481 h3481 h3721).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4096 with h4096 | h4096
  · exact (pst_cell_3721 h3721 h4096).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4489 with h4489 | h4489
  · exact (pst_cell_4096 h4096 h4489).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4913 with h4913 | h4913
  · exact (pst_cell_4489 h4489 h4913).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 5041 with h5041 | h5041
  · exact (pst_cell_4913 h4913 h5041).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 5329 with h5329 | h5329
  · exact (pst_cell_5041 h5041 h5329).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6241 with h6241 | h6241
  · exact (pst_cell_5329 h5329 h6241).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6561 with h6561 | h6561
  · exact (pst_cell_6241 h6241 h6561).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6859 with h6859 | h6859
  · exact (pst_cell_6561 h6561 h6859).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6889 with h6889 | h6889
  · exact (pst_cell_6859 h6859 h6889).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 7921 with h7921 | h7921
  · exact (pst_cell_6889 h6889 h7921).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 8192 with h8192 | h8192
  · exact (pst_cell_7921 h7921 h8192).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 9409 with h9409 | h9409
  · exact (pst_cell_8192 h8192 h9409).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 10201 with h10201 | h10201
  · exact (pst_cell_9409 h9409 h10201).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 10609 with h10609 | h10609
  · exact (pst_cell_10201 h10201 h10609).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 11449 with h11449 | h11449
  · exact (pst_cell_10609 h10609 h11449).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 11881 with h11881 | h11881
  · exact (pst_cell_11449 h11449 h11881).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 12167 with h12167 | h12167
  · exact (pst_cell_11881 h11881 h12167).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 12769 with h12769 | h12769
  · exact (pst_cell_12167 h12167 h12769).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 14641 with h14641 | h14641
  · exact (pst_cell_12769 h12769 h14641).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 15625 with h15625 | h15625
  · exact (pst_cell_14641 h14641 h15625).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16129 with h16129 | h16129
  · exact (pst_cell_15625 h15625 h16129).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16384 with h16384 | h16384
  · exact (pst_cell_16129 h16129 h16384).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16807 with h16807 | h16807
  · exact (pst_cell_16384 h16384 h16807).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 17161 with h17161 | h17161
  · exact (pst_cell_16807 h16807 h17161).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 18769 with h18769 | h18769
  · exact (pst_cell_17161 h17161 h18769).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 19321 with h19321 | h19321
  · exact (pst_cell_18769 h18769 h19321).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 19683 with h19683 | h19683
  · exact (pst_cell_19321 h19321 h19683).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 22201 with h22201 | h22201
  · exact (pst_cell_19683 h19683 h22201).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 22801 with h22801 | h22801
  · exact (pst_cell_22201 h22201 h22801).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 24389 with h24389 | h24389
  · exact (pst_cell_22801 h22801 h24389).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 24649 with h24649 | h24649
  · exact (pst_cell_24389 h24389 h24649).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 26569 with h26569 | h26569
  · exact (pst_cell_24649 h24649 h26569).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 27889 with h27889 | h27889
  · exact (pst_cell_26569 h26569 h27889).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 28561 with h28561 | h28561
  · exact (pst_cell_27889 h27889 h28561).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 29791 with h29791 | h29791
  · exact (pst_cell_28561 h28561 h29791).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 29929 with h29929 | h29929
  · exact (pst_cell_29791 h29791 h29929).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32041 with h32041 | h32041
  · exact (pst_cell_29929 h29929 h32041).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32761 with h32761 | h32761
  · exact (pst_cell_32041 h32041 h32761).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32768 with h32768 | h32768
  · exact (pst_cell_32761 h32761 h32768).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 36481 with h36481 | h36481
  · exact (pst_cell_32768 h32768 h36481).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 37249 with h37249 | h37249
  · exact (pst_cell_36481 h36481 h37249).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 38809 with h38809 | h38809
  · exact (pst_cell_37249 h37249 h38809).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 39601 with h39601 | h39601
  · exact (pst_cell_38809 h38809 h39601).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 44521 with h44521 | h44521
  · exact (pst_cell_39601 h39601 h44521).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 49729 with h49729 | h49729
  · exact (pst_cell_44521 h44521 h49729).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 50653 with h50653 | h50653
  · exact (pst_cell_49729 h49729 h50653).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 51529 with h51529 | h51529
  · exact (pst_cell_50653 h50653 h51529).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 52441 with h52441 | h52441
  · exact (pst_cell_51529 h51529 h52441).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 54289 with h54289 | h54289
  · exact (pst_cell_52441 h52441 h54289).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 57121 with h57121 | h57121
  · exact (pst_cell_54289 h54289 h57121).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 58081 with h58081 | h58081
  · exact (pst_cell_57121 h57121 h58081).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 59049 with h59049 | h59049
  · exact (pst_cell_58081 h58081 h59049).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 63001 with h63001 | h63001
  · exact (pst_cell_59049 h59049 h63001).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  exact (pst_cell_63001 h63001 hB).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)

/-- `ψ x - θ x ≤ a √x` on `[420, 2^16)` (true sup ≈ 1.3449). -/
theorem psi_sub_theta_le_of_ge_420_of_lt_65536 {x : ℝ} (hA : 420 ≤ x) (hB : x < 65536) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.35 * √x := by
  have hs := Real.sqrt_nonneg x
  rcases lt_or_ge x 512 with h512 | h512
  · exact (pst_cell_420 hA h512).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 529 with h529 | h529
  · exact (pst_cell_512 h512 h529).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 625 with h625 | h625
  · exact (pst_cell_529 h529 h625).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 729 with h729 | h729
  · exact (pst_cell_625 h625 h729).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 841 with h841 | h841
  · exact (pst_cell_729 h729 h841).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 961 with h961 | h961
  · exact (pst_cell_841 h841 h961).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1024 with h1024 | h1024
  · exact (pst_cell_961 h961 h1024).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1331 with h1331 | h1331
  · exact (pst_cell_1024 h1024 h1331).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1369 with h1369 | h1369
  · exact (pst_cell_1331 h1331 h1369).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1681 with h1681 | h1681
  · exact (pst_cell_1369 h1369 h1681).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 1849 with h1849 | h1849
  · exact (pst_cell_1681 h1681 h1849).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2000 with h2000 | h2000
  · exact (pst_cell_1849 h1849 h2000).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2048 with h2048 | h2048
  · exact (pst_cell_2000 h2000 h2048).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2187 with h2187 | h2187
  · exact (pst_cell_2048 h2048 h2187).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2197 with h2197 | h2197
  · exact (pst_cell_2187 h2187 h2197).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2209 with h2209 | h2209
  · exact (pst_cell_2197 h2197 h2209).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2401 with h2401 | h2401
  · exact (pst_cell_2209 h2209 h2401).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2500 with h2500 | h2500
  · exact (pst_cell_2401 h2401 h2500).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2809 with h2809 | h2809
  · exact (pst_cell_2500 h2500 h2809).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3000 with h3000 | h3000
  · exact (pst_cell_2809 h2809 h3000).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3125 with h3125 | h3125
  · exact (pst_cell_3000 h3000 h3125).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3481 with h3481 | h3481
  · exact (pst_cell_3125 h3125 h3481).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3721 with h3721 | h3721
  · exact (pst_cell_3481 h3481 h3721).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4096 with h4096 | h4096
  · exact (pst_cell_3721 h3721 h4096).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4489 with h4489 | h4489
  · exact (pst_cell_4096 h4096 h4489).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4913 with h4913 | h4913
  · exact (pst_cell_4489 h4489 h4913).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 5041 with h5041 | h5041
  · exact (pst_cell_4913 h4913 h5041).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 5329 with h5329 | h5329
  · exact (pst_cell_5041 h5041 h5329).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6241 with h6241 | h6241
  · exact (pst_cell_5329 h5329 h6241).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6561 with h6561 | h6561
  · exact (pst_cell_6241 h6241 h6561).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6859 with h6859 | h6859
  · exact (pst_cell_6561 h6561 h6859).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6889 with h6889 | h6889
  · exact (pst_cell_6859 h6859 h6889).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 7921 with h7921 | h7921
  · exact (pst_cell_6889 h6889 h7921).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 8192 with h8192 | h8192
  · exact (pst_cell_7921 h7921 h8192).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 9409 with h9409 | h9409
  · exact (pst_cell_8192 h8192 h9409).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 10201 with h10201 | h10201
  · exact (pst_cell_9409 h9409 h10201).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 10609 with h10609 | h10609
  · exact (pst_cell_10201 h10201 h10609).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 11449 with h11449 | h11449
  · exact (pst_cell_10609 h10609 h11449).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 11881 with h11881 | h11881
  · exact (pst_cell_11449 h11449 h11881).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 12167 with h12167 | h12167
  · exact (pst_cell_11881 h11881 h12167).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 12769 with h12769 | h12769
  · exact (pst_cell_12167 h12167 h12769).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 14641 with h14641 | h14641
  · exact (pst_cell_12769 h12769 h14641).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 15625 with h15625 | h15625
  · exact (pst_cell_14641 h14641 h15625).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16129 with h16129 | h16129
  · exact (pst_cell_15625 h15625 h16129).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16384 with h16384 | h16384
  · exact (pst_cell_16129 h16129 h16384).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16807 with h16807 | h16807
  · exact (pst_cell_16384 h16384 h16807).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 17161 with h17161 | h17161
  · exact (pst_cell_16807 h16807 h17161).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 18769 with h18769 | h18769
  · exact (pst_cell_17161 h17161 h18769).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 19321 with h19321 | h19321
  · exact (pst_cell_18769 h18769 h19321).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 19683 with h19683 | h19683
  · exact (pst_cell_19321 h19321 h19683).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 22201 with h22201 | h22201
  · exact (pst_cell_19683 h19683 h22201).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 22801 with h22801 | h22801
  · exact (pst_cell_22201 h22201 h22801).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 24389 with h24389 | h24389
  · exact (pst_cell_22801 h22801 h24389).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 24649 with h24649 | h24649
  · exact (pst_cell_24389 h24389 h24649).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 26569 with h26569 | h26569
  · exact (pst_cell_24649 h24649 h26569).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 27889 with h27889 | h27889
  · exact (pst_cell_26569 h26569 h27889).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 28561 with h28561 | h28561
  · exact (pst_cell_27889 h27889 h28561).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 29791 with h29791 | h29791
  · exact (pst_cell_28561 h28561 h29791).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 29929 with h29929 | h29929
  · exact (pst_cell_29791 h29791 h29929).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32041 with h32041 | h32041
  · exact (pst_cell_29929 h29929 h32041).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32761 with h32761 | h32761
  · exact (pst_cell_32041 h32041 h32761).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32768 with h32768 | h32768
  · exact (pst_cell_32761 h32761 h32768).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 36481 with h36481 | h36481
  · exact (pst_cell_32768 h32768 h36481).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 37249 with h37249 | h37249
  · exact (pst_cell_36481 h36481 h37249).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 38809 with h38809 | h38809
  · exact (pst_cell_37249 h37249 h38809).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 39601 with h39601 | h39601
  · exact (pst_cell_38809 h38809 h39601).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 44521 with h44521 | h44521
  · exact (pst_cell_39601 h39601 h44521).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 49729 with h49729 | h49729
  · exact (pst_cell_44521 h44521 h49729).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 50653 with h50653 | h50653
  · exact (pst_cell_49729 h49729 h50653).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 51529 with h51529 | h51529
  · exact (pst_cell_50653 h50653 h51529).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 52441 with h52441 | h52441
  · exact (pst_cell_51529 h51529 h52441).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 54289 with h54289 | h54289
  · exact (pst_cell_52441 h52441 h54289).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 57121 with h57121 | h57121
  · exact (pst_cell_54289 h54289 h57121).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 58081 with h58081 | h58081
  · exact (pst_cell_57121 h57121 h58081).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 59049 with h59049 | h59049
  · exact (pst_cell_58081 h58081 h59049).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 63001 with h63001 | h63001
  · exact (pst_cell_59049 h59049 h63001).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  exact (pst_cell_63001 h63001 hB).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)

/-- `ψ x - θ x ≤ a √x` on `[2000, 2^16)` (true sup ≈ 1.3375). -/
theorem psi_sub_theta_le_of_ge_2000_of_lt_65536 {x : ℝ} (hA : 2000 ≤ x) (hB : x < 65536) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.34 * √x := by
  have hs := Real.sqrt_nonneg x
  rcases lt_or_ge x 2048 with h2048 | h2048
  · exact (pst_cell_2000 hA h2048).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2187 with h2187 | h2187
  · exact (pst_cell_2048 h2048 h2187).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2197 with h2197 | h2197
  · exact (pst_cell_2187 h2187 h2197).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2209 with h2209 | h2209
  · exact (pst_cell_2197 h2197 h2209).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2401 with h2401 | h2401
  · exact (pst_cell_2209 h2209 h2401).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2500 with h2500 | h2500
  · exact (pst_cell_2401 h2401 h2500).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 2809 with h2809 | h2809
  · exact (pst_cell_2500 h2500 h2809).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3000 with h3000 | h3000
  · exact (pst_cell_2809 h2809 h3000).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3125 with h3125 | h3125
  · exact (pst_cell_3000 h3000 h3125).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3481 with h3481 | h3481
  · exact (pst_cell_3125 h3125 h3481).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3721 with h3721 | h3721
  · exact (pst_cell_3481 h3481 h3721).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4096 with h4096 | h4096
  · exact (pst_cell_3721 h3721 h4096).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4489 with h4489 | h4489
  · exact (pst_cell_4096 h4096 h4489).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4913 with h4913 | h4913
  · exact (pst_cell_4489 h4489 h4913).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 5041 with h5041 | h5041
  · exact (pst_cell_4913 h4913 h5041).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 5329 with h5329 | h5329
  · exact (pst_cell_5041 h5041 h5329).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6241 with h6241 | h6241
  · exact (pst_cell_5329 h5329 h6241).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6561 with h6561 | h6561
  · exact (pst_cell_6241 h6241 h6561).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6859 with h6859 | h6859
  · exact (pst_cell_6561 h6561 h6859).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6889 with h6889 | h6889
  · exact (pst_cell_6859 h6859 h6889).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 7921 with h7921 | h7921
  · exact (pst_cell_6889 h6889 h7921).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 8192 with h8192 | h8192
  · exact (pst_cell_7921 h7921 h8192).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 9409 with h9409 | h9409
  · exact (pst_cell_8192 h8192 h9409).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 10201 with h10201 | h10201
  · exact (pst_cell_9409 h9409 h10201).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 10609 with h10609 | h10609
  · exact (pst_cell_10201 h10201 h10609).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 11449 with h11449 | h11449
  · exact (pst_cell_10609 h10609 h11449).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 11881 with h11881 | h11881
  · exact (pst_cell_11449 h11449 h11881).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 12167 with h12167 | h12167
  · exact (pst_cell_11881 h11881 h12167).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 12769 with h12769 | h12769
  · exact (pst_cell_12167 h12167 h12769).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 14641 with h14641 | h14641
  · exact (pst_cell_12769 h12769 h14641).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 15625 with h15625 | h15625
  · exact (pst_cell_14641 h14641 h15625).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16129 with h16129 | h16129
  · exact (pst_cell_15625 h15625 h16129).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16384 with h16384 | h16384
  · exact (pst_cell_16129 h16129 h16384).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16807 with h16807 | h16807
  · exact (pst_cell_16384 h16384 h16807).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 17161 with h17161 | h17161
  · exact (pst_cell_16807 h16807 h17161).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 18769 with h18769 | h18769
  · exact (pst_cell_17161 h17161 h18769).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 19321 with h19321 | h19321
  · exact (pst_cell_18769 h18769 h19321).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 19683 with h19683 | h19683
  · exact (pst_cell_19321 h19321 h19683).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 22201 with h22201 | h22201
  · exact (pst_cell_19683 h19683 h22201).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 22801 with h22801 | h22801
  · exact (pst_cell_22201 h22201 h22801).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 24389 with h24389 | h24389
  · exact (pst_cell_22801 h22801 h24389).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 24649 with h24649 | h24649
  · exact (pst_cell_24389 h24389 h24649).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 26569 with h26569 | h26569
  · exact (pst_cell_24649 h24649 h26569).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 27889 with h27889 | h27889
  · exact (pst_cell_26569 h26569 h27889).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 28561 with h28561 | h28561
  · exact (pst_cell_27889 h27889 h28561).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 29791 with h29791 | h29791
  · exact (pst_cell_28561 h28561 h29791).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 29929 with h29929 | h29929
  · exact (pst_cell_29791 h29791 h29929).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32041 with h32041 | h32041
  · exact (pst_cell_29929 h29929 h32041).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32761 with h32761 | h32761
  · exact (pst_cell_32041 h32041 h32761).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32768 with h32768 | h32768
  · exact (pst_cell_32761 h32761 h32768).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 36481 with h36481 | h36481
  · exact (pst_cell_32768 h32768 h36481).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 37249 with h37249 | h37249
  · exact (pst_cell_36481 h36481 h37249).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 38809 with h38809 | h38809
  · exact (pst_cell_37249 h37249 h38809).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 39601 with h39601 | h39601
  · exact (pst_cell_38809 h38809 h39601).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 44521 with h44521 | h44521
  · exact (pst_cell_39601 h39601 h44521).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 49729 with h49729 | h49729
  · exact (pst_cell_44521 h44521 h49729).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 50653 with h50653 | h50653
  · exact (pst_cell_49729 h49729 h50653).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 51529 with h51529 | h51529
  · exact (pst_cell_50653 h50653 h51529).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 52441 with h52441 | h52441
  · exact (pst_cell_51529 h51529 h52441).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 54289 with h54289 | h54289
  · exact (pst_cell_52441 h52441 h54289).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 57121 with h57121 | h57121
  · exact (pst_cell_54289 h54289 h57121).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 58081 with h58081 | h58081
  · exact (pst_cell_57121 h57121 h58081).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 59049 with h59049 | h59049
  · exact (pst_cell_58081 h58081 h59049).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 63001 with h63001 | h63001
  · exact (pst_cell_59049 h59049 h63001).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  exact (pst_cell_63001 h63001 hB).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)

/-- `ψ x - θ x ≤ a √x` on `[2500, 2^16)` (true sup ≈ 1.2991). -/
theorem psi_sub_theta_le_of_ge_2500_of_lt_65536 {x : ℝ} (hA : 2500 ≤ x) (hB : x < 65536) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.3 * √x := by
  have hs := Real.sqrt_nonneg x
  rcases lt_or_ge x 2809 with h2809 | h2809
  · exact (pst_cell_2500 hA h2809).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3000 with h3000 | h3000
  · exact (pst_cell_2809 h2809 h3000).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3125 with h3125 | h3125
  · exact (pst_cell_3000 h3000 h3125).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3481 with h3481 | h3481
  · exact (pst_cell_3125 h3125 h3481).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 3721 with h3721 | h3721
  · exact (pst_cell_3481 h3481 h3721).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4096 with h4096 | h4096
  · exact (pst_cell_3721 h3721 h4096).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4489 with h4489 | h4489
  · exact (pst_cell_4096 h4096 h4489).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 4913 with h4913 | h4913
  · exact (pst_cell_4489 h4489 h4913).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 5041 with h5041 | h5041
  · exact (pst_cell_4913 h4913 h5041).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 5329 with h5329 | h5329
  · exact (pst_cell_5041 h5041 h5329).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6241 with h6241 | h6241
  · exact (pst_cell_5329 h5329 h6241).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6561 with h6561 | h6561
  · exact (pst_cell_6241 h6241 h6561).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6859 with h6859 | h6859
  · exact (pst_cell_6561 h6561 h6859).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 6889 with h6889 | h6889
  · exact (pst_cell_6859 h6859 h6889).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 7921 with h7921 | h7921
  · exact (pst_cell_6889 h6889 h7921).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 8192 with h8192 | h8192
  · exact (pst_cell_7921 h7921 h8192).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 9409 with h9409 | h9409
  · exact (pst_cell_8192 h8192 h9409).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 10201 with h10201 | h10201
  · exact (pst_cell_9409 h9409 h10201).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 10609 with h10609 | h10609
  · exact (pst_cell_10201 h10201 h10609).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 11449 with h11449 | h11449
  · exact (pst_cell_10609 h10609 h11449).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 11881 with h11881 | h11881
  · exact (pst_cell_11449 h11449 h11881).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 12167 with h12167 | h12167
  · exact (pst_cell_11881 h11881 h12167).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 12769 with h12769 | h12769
  · exact (pst_cell_12167 h12167 h12769).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 14641 with h14641 | h14641
  · exact (pst_cell_12769 h12769 h14641).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 15625 with h15625 | h15625
  · exact (pst_cell_14641 h14641 h15625).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16129 with h16129 | h16129
  · exact (pst_cell_15625 h15625 h16129).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16384 with h16384 | h16384
  · exact (pst_cell_16129 h16129 h16384).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 16807 with h16807 | h16807
  · exact (pst_cell_16384 h16384 h16807).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 17161 with h17161 | h17161
  · exact (pst_cell_16807 h16807 h17161).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 18769 with h18769 | h18769
  · exact (pst_cell_17161 h17161 h18769).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 19321 with h19321 | h19321
  · exact (pst_cell_18769 h18769 h19321).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 19683 with h19683 | h19683
  · exact (pst_cell_19321 h19321 h19683).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 22201 with h22201 | h22201
  · exact (pst_cell_19683 h19683 h22201).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 22801 with h22801 | h22801
  · exact (pst_cell_22201 h22201 h22801).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 24389 with h24389 | h24389
  · exact (pst_cell_22801 h22801 h24389).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 24649 with h24649 | h24649
  · exact (pst_cell_24389 h24389 h24649).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 26569 with h26569 | h26569
  · exact (pst_cell_24649 h24649 h26569).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 27889 with h27889 | h27889
  · exact (pst_cell_26569 h26569 h27889).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 28561 with h28561 | h28561
  · exact (pst_cell_27889 h27889 h28561).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 29791 with h29791 | h29791
  · exact (pst_cell_28561 h28561 h29791).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 29929 with h29929 | h29929
  · exact (pst_cell_29791 h29791 h29929).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32041 with h32041 | h32041
  · exact (pst_cell_29929 h29929 h32041).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32761 with h32761 | h32761
  · exact (pst_cell_32041 h32041 h32761).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 32768 with h32768 | h32768
  · exact (pst_cell_32761 h32761 h32768).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 36481 with h36481 | h36481
  · exact (pst_cell_32768 h32768 h36481).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 37249 with h37249 | h37249
  · exact (pst_cell_36481 h36481 h37249).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 38809 with h38809 | h38809
  · exact (pst_cell_37249 h37249 h38809).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 39601 with h39601 | h39601
  · exact (pst_cell_38809 h38809 h39601).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 44521 with h44521 | h44521
  · exact (pst_cell_39601 h39601 h44521).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 49729 with h49729 | h49729
  · exact (pst_cell_44521 h44521 h49729).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 50653 with h50653 | h50653
  · exact (pst_cell_49729 h49729 h50653).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 51529 with h51529 | h51529
  · exact (pst_cell_50653 h50653 h51529).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 52441 with h52441 | h52441
  · exact (pst_cell_51529 h51529 h52441).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 54289 with h54289 | h54289
  · exact (pst_cell_52441 h52441 h54289).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 57121 with h57121 | h57121
  · exact (pst_cell_54289 h54289 h57121).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 58081 with h58081 | h58081
  · exact (pst_cell_57121 h57121 h58081).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 59049 with h59049 | h59049
  · exact (pst_cell_58081 h58081 h59049).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  rcases lt_or_ge x 63001 with h63001 | h63001
  · exact (pst_cell_59049 h59049 h63001).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)
  exact (pst_cell_63001 h63001 hB).trans (mul_le_mul_of_nonneg_right (by norm_num) hs)


/-! ## The uniform bound `ψ x - θ x ≤ 1.84 √x` -/

/-- From an inductive hypothesis `ψ y - θ y ≤ A √y` (`y < N`) to `ψ(x^a) ≤ log 4 · x^a + A x^{a/2}`. -/
theorem psi_rpow_le_of_ih {A N : ℝ}
    (ih : ∀ y : ℝ, 0 ≤ y → y < N → Chebyshev.psi y - Chebyshev.theta y ≤ A * √y)
    {x : ℝ} (hx : 1 ≤ x) {a b : ℝ} (hb : a / 2 = b) (hlt : x ^ a < N) :
    Chebyshev.psi (x ^ a) ≤ Real.log 4 * x ^ a + A * x ^ b := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ x ^ a := Real.rpow_nonneg hx0 a
  have h1 := ih (x ^ a) hy0 hlt
  have h2 := Chebyshev.theta_le_log4_mul_x hy0
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0, show a * (1 / 2) = b by rw [← hb]; ring] at h1
  linarith

/-- `x^b ≤ (65536^b / 256) √x` for `x ≥ 2^16`, `b ≤ 1/2`. -/
theorem rpow_le_const_mul_sqrt {x c b : ℝ} (hx : 65536 ≤ x) (hb : b ≤ 1 / 2)
    (hc : (65536 : ℝ) ^ b ≤ c) : x ^ b ≤ c / 256 * √x := by
  have ht : 1 ≤ x / 65536 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have h := rpow_mul_le_sqrt (x0 := 65536) (t := x / 65536) (b := b) (by norm_num) ht hb
  have e1 : (65536 : ℝ) * (x / 65536) = x := by ring
  have hs : √(65536 : ℝ) = 256 := by
    rw [show (65536 : ℝ) = 256 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have e2 : √x = 256 * √(x / 65536) := by
    rw [← hs, ← Real.sqrt_mul (show (0 : ℝ) ≤ 65536 by norm_num), e1]
  rw [e1] at h
  have hsq : √(x / 65536) = √x / 256 := by rw [e2]; ring
  rw [hsq] at h
  calc x ^ b ≤ (65536 : ℝ) ^ b * (√x / 256) := h
    _ ≤ c * (√x / 256) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = c / 256 * √x := by ring

theorem psi_sub_theta_le_aux :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → x < 2 ^ n → Chebyshev.psi x - Chebyshev.theta x ≤ 1.84 * √x := by
  intro n
  induction n with
  | zero =>
    intro x h0 h1
    have h1' : x < 65536 := by norm_num at h1; linarith
    exact (psi_sub_theta_le_of_lt_65536 h0 h1').trans
      (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg x))
  | succ n ih =>
    intro x h0 h1
    rcases lt_or_ge x 65536 with h | h
    · exact (psi_sub_theta_le_of_lt_65536 h0 h).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg x))
    · have hx1 : 1 ≤ x := by linarith
      have hS0 : 0 ≤ √x := Real.sqrt_nonneg x
      have hS : (256 : ℝ) ≤ √x :=
        (le_abs_self _).trans (Real.abs_le_sqrt (by norm_num; linarith))
      have hSS : √x * √x = x := Real.mul_self_sqrt h0
      have hpow : (0 : ℝ) < 2 ^ n := by positivity
      have hSlt : √x < 2 ^ n := by
        have : √x * 256 ≤ √x * √x := mul_le_mul_of_nonneg_left hS hS0
        rw [pow_succ] at h1
        nlinarith
      have e2 : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm
      have l3 : x ^ (1 / 3 : ℝ) < 2 ^ n :=
        lt_of_le_of_lt (by
          rw [← e2]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) hSlt
      have l5 : x ^ (1 / 5 : ℝ) < 2 ^ n :=
        lt_of_le_of_lt (by
          rw [← e2]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) hSlt
      have l2 : x ^ (1 / 2 : ℝ) < 2 ^ n := by rw [e2]; exact hSlt
      have hcp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, show (3 : ℝ)⁻¹ = 1 / 3 by norm_num,
        show (5 : ℝ)⁻¹ = 1 / 5 by norm_num] at hcp
      have p2 := psi_rpow_le_of_ih ih hx1 (a := 1 / 2) (b := 1 / 4) (by norm_num) l2
      have p3 := psi_rpow_le_of_ih ih hx1 (a := 1 / 3) (b := 1 / 6) (by norm_num) l3
      have p5 := psi_rpow_le_of_ih ih hx1 (a := 1 / 5) (b := 1 / 10) (by norm_num) l5
      rw [e2] at p2 hcp
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
      have q3 := rpow_le_const_mul_sqrt h (by norm_num) r3
      have q4 := rpow_le_const_mul_sqrt h (by norm_num) r4
      have q5 := rpow_le_const_mul_sqrt h (by norm_num) r5
      have q6 := rpow_le_const_mul_sqrt h (by norm_num) r6
      have q10 := rpow_le_const_mul_sqrt h (by norm_num) r10
      have n3 := Real.rpow_nonneg h0 (1 / 3 : ℝ)
      have n5 := Real.rpow_nonneg h0 (1 / 5 : ℝ)
      have h4 : Real.log (4 : ℝ) ≤ 1.3862943616 := by
        have : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_two_pow]; norm_num
        rw [this]; linarith [Real.log_two_lt_d9]
      have hsum : √x + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ) ≤ 305.52 / 256 * √x := by linarith
      have hmain : Real.log 4 * (√x + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ))
          ≤ 1.3862943616 * (305.52 / 256 * √x) :=
        mul_le_mul h4 hsum (by linarith) (by norm_num)
      have hmain' : Real.log 4 * √x + Real.log 4 * x ^ (1 / 3 : ℝ) + Real.log 4 * x ^ (1 / 5 : ℝ)
          ≤ 1.3862943616 * (305.52 / 256 * √x) := by
        have e : Real.log 4 * √x + Real.log 4 * x ^ (1 / 3 : ℝ) + Real.log 4 * x ^ (1 / 5 : ℝ)
            = Real.log 4 * (√x + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ)) := by ring
        rw [e]; exact hmain
      linarith

/-- **Uniform bound.** `ψ x - θ x ≤ 1.84 √x` for every real `x`. -/
theorem psi_sub_theta_le_small (x : ℝ) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.84 * √x := by
  rcases lt_or_ge x 0 with h | h
  · rw [Chebyshev.psi_eq_zero_of_lt_two (x := x) (by linarith), Real.sqrt_eq_zero_of_nonpos h.le]
    linarith [Chebyshev.theta_nonneg x]
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    exact psi_sub_theta_le_aux n x h hn

/-- `ψ x - θ x ≤ 1.30 √x` on `[2500, 2^16)` and `≤ 1.84 √x` beyond: the form `a √x` with the
small-range constant, for use near the bootstrap point. -/
theorem psi_sub_theta_le_small_of_ge_2500 {x : ℝ} (hx : 2500 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (if x < 65536 then (1.3 : ℝ) else 1.84) * √x := by
  split_ifs with h
  · exact psi_sub_theta_le_of_ge_2500_of_lt_65536 hx h
  · exact psi_sub_theta_le_small x

/-! ## §6.2 corollaries for `noncoprimeSum` -/

/-- §6.2, uniform: `∑_{m<x, (m,n)>1} Λ(m) ≤ log n + 1.84 √x` for every real `x`. -/
theorem noncoprimeSum_le_small {n : ℕ} (hn : 0 < n) (x : ℝ) :
    noncoprimeSum n x ≤ Real.log n + 1.84 * √x := by
  have h1 := noncoprimeSum_le_log_add_psi_sub_theta hn x
  have h2 := psi_sub_theta_le_small x
  linarith

/-- §6.2 on `[0, 2^16)`: constant `1.43`. -/
theorem noncoprimeSum_le_of_lt_65536 {n : ℕ} (hn : 0 < n) {x : ℝ} (hA : 0 ≤ x) (hB : x < 65536) :
    noncoprimeSum n x ≤ Real.log n + 1.43 * √x := by
  have h1 := noncoprimeSum_le_log_add_psi_sub_theta hn x
  have h2 := psi_sub_theta_le_of_lt_65536 hA hB
  linarith

/-- §6.2 on `[420, 2^16)`: constant `1.35`. -/
theorem noncoprimeSum_le_of_ge_420_of_lt_65536 {n : ℕ} (hn : 0 < n) {x : ℝ} (hA : 420 ≤ x)
    (hB : x < 65536) : noncoprimeSum n x ≤ Real.log n + 1.35 * √x := by
  have h1 := noncoprimeSum_le_log_add_psi_sub_theta hn x
  have h2 := psi_sub_theta_le_of_ge_420_of_lt_65536 hA hB
  linarith

/-- §6.2 on `[2000, 2^16)`: constant `1.34`. -/
theorem noncoprimeSum_le_of_ge_2000_of_lt_65536 {n : ℕ} (hn : 0 < n) {x : ℝ} (hA : 2000 ≤ x)
    (hB : x < 65536) : noncoprimeSum n x ≤ Real.log n + 1.34 * √x := by
  have h1 := noncoprimeSum_le_log_add_psi_sub_theta hn x
  have h2 := psi_sub_theta_le_of_ge_2000_of_lt_65536 hA hB
  linarith

/-- §6.2 on `[2500, 2^16)`: constant `1.30`. -/
theorem noncoprimeSum_le_of_ge_2500_of_lt_65536 {n : ℕ} (hn : 0 < n) {x : ℝ} (hA : 2500 ≤ x)
    (hB : x < 65536) : noncoprimeSum n x ≤ Real.log n + 1.3 * √x := by
  have h1 := noncoprimeSum_le_log_add_psi_sub_theta hn x
  have h2 := psi_sub_theta_le_of_ge_2500_of_lt_65536 hA hB
  linarith

end DetPrimality.Bach
