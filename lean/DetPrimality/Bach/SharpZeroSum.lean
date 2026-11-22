import DetPrimality.Bach.Assembly

/-!
# Sharper bounds for the zero sum `T(χ) = ∑_ρ 1/|ρ(ρ+1)|` under GRH

`Assembly.lean` proves `zeroSum χ ≤ log q + 2` from the partial-fraction identity at `s = 2`,
with the crude inputs `|L'/L(2)| ≤ 1` and `Re (γ'/γ)(2) ≤ 0`.  Here we prove

* `norm_logDeriv_LFunction_two_le_sharp` : `‖L'/L(2, χ)‖ ≤ 0.5708` (true value of
  `∑ Λ(n)/n² = -ζ'/ζ(2)` is `0.56996…`);
* `zeroSum_le_sharp2` : `zeroSum χ ≤ log q + 0.036` (identity at `s = 2`);
* `zeroSum_le_sharp32` : `zeroSum χ ≤ (2/3) log q + 1.097` (identity at `s = 3/2`, using
  `1/(|ρ||ρ+1|) ≤ (4/3) Re 1/(3/2 - ρ)` on the critical line).

## Method for `∑ Λ(n) n^{-σ}` (`σ = 2, 3/2`)

No prime needs to be detected.  From `Λ * 1 = log` (Mathlib: `convolution_vonMangoldt_const_one`,
`LSeries_convolution'`) we get the identity of real series
`(∑ Λ(n) n^{-σ}) (∑ n^{-σ}) = ∑ log n · n^{-σ}` (`szs_tsum_mul`), so it suffices to bound
`∑ log n · n^{-σ}` from above and `∑ n^{-σ}` from below.  Both are sums of monotone functions:
the first `100` terms are bounded by exact rational arithmetic (`decide +kernel`; `log n` through
`n^1024 < 2^(log2(n^1024)+1)`, `√n` through a self-certifying integer Newton iteration), and the
tails by telescoping against the antiderivatives.

## Gamma factors

`Re (γ'/γ)(s) = (-log π + Re ψ((s + a)/2))/2`, with `ψ(1) = -γ`, `ψ(3/2) = 2 - 2 log 2 - γ`
(Mathlib), `ψ(3/4) ≤ ψ(1)` and `ψ(5/4) ≤ ψ(3/2) + ∑_{k<1024} (1/(k+3/2) - 1/(k+5/4))`
(partial-fraction series of `ExplicitDigamma.lean`; the terms are negative).  Numerical inputs:
`γ > 0.5767` (from `H_1023 - 10 log 2 < γ`) and `log π > 1.14396` (from `2^845 ≤ 3.1415^512`).
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## L-series glue -/

/-- An L-series term of a real sequence at a real point is real. -/
theorem szs_term_ofReal (f : ℕ → ℝ) {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) (σ : ℂ) n = ((f n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hσ]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp

theorem szs_LSeries_ofReal (f : ℕ → ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    LSeries (fun n => (f n : ℂ)) (σ : ℂ) = ((∑' n : ℕ, f n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr fun n => szs_term_ofReal f hσ n

/-- `(∑ Λ(n) n^{-σ}) (∑ n^{-σ}) = ∑ log n · n^{-σ}` for real `σ > 1`. -/
theorem szs_tsum_mul {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, Λ n / (n : ℝ) ^ σ) * (∑' n : ℕ, 1 / (n : ℝ) ^ σ)
      = ∑' n : ℕ, Real.log n / (n : ℝ) ^ σ := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have hσ0 : σ ≠ 0 := by linarith
  have h1 := LSeries_convolution' (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (LSeriesSummable_one_iff.mpr hs)
  rw [ArithmeticFunction.convolution_vonMangoldt_const_one] at h1
  have e1 : (fun n : ℕ => Complex.log (n : ℂ)) = fun n : ℕ => ((Real.log n : ℝ) : ℂ) := by
    funext n
    exact (Complex.natCast_log).symm
  have e2 : (1 : ℕ → ℂ) = fun n : ℕ => (((fun _ : ℕ => (1 : ℝ)) n : ℝ) : ℂ) := by
    funext n
    simp
  rw [e1, e2, szs_LSeries_ofReal _ hσ0, szs_LSeries_ofReal _ hσ0,
    szs_LSeries_ofReal (fun _ => (1 : ℝ)) hσ0] at h1
  exact_mod_cast h1.symm

/-- `‖L'/L(σ, χ)‖ ≤ ∑ Λ(n) n^{-σ}` for real `σ > 1`. -/
theorem szs_norm_logDeriv_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) :
    ‖deriv (LFunction χ) σ / LFunction χ σ‖ ≤ ∑' n : ℕ, Λ n / (n : ℝ) ^ σ := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have hσ0 : σ ≠ 0 := by linarith
  have hsum : Summable fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) σ n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  have h1 := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs, neg_div] at h1
  rw [← norm_neg]
  refine (HasSum.norm_le_of_bounded h1 hsum.hasSum fun n => ?_).trans (le_of_eq ?_)
  · refine LSeries.norm_term_le (σ : ℂ) (g := fun n => (Λ n : ℂ)) ?_
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  · refine tsum_congr fun n => ?_
    rw [szs_term_ofReal _ hσ0, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))]

/-! ## Telescoping -/

theorem szs_sum_range_le_of_tele (a G : ℕ → ℝ) (K : ℕ) (ha : ∀ n, 0 ≤ a n)
    (hG : ∀ n, K ≤ n → 0 ≤ G n) (h : ∀ n, K ≤ n → a (n + 1) ≤ G n - G (n + 1)) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n ≤ ∑ n ∈ Finset.range (K + 1), a n + G K := by
  have key : ∀ k, ∑ n ∈ Finset.range (K + k + 1), a n + G (K + k)
      ≤ ∑ n ∈ Finset.range (K + 1), a n + G K := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : K + (k + 1) = K + k + 1 := rfl
      rw [e, Finset.sum_range_succ]
      linarith [h (K + k) (by omega)]
  rcases le_or_gt N (K + 1) with hN | hN
  · have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hN)
      (fun i _ _ => ha i)
    linarith [hG K le_rfl]
  · obtain ⟨k, rfl⟩ : ∃ k, N = K + k + 1 := ⟨N - (K + 1), by omega⟩
    linarith [key k, hG (K + k) (by omega)]

theorem szs_sum_range_ge_of_tele (a H : ℕ → ℝ) (K : ℕ)
    (h : ∀ n, K ≤ n → H n - H (n + 1) ≤ a n) (k : ℕ) :
    ∑ n ∈ Finset.range K, a n + H K - H (K + k) ≤ ∑ n ∈ Finset.range (K + k), a n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : K + (k + 1) = K + k + 1 := rfl
    rw [e, Finset.sum_range_succ]
    linarith [h (K + k) (by omega)]

/-! ## Rational bounds for `log n` and `n^{-3/2}` -/

/-- `log n ≤ szs_logq n · log 2`, from `n^1024 < 2^(log2(n^1024)+1)`. -/
def szs_logq (n : ℕ) : ℚ := ((Nat.log2 (n ^ 1024) + 1 : ℕ) : ℚ) / 1024

theorem szs_logq_nonneg (n : ℕ) : 0 ≤ szs_logq n := by
  unfold szs_logq; positivity

theorem szs_log_le (n : ℕ) : Real.log n ≤ (szs_logq n : ℝ) * Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Rat.cast_nonneg.mpr (szs_logq_nonneg 0)) h2.le
  · have h1 : n ^ 1024 < 2 ^ (Nat.log2 (n ^ 1024) + 1) := Nat.lt_log2_self
    have h3 : ((n : ℝ)) ^ 1024 ≤ (2 : ℝ) ^ (Nat.log2 (n ^ 1024) + 1) := by exact_mod_cast h1.le
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow, Real.log_pow] at h4
    rw [szs_logq]
    push_cast at h4 ⊢
    linarith

/-- Integer Newton iteration for the square root (only a candidate; certified in `szs_lo`). -/
def szs_newton (m : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | f + 1, x => szs_newton m f ((x + m / x) / 2)

def szs_cand (m : ℕ) : ℕ := szs_newton m 12 (2 ^ (Nat.log2 m / 2 + 1))

/-- A lower integer square root (self-certifying). -/
def szs_lo (m : ℕ) : ℕ :=
  if szs_cand m * szs_cand m ≤ m then szs_cand m
  else if (szs_cand m - 1) * (szs_cand m - 1) ≤ m then szs_cand m - 1 else 0

/-- An upper integer square root (self-certifying, positive). -/
def szs_hi (m : ℕ) : ℕ :=
  if m ≤ (szs_lo m + 1) * (szs_lo m + 1) then szs_lo m + 1 else m + 1

theorem szs_lo_sq_le (m : ℕ) : szs_lo m * szs_lo m ≤ m := by
  unfold szs_lo
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · simp

theorem szs_le_hi_sq (m : ℕ) : m ≤ szs_hi m * szs_hi m := by
  unfold szs_hi
  split_ifs with h
  · exact h
  · nlinarith

theorem szs_hi_pos (m : ℕ) : 0 < szs_hi m := by
  unfold szs_hi
  split_ifs <;> omega

/-- Rational upper bound for `n^{-3/2}`. -/
def szs_ru (n : ℕ) : ℚ :=
  if szs_lo (n * 4 ^ 20) = 0 then 1 else 2 ^ 20 / ((n : ℚ) * szs_lo (n * 4 ^ 20))

/-- Rational lower bound for `n^{-3/2}`. -/
def szs_rl (n : ℕ) : ℚ := 2 ^ 20 / ((n : ℚ) * szs_hi (n * 4 ^ 20))

theorem szs_rpow_three_halves {u : ℝ} (hu : 0 < u) : u ^ (3 / 2 : ℝ) = u * √u := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hu, Real.rpow_one,
    Real.sqrt_eq_rpow]

theorem szs_sqrt_scale (n : ℕ) : √((n : ℝ) * 4 ^ 20) = √(n : ℝ) * 2 ^ 20 := by
  rw [Real.sqrt_mul (Nat.cast_nonneg n), show (4 : ℝ) ^ 20 = (2 ^ 20) ^ 2 by norm_num,
    Real.sqrt_sq (by positivity)]

theorem szs_ru_nonneg (n : ℕ) : 0 ≤ szs_ru n := by
  unfold szs_ru; split_ifs <;> positivity

theorem szs_div_aux1 {n r s : ℝ} (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (h : s ≤ r * 2 ^ 20) :
    1 / (n * r) ≤ 2 ^ 20 / (n * s) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left h hn.le
  linarith

theorem szs_div_aux2 {n r s : ℝ} (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (h : r * 2 ^ 20 ≤ s) :
    2 ^ 20 / (n * s) ≤ 1 / (n * r) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left h hn.le
  linarith

theorem szs_inv_rpow_le (n : ℕ) : 1 / (n : ℝ) ^ (3 / 2 : ℝ) ≤ (szs_ru n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by norm_num), div_zero]
    exact Rat.cast_nonneg.mpr (szs_ru_nonneg 0)
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
    rw [szs_rpow_three_halves hn']
    by_cases h0 : szs_lo (n * 4 ^ 20) = 0
    · rw [szs_ru, if_pos h0, Rat.cast_one, div_le_one (by positivity)]
      have : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
      nlinarith
    · have hpos : (0 : ℝ) < (szs_lo (n * 4 ^ 20) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero h0
      have hle : ((szs_lo (n * 4 ^ 20) : ℝ)) ^ 2 ≤ (n : ℝ) * 4 ^ 20 := by
        have := szs_lo_sq_le (n * 4 ^ 20)
        rw [sq]
        exact_mod_cast this
      have hs : (szs_lo (n * 4 ^ 20) : ℝ) ≤ √(n : ℝ) * 2 ^ 20 := by
        rw [← szs_sqrt_scale, ← Real.sqrt_sq hpos.le]
        exact Real.sqrt_le_sqrt hle
      rw [szs_ru, if_neg h0]
      push_cast
      exact szs_div_aux1 hn' hsq hpos hs

theorem szs_le_inv_rpow (n : ℕ) : (szs_rl n : ℝ) ≤ 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [szs_rl]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
    have hpos : (0 : ℝ) < (szs_hi (n * 4 ^ 20) : ℝ) := by
      exact_mod_cast szs_hi_pos _
    have hle : (n : ℝ) * 4 ^ 20 ≤ ((szs_hi (n * 4 ^ 20) : ℝ)) ^ 2 := by
      have := szs_le_hi_sq (n * 4 ^ 20)
      rw [sq]
      exact_mod_cast this
    have hs : √(n : ℝ) * 2 ^ 20 ≤ (szs_hi (n * 4 ^ 20) : ℝ) := by
      rw [← szs_sqrt_scale, ← Real.sqrt_sq hpos.le]
      exact Real.sqrt_le_sqrt hle
    rw [szs_rpow_three_halves hn', szs_rl]
    push_cast
    exact szs_div_aux2 hn' hsq hpos hs

/-! ## Certificates (exact rational arithmetic) -/

theorem szs_cert_logq_100 : szs_logq 100 ≤ 6804 / 1024 := by decide +kernel

theorem szs_cert_Q2 :
    ∑ n ∈ Finset.range 101, szs_logq n / (n : ℚ) ^ 2 ≤ 127358 / 100000 := by decide +kernel

theorem szs_cert_Z2 :
    (163488 / 100000 : ℚ) ≤ ∑ n ∈ Finset.range 100, 1 / (n : ℚ) ^ 2 := by decide +kernel

theorem szs_cert_Q32 :
    ∑ n ∈ Finset.range 101, szs_logq n * szs_ru n ≤ 377355 / 100000 := by decide +kernel

theorem szs_cert_Z32 :
    (241187 / 100000 : ℚ) ≤ ∑ n ∈ Finset.range 100, szs_rl n := by decide +kernel

theorem szs_cert_harmonic : (750819 / 100000 : ℚ) ≤ harmonic 1023 := by decide +kernel

theorem szs_cert_pi : 2 ^ 845 * 10000 ^ 512 ≤ 31415 ^ 512 := by decide +kernel

theorem szs_cert_digamma :
    ∑ k ∈ Finset.range 1024, (1 / ((k : ℚ) + 3 / 2) - 1 / ((k : ℚ) + 5 / 4))
      ≤ -26369 / 100000 := by decide +kernel

theorem szs_log_100 : Real.log ((100 : ℕ) : ℝ) ≤ 6804 / 1024 * Real.log 2 := by
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h100 := szs_log_le 100
  have hc := (Rat.cast_le (K := ℝ)).mpr szs_cert_logq_100
  rw [show ((6804 / 1024 : ℚ) : ℝ) = 6804 / 1024 by norm_num] at hc
  exact h100.trans (mul_le_mul_of_nonneg_right hc hl2p.le)

/-! ## `σ = 2` -/

theorem szs_D2_le : ∑' n : ℕ, Real.log n / (n : ℝ) ^ (2 : ℝ) ≤ 0.93884 := by
  have hl2 := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : ∀ n : ℕ, 0 ≤ Real.log n / (n : ℝ) ^ (2 : ℝ) := fun n =>
    div_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine Real.tsum_le_of_sum_range_le hnn fun N => ?_
  have htele := szs_sum_range_le_of_tele (fun n : ℕ => Real.log n / (n : ℝ) ^ (2 : ℝ))
    (fun n : ℕ => Numerics.g n) 100 hnn
    (fun n hn => Numerics.g_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
    (fun n hn => by
      have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
      have := Numerics.log_div_sq_le_g_sub (x := (n : ℝ) + 1) (by linarith)
      rw [add_sub_cancel_right] at this
      simp only [Nat.cast_add, Nat.cast_one, Real.rpow_two]
      exact this) N
  have hfin : ∑ n ∈ Finset.range 101, Real.log n / (n : ℝ) ^ (2 : ℝ)
      ≤ ((∑ n ∈ Finset.range 101, szs_logq n / (n : ℚ) ^ 2 : ℚ) : ℝ) * Real.log 2 := by
    rw [Rat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [Real.rpow_two]
    push_cast
    rw [div_mul_eq_mul_div]
    have := szs_log_le n
    gcongr
  have hQ := (Rat.cast_le (K := ℝ)).mpr szs_cert_Q2
  rw [show ((127358 / 100000 : ℚ) : ℝ) = 127358 / 100000 by norm_num] at hQ
  have hg : Numerics.g ((100 : ℕ) : ℝ) ≤ (6804 / 1024 * Real.log 2 + 1) / 100 := by
    unfold Numerics.g
    have := szs_log_100
    rw [show (((100 : ℕ) : ℝ)) = 100 by norm_num] at this ⊢
    linarith
  have h1 := mul_le_mul_of_nonneg_right hQ hl2p.le
  have e : (100 + 1 : ℕ) = 101 := rfl
  beta_reduce at htele
  rw [e] at htele
  linarith

theorem szs_Z2_ge : (1.64487 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((100 + k : ℕ) : ℝ) = 10 ^ 8 := ⟨10 ^ 8 - 100, by norm_num⟩
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have htele := szs_sum_range_ge_of_tele (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ))
    (fun n : ℕ => 1 / (n : ℝ)) 100 (fun n hn => by
      have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
      have hx : (0 : ℝ) < n := by linarith
      simp only [Nat.cast_add, Nat.cast_one, Real.rpow_two]
      have e : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [e]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)) k
  have hle := hsum.sum_le_tsum (Finset.range (100 + k)) (fun i _ => by positivity)
  have hfin : ∑ n ∈ Finset.range 100, 1 / (n : ℝ) ^ (2 : ℝ)
      = ((∑ n ∈ Finset.range 100, 1 / (n : ℚ) ^ 2 : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_congr rfl fun n _ => by rw [Real.rpow_two]
  have hZ := (Rat.cast_le (K := ℝ)).mpr szs_cert_Z2
  rw [show ((163488 / 100000 : ℚ) : ℝ) = 163488 / 100000 by norm_num] at hZ
  have hH1 : (1 : ℝ) / ((100 : ℕ) : ℝ) = 1 / 100 := by norm_num
  have hH2 : (1 : ℝ) / ((100 + k : ℕ) : ℝ) = 1 / 10 ^ 8 := by rw [hk]
  beta_reduce at htele
  rw [hH1, hH2, hfin] at htele
  linarith

/-- `∑ Λ(n)/n² ≤ 0.5708` (true value `0.56996…`). -/
theorem szs_S2_le : ∑' n : ℕ, Λ n / (n : ℝ) ^ (2 : ℝ) ≤ 0.5708 := by
  have hmul := szs_tsum_mul (σ := 2) (by norm_num)
  have hD := szs_D2_le
  have hZ := szs_Z2_ge
  have h0 : 0 ≤ ∑' n : ℕ, Λ n / (n : ℝ) ^ (2 : ℝ) :=
    tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [← hmul] at hD
  have := mul_le_mul_of_nonneg_left hZ h0
  linarith

/-- **Sharp `|L'/L(2, χ)|`**: `‖L'/L(2, χ)‖ ≤ ∑ Λ(n)/n² ≤ 0.5708` for every Dirichlet character. -/
theorem norm_logDeriv_LFunction_two_le_sharp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖deriv (LFunction χ) 2 / LFunction χ 2‖ ≤ 0.5708 := by
  have h := szs_norm_logDeriv_le χ (σ := 2) (by norm_num)
  rw [Complex.ofReal_ofNat] at h
  exact h.trans szs_S2_le

/-! ## `σ = 3/2` -/

/-- Antiderivative of `-log t · t^{-3/2}`. -/
noncomputable def szs_G (t : ℝ) : ℝ := (2 * Real.log t + 4) * t ^ (-(1 / 2) : ℝ)

theorem szs_hasDerivAt_G {t : ℝ} (ht : 0 < t) :
    HasDerivAt szs_G (-(Real.log t / t ^ (3 / 2 : ℝ))) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * Real.log t + 4) (2 * t⁻¹) t :=
    ((Real.hasDerivAt_log ht.ne').const_mul 2).add_const 4
  have h2 : HasDerivAt (fun t : ℝ => t ^ (-(1 / 2) : ℝ))
      (-(1 / 2) * t ^ (-(1 / 2) - 1 : ℝ)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h : HasDerivAt szs_G (2 * t⁻¹ * t ^ (-(1 / 2) : ℝ)
      + (2 * Real.log t + 4) * (-(1 / 2) * t ^ (-(1 / 2) - 1 : ℝ))) t := h1.mul h2
  have e1 : t ^ (-(1 / 2) - 1 : ℝ) = t ^ (-(3 / 2) : ℝ) := by
    congr 1; norm_num
  have e2 : t ^ (-(1 / 2) : ℝ) = t * t ^ (-(3 / 2) : ℝ) := by
    rw [show (-(1 / 2) : ℝ) = 1 + -(3 / 2) by norm_num, Real.rpow_add ht, Real.rpow_one]
  have e3 : Real.log t / t ^ (3 / 2 : ℝ) = Real.log t * t ^ (-(3 / 2) : ℝ) := by
    rw [Real.rpow_neg ht.le, div_eq_mul_inv]
  convert h using 1
  rw [e3, e1, e2]
  have ht' := ht.ne'
  generalize t ^ (-(3 / 2) : ℝ) = u
  field_simp
  ring

theorem szs_tele32 {x : ℝ} (hx : 2 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ (3 / 2 : ℝ) ≤ szs_G x - szs_G (x + 1) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.log (x + 1) / (x + 1) ^ (3 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← hc]
  have hexp : Real.exp ((3 / 2 : ℝ)⁻¹) ≤ 2 := by
    have h2 : ((3 / 2 : ℝ)⁻¹) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    calc Real.exp ((3 / 2 : ℝ)⁻¹) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h2
      _ = 2 := Real.exp_log (by norm_num)
  have hanti := Real.log_div_self_rpow_antitoneOn (a := 3 / 2) (by norm_num)
  have hder : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => szs_G t + c * t)
      (-(Real.log t / t ^ (3 / 2 : ℝ)) + c * 1) t :=
    fun t ht => (szs_hasDerivAt_G ht).add ((hasDerivAt_id t).const_mul c)
  have hmono : AntitoneOn (fun t => szs_G t + c * t) (Set.Icc x (x + 1)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (fun t ht => ?_) (fun t ht => ?_)
      (fun t ht => ?_)
    · exact (hder t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · rw [interior_Icc] at ht
      exact (hder t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hder t (by linarith [ht.1])).deriv]
      have := hanti (a := t) (b := x + 1)
        (Set.mem_Ici.mpr (by linarith [ht.1])) (Set.mem_Ici.mpr (by linarith)) ht.2.le
      simp only at this
      rw [hc]
      linarith
  have := hmono (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
    (by linarith : x ≤ x + 1)
  simp only at this
  linarith

theorem szs_D32_le : ∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 3.93676 := by
  have hl2 := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : ∀ n : ℕ, 0 ≤ Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) := fun n =>
    div_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine Real.tsum_le_of_sum_range_le hnn fun N => ?_
  have htele := szs_sum_range_le_of_tele (fun n : ℕ => Real.log n / (n : ℝ) ^ (3 / 2 : ℝ))
    (fun n : ℕ => szs_G n) 100 hnn
    (fun n hn => by
      show 0 ≤ (2 * Real.log (n : ℝ) + 4) * (n : ℝ) ^ (-(1 / 2) : ℝ)
      exact mul_nonneg (by linarith [Real.log_natCast_nonneg n])
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n hn => by
      have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
      have := szs_tele32 (x := (n : ℝ)) (by linarith)
      simp only [Nat.cast_add, Nat.cast_one]
      exact this) N
  have hfin : ∑ n ∈ Finset.range 101, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ)
      ≤ ((∑ n ∈ Finset.range 101, szs_logq n * szs_ru n : ℚ) : ℝ) * Real.log 2 := by
    rw [Rat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    push_cast
    have h1 := szs_log_le n
    have h2 := szs_inv_rpow_le n
    have h3 : (0 : ℝ) ≤ szs_logq n := Rat.cast_nonneg.mpr (szs_logq_nonneg n)
    calc Real.log n / (n : ℝ) ^ (3 / 2 : ℝ)
        = Real.log n * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by ring
      _ ≤ ((szs_logq n : ℝ) * Real.log 2) * (szs_ru n : ℝ) :=
          mul_le_mul h1 h2 (by positivity) (mul_nonneg h3 hl2p.le)
      _ = _ := by ring
  have hQ := (Rat.cast_le (K := ℝ)).mpr szs_cert_Q32
  rw [show ((377355 / 100000 : ℚ) : ℝ) = 377355 / 100000 by norm_num] at hQ
  have hG100 : szs_G ((100 : ℕ) : ℝ) ≤ (2 * (6804 / 1024 * Real.log 2) + 4) / 10 := by
    have := szs_log_100
    unfold szs_G
    rw [show (((100 : ℕ) : ℝ)) = 100 by norm_num] at this ⊢
    have hr : (100 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 10 := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, show (100 : ℝ) = 10 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
      norm_num
    rw [hr]
    linarith
  have h1 := mul_le_mul_of_nonneg_right hQ hl2p.le
  have e : (100 + 1 : ℕ) = 101 := rfl
  beta_reduce at htele
  rw [e] at htele
  linarith

theorem szs_tele_Z32 (n : ℕ) (hn : 0 < n) :
    2 / √(n : ℝ) - 2 / √((n : ℝ) + 1) ≤ 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [szs_rpow_three_halves hn']
  have ha0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
  have hb0 : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
  have ha2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
  have hb2' : √((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hab : √(n : ℝ) ≤ √((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  generalize √((n : ℝ) + 1) = b at *
  generalize √(n : ℝ) = a at *
  have hb2 : b ^ 2 = a ^ 2 + 1 := by rw [ha2, hb2']
  rw [← ha2]
  have key : (2 * a ^ 3 + b - 2 * a ^ 2 * b) * (a + b) = a * b + b ^ 2 - 2 * a ^ 2 := by
    linear_combination (-2 * a ^ 2) * hb2
  have hX : 0 ≤ 2 * a ^ 3 + b - 2 * a ^ 2 * b := by
    have : 0 ≤ (2 * a ^ 3 + b - 2 * a ^ 2 * b) * (a + b) := by
      rw [key]
      nlinarith [mul_le_mul_of_nonneg_left hab ha0.le, mul_le_mul hab hab ha0.le hb0.le]
    exact nonneg_of_mul_nonneg_left this (by linarith)
  have e : 1 / (a ^ 2 * a) - (2 / a - 2 / b)
      = (2 * a ^ 3 + b - 2 * a ^ 2 * b) / (a ^ 3 * b) := by
    field_simp
    ring
  have : 0 ≤ (2 * a ^ 3 + b - 2 * a ^ 2 * b) / (a ^ 3 * b) := div_nonneg hX (by positivity)
  linarith

theorem szs_Z32_ge : (2.61167 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((100 + k : ℕ) : ℝ) = 10 ^ 8 := ⟨10 ^ 8 - 100, by norm_num⟩
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have htele := szs_sum_range_ge_of_tele (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ))
    (fun n : ℕ => 2 / √(n : ℝ)) 100 (fun n hn => by
      have := szs_tele_Z32 n (by omega)
      simp only [Nat.cast_add, Nat.cast_one]
      exact this) k
  have hle := hsum.sum_le_tsum (Finset.range (100 + k)) (fun i _ => by positivity)
  have hfin : ((∑ n ∈ Finset.range 100, szs_rl n : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.range 100, 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum fun n _ => szs_le_inv_rpow n
  have hZ := (Rat.cast_le (K := ℝ)).mpr szs_cert_Z32
  rw [show ((241187 / 100000 : ℚ) : ℝ) = 241187 / 100000 by norm_num] at hZ
  have hH1 : (2 : ℝ) / √((100 : ℕ) : ℝ) = 2 / 10 := by
    rw [show (((100 : ℕ) : ℝ)) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hH2 : (2 : ℝ) / √((100 + k : ℕ) : ℝ) = 2 / 10 ^ 4 := by
    rw [hk, show ((10 : ℝ) ^ 8) = (10 ^ 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  beta_reduce at htele
  rw [hH1, hH2] at htele
  linarith

/-- `∑ Λ(n) n^{-3/2} ≤ 1.5075` (true value `1.50523…`). -/
theorem szs_S32_le : ∑' n : ℕ, Λ n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 1.5075 := by
  have hmul := szs_tsum_mul (σ := 3 / 2) (by norm_num)
  have hD := szs_D32_le
  have hZ := szs_Z32_ge
  have h0 : 0 ≤ ∑' n : ℕ, Λ n / (n : ℝ) ^ (3 / 2 : ℝ) :=
    tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [← hmul] at hD
  have := mul_le_mul_of_nonneg_left hZ h0
  linarith

/-- `‖L'/L(3/2, χ)‖ ≤ ∑ Λ(n) n^{-3/2} ≤ 1.5075` for every Dirichlet character. -/
theorem norm_logDeriv_LFunction_three_halves_le_sharp {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)‖ ≤ 1.5075 := by
  have h := szs_norm_logDeriv_le χ (σ := 3 / 2) (by norm_num)
  rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by norm_num] at h
  exact h.trans szs_S32_le

/-! ## Numerical constants `γ`, `log π`, digamma values -/

theorem szs_gamma_gt : (0.5767 : ℝ) < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 1023
  unfold Real.eulerMascheroniSeq at h
  have hH := (Rat.cast_le (K := ℝ)).mpr szs_cert_harmonic
  rw [show ((750819 / 100000 : ℚ) : ℝ) = 750819 / 100000 by norm_num] at hH
  have hl : Real.log (((1023 : ℕ) : ℝ) + 1) = 10 * Real.log 2 := by
    rw [show (((1023 : ℕ) : ℝ) + 1) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [hl] at h
  linarith [Real.log_two_lt_d9]

theorem szs_log_pi_gt : (1.14396 : ℝ) < Real.log Real.pi := by
  have h1 : (2 : ℝ) ^ 845 ≤ Real.pi ^ 512 := by
    have h2 : (3.1415 : ℝ) ^ 512 ≤ Real.pi ^ 512 :=
      pow_le_pow_left₀ (by norm_num) Real.pi_gt_d4.le 512
    have h3 : (2 : ℝ) ^ 845 ≤ (3.1415 : ℝ) ^ 512 := by
      rw [show (3.1415 : ℝ) = 31415 / 10000 by norm_num, div_pow, le_div_iff₀ (by positivity)]
      exact_mod_cast szs_cert_pi
    exact h3.trans h2
  have := Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith [Real.log_two_gt_d9]

/-- `Re ψ(x) ≤ Re ψ(x₀) + ∑_{k<N} (1/(k+x₀) - 1/(k+x))` for rational `0 < x ≤ x₀`
(the omitted terms of the partial-fraction series are `≤ 0`). -/
theorem szs_digamma_re_le (x x₀ : ℚ) (hx : 0 < x) (h : x ≤ x₀) (N : ℕ) :
    (digamma (x : ℂ)).re ≤ (digamma (x₀ : ℂ)).re
      + ((∑ k ∈ Finset.range N, (1 / ((k : ℚ) + x₀) - 1 / ((k : ℚ) + x)) : ℚ) : ℝ) := by
  have hx0 : 0 < x₀ := lt_of_lt_of_le hx h
  have hs := hasSum_digamma_sub (z := (x : ℂ)) (z₀ := (x₀ : ℂ)) (by simpa using hx)
    (by simpa using hx0)
  have hre := Complex.hasSum_re hs
  have hterm : ∀ k : ℕ, (1 / ((k : ℂ) + (x₀ : ℂ)) - 1 / ((k : ℂ) + (x : ℂ))).re
      = ((1 / ((k : ℚ) + x₀) - 1 / ((k : ℚ) + x) : ℚ) : ℝ) := by
    intro k
    have e : (1 / ((k : ℂ) + (x₀ : ℂ)) - 1 / ((k : ℂ) + (x : ℂ)))
        = (((1 / ((k : ℚ) + x₀) - 1 / ((k : ℚ) + x) : ℚ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.ofReal_re]
  simp_rw [hterm] at hre
  have hneg : ∀ k ∉ Finset.range N,
      0 ≤ -(((1 / ((k : ℚ) + x₀) - 1 / ((k : ℚ) + x) : ℚ)) : ℝ) := by
    intro k _
    have hq : 1 / ((k : ℚ) + x₀) - 1 / ((k : ℚ) + x) ≤ 0 := by
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have := one_div_le_one_div_of_le (show 0 < (k : ℚ) + x by linarith)
        (show (k : ℚ) + x ≤ k + x₀ by linarith)
      linarith
    have : ((1 / ((k : ℚ) + x₀) - 1 / ((k : ℚ) + x) : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hq
    linarith
  have := sum_le_hasSum (Finset.range N) hneg hre.neg
  rw [Finset.sum_neg_distrib, Complex.sub_re] at this
  rw [Rat.cast_sum]
  linarith

theorem szs_digamma_five_quarters :
    (digamma ((5 / 4 : ℚ) : ℂ)).re ≤ (digamma ((3 / 2 : ℚ) : ℂ)).re - 26369 / 100000 := by
  have h := szs_digamma_re_le (5 / 4) (3 / 2) (by norm_num) (by norm_num) 1024
  have hP := (Rat.cast_le (K := ℝ)).mpr szs_cert_digamma
  generalize (∑ k ∈ Finset.range 1024, (1 / ((k : ℚ) + 3 / 2) - 1 / ((k : ℚ) + 5 / 4))) = P
    at h hP
  rw [show ((-26369 / 100000 : ℚ) : ℝ) = -26369 / 100000 by norm_num] at hP
  linarith

/-! ## Gamma factors -/

/-- `Re (γ'/γ)(2) ≤ -0.5534` (true values: `-0.861` even, `-0.5540` odd). -/
theorem re_logDeriv_gammaFactor_two_le_sharp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (deriv (gammaFactor χ) 2 / gammaFactor χ 2).re ≤ -0.5534 := by
  have hγ := szs_gamma_gt
  have hπ1 := szs_log_pi_gt
  rcases χ.even_or_odd with he | ho
  · have hfun : gammaFactor χ = Gammaℝ := funext fun s => he.gammaFactor_def s
    rw [hfun, logDeriv_Gammaℝ (by norm_num), show (2 : ℂ) / 2 = 1 by norm_num, digamma_one]
    have h : (-(Real.log Real.pi : ℂ) / 2 + -(Real.eulerMascheroniConstant : ℂ) / 2)
        = ((-(Real.log Real.pi) / 2 - Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, Complex.ofReal_re]
    linarith
  · have hfun : gammaFactor χ = fun s => Gammaℝ (s + 1) := funext fun s => ho.gammaFactor_def s
    have hhalf : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -m := fun m h => by
      have h1 := congrArg Complex.re h
      have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      norm_num at h1
      linarith
    have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; norm_num
    have h2 := Real.log_two_gt_d9
    rw [hfun, deriv_comp_add_const, logDeriv_Gammaℝ (by norm_num),
      show ((2 : ℂ) + 1) / 2 = 1 / 2 + 1 by norm_num, digamma_apply_add_one _ hhalf,
      digamma_one_half, hlog]
    have h : (-(Real.log Real.pi : ℂ) / 2
        + (-2 * (Real.log 2 : ℂ) - (Real.eulerMascheroniConstant : ℂ) + (1 / 2 : ℂ)⁻¹) / 2)
        = ((-(Real.log Real.pi) / 2
          + (-2 * Real.log 2 - Real.eulerMascheroniConstant + 2) / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, Complex.ofReal_re]
    linarith

/-- `Re (γ'/γ)(3/2) ≤ -0.6853` (true values: `-1.1153` even, `-0.6861` odd). -/
theorem re_logDeriv_gammaFactor_three_halves_le_sharp {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (deriv (gammaFactor χ) (3 / 2) / gammaFactor χ (3 / 2)).re ≤ -0.6853 := by
  have hγ := szs_gamma_gt
  have hπ1 := szs_log_pi_gt
  have hdiv2 : ∀ z : ℂ, (z / 2).re = z.re / 2 := fun z => by simp
  rcases χ.even_or_odd with he | ho
  · have hfun : gammaFactor χ = Gammaℝ := funext fun s => he.gammaFactor_def s
    rw [hfun, logDeriv_Gammaℝ (by norm_num), show (3 / 2 : ℂ) / 2 = ((3 / 4 : ℚ) : ℂ) by norm_num,
      Complex.add_re, hdiv2, hdiv2, Complex.neg_re, Complex.ofReal_re]
    have h := szs_digamma_re_le (3 / 4) 1 (by norm_num) (by norm_num) 0
    rw [Rat.cast_one, digamma_one] at h
    simp only [Finset.range_zero, Finset.sum_empty, Rat.cast_zero, Complex.neg_re,
      Complex.ofReal_re, add_zero] at h
    linarith
  · have hfun : gammaFactor χ = fun s => Gammaℝ (s + 1) := funext fun s => ho.gammaFactor_def s
    have hhalf : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -m := fun m h => by
      have h1 := congrArg Complex.re h
      have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      norm_num at h1
      linarith
    have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; norm_num
    rw [hfun, deriv_comp_add_const, logDeriv_Gammaℝ (by norm_num),
      show ((3 / 2 : ℂ) + 1) / 2 = ((5 / 4 : ℚ) : ℂ) by norm_num,
      Complex.add_re, hdiv2, hdiv2, Complex.neg_re, Complex.ofReal_re]
    have h := szs_digamma_five_quarters
    have h32 : digamma ((3 / 2 : ℚ) : ℂ)
        = ((-2 * Real.log 2 - Real.eulerMascheroniConstant + 2 : ℝ) : ℂ) := by
      rw [show ((3 / 2 : ℚ) : ℂ) = 1 / 2 + 1 by norm_num, digamma_apply_add_one _ hhalf,
        digamma_one_half, hlog]
      norm_num
    rw [h32, Complex.ofReal_re] at h
    linarith [Real.log_two_gt_d9]

/-! ## The zero sum -/

/-- (tier (a), `s = 2`) Under GRH, `T(χ) = ∑_ρ 1/|ρ(ρ+1)| ≤ log q + 0.036`. -/
theorem zeroSum_le_sharp2 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    zeroSum χ ≤ Real.log q + 0.036 := by
  have hI := bachInputs
  have hsum := hI.summable χ hχ hχ1
  have hre := hI.reLogDeriv χ hχ hχ1 (s := 2) (by norm_num)
  have key : ∀ ρ : ℂ, (zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
      ≤ 2 * ((zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re) := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    · obtain ⟨ha, hab, -, h9, hre'⟩ := zero_facts hGRH χ h0
      have hb : 0 < ‖ρ + 1‖ := lt_of_lt_of_le ha hab
      have hb3 : ‖ρ + 1‖ ≤ 3 * ‖ρ‖ := by
        by_contra hcon
        push Not at hcon
        nlinarith
      have h1 : 1 / (‖ρ‖ * ‖ρ + 1‖) ≤ 3 / ‖ρ + 1‖ ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      rw [hre']
      calc (zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
          = (zeroOrd χ ρ : ℝ) * (1 / (‖ρ‖ * ‖ρ + 1‖)) := by ring
        _ ≤ (zeroOrd χ ρ : ℝ) * (3 / ‖ρ + 1‖ ^ 2) := by gcongr
        _ = 2 * ((zeroOrd χ ρ : ℝ) * ((3 / 2) / ‖ρ + 1‖ ^ 2)) := by ring
  have hsummR : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) (hsum.mul_left (3 / 2))
    · by_cases h0 : zeroOrd χ ρ = 0
      · simp [h0]
      · obtain ⟨-, -, -, -, hre'⟩ := zero_facts hGRH χ h0
        rw [hre']; positivity
    · by_cases h0 : zeroOrd χ ρ = 0
      · simp [h0]
      · obtain ⟨ha, hab, -, -, hre'⟩ := zero_facts hGRH χ h0
        rw [hre']
        have : (3 / 2 : ℝ) / ‖ρ + 1‖ ^ 2 ≤ (3 / 2) / ‖ρ‖ ^ 2 := by gcongr
        calc (zeroOrd χ ρ : ℝ) * ((3 / 2) / ‖ρ + 1‖ ^ 2)
            ≤ (zeroOrd χ ρ : ℝ) * ((3 / 2) / ‖ρ‖ ^ 2) := by gcongr
          _ = 3 / 2 * ((zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) := by ring
  have hL := norm_logDeriv_LFunction_two_le_sharp χ
  have hG := re_logDeriv_gammaFactor_two_le_sharp χ
  have hreL := Complex.re_le_norm (deriv (LFunction χ) 2 / LFunction χ 2)
  calc zeroSum χ ≤ ∑' ρ : ℂ, 2 * ((zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re) :=
        (summable_zeroSum_of_inputs hI hGRH χ hχ hχ1).tsum_le_tsum key (hsummR.mul_left 2)
    _ = 2 * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re := tsum_mul_left
    _ = 2 * ((deriv (LFunction χ) 2 / LFunction χ 2
          + deriv (gammaFactor χ) 2 / gammaFactor χ 2).re + Real.log q / 2) := by
        rw [hre]; ring
    _ ≤ Real.log q + 0.036 := by rw [Complex.add_re]; linarith

/-- Geometry at `s = 3/2` of a zero on the critical line: `Re 1/(3/2 - ρ) = 1/(1 + γ²)` and
`1/(|ρ||ρ+1|) ≤ (4/3) · 1/(1 + γ²)` (equality at `γ = 0`). -/
theorem szs_zero_facts32 (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) :
    (1 / (3 / 2 - ρ)).re = 1 / (1 + ρ.im ^ 2) ∧ ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 ∧
      1 / (‖ρ‖ * ‖ρ + 1‖) ≤ 4 / 3 * (1 / (1 + ρ.im ^ 2)) := by
  have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h
  obtain ⟨ha, hab, -, -, -⟩ := zero_facts hGRH χ h
  have hb : 0 < ‖ρ + 1‖ := lt_of_lt_of_le ha hab
  have ha2 : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hρ]; ring
  have hb2 : ‖ρ + 1‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hρ]; ring
  have e32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by norm_num
  have hre1 : ((3 / 2 : ℂ) - ρ).re = 1 := by
    rw [e32, Complex.sub_re, Complex.ofReal_re, hρ]; norm_num
  have him1 : ((3 / 2 : ℂ) - ρ).im = -ρ.im := by
    rw [e32, Complex.sub_im, Complex.ofReal_im]; ring
  have hpos : 0 < 1 + ρ.im ^ 2 := by positivity
  refine ⟨?_, ha2, ?_⟩
  · rw [one_div, Complex.inv_re, Complex.normSq_apply, hre1, him1]
    congr 1; ring
  · have h43 : 3 * (1 + ρ.im ^ 2) ≤ 4 * (‖ρ‖ * ‖ρ + 1‖) := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
      have : (4 * (‖ρ‖ * ‖ρ + 1‖)) ^ 2 = 16 * ‖ρ‖ ^ 2 * ‖ρ + 1‖ ^ 2 := by ring
      rw [this, ha2, hb2]
      nlinarith [sq_nonneg ρ.im, sq_nonneg (ρ.im ^ 2)]
    rw [div_le_iff₀ (by positivity)]
    have e : 4 / 3 * (1 / (1 + ρ.im ^ 2)) * (‖ρ‖ * ‖ρ + 1‖)
        = (4 * (‖ρ‖ * ‖ρ + 1‖)) / (3 * (1 + ρ.im ^ 2)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith

/-- (tier (b), `s = 3/2`) Under GRH, `T(χ) = ∑_ρ 1/|ρ(ρ+1)| ≤ (2/3) log q + 1.097`. -/
theorem zeroSum_le_sharp32 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    zeroSum χ ≤ 2 / 3 * Real.log q + 1.097 := by
  have hI := bachInputs
  have hsum := hI.summable χ hχ hχ1
  have hre := hI.reLogDeriv χ hχ hχ1 (s := 3 / 2) (by norm_num)
  have key : ∀ ρ : ℂ, (zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
      ≤ 4 / 3 * ((zeroOrd χ ρ : ℝ) * (1 / (3 / 2 - ρ)).re) := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    · obtain ⟨hre', -, h43⟩ := szs_zero_facts32 hGRH χ h0
      rw [hre']
      calc (zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
          = (zeroOrd χ ρ : ℝ) * (1 / (‖ρ‖ * ‖ρ + 1‖)) := by ring
        _ ≤ (zeroOrd χ ρ : ℝ) * (4 / 3 * (1 / (1 + ρ.im ^ 2))) := by gcongr
        _ = _ := by ring
  have hsummR : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * (1 / (3 / 2 - ρ)).re := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hsum
    · by_cases h0 : zeroOrd χ ρ = 0
      · simp [h0]
      · obtain ⟨hre', -, -⟩ := szs_zero_facts32 hGRH χ h0
        rw [hre']; positivity
    · by_cases h0 : zeroOrd χ ρ = 0
      · simp [h0]
      · obtain ⟨hre', ha2, -⟩ := szs_zero_facts32 hGRH χ h0
        rw [hre', ha2]
        have : 1 / (1 + ρ.im ^ 2) ≤ 1 / (1 / 4 + ρ.im ^ 2) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        calc (zeroOrd χ ρ : ℝ) * (1 / (1 + ρ.im ^ 2))
            ≤ (zeroOrd χ ρ : ℝ) * (1 / (1 / 4 + ρ.im ^ 2)) := by gcongr
          _ = _ := by ring
  have hL := norm_logDeriv_LFunction_three_halves_le_sharp χ
  have hG := re_logDeriv_gammaFactor_three_halves_le_sharp χ
  have hreL := Complex.re_le_norm (deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2))
  calc zeroSum χ ≤ ∑' ρ : ℂ, 4 / 3 * ((zeroOrd χ ρ : ℝ) * (1 / (3 / 2 - ρ)).re) :=
        (summable_zeroSum_of_inputs hI hGRH χ hχ hχ1).tsum_le_tsum key (hsummR.mul_left _)
    _ = 4 / 3 * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (3 / 2 - ρ)).re := tsum_mul_left
    _ = 4 / 3 * ((deriv (LFunction χ) (3 / 2) / LFunction χ (3 / 2)
          + deriv (gammaFactor χ) (3 / 2) / gammaFactor χ (3 / 2)).re + Real.log q / 2) := by
        rw [hre]; ring
    _ ≤ 2 / 3 * Real.log q + 1.097 := by rw [Complex.add_re]; linarith

end DetPrimality.Bach
