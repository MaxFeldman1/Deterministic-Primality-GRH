import DetPrimality.Bach.SharpZeroSum
import DetPrimality.Bach.ConstPsiOneSharp

/-!
# The zero sum under the "no small witness" hypothesis: two-point majorant with gain

For a primitive `χ ≠ 1` mod `q` under GRH, `zeroSum χ = ∑_ρ 1/(|ρ||ρ+1|)`.

## Two-point majorant (`zeroSum_le_twoPoint`)

On the critical line `ρ = 1/2 + iγ`, with `t = γ²`,

  `1/(|ρ||ρ+1|) = 1/√((1/4+t)(9/4+t)) ≤ (8/9) Re 1/(5/4 - ρ) + (2/9) Re 1/(2 - ρ)`,

because after clearing denominators and squaring the difference is
`(9/4+t)(t²/4 + 27t/32) ≥ 0` (equality at `t = 0` and asymptotically at `t = ∞`).  Summing with
the partial-fraction identity `BachInputs.reLogDeriv` at `s = 5/4` and `s = 2`:

  `zeroSum χ ≤ (5/9) log q + (8/9) Re (L'/L + γ'/γ)(5/4) + (2/9) Re (L'/L + γ'/γ)(2)`.

## Hypothesis gain (`zsg_re_logDeriv_le`)

If `χ(m) = 1` for all `1 ≤ m < K` then, for real `σ > 1`,

  `Re L'/L(σ, χ) = -Re ∑ Λ(m)χ(m)m^{-σ} ≤ Z(σ) - 2 ∑_{m<K} Λ(m) m^{-σ}`,  `Z(σ) = ∑ Λ(m) m^{-σ}`.

## Numerics

* `zsg_S54_le` : `Z(5/4) ≤ 3.4686` (true `3.46665…`), by the method of `SharpZeroSum.lean`
  (`Λ * 1 = log`, 256 exact terms, telescoped tails; fourth roots by nested integer Newton);
* `re_logDeriv_gammaFactor_five_quarters_le` : `Re (γ'/γ)(5/4) ≤ -0.7657`
  (true: `-0.76661` odd, `-1.67…` even);
* lower bounds for `∑_{m<K} Λ(m) m^{-σ}` (`σ = 5/4, 2`) from one kernel computation each:
  `Λ(m) = log (lcm(1..m)/lcm(1..m-1))`, so with integer weights `c m ≤ 2^20 m^{-σ}`,
  `2^20 ∑_{m ≤ K} Λ(m) m^{-σ} ≥ log ∏_{m ≤ K} (lcm(1..m)/lcm(1..m-1))^{c m}` (`zsg_acc`).

## Results

`zeroSum_le_gain_of_sums` (general `K`), `zeroSum_le_gain_of_certs`, and the instances
`zeroSum_le_gain_X` for `X ∈ {168, 200, 240, 320, 512, 1024, 2048, 4096}`:
if `χ(m) = 1` for all `1 ≤ m < x` and `x ≥ X` then `zeroSum χ ≤ (5/9) log q - b_X`.
`b_X = 2.0335, 2.1355, 2.2016, 2.3323, 2.5165, 2.7516, 2.9495, 3.1173` (as `x → ∞` the true
value tends to `≈ 4.01`).

No gain is available for the companion constant `D ≥ |L'/L(2, χ)|` of the explicit formula:
under the hypothesis `-Re L'/L(2, χ) ≥ 2 S_K(2) - Z(2) ≈ 0.56`, i.e. the term `-Re(L'/L(2)(1-1/x))`
is genuinely `≈ +0.57`; keep `norm_logDeriv_LFunction_two_le_sharp` (`D = 0.5708`).
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Geometry: the two-point majorant -/

/-- `1/√((1/4+t)(9/4+t)) ≤ (8/9)·(3/4)/(9/16+t) + (2/9)·(3/2)/(9/4+t)` for `t ≥ 0`. -/
theorem zsg_majorant {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = 1 / 4 + t) (hb2 : b ^ 2 = 9 / 4 + t) :
    1 / (a * b) ≤ 8 / 9 * ((3 / 4) / (9 / 16 + t)) + 2 / 9 * ((3 / 2) / (9 / 4 + t)) := by
  have h1 : (9 / 16 + t) * (9 / 4 + t) ≤ a * b * (t + 27 / 16) := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    have e : (a * b * (t + 27 / 16)) ^ 2 = a ^ 2 * b ^ 2 * (t + 27 / 16) ^ 2 := by ring
    rw [e, ha2, hb2]
    nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]
  have e : 8 / 9 * ((3 / 4) / (9 / 16 + t)) + 2 / 9 * ((3 / 2) / (9 / 4 + t))
      = (t + 27 / 16) / ((9 / 16 + t) * (9 / 4 + t)) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Geometry at `s = 5/4` and `s = 2` of a zero on the critical line. -/
theorem zsg_zero_facts (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) :
    (1 / (5 / 4 - ρ)).re = (3 / 4) / (9 / 16 + ρ.im ^ 2) ∧
      (1 / (2 - ρ)).re = (3 / 2) / (9 / 4 + ρ.im ^ 2) ∧ ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 ∧
      1 / (‖ρ‖ * ‖ρ + 1‖)
        ≤ 8 / 9 * ((3 / 4) / (9 / 16 + ρ.im ^ 2)) + 2 / 9 * ((3 / 2) / (9 / 4 + ρ.im ^ 2)) := by
  have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h
  obtain ⟨ha, hab, -, -, hre2⟩ := zero_facts hGRH χ h
  have hb : 0 < ‖ρ + 1‖ := lt_of_lt_of_le ha hab
  have ha2 : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hρ]; ring
  have hb2 : ‖ρ + 1‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hρ]; ring
  have e54 : (5 / 4 : ℂ) = ((5 / 4 : ℝ) : ℂ) := by norm_num
  have hre1 : ((5 / 4 : ℂ) - ρ).re = 3 / 4 := by
    rw [e54, Complex.sub_re, Complex.ofReal_re, hρ]; norm_num
  have him1 : ((5 / 4 : ℂ) - ρ).im = -ρ.im := by
    rw [e54, Complex.sub_im, Complex.ofReal_im]; ring
  refine ⟨?_, ?_, ha2, zsg_majorant (sq_nonneg _) ha hb ha2 hb2⟩
  · rw [one_div, Complex.inv_re, Complex.normSq_apply, hre1, him1]
    congr 1; ring
  · rw [hre2, hb2]

/-- **Two-point bound.** Under GRH, for primitive `χ ≠ 1` mod `q`,
`T(χ) ≤ (5/9) log q + (8/9) Re (L'/L + γ'/γ)(5/4) + (2/9) Re (L'/L + γ'/γ)(2)`. -/
theorem zeroSum_le_twoPoint (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q
      + 8 / 9 * (deriv (LFunction χ) (5 / 4) / LFunction χ (5 / 4)
          + deriv (gammaFactor χ) (5 / 4) / gammaFactor χ (5 / 4)).re
      + 2 / 9 * (deriv (LFunction χ) 2 / LFunction χ 2
          + deriv (gammaFactor χ) 2 / gammaFactor χ 2).re := by
  have hI := bachInputs
  have hsum := hI.summable χ hχ hχ1
  have hre54 := hI.reLogDeriv χ hχ hχ1 (s := 5 / 4) (by norm_num)
  have hre2 := hI.reLogDeriv χ hχ hχ1 (s := 2) (by norm_num)
  have key : ∀ ρ : ℂ, (zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
      ≤ 8 / 9 * ((zeroOrd χ ρ : ℝ) * (1 / (5 / 4 - ρ)).re)
        + 2 / 9 * ((zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re) := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [h0]
    · obtain ⟨h54, h2, -, hmaj⟩ := zsg_zero_facts hGRH χ h0
      rw [h54, h2]
      calc (zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
          = (zeroOrd χ ρ : ℝ) * (1 / (‖ρ‖ * ‖ρ + 1‖)) := by ring
        _ ≤ (zeroOrd χ ρ : ℝ) * (8 / 9 * ((3 / 4) / (9 / 16 + ρ.im ^ 2))
              + 2 / 9 * ((3 / 2) / (9 / 4 + ρ.im ^ 2))) := by gcongr
        _ = _ := by ring
  have hs54 : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * (1 / (5 / 4 - ρ)).re := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) (hsum.mul_left (3 / 4))
    · by_cases h0 : zeroOrd χ ρ = 0
      · simp [h0]
      · obtain ⟨h54, -, -, -⟩ := zsg_zero_facts hGRH χ h0
        rw [h54]; positivity
    · by_cases h0 : zeroOrd χ ρ = 0
      · simp [h0]
      · obtain ⟨h54, -, ha2, -⟩ := zsg_zero_facts hGRH χ h0
        rw [h54, ha2]
        have : (3 / 4 : ℝ) / (9 / 16 + ρ.im ^ 2) ≤ (3 / 4) / (1 / 4 + ρ.im ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        calc (zeroOrd χ ρ : ℝ) * ((3 / 4) / (9 / 16 + ρ.im ^ 2))
            ≤ (zeroOrd χ ρ : ℝ) * ((3 / 4) / (1 / 4 + ρ.im ^ 2)) := by gcongr
          _ = _ := by ring
  have hs2 : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) (hsum.mul_left (3 / 2))
    · by_cases h0 : zeroOrd χ ρ = 0
      · simp [h0]
      · obtain ⟨-, h2, -, -⟩ := zsg_zero_facts hGRH χ h0
        rw [h2]; positivity
    · by_cases h0 : zeroOrd χ ρ = 0
      · simp [h0]
      · obtain ⟨-, h2, ha2, -⟩ := zsg_zero_facts hGRH χ h0
        rw [h2, ha2]
        have : (3 / 2 : ℝ) / (9 / 4 + ρ.im ^ 2) ≤ (3 / 2) / (1 / 4 + ρ.im ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        calc (zeroOrd χ ρ : ℝ) * ((3 / 2) / (9 / 4 + ρ.im ^ 2))
            ≤ (zeroOrd χ ρ : ℝ) * ((3 / 2) / (1 / 4 + ρ.im ^ 2)) := by gcongr
          _ = _ := by ring
  calc zeroSum χ ≤ ∑' ρ : ℂ, (8 / 9 * ((zeroOrd χ ρ : ℝ) * (1 / (5 / 4 - ρ)).re)
          + 2 / 9 * ((zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re)) :=
        (summable_zeroSum_of_inputs hI hGRH χ hχ hχ1).tsum_le_tsum key
          ((hs54.mul_left _).add (hs2.mul_left _))
    _ = 8 / 9 * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (5 / 4 - ρ)).re
          + 2 / 9 * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re := by
        rw [Summable.tsum_add (hs54.mul_left _) (hs2.mul_left _), tsum_mul_left, tsum_mul_left]
    _ = _ := by rw [hre54, hre2]; ring

/-! ## The hypothesis gain -/

theorem zsg_term_re_ge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ)
    {K : ℕ} (hK : ∀ m : ℕ, 1 ≤ m → m < K → χ (m : ZMod q) = 1) (n : ℕ) :
    2 * (if n < K then Λ n / (n : ℝ) ^ σ else 0) - Λ n / (n : ℝ) ^ σ
      ≤ (LSeries.term (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)) σ n).re := by
  have hσ0 : σ ≠ 0 := by linarith
  have hterm : ‖LSeries.term (fun n => (Λ n : ℂ)) σ n‖ = Λ n / (n : ℝ) ^ σ := by
    rw [szs_term_ofReal _ hσ0, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))]
  by_cases hn : n < K
  · rw [if_pos hn]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have ht : LSeries.term (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)) σ n
          = LSeries.term (fun n => (Λ n : ℂ)) σ n := by
        rw [LSeries.term_of_ne_zero hn0.ne', LSeries.term_of_ne_zero hn0.ne', hK n hn0 hn, one_mul]
      rw [ht, szs_term_ofReal _ hσ0, Complex.ofReal_re]
      linarith
  · rw [if_neg hn]
    have hnorm : ‖LSeries.term (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)) σ n‖
        ≤ Λ n / (n : ℝ) ^ σ := by
      rw [← hterm]
      refine LSeries.norm_term_le (σ : ℂ) ?_
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    have := (abs_le.mp (Complex.abs_re_le_norm
      (LSeries.term (fun n : ℕ => χ (n : ZMod q) * (Λ n : ℂ)) σ n))).1
    linarith

/-- **Hypothesis gain.** If `χ(m) = 1` for `1 ≤ m < K` then for real `σ > 1`
`Re L'/L(σ, χ) ≤ ∑ Λ(n) n^{-σ} - 2 ∑_{n<K} Λ(n) n^{-σ}`. -/
theorem zsg_re_logDeriv_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) {K : ℕ} (hK : ∀ m : ℕ, 1 ≤ m → m < K → χ (m : ZMod q) = 1) :
    (deriv (LFunction χ) σ / LFunction χ σ).re
      ≤ (∑' n : ℕ, Λ n / (n : ℝ) ^ σ) - 2 * ∑ n ∈ Finset.range K, Λ n / (n : ℝ) ^ σ := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have hσ0 : σ ≠ 0 := by linarith
  have hsa : Summable fun n : ℕ => Λ n / (n : ℝ) ^ σ := by
    refine ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm).congr fun n => ?_
    rw [szs_term_ofReal _ hσ0, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))]
  have h1 := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs, neg_div] at h1
  have h2 := Complex.hasSum_re h1
  have hind : HasSum (fun n : ℕ => if n < K then Λ n / (n : ℝ) ^ σ else 0)
      (∑ n ∈ Finset.range K, Λ n / (n : ℝ) ^ σ) := by
    have h0 : HasSum (fun n : ℕ => if n < K then Λ n / (n : ℝ) ^ σ else 0)
        (∑ n ∈ Finset.range K, (if n < K then Λ n / (n : ℝ) ^ σ else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => if_neg (by simpa using hn))
    have e : ∑ n ∈ Finset.range K, (if n < K then Λ n / (n : ℝ) ^ σ else 0)
        = ∑ n ∈ Finset.range K, Λ n / (n : ℝ) ^ σ :=
      Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.mp hn)
    rw [e] at h0
    exact h0
  have hb := (hind.mul_left 2).sub hsa.hasSum
  have := hasSum_le (zsg_term_re_ge χ hσ hK) hb h2
  rw [Complex.neg_re] at this
  linarith

/-! ## Fourth roots: rational bounds for `n^{-5/4}` -/

/-- A lower integer fourth root (self-certifying). -/
def zsg_lo4 (m : ℕ) : ℕ := szs_lo (szs_lo m)

/-- An upper integer fourth root (self-certifying, positive). -/
def zsg_hi4 (m : ℕ) : ℕ := szs_hi (szs_hi m)

theorem zsg_lo4_pow_le (m : ℕ) : zsg_lo4 m ^ 4 ≤ m := by
  have h1 := szs_lo_sq_le (szs_lo m)
  have h2 := szs_lo_sq_le m
  unfold zsg_lo4
  calc szs_lo (szs_lo m) ^ 4
      = (szs_lo (szs_lo m) * szs_lo (szs_lo m)) * (szs_lo (szs_lo m) * szs_lo (szs_lo m)) := by
        ring
    _ ≤ szs_lo m * szs_lo m := Nat.mul_le_mul h1 h1
    _ ≤ m := h2

theorem zsg_le_hi4_pow (m : ℕ) : m ≤ zsg_hi4 m ^ 4 := by
  have h1 := szs_le_hi_sq (szs_hi m)
  have h2 := szs_le_hi_sq m
  unfold zsg_hi4
  calc m ≤ szs_hi m * szs_hi m := h2
    _ ≤ (szs_hi (szs_hi m) * szs_hi (szs_hi m)) * (szs_hi (szs_hi m) * szs_hi (szs_hi m)) :=
        Nat.mul_le_mul h1 h1
    _ = szs_hi (szs_hi m) ^ 4 := by ring

theorem zsg_hi4_pos (m : ℕ) : 0 < zsg_hi4 m := szs_hi_pos _

/-- Rational upper bound for `n^{-5/4}`. -/
def zsg_ru (n : ℕ) : ℚ :=
  if zsg_lo4 (n * 16 ^ 20) = 0 then 1 else 2 ^ 20 / ((n : ℚ) * zsg_lo4 (n * 16 ^ 20))

/-- Rational lower bound for `n^{-5/4}`. -/
def zsg_rl (n : ℕ) : ℚ := 2 ^ 20 / ((n : ℚ) * zsg_hi4 (n * 16 ^ 20))

theorem zsg_ru_nonneg (n : ℕ) : 0 ≤ zsg_ru n := by
  unfold zsg_ru; split_ifs <;> positivity

theorem zsg_rpow_five_quarters {u : ℝ} (hu : 0 < u) :
    u ^ (5 / 4 : ℝ) = u * u ^ (1 / 4 : ℝ) := by
  rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hu, Real.rpow_one]

theorem zsg_root_pow {u : ℝ} (hu : 0 ≤ u) : (u ^ (1 / 4 : ℝ)) ^ 4 = u := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
  norm_num

theorem zsg_pow_root {y : ℝ} (hy : 0 ≤ y) : (y ^ 4) ^ (1 / 4 : ℝ) = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

theorem zsg_inv_rpow_le (n : ℕ) : 1 / (n : ℝ) ^ (5 / 4 : ℝ) ≤ (zsg_ru n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by norm_num), div_zero]
    exact Rat.cast_nonneg.mpr (zsg_ru_nonneg 0)
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hr : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hn' _
    have hr4 := zsg_root_pow hn'.le
    have e16 : ((2 : ℝ) ^ 20) ^ 4 = 16 ^ 20 := by norm_num
    rw [zsg_rpow_five_quarters hn']
    by_cases h0 : zsg_lo4 (n * 16 ^ 20) = 0
    · rw [zsg_ru, if_pos h0, Rat.cast_one, div_le_one (by positivity)]
      have : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
      nlinarith
    · have hpos : (0 : ℝ) < (zsg_lo4 (n * 16 ^ 20) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero h0
      have hle : ((zsg_lo4 (n * 16 ^ 20) : ℝ)) ^ 4 ≤ (n : ℝ) * 16 ^ 20 := by
        exact_mod_cast zsg_lo4_pow_le (n * 16 ^ 20)
      have hs : (zsg_lo4 (n * 16 ^ 20) : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) * 2 ^ 20 := by
        refine (pow_le_pow_iff_left₀ hpos.le (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp ?_
        rw [mul_pow, hr4, e16]
        exact hle
      rw [zsg_ru, if_neg h0]
      push_cast
      exact szs_div_aux1 hn' hr hpos hs

theorem zsg_le_inv_rpow (n : ℕ) : (zsg_rl n : ℝ) ≤ 1 / (n : ℝ) ^ (5 / 4 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : zsg_rl 0 = 0 := by simp [zsg_rl]
    rw [h0, Rat.cast_zero]
    positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hr : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hn' _
    have hr4 := zsg_root_pow hn'.le
    have e16 : ((2 : ℝ) ^ 20) ^ 4 = 16 ^ 20 := by norm_num
    have hpos : (0 : ℝ) < (zsg_hi4 (n * 16 ^ 20) : ℝ) := by
      exact_mod_cast zsg_hi4_pos _
    have hle : (n : ℝ) * 16 ^ 20 ≤ ((zsg_hi4 (n * 16 ^ 20) : ℝ)) ^ 4 := by
      exact_mod_cast zsg_le_hi4_pow (n * 16 ^ 20)
    have hs : (n : ℝ) ^ (1 / 4 : ℝ) * 2 ^ 20 ≤ (zsg_hi4 (n * 16 ^ 20) : ℝ) := by
      refine (pow_le_pow_iff_left₀ (by positivity) hpos.le (by norm_num : (4 : ℕ) ≠ 0)).mp ?_
      rw [mul_pow, hr4, e16]
      exact hle
    rw [zsg_rpow_five_quarters hn', zsg_rl]
    push_cast
    exact szs_div_aux2 hn' hr hpos hs

/-! ## A kernel-fast rational upper bound for `log n / log 2` -/

/-- Bit-by-bit search for `⌊log₂ M⌋` (only a candidate; certified in `zsg_logq`). -/
def zsg_bits (M : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | b + 1, acc =>
    if 2 ^ (acc + 2 ^ b) ≤ M then zsg_bits M b (acc + 2 ^ b) else zsg_bits M b acc

/-- `log n ≤ zsg_logq n · log 2` (self-certifying; equals `(⌊log₂ n^1024⌋ + 1)/1024` for
`n < 2^16`). -/
def zsg_logq (n : ℕ) : ℚ :=
  if n ^ 1024 ≤ 2 ^ (zsg_bits (n ^ 1024) 14 0 + 1) then
    ((zsg_bits (n ^ 1024) 14 0 + 1 : ℕ) : ℚ) / 1024
  else n

theorem zsg_logq_nonneg (n : ℕ) : 0 ≤ zsg_logq n := by
  unfold zsg_logq
  split_ifs
  · exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  · exact Nat.cast_nonneg n

theorem zsg_log_le (n : ℕ) : Real.log n ≤ (zsg_logq n : ℝ) * Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Rat.cast_nonneg.mpr (zsg_logq_nonneg 0)) h2.le
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    unfold zsg_logq
    split_ifs with h
    · have h3 : ((n : ℝ)) ^ 1024 ≤ (2 : ℝ) ^ (zsg_bits (n ^ 1024) 14 0 + 1) := by
        exact_mod_cast h
      have h4 := Real.log_le_log (by positivity) h3
      rw [Real.log_pow, Real.log_pow] at h4
      push_cast at h4 ⊢
      linarith
    · have h3 : (n : ℝ) ≤ (2 : ℝ) ^ n := by
        exact_mod_cast (Nat.lt_two_pow_self : n < 2 ^ n).le
      have h4 := Real.log_le_log hn' h3
      rw [Real.log_pow] at h4
      push_cast
      exact h4

/-! ## Certificates (exact rational arithmetic) -/

theorem zsg_cert_Q54 :
    ∑ n ∈ Finset.range 257, zsg_logq n * zsg_ru n ≤ 921859 / 100000 := by decide +kernel

theorem zsg_cert_Z54 :
    (359462 / 100000 : ℚ) ≤ ∑ n ∈ Finset.range 256, zsg_rl n := by decide +kernel

theorem zsg_cert_digamma :
    ∑ k ∈ Finset.range 1024, (1 / ((k : ℚ) + 3 / 2) - 1 / ((k : ℚ) + 9 / 8))
      ≤ -42461 / 100000 := by decide +kernel

/-! ## `σ = 5/4`: `∑ Λ(n) n^{-5/4} ≤ 3.4686` -/

/-- Antiderivative of `-log t · t^{-5/4}`. -/
noncomputable def zsg_G (t : ℝ) : ℝ := (4 * Real.log t + 16) * t ^ (-(1 / 4) : ℝ)

theorem zsg_hasDerivAt_G {t : ℝ} (ht : 0 < t) :
    HasDerivAt zsg_G (-(Real.log t / t ^ (5 / 4 : ℝ))) t := by
  have h1 : HasDerivAt (fun t : ℝ => 4 * Real.log t + 16) (4 * t⁻¹) t :=
    ((Real.hasDerivAt_log ht.ne').const_mul 4).add_const 16
  have h2 : HasDerivAt (fun t : ℝ => t ^ (-(1 / 4) : ℝ))
      (-(1 / 4) * t ^ (-(1 / 4) - 1 : ℝ)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h : HasDerivAt zsg_G (4 * t⁻¹ * t ^ (-(1 / 4) : ℝ)
      + (4 * Real.log t + 16) * (-(1 / 4) * t ^ (-(1 / 4) - 1 : ℝ))) t := h1.mul h2
  have e1 : t ^ (-(1 / 4) - 1 : ℝ) = t ^ (-(5 / 4) : ℝ) := by
    congr 1; norm_num
  have e2 : t ^ (-(1 / 4) : ℝ) = t * t ^ (-(5 / 4) : ℝ) := by
    rw [show (-(1 / 4) : ℝ) = 1 + -(5 / 4) by norm_num, Real.rpow_add ht, Real.rpow_one]
  have e3 : Real.log t / t ^ (5 / 4 : ℝ) = Real.log t * t ^ (-(5 / 4) : ℝ) := by
    rw [Real.rpow_neg ht.le, div_eq_mul_inv]
  convert h using 1
  rw [e3, e1, e2]
  have ht' := ht.ne'
  generalize t ^ (-(5 / 4) : ℝ) = u
  field_simp
  ring

theorem zsg_tele54 {x : ℝ} (hx : 3 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ (5 / 4 : ℝ) ≤ zsg_G x - zsg_G (x + 1) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.log (x + 1) / (x + 1) ^ (5 / 4 : ℝ) := ⟨_, rfl⟩
  rw [← hc]
  have hexp : Real.exp ((5 / 4 : ℝ)⁻¹) ≤ 3 := by
    have h1 : Real.exp ((5 / 4 : ℝ)⁻¹) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    have h2 := Real.exp_one_lt_d9
    linarith
  have hanti := Real.log_div_self_rpow_antitoneOn (a := 5 / 4) (by norm_num)
  have hder : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => zsg_G t + c * t)
      (-(Real.log t / t ^ (5 / 4 : ℝ)) + c * 1) t :=
    fun t ht => (zsg_hasDerivAt_G ht).add ((hasDerivAt_id t).const_mul c)
  have hmono : AntitoneOn (fun t => zsg_G t + c * t) (Set.Icc x (x + 1)) := by
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

theorem zsg_log_256 : Real.log ((256 : ℕ) : ℝ) = 8 * Real.log 2 := by
  rw [show (((256 : ℕ) : ℝ)) = 2 ^ 8 by norm_num, Real.log_pow]
  norm_num

theorem zsg_rpow_256 : (((256 : ℕ) : ℝ)) ^ (-(1 / 4) : ℝ) = 1 / 4 := by
  rw [Real.rpow_neg (by positivity), show (((256 : ℕ) : ℝ)) = 4 ^ 4 by norm_num,
    zsg_pow_root (by norm_num)]
  norm_num

theorem zsg_D54_le : ∑' n : ℕ, Real.log n / (n : ℝ) ^ (5 / 4 : ℝ) ≤ 15.9351 := by
  have hl2 := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : ∀ n : ℕ, 0 ≤ Real.log n / (n : ℝ) ^ (5 / 4 : ℝ) := fun n =>
    div_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine Real.tsum_le_of_sum_range_le hnn fun N => ?_
  have htele := szs_sum_range_le_of_tele (fun n : ℕ => Real.log n / (n : ℝ) ^ (5 / 4 : ℝ))
    (fun n : ℕ => zsg_G n) 256 hnn
    (fun n hn => by
      show 0 ≤ (4 * Real.log (n : ℝ) + 16) * (n : ℝ) ^ (-(1 / 4) : ℝ)
      exact mul_nonneg (by linarith [Real.log_natCast_nonneg n])
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n hn => by
      have hn' : (256 : ℝ) ≤ n := by exact_mod_cast hn
      have := zsg_tele54 (x := (n : ℝ)) (by linarith)
      simp only [Nat.cast_add, Nat.cast_one]
      exact this) N
  have hfin : ∑ n ∈ Finset.range 257, Real.log n / (n : ℝ) ^ (5 / 4 : ℝ)
      ≤ ((∑ n ∈ Finset.range 257, zsg_logq n * zsg_ru n : ℚ) : ℝ) * Real.log 2 := by
    rw [Rat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n _ => ?_
    push_cast
    have h1 := zsg_log_le n
    have h2 := zsg_inv_rpow_le n
    have h3 : (0 : ℝ) ≤ zsg_logq n := Rat.cast_nonneg.mpr (zsg_logq_nonneg n)
    calc Real.log n / (n : ℝ) ^ (5 / 4 : ℝ)
        = Real.log n * (1 / (n : ℝ) ^ (5 / 4 : ℝ)) := by ring
      _ ≤ ((zsg_logq n : ℝ) * Real.log 2) * (zsg_ru n : ℝ) :=
          mul_le_mul h1 h2 (by positivity) (mul_nonneg h3 hl2p.le)
      _ = _ := by ring
  have hQ := (Rat.cast_le (K := ℝ)).mpr zsg_cert_Q54
  rw [show ((921859 / 100000 : ℚ) : ℝ) = 921859 / 100000 by norm_num] at hQ
  have hG : zsg_G ((256 : ℕ) : ℝ) = (4 * (8 * Real.log 2) + 16) * (1 / 4) := by
    unfold zsg_G
    rw [zsg_log_256, zsg_rpow_256]
  have h1 := mul_le_mul_of_nonneg_right hQ hl2p.le
  have e : (256 + 1 : ℕ) = 257 := rfl
  beta_reduce at htele
  rw [e, hG] at htele
  linarith

theorem zsg_hasDerivAt_H {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => 4 * t ^ (-(1 / 4) : ℝ)) (-(t ^ (-(5 / 4) : ℝ))) t := by
  have h2 : HasDerivAt (fun t : ℝ => t ^ (-(1 / 4) : ℝ))
      (-(1 / 4) * t ^ (-(1 / 4) - 1 : ℝ)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have e1 : t ^ (-(1 / 4) - 1 : ℝ) = t ^ (-(5 / 4) : ℝ) := by
    congr 1; norm_num
  have h := h2.const_mul 4
  have e : (4 : ℝ) * (-(1 / 4) * t ^ (-(5 / 4) : ℝ)) = -(t ^ (-(5 / 4) : ℝ)) := by ring
  rw [e1, e] at h
  exact h

theorem zsg_tele_Z54 (n : ℕ) (hn : 0 < n) :
    4 * (n : ℝ) ^ (-(1 / 4) : ℝ) - 4 * ((n : ℝ) + 1) ^ (-(1 / 4) : ℝ)
      ≤ 1 / (n : ℝ) ^ (5 / 4 : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (n : ℝ) ^ (-(5 / 4) : ℝ) := ⟨_, rfl⟩
  have hc' : 1 / (n : ℝ) ^ (5 / 4 : ℝ) = c := by
    rw [hc, Real.rpow_neg hn'.le, one_div]
  rw [hc']
  have hder : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => 4 * t ^ (-(1 / 4) : ℝ) + c * t)
      (-(t ^ (-(5 / 4) : ℝ)) + c * 1) t :=
    fun t ht => (zsg_hasDerivAt_H ht).add ((hasDerivAt_id t).const_mul c)
  have hmono : MonotoneOn (fun t : ℝ => 4 * t ^ (-(1 / 4) : ℝ) + c * t)
      (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (fun t ht => ?_) (fun t ht => ?_)
      (fun t ht => ?_)
    · exact (hder t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · rw [interior_Icc] at ht
      exact (hder t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [(hder t (by linarith [ht.1])).deriv]
      have := Real.rpow_le_rpow_of_nonpos hn' ht.1.le
        (by norm_num : (-(5 / 4) : ℝ) ≤ 0)
      rw [hc]
      linarith
  have := hmono (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
    (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
  simp only at this
  linarith

theorem zsg_Z54_ge : (4.59422 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (5 / 4 : ℝ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((256 + k : ℕ) : ℝ) = 10 ^ 16 := ⟨10 ^ 16 - 256, by norm_num⟩
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (5 / 4 : ℝ) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have htele := szs_sum_range_ge_of_tele (fun n : ℕ => 1 / (n : ℝ) ^ (5 / 4 : ℝ))
    (fun n : ℕ => 4 * (n : ℝ) ^ (-(1 / 4) : ℝ)) 256 (fun n hn => by
      have := zsg_tele_Z54 n (by omega)
      simp only [Nat.cast_add, Nat.cast_one]
      exact this) k
  have hle := hsum.sum_le_tsum (Finset.range (256 + k)) (fun i _ => by positivity)
  have hfin : ((∑ n ∈ Finset.range 256, zsg_rl n : ℚ) : ℝ)
      ≤ ∑ n ∈ Finset.range 256, 1 / (n : ℝ) ^ (5 / 4 : ℝ) := by
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum fun n _ => zsg_le_inv_rpow n
  have hZ := (Rat.cast_le (K := ℝ)).mpr zsg_cert_Z54
  rw [show ((359462 / 100000 : ℚ) : ℝ) = 359462 / 100000 by norm_num] at hZ
  have hH2 : (((256 + k : ℕ) : ℝ)) ^ (-(1 / 4) : ℝ) = 1 / 10 ^ 4 := by
    rw [hk, Real.rpow_neg (by positivity), show ((10 : ℝ) ^ 16) = (10 ^ 4) ^ 4 by norm_num,
      zsg_pow_root (by positivity)]
    norm_num
  beta_reduce at htele
  rw [zsg_rpow_256, hH2] at htele
  linarith

/-- `∑ Λ(n) n^{-5/4} ≤ 3.4686` (true value `3.46665…`). -/
theorem zsg_S54_le : ∑' n : ℕ, Λ n / (n : ℝ) ^ (5 / 4 : ℝ) ≤ 3.4686 := by
  have hmul := szs_tsum_mul (σ := 5 / 4) (by norm_num)
  have hD := zsg_D54_le
  have hZ := zsg_Z54_ge
  have h0 : 0 ≤ ∑' n : ℕ, Λ n / (n : ℝ) ^ (5 / 4 : ℝ) :=
    tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [← hmul] at hD
  have := mul_le_mul_of_nonneg_left hZ h0
  linarith

/-! ## Gamma factor at `5/4` -/

theorem zsg_digamma_nine_eighths :
    (digamma ((9 / 8 : ℚ) : ℂ)).re ≤ (digamma ((3 / 2 : ℚ) : ℂ)).re - 42461 / 100000 := by
  have h := szs_digamma_re_le (9 / 8) (3 / 2) (by norm_num) (by norm_num) 1024
  have hP := (Rat.cast_le (K := ℝ)).mpr zsg_cert_digamma
  generalize (∑ k ∈ Finset.range 1024, (1 / ((k : ℚ) + 3 / 2) - 1 / ((k : ℚ) + 9 / 8))) = P
    at h hP
  rw [show ((-42461 / 100000 : ℚ) : ℝ) = -42461 / 100000 by norm_num] at hP
  linarith

/-- `Re (γ'/γ)(5/4) ≤ -0.7657` (true values: `-1.67…` even, `-0.76661` odd). -/
theorem re_logDeriv_gammaFactor_five_quarters_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (deriv (gammaFactor χ) (5 / 4) / gammaFactor χ (5 / 4)).re ≤ -0.7657 := by
  have hγ := szs_gamma_gt
  have hπ1 := szs_log_pi_gt
  have hdiv2 : ∀ z : ℂ, (z / 2).re = z.re / 2 := fun z => by simp
  rcases χ.even_or_odd with he | ho
  · have hfun : gammaFactor χ = Gammaℝ := funext fun s => he.gammaFactor_def s
    rw [hfun, logDeriv_Gammaℝ (by norm_num), show (5 / 4 : ℂ) / 2 = ((5 / 8 : ℚ) : ℂ) by norm_num,
      Complex.add_re, hdiv2, hdiv2, Complex.neg_re, Complex.ofReal_re]
    have h := szs_digamma_re_le (5 / 8) 1 (by norm_num) (by norm_num) 0
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
      show ((5 / 4 : ℂ) + 1) / 2 = ((9 / 8 : ℚ) : ℂ) by norm_num,
      Complex.add_re, hdiv2, hdiv2, Complex.neg_re, Complex.ofReal_re]
    have h := zsg_digamma_nine_eighths
    have h32 : digamma ((3 / 2 : ℚ) : ℂ)
        = ((-2 * Real.log 2 - Real.eulerMascheroniConstant + 2 : ℝ) : ℂ) := by
      rw [show ((3 / 2 : ℚ) : ℂ) = 1 / 2 + 1 by norm_num, digamma_apply_add_one _ hhalf,
        digamma_one_half, hlog]
      norm_num
    rw [h32, Complex.ofReal_re] at h
    linarith [Real.log_two_gt_d9]

/-! ## Lower bounds for `∑_{m ≤ K} Λ(m) m^{-σ}` from one kernel computation -/

/-- `zsg_acc c n = (lcm(1..n), ∏_{m ≤ n} (lcm(1..m)/lcm(1..m-1))^{c m})`. -/
def zsg_acc (c : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => (Nat.lcm (zsg_acc c n).1 (n + 1),
      (zsg_acc c n).2 * (Nat.lcm (zsg_acc c n).1 (n + 1) / (zsg_acc c n).1) ^ c (n + 1))

theorem zsg_acc_fst (c : ℕ → ℕ) (n : ℕ) : (zsg_acc c n).1 = Nat.lcmUpto n := by
  induction n with
  | zero => simp [zsg_acc, lcmUpto_zero']
  | succ n ih => simp only [zsg_acc, ih, lcmUpto_succ']

theorem zsg_acc_snd_succ (c : ℕ → ℕ) (n : ℕ) :
    (zsg_acc c (n + 1)).2
      = (zsg_acc c n).2 * (Nat.lcmUpto (n + 1) / Nat.lcmUpto n) ^ c (n + 1) := by
  show (zsg_acc c n).2 * (Nat.lcm (zsg_acc c n).1 (n + 1) / (zsg_acc c n).1) ^ c (n + 1) = _
  rw [zsg_acc_fst, lcmUpto_succ']

theorem zsg_vonMangoldt_succ (n : ℕ) :
    Λ (n + 1) = Real.log (Nat.lcmUpto (n + 1) : ℝ) - Real.log (Nat.lcmUpto n : ℝ) := by
  have h1 := psi_natCast_eq_sum_range (n + 1)
  have h2 := psi_natCast_eq_sum_range n
  rw [Finset.sum_range_succ, ← h2, Chebyshev.psi_eq_log_lcmUpto,
    Chebyshev.psi_eq_log_lcmUpto] at h1
  linarith

theorem zsg_log_acc (c : ℕ → ℕ) (n : ℕ) :
    0 < (zsg_acc c n).2 ∧
      Real.log ((zsg_acc c n).2 : ℝ) = ∑ m ∈ Finset.range (n + 1), (c m : ℝ) * Λ m := by
  induction n with
  | zero => simp [zsg_acc]
  | succ n ih =>
    have hl : 0 < Nat.lcmUpto n := Nat.lcmUpto_pos n
    have hl1 : 0 < Nat.lcmUpto (n + 1) := Nat.lcmUpto_pos (n + 1)
    have hlR : (0 : ℝ) < (Nat.lcmUpto n : ℝ) := by exact_mod_cast hl
    have hl1R : (0 : ℝ) < (Nat.lcmUpto (n + 1) : ℝ) := by exact_mod_cast hl1
    have hdvd : Nat.lcmUpto n ∣ Nat.lcmUpto (n + 1) := by
      rw [lcmUpto_succ']; exact Nat.dvd_lcm_left _ _
    have hquot : ((Nat.lcmUpto (n + 1) / Nat.lcmUpto n : ℕ) : ℝ)
        = (Nat.lcmUpto (n + 1) : ℝ) / (Nat.lcmUpto n : ℝ) :=
      Nat.cast_div hdvd hlR.ne'
    have hqpos : 0 < Nat.lcmUpto (n + 1) / Nat.lcmUpto n :=
      Nat.div_pos (Nat.le_of_dvd hl1 hdvd) hl
    have hPR : (0 : ℝ) < ((zsg_acc c n).2 : ℝ) := by exact_mod_cast ih.1
    refine ⟨?_, ?_⟩
    · rw [zsg_acc_snd_succ]
      exact Nat.mul_pos ih.1 (pow_pos hqpos _)
    · rw [Finset.sum_range_succ, ← ih.2, zsg_acc_snd_succ, Nat.cast_mul, Nat.cast_pow, hquot,
        Real.log_mul hPR.ne' (pow_pos (div_pos hl1R hlR) _).ne', Real.log_pow,
        Real.log_div hl1R.ne' hlR.ne', zsg_vonMangoldt_succ]

/-- Integer weight `≤ 2^20 · m^{-2}`. -/
def zsg_c2 (m : ℕ) : ℕ := 2 ^ 20 / (m * m)

/-- Integer weight `≤ 2^20 · m^{-5/4}`. -/
def zsg_c54 (m : ℕ) : ℕ := 2 ^ 40 / (m * zsg_hi4 (m * 16 ^ 20))

theorem zsg_c2_le (m : ℕ) :
    (zsg_c2 m : ℝ) * Λ m ≤ 2 ^ 20 * (Λ m / (m : ℝ) ^ (2 : ℝ)) := by
  have h0 : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : (zsg_c2 m : ℝ) ≤ 2 ^ 20 / ((m : ℝ) * m) :=
    calc (zsg_c2 m : ℝ) ≤ ((2 ^ 20 : ℕ) : ℝ) / ((m * m : ℕ) : ℝ) := Nat.cast_div_le
      _ = 2 ^ 20 / ((m : ℝ) * m) := by norm_num
  rw [Real.rpow_two]
  calc (zsg_c2 m : ℝ) * Λ m ≤ 2 ^ 20 / ((m : ℝ) * m) * Λ m :=
        mul_le_mul_of_nonneg_right h1 h0
    _ = 2 ^ 20 * (Λ m / (m : ℝ) ^ 2) := by ring

theorem zsg_c54_le (m : ℕ) :
    (zsg_c54 m : ℝ) * Λ m ≤ 2 ^ 20 * (Λ m / (m : ℝ) ^ (5 / 4 : ℝ)) := by
  have h0 : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : (zsg_c54 m : ℝ) ≤ 2 ^ 20 * (zsg_rl m : ℝ) :=
    calc (zsg_c54 m : ℝ)
        ≤ ((2 ^ 40 : ℕ) : ℝ) / ((m * zsg_hi4 (m * 16 ^ 20) : ℕ) : ℝ) := Nat.cast_div_le
      _ = 2 ^ 20 * (zsg_rl m : ℝ) := by
        rw [zsg_rl, Nat.cast_mul, Nat.cast_pow, Rat.cast_div, Rat.cast_mul, Rat.cast_pow]
        simp only [Nat.cast_ofNat, Rat.cast_ofNat, Rat.cast_natCast]
        ring
  have h2 := zsg_le_inv_rpow m
  calc (zsg_c54 m : ℝ) * Λ m ≤ 2 ^ 20 * (1 / (m : ℝ) ^ (5 / 4 : ℝ)) * Λ m :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) h0
    _ = 2 ^ 20 * (Λ m / (m : ℝ) ^ (5 / 4 : ℝ)) := by ring

/-- **Certificate form.** If `c m · Λ(m) ≤ 2^20 Λ(m) m^{-σ}` and `2^B ≤ (zsg_acc c K).2` then
`B log 2 / 2^20 ≤ ∑_{m ≤ K} Λ(m) m^{-σ}`. -/
theorem zsg_sum_ge_of_cert {c : ℕ → ℕ} {σ : ℝ}
    (hc : ∀ m : ℕ, (c m : ℝ) * Λ m ≤ 2 ^ 20 * (Λ m / (m : ℝ) ^ σ)) {B K : ℕ}
    (hcert : 2 ^ B ≤ (zsg_acc c K).2) :
    (B : ℝ) * Real.log 2 / 2 ^ 20 ≤ ∑ m ∈ Finset.range (K + 1), Λ m / (m : ℝ) ^ σ := by
  have h1 : (B : ℝ) * Real.log 2 ≤ Real.log ((zsg_acc c K).2 : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hcert)
  rw [(zsg_log_acc c K).2] at h1
  have h2 : ∑ m ∈ Finset.range (K + 1), (c m : ℝ) * Λ m
      ≤ 2 ^ 20 * ∑ m ∈ Finset.range (K + 1), Λ m / (m : ℝ) ^ σ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun m _ => hc m
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ## The zero sum with gain -/

/-- **Zero sum with hypothesis gain, general form.** Under GRH, for primitive `χ ≠ 1` mod `q`
with `χ(m) = 1` for all `1 ≤ m < K`:
`T(χ) ≤ (5/9) log q + (8/9)(2.7029 - 2 S_K(5/4)) + (2/9)(0.0174 - 2 S_K(2))`,
`S_K(σ) = ∑_{m<K} Λ(m) m^{-σ}`. -/
theorem zeroSum_le_gain_of_sums (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {K : ℕ}
    (hK : ∀ m : ℕ, 1 ≤ m → m < K → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q
      + (8 / 9 * (2.7029 - 2 * ∑ m ∈ Finset.range K, Λ m / (m : ℝ) ^ (5 / 4 : ℝ))
        + 2 / 9 * (0.0174 - 2 * ∑ m ∈ Finset.range K, Λ m / (m : ℝ) ^ (2 : ℝ))) := by
  have h := zeroSum_le_twoPoint hGRH χ hχ hχ1
  have hL54 := zsg_re_logDeriv_le χ (σ := 5 / 4) (by norm_num) hK
  have hL2 := zsg_re_logDeriv_le χ (σ := 2) (by norm_num) hK
  rw [show ((5 / 4 : ℝ) : ℂ) = 5 / 4 by norm_num] at hL54
  rw [Complex.ofReal_ofNat] at hL2
  have hZ54 := zsg_S54_le
  have hZ2 := szs_S2_le
  have hG54 := re_logDeriv_gammaFactor_five_quarters_le χ
  have hG2 := re_logDeriv_gammaFactor_two_le_sharp χ
  rw [Complex.add_re, Complex.add_re] at h
  linarith

/-- **Zero sum with hypothesis gain, certificate form.** -/
theorem zeroSum_le_gain_of_certs (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {K B54 B2 : ℕ}
    (h54 : 2 ^ B54 ≤ (zsg_acc zsg_c54 K).2) (h2 : 2 ^ B2 ≤ (zsg_acc zsg_c2 K).2) {x : ℝ}
    (hx : (K : ℝ) + 1 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q
      + (8 / 9 * (2.7029 - 2 * ((B54 : ℝ) * Real.log 2 / 2 ^ 20))
        + 2 / 9 * (0.0174 - 2 * ((B2 : ℝ) * Real.log 2 / 2 ^ 20))) := by
  have hK : ∀ m : ℕ, 1 ≤ m → m < K + 1 → χ (m : ZMod q) = 1 := fun m hm hmK =>
    hx1 m hm (lt_of_lt_of_le (by exact_mod_cast hmK) hx)
  have h := zeroSum_le_gain_of_sums hGRH χ hχ hχ1 hK
  have s54 := zsg_sum_ge_of_cert zsg_c54_le h54
  have s2 := zsg_sum_ge_of_cert zsg_c2_le h2
  linarith

set_option maxRecDepth 100000 in
theorem zsg_cert54_168 : 2 ^ 3564934 ≤ (zsg_acc zsg_c54 167).2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem zsg_cert2_168 : 2 ^ 853137 ≤ (zsg_acc zsg_c2 167).2 := by decide +kernel

/-- `x ≥ 168`, no witness below `x`: `T(χ) ≤ (5/9) log q - 2.0335`. -/
theorem zeroSum_le_gain_168 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 168 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q - 2.0335 := by
  have h := zeroSum_le_gain_of_certs hGRH χ hχ hχ1 zsg_cert54_168 zsg_cert2_168 (x := x)
    (by norm_num; linarith) hx1
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

set_option maxRecDepth 100000 in
theorem zsg_cert54_200 : 2 ^ 3651322 ≤ (zsg_acc zsg_c54 199).2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem zsg_cert2_200 : 2 ^ 854839 ≤ (zsg_acc zsg_c2 199).2 := by decide +kernel

/-- `x ≥ 200`, no witness below `x`: `T(χ) ≤ (5/9) log q - 2.1355`. -/
theorem zeroSum_le_gain_200 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 200 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q - 2.1355 := by
  have h := zeroSum_le_gain_of_certs hGRH χ hχ hχ1 zsg_cert54_200 zsg_cert2_200 (x := x)
    (by norm_num; linarith) hx1
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

set_option maxRecDepth 100000 in
theorem zsg_cert54_240 : 2 ^ 3707270 ≤ (zsg_acc zsg_c54 239).2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem zsg_cert2_240 : 2 ^ 855778 ≤ (zsg_acc zsg_c2 239).2 := by decide +kernel

/-- `x ≥ 240`, no witness below `x`: `T(χ) ≤ (5/9) log q - 2.2016`. -/
theorem zeroSum_le_gain_240 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 240 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q - 2.2016 := by
  have h := zeroSum_le_gain_of_certs hGRH χ hχ hχ1 zsg_cert54_240 zsg_cert2_240 (x := x)
    (by norm_num; linarith) hx1
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

set_option maxRecDepth 100000 in
theorem zsg_cert54_320 : 2 ^ 3818144 ≤ (zsg_acc zsg_c54 319).2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem zsg_cert2_320 : 2 ^ 857362 ≤ (zsg_acc zsg_c2 319).2 := by decide +kernel

/-- `x ≥ 320`, no witness below `x`: `T(χ) ≤ (5/9) log q - 2.3323`. -/
theorem zeroSum_le_gain_320 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 320 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q - 2.3323 := by
  have h := zeroSum_le_gain_of_certs hGRH χ hχ hχ1 zsg_cert54_320 zsg_cert2_320 (x := x)
    (by norm_num; linarith) hx1
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

set_option maxRecDepth 100000 in
theorem zsg_cert54_512 : 2 ^ 3974461 ≤ (zsg_acc zsg_c54 511).2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem zsg_cert2_512 : 2 ^ 858958 ≤ (zsg_acc zsg_c2 511).2 := by decide +kernel

/-- `x ≥ 512`, no witness below `x`: `T(χ) ≤ (5/9) log q - 2.5165`. -/
theorem zeroSum_le_gain_512 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 512 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q - 2.5165 := by
  have h := zeroSum_le_gain_of_certs hGRH χ hχ hχ1 zsg_cert54_512 zsg_cert2_512 (x := x)
    (by norm_num; linarith) hx1
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

set_option maxRecDepth 100000 in
theorem zsg_cert54_1024 : 2 ^ 4174243 ≤ (zsg_acc zsg_c54 1023).2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem zsg_cert2_1024 : 2 ^ 860087 ≤ (zsg_acc zsg_c2 1023).2 := by decide +kernel

/-- `x ≥ 1024`, no witness below `x`: `T(χ) ≤ (5/9) log q - 2.7516`. -/
theorem zeroSum_le_gain_1024 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 1024 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q - 2.7516 := by
  have h := zeroSum_le_gain_of_certs hGRH χ hχ hχ1 zsg_cert54_1024 zsg_cert2_1024 (x := x)
    (by norm_num; linarith) hx1
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

set_option maxRecDepth 100000 in
theorem zsg_cert54_2048 : 2 ^ 4342611 ≤ (zsg_acc zsg_c54 2047).2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem zsg_cert2_2048 : 2 ^ 860088 ≤ (zsg_acc zsg_c2 2047).2 := by decide +kernel

/-- `x ≥ 2048`, no witness below `x`: `T(χ) ≤ (5/9) log q - 2.9495`. -/
theorem zeroSum_le_gain_2048 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 2048 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q - 2.9495 := by
  have h := zeroSum_le_gain_of_certs hGRH χ hχ hχ1 zsg_cert54_2048 zsg_cert2_2048 (x := x)
    (by norm_num; linarith) hx1
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

set_option maxRecDepth 100000 in
theorem zsg_cert54_4096 : 2 ^ 4485453 ≤ (zsg_acc zsg_c54 4095).2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem zsg_cert2_4096 : 2 ^ 860088 ≤ (zsg_acc zsg_c2 4095).2 := by decide +kernel

/-- `x ≥ 4096`, no witness below `x`: `T(χ) ≤ (5/9) log q - 3.1173`. -/
theorem zeroSum_le_gain_4096 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 4096 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q - 3.1173 := by
  have h := zeroSum_le_gain_of_certs hGRH χ hχ hχ1 zsg_cert54_4096 zsg_cert2_4096 (x := x)
    (by norm_num; linarith) hx1
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

end DetPrimality.Bach
