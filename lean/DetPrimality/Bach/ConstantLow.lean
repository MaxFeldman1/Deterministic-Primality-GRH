import DetPrimality.Bach.SharpZeroSum
import DetPrimality.Bach.SharpExplicit
import DetPrimality.Bach.ConstNoncoprimeOmega
import DetPrimality.Bach.ConstPsiOneGrid
import DetPrimality.Bach.ConstPsiTheta

/-!
# Lowering Bach's constant to `8` (and, more simply, to `9`)

Main results: `bachBoundChar_of_GRH_c8 : BachBoundChar 8`, `grh_implies_bach_c8 : GRHImpliesBach 8`
(and the simpler `bachBoundChar_of_GRH_c9`, `grh_implies_bach_c9`, kept because their proof has
no number-theoretic case analysis and much larger margins).

Write `L = log n`, `x = c L²`, `s = √x`.  Assume that no unit `a < x` has `χ a ≠ 1`, and let
`χ*` (conductor `q ∣ n`) be the primitive character inducing `χ`.  Then

* (upper bound, GRH; `SharpExplicit.lean` + `SharpZeroSum.lean`)
  `Re ψ̃(x, χ*) ≤ (s + 2 + 3/x) (⅔ log q + 1.097) + 0.5708 - 1 + (log x + 13/6)/x`
  (`re_smoothPsi_le_of_zeroSum_le_of_logDeriv` with `zeroSum_le_sharp32` and
  `norm_logDeriv_LFunction_two_le_sharp`);
* (lower bound, `re_smoothPsi_primitive_lower`)
  `Re ψ̃(x, χ*) ≥ ψ₁(x) - 2 E`, `E = ∑_{m<x,(m,n)>1} Λ(m)`.

The contradiction is `ψ₁(x) - 2 E > W`, where `W` is a simplified form of the upper bound.

## `c = 9`

Here `s = 3L` exactly and `W(L) = (3L + 2)(⅔ L + 1.097) - 0.347` (`clow_upper`, `L ≥ 5.664`).

* Bootstrap (`clow_log_ge`): `n > 9 (log n)² ⟹ n ≥ 289`, hence `L ≥ 5.6656`, `x > 288.8`.
  The chain is `n ≥ 10, 48, 135, 217, 261, 279, 286, 288, 289`; each step uses a certificate
  `2^k ≤ N^j` (so `log n ≥ (k/j) log 2`) and integer rounding (`clow_boot_step`).  The bound is
  sharp: `n = 289` does satisfy `289 > 9 (log 289)² ≈ 288.97`.
* `ψ₁`: `psiOne_lower_grid` (`x/2 - 2.6` on `(256, 1536]`), `psiOne_lower_1024`,
  `psiOne_lower_2048_of_le`, `psiOne_lower_integral`.
* `E ≤ ω(n) log x ≤ 4 log x` for `n < 2310` (`noncoprimeSum_le_omega_mul_log`,
  `cno_primorial_le_of_card`); `E ≤ L + 1.35 √x` for `420 ≤ x < 65536`; `E ≤ L + 1.84 √x` always.
* `log x ≤ (527/64) log 2 + x/300 - 1` (tangent at `300`, from `300^64 ≤ 2^527`).

| range (`c = 9`)               | `ψ₁` bound                         | `E`              | margin  |
|-------------------------------|------------------------------------|------------------|---------|
| `x ≤ 1536`, `n < 2310`        | `x/2 - 2.6`                        | `4 log x`        | ≈ 4.2   |
| `x ≤ 1536`, `n ≥ 2310`        | `x/2 - 2.6`                        | `L + 1.35 · 3L`  | ≈ 28    |
| `1536 < x ≤ 2048`             | `psiOne_lower_1024` (gain at 2048) | `L + 1.84 · 3L`  | ≈ 30    |
| `2048 < x ≤ 4096`             | `psiOne_lower_2048_of_le` (4096)   | `L + 1.84 · 3L`  | ≈ 137   |
| `x > 4096`                    | `psiOne_lower_integral`            | `L + 1.84 · 3L`  | ≈ 121   |

(margin = minimum over the range of `ψ₁ - 2E - W` in the form given to `linarith`.)

## `c = 8`

Here `s ≤ 2.8285 L` and `W(L, lq) = (2.8285 L + 2)(⅔ lq + 1.097) - 0.336` for `0 ≤ lq ≤ L`,
`lq = log q` (`clow8_upper`, `L ≥ 5.48`).  The bootstrap (`clow8_log_ge`) gives `n ≥ 241`
(sharp: `241 > 8 (log 241)² ≈ 240.66`), `L ≥ 5.484`, `x > 240.5`.

With `E ≤ 4 log x` the inequality *fails* for `241 ≤ n ≲ 410`, so two extra ideas are needed.

* **Three prime factors.**  If `ω(n) ≤ 3` then `E ≤ 3 log x`, which is enough (margin `≈ 1.9`).
* **Four prime factors** (`clow8_omega4`): a number `n ≥ 241` with `ω(n) ≥ 4` is `≥ 420`, or
  `n ≡ 2 (mod 4)` and `n ≥ 330` (in fact `n ∈ {330, 390}`).  The proof peels off the primes
  `2, 3, 5` with `cno_primorial_le_of_card` (`clow8_card_mul`, `clow8_primeFactors_mul`).
* **Conductors are never `≡ 2 (mod 4)`** (`clow8_conductor_le`): for `n ≡ 2 (mod 4)` the map
  `(ℤ/n)ˣ → (ℤ/(n/2))ˣ` is a bijection, so every character mod `n` factors through `n/2` and
  `q ≤ n/2`, i.e. `log q ≤ L - log 2`.  This lowers `W` by `≈ 8.5` and settles `n = 330, 390`.
* For `n ≥ 420` with `ω(n) = 4` and `x ≤ 304` the bound `x/2 - 2.6` is too weak; the grid cell
  `psiOne_lower_grid_288` (`290.688 - 42761/x`) is used with a chord bound for `1/x` on
  `[291.5, 304]` (`clow8_inv_chord`).
* `ψ₁ ≥ x/2 - 2.6` is extended to `(240, 256]` by a new certificate (`clow8_cert_240`,
  `clow8_psiOne_half`).

| range (`c = 8`)                              | `ψ₁` bound              | `E`, `log q`                 | margin  |
|----------------------------------------------|-------------------------|------------------------------|---------|
| `x ≤ 1536`, `n < 2310`, `ω ≤ 3`              | `x/2 - 2.6`             | `3 log x`, `L`               | ≈ 1.89  |
| `ω = 4`, `n ≡ 2 (4)`, `n ≥ 330`              | `x/2 - 2.6`             | `4 log x`, `L - log 2`       | ≈ 4.57  |
| `ω = 4`, `n ≥ 420`, `x ≤ 304`                | cell `288` + chord      | `4 log x`, `L`               | ≈ 1.26  |
| `ω = 4`, `n ≥ 420`, `x > 304`                | `x/2 - 2.6`             | `4 log x`, `L`               | ≈ 2.76  |
| `x ≤ 1536`, `n ≥ 2310`                       | `x/2 - 2.6`             | `L + 1.35 s`, `L`            | ≈ 11.1  |
| `1536 < x ≤ 2048`                            | `psiOne_lower_1024`     | `L + 1.35 s`, `L`            | ≈ 45.8  |
| `2048 < x ≤ 4096`                            | `psiOne_lower_2048_of_le` | `L + 1.84 s`, `L`          | ≈ 106   |
| `x > 4096`                                   | `psiOne_lower_integral` | `L + 1.84 s`, `L`            | ≈ 61.6  |

`c = 7` is out of reach with these inputs: e.g. for `n = 210` (`x ≈ 200`) the inequality fails
by about `5` even with the exact value of `E` and `q ≤ 105`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- One bootstrap step: from `n ≥ N`, a certificate `2^k ≤ N^j` and `n > 9 (log n)²` we get
`log n ≥ lb` and `n ≥ M + 1` as soon as `lb ≤ (k/j) · 0.6931471803` and `M ≤ 9 lb²`. -/
theorem clow_boot_step {n N k j M : ℕ} {lb : ℝ} (hbig : 9 * Real.log n ^ 2 < n) (hN : N ≤ n)
    (hj : 0 < j) (hpow : 2 ^ k ≤ N ^ j) (hlb0 : 0 ≤ lb)
    (hlb : lb * (j : ℝ) ≤ (k : ℝ) * 0.6931471803) (hM : (M : ℝ) ≤ 9 * lb ^ 2) :
    lb ≤ Real.log n ∧ M + 1 ≤ n := by
  have h2 := Real.log_two_gt_d9
  have hp : (2 : ℝ) ^ k ≤ (n : ℝ) ^ j := by
    exact_mod_cast hpow.trans (Nat.pow_le_pow_left hN j)
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((n : ℝ) ^ j) := Real.log_le_log (by positivity) hp
  rw [Real.log_pow, Real.log_pow] at h1
  have hk : (k : ℝ) * 0.6931471803 ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2.le (Nat.cast_nonneg k)
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hL : lb ≤ Real.log n := by
    have : lb * (j : ℝ) ≤ Real.log n * (j : ℝ) := by linarith
    exact le_of_mul_le_mul_right this hj'
  refine ⟨hL, ?_⟩
  have hlt : (M : ℝ) < n := by nlinarith [sq_nonneg (Real.log n - lb)]
  have : M < n := by exact_mod_cast hlt
  omega

/-- (§7.1, `c = 9`) If no unit `a < 9 (log n)²` has `χ a ≠ 1`, then `n ≥ 289` and
`log n ≥ 5.6656`. -/
theorem clow_log_ge {n : ℕ} (hn : 2 < n) (χ : DirichletCharacter ℂ n) (hχ : χ ≠ 1)
    (h : ∀ a : ℕ, (a : ℝ) < 9 * (Real.log n) ^ 2 → IsUnit (a : ZMod n) → χ (a : ZMod n) = 1) :
    289 ≤ n ∧ 5.6656 ≤ Real.log n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod n)ˣ, χ u ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hχ (MulChar.ext fun a => by rw [hc a, MulChar.one_apply_coe])
  have hval : ¬ (((u : ZMod n).val : ℝ) < 9 * Real.log n ^ 2) := fun hlt => hu (by
    have h1 := h (u : ZMod n).val hlt (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    rwa [ZMod.natCast_zmod_val] at h1)
  have hlt : ((u : ZMod n).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
  have hbig : 9 * Real.log n ^ 2 < n := by linarith [not_lt.mp hval]
  have hn0 : (0 : ℝ) < n := by positivity
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  have h0 : 10 ≤ n := by
    have : (9 : ℝ) < n := by nlinarith
    have : 9 < n := by exact_mod_cast this
    omega
  obtain ⟨-, h1⟩ := clow_boot_step (N := 10) (k := 425) (j := 128) (M := 47) (lb := 2.30146)
    hbig h0 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h2⟩ := clow_boot_step (N := 48) (k := 5719) (j := 1024) (M := 134) (lb := 3.87119)
    hbig h1 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h3⟩ := clow_boot_step (N := 135) (k := 1811) (j := 256) (M := 216) (lb := 4.90347)
    hbig h2 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h4⟩ := clow_boot_step (N := 217) (k := 993) (j := 128) (M := 260) (lb := 5.3773)
    hbig h3 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h5⟩ := clow_boot_step (N := 261) (k := 1027) (j := 128) (M := 278) (lb := 5.56142)
    hbig h4 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h6⟩ := clow_boot_step (N := 279) (k := 4159) (j := 512) (M := 285) (lb := 5.63046)
    hbig h5 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h7⟩ := clow_boot_step (N := 286) (k := 261) (j := 32) (M := 287) (lb := 5.65348)
    hbig h6 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h8⟩ := clow_boot_step (N := 288) (k := 4183) (j := 512) (M := 288) (lb := 5.66295)
    hbig h7 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨h9, -⟩ := clow_boot_step (N := 289) (k := 4185) (j := 512) (M := 0) (lb := 5.6656)
    hbig h8 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h8, h9⟩

/-- Tangent bound `log x ≤ k log 2 + x / 2^k - 1` for `x > 0`. -/
theorem clow_log_le_two_pow {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.log x ≤ k * Real.log 2 + x / 2 ^ k - 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 2 ^ k by positivity)
  rw [Real.log_div hx.ne' (by positivity), Real.log_pow] at h1
  linarith

/-- Tangent bound at `300`: `log x ≤ (527/64) · 0.6931471808 + x/300 - 1`
(`log 300 ≈ 5.70378`, the constant is `≈ 5.70763`). -/
theorem clow_log_le_300 {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 527 / 64 * 0.6931471808 + x / 300 - 1 := by
  have h2u := Real.log_two_lt_d9
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 300 by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h1
  have hp : (300 : ℝ) ^ 64 ≤ 2 ^ 527 := by
    exact_mod_cast (by decide +kernel : (300 : ℕ) ^ 64 ≤ 2 ^ 527)
  have h3 : Real.log ((300 : ℝ) ^ 64) ≤ Real.log ((2 : ℝ) ^ 527) :=
    Real.log_le_log (by positivity) hp
  rw [Real.log_pow, Real.log_pow] at h3
  push_cast at h3
  linarith

/-- The GRH upper bound simplified: for `L ≥ 5.664`, `s = √(9L²) = 3L` and `log q ≤ L`,
the right-hand side of `re_smoothPsi_le_of_zeroSum_le_of_logDeriv` (with `A = 2/3`,
`B = 1.097`, `D = 0.5708`) is at most `(3L + 2)(⅔L + 1.097) - 0.347`. -/
theorem clow_upper {L s lq : ℝ} (hL : 5.664 ≤ L) (hs0 : 0 ≤ s) (hs : s ^ 2 = 9 * L ^ 2)
    (hlq : lq ≤ L) :
    (s + 2 + 3 / (9 * L ^ 2)) * (2 / 3 * lq + 1.097) + 0.5708 - 1
        + (Real.log (9 * L ^ 2) + 13 / 6) / (9 * L ^ 2)
      ≤ (3 * L + 2) * (2 / 3 * L + 1.097) - 0.347 := by
  have h2u := Real.log_two_lt_d9
  have hs3 : s = 3 * L := by
    have h0 : (s - 3 * L) * (s + 3 * L) = 0 := by
      have : (s - 3 * L) * (s + 3 * L) = s ^ 2 - 9 * L ^ 2 := by ring
      rw [this, hs]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exfalso; linarith
  subst hs3
  have hx : (288 : ℝ) ≤ 9 * L ^ 2 := by nlinarith
  have hx0 : (0 : ℝ) < 9 * L ^ 2 := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 3 / (9 * L ^ 2) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hux : u * (9 * L ^ 2) = 3 := by rw [hu]; field_simp
  have hu1 : u ≤ 3 / 288 := by
    rw [hu]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have huL : u * L ≤ 0.06 := by
    have h50 : 0 ≤ 9 * L ^ 2 - 50 * L := by nlinarith
    have := mul_nonneg hu0 h50
    nlinarith
  have hR : (Real.log (9 * L ^ 2) + 13 / 6) / (9 * L ^ 2) ≤ 0.03 := by
    rw [div_le_iff₀ hx0]
    have hlog := clow_log_le_two_pow hx0 8
    push_cast at hlog
    linarith
  rw [← hu]
  have hpre : 0 ≤ 3 * L + 2 + u := by linarith
  have hmul : (3 * L + 2 + u) * (2 / 3 * lq + 1.097) ≤ (3 * L + 2 + u) * (2 / 3 * L + 1.097) :=
    mul_le_mul_of_nonneg_left (by linarith) hpre
  have hexp : (3 * L + 2 + u) * (2 / 3 * L + 1.097)
      = (3 * L + 2) * (2 / 3 * L + 1.097) + 2 / 3 * (u * L) + 1.097 * u := by ring
  linarith

/-- (§7.3) **GRH ⟹ character form of Bach's bound with `c = 9`** (sorry-free). -/
theorem bachBoundChar_of_GRH_c9 (hGRH : DirichletLZerosOnLine) : BachBoundChar 9 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hn289, hL⟩ := clow_log_ge hn χ hχ hcon
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have hn0 : 0 < n := by omega
  have hx288 : (288 : ℝ) < 9 * Real.log n ^ 2 := by nlinarith
  have hx0 : (0 : ℝ) < 9 * Real.log n ^ 2 := by linarith
  have hx1 : (1 : ℝ) ≤ 9 * Real.log n ^ 2 := by linarith
  have hs3 : √(9 * Real.log n ^ 2) = 3 * Real.log n := by
    rw [show 9 * Real.log n ^ 2 = (3 * Real.log n) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  have hlx2 : 2 ≤ Real.log (9 * Real.log n ^ 2) := by
    have h1 : Real.log ((2 : ℝ) ^ 8) ≤ Real.log (9 * Real.log n ^ 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hne1 : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, changeLevel_one]
  have hq : Real.log χ.conductor ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level)
  have hT := zeroSum_le_sharp32 hGRH χ.primitiveCharacter hprim hne1
  have hD := norm_logDeriv_LFunction_two_le_sharp χ.primitiveCharacter
  have hre := re_smoothPsi_le_of_zeroSum_le_of_logDeriv hGRH χ.primitiveCharacter hprim hne1
    hT hD hx1 hlx2
  have hup := clow_upper (L := Real.log n) (s := √(9 * Real.log n ^ 2))
    (lq := Real.log χ.conductor) (by linarith) (Real.sqrt_nonneg _)
    (Real.sq_sqrt hx0.le) hq
  have hU : (smoothPsi χ.primitiveCharacter (9 * Real.log n ^ 2)).re
      ≤ (3 * Real.log n + 2) * (2 / 3 * Real.log n + 1.097) - 0.347 := by linarith
  have hlow := re_smoothPsi_primitive_lower χ (x := 9 * Real.log n ^ 2) hx0 hcon
  rcases le_or_gt (9 * Real.log n ^ 2) 1536 with h1536 | h1536
  · have hψ := psiOne_lower_grid (x := 9 * Real.log n ^ 2) (by linarith) h1536
    rcases lt_or_ge n 2310 with hsmall | hbig
    · -- `n < 2310`: at most four prime factors
      have hcard : n.primeFactors.card ≤ 4 := by
        by_contra hc
        have := (cno_primorial_le_of_card hn0).2.2.2.2.1 (by omega)
        omega
      have hE := noncoprimeSum_le_omega_mul_log hn0 (x := 9 * Real.log n ^ 2) hx1
      have hcard' : (n.primeFactors.card : ℝ) ≤ 4 := by exact_mod_cast hcard
      have hlog0 : 0 ≤ Real.log (9 * Real.log n ^ 2) := by linarith
      have hE' : noncoprimeSum n (9 * Real.log n ^ 2) ≤ 4 * Real.log (9 * Real.log n ^ 2) :=
        hE.trans (mul_le_mul_of_nonneg_right hcard' hlog0)
      have hlog := clow_log_le_300 hx0
      nlinarith [sq_nonneg (Real.log n - 5.6656)]
    · -- `n ≥ 2310`
      have hL' : 7.62 ≤ Real.log n := by
        have hp : (2 : ℝ) ^ 11 ≤ (n : ℝ) := by
          have : (2310 : ℝ) ≤ n := by exact_mod_cast hbig
          linarith
        have h1 : Real.log ((2 : ℝ) ^ 11) ≤ Real.log n := Real.log_le_log (by norm_num) hp
        rw [Real.log_pow] at h1
        push_cast at h1
        linarith
      have hE := noncoprimeSum_le_of_ge_420_of_lt_65536 (n := n) hn0
        (x := 9 * Real.log n ^ 2) (by nlinarith) (by linarith)
      nlinarith [sq_nonneg (Real.log n - 7.62)]
  · have hE := noncoprimeSum_le_small (n := n) hn0 (9 * Real.log n ^ 2)
    have hL0 : 0 ≤ Real.log n := by linarith
    have a1 : (9 * Real.log n ^ 2 - 3) * 0.6931471803 ≤ (9 * Real.log n ^ 2 - 3) * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2l.le (by linarith)
    rcases le_or_gt (9 * Real.log n ^ 2) 2048 with h2048 | h2048
    · -- `1536 < x ≤ 2048`
      have hL' : 13.06 ≤ Real.log n := by nlinarith
      have hψ := psiOne_lower_1024 (x := 9 * Real.log n ^ 2) (by linarith)
      have hg : 239571 * 0.6931471803 / 2048 ≤ 239571 * Real.log 2 / (9 * Real.log n ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) hx0]
        nlinarith
      have hlog : Real.log (9 * Real.log n ^ 2) ≤ 11 * Real.log 2 := by
        have h1 : Real.log (9 * Real.log n ^ 2) ≤ Real.log ((2 : ℝ) ^ 11) :=
          Real.log_le_log hx0 (by linarith)
        rw [Real.log_pow] at h1
        push_cast at h1
        exact h1
      nlinarith [sq_nonneg (Real.log n - 13.06)]
    · rcases le_or_gt (9 * Real.log n ^ 2) 4096 with h4096 | h4096
      · -- `2048 < x ≤ 4096`
        have hL' : 15.08 ≤ Real.log n := by nlinarith
        have hψ := psiOne_lower_2048_of_le (x := 9 * Real.log n ^ 2) (X := 4096) h2048 h4096
        have hg : 946453 * 0.6931471803 / 4096 ≤ 946453 * Real.log 2 / 4096 := by linarith
        have hlog : Real.log (9 * Real.log n ^ 2) ≤ 12 * Real.log 2 := by
          have h1 : Real.log (9 * Real.log n ^ 2) ≤ Real.log ((2 : ℝ) ^ 12) :=
            Real.log_le_log hx0 (by linarith)
          rw [Real.log_pow] at h1
          push_cast at h1
          exact h1
        nlinarith [sq_nonneg (Real.log n - 15.08)]
      · -- `x > 4096`
        have hL' : 21.33 ≤ Real.log n := by nlinarith
        have hψ := psiOne_lower_integral (x := 9 * Real.log n ^ 2) hx1
        have hlog := clow_log_le_two_pow hx0 12
        push_cast at hlog
        nlinarith [sq_nonneg (Real.log n - 21.33)]

/-- **Main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's bound with the
explicit constant `c = 9`. -/
theorem grh_implies_bach_c9 : GRHImpliesBach 9 :=
  fun hGRH => bachBound_of_bachBoundChar (bachBoundChar_of_GRH_c9 hGRH)

/-! ## The constant `8` -/

/-- `log n ≥ lb` from `n ≥ N` and a certificate `2^k ≤ N^j` with `lb ≤ (k/j) · 0.6931471803`. -/
theorem clow_log_ge_of_pow {n N k j : ℕ} {lb : ℝ} (hN : N ≤ n) (hj : 0 < j)
    (hpow : 2 ^ k ≤ N ^ j) (hlb : lb * (j : ℝ) ≤ (k : ℝ) * 0.6931471803) :
    lb ≤ Real.log n := by
  have h2 := Real.log_two_gt_d9
  have hp : (2 : ℝ) ^ k ≤ (n : ℝ) ^ j := by
    exact_mod_cast hpow.trans (Nat.pow_le_pow_left hN j)
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((n : ℝ) ^ j) := Real.log_le_log (by positivity) hp
  rw [Real.log_pow, Real.log_pow] at h1
  have hk : (k : ℝ) * 0.6931471803 ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2.le (Nat.cast_nonneg k)
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have : lb * (j : ℝ) ≤ Real.log n * (j : ℝ) := by linarith
  exact le_of_mul_le_mul_right this hj'

/-- Bootstrap step for `c = 8` (same as `clow_boot_step`). -/
theorem clow8_boot_step {n N k j M : ℕ} {lb : ℝ} (hbig : 8 * Real.log n ^ 2 < n) (hN : N ≤ n)
    (hj : 0 < j) (hpow : 2 ^ k ≤ N ^ j) (hlb0 : 0 ≤ lb)
    (hlb : lb * (j : ℝ) ≤ (k : ℝ) * 0.6931471803) (hM : (M : ℝ) ≤ 8 * lb ^ 2) :
    lb ≤ Real.log n ∧ M + 1 ≤ n := by
  have hL := clow_log_ge_of_pow hN hj hpow hlb
  refine ⟨hL, ?_⟩
  have hlt : (M : ℝ) < n := by nlinarith [sq_nonneg (Real.log n - lb)]
  have : M < n := by exact_mod_cast hlt
  omega

/-- (§7.1, `c = 8`) If no unit `a < 8 (log n)²` has `χ a ≠ 1`, then `n ≥ 241` and
`log n ≥ 5.484`. -/
theorem clow8_log_ge {n : ℕ} (hn : 2 < n) (χ : DirichletCharacter ℂ n) (hχ : χ ≠ 1)
    (h : ∀ a : ℕ, (a : ℝ) < 8 * (Real.log n) ^ 2 → IsUnit (a : ZMod n) → χ (a : ZMod n) = 1) :
    241 ≤ n ∧ 5.484 ≤ Real.log n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod n)ˣ, χ u ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hχ (MulChar.ext fun a => by rw [hc a, MulChar.one_apply_coe])
  have hval : ¬ (((u : ZMod n).val : ℝ) < 8 * Real.log n ^ 2) := fun hlt => hu (by
    have h1 := h (u : ZMod n).val hlt (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    rwa [ZMod.natCast_zmod_val] at h1)
  have hlt : ((u : ZMod n).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
  have hbig : 8 * Real.log n ^ 2 < n := by linarith [not_lt.mp hval]
  have hn0 : (0 : ℝ) < n := by positivity
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  have h0 : 9 ≤ n := by
    have : (8 : ℝ) < n := by nlinarith
    have : 8 < n := by exact_mod_cast this
    omega
  obtain ⟨-, h1⟩ := clow8_boot_step (N := 9) (k := 1623) (j := 512) (M := 38) (lb := 2.19722)
    hbig h0 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h2⟩ := clow8_boot_step (N := 39) (k := 1353) (j := 256) (M := 107) (lb := 3.66339)
    hbig h1 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h3⟩ := clow8_boot_step (N := 108) (k := 1729) (j := 256) (M := 175) (lb := 4.68145)
    hbig h2 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h4⟩ := clow8_boot_step (N := 176) (k := 1909) (j := 256) (M := 213) (lb := 5.16882)
    hbig h3 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h5⟩ := clow8_boot_step (N := 214) (k := 1981) (j := 256) (M := 230) (lb := 5.36376)
    hbig h4 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h6⟩ := clow8_boot_step (N := 231) (k := 1005) (j := 128) (M := 236) (lb := 5.44228)
    hbig h5 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h7⟩ := clow8_boot_step (N := 237) (k := 4039) (j := 512) (M := 239) (lb := 5.46801)
    hbig h6 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h8⟩ := clow8_boot_step (N := 240) (k := 253) (j := 32) (M := 240) (lb := 5.48019)
    hbig h7 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h8, clow_log_ge_of_pow (N := 241) (k := 4051) (j := 512) h8 (by norm_num)
    (by decide +kernel) (by norm_num)⟩

/-! ### Numbers with four prime factors below `420` -/

theorem clow8_card_mul {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hpn : ¬ p ∣ n) :
    (p * n).primeFactors.card = n.primeFactors.card + 1 := by
  rw [Nat.primeFactors_mul hp.ne_zero hn.ne', hp.primeFactors,
    Finset.card_union_of_disjoint
      (Finset.disjoint_singleton_left.mpr fun h => hpn (Nat.dvd_of_mem_primeFactors h)),
    Finset.card_singleton, add_comm]

theorem clow8_primeFactors_mul {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m) :
    (p * m).primeFactors = m.primeFactors := by
  rw [Nat.primeFactors_mul hp.ne_zero hm.ne', hp.primeFactors]
  exact Finset.union_eq_right.mpr
    (Finset.singleton_subset_iff.mpr (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.ne'⟩))

/-- A number `n ≥ 241` with at least four distinct prime factors is either `≥ 420`, or
`≡ 2 (mod 4)` and `≥ 330` (in fact `n ∈ {330, 390}`). -/
theorem clow8_omega4 {n : ℕ} (h241 : 241 ≤ n) (hcard : 4 ≤ n.primeFactors.card) :
    (n % 4 = 2 ∧ 330 ≤ n) ∨ 420 ≤ n := by
  by_contra hcon
  have h2 : 2 ∣ n := by
    by_contra h
    have hc := clow8_card_mul Nat.prime_two (by omega : 0 < n) h
    have := (cno_primorial_le_of_card (show 0 < 2 * n by omega)).2.2.2.2.1 (by omega)
    omega
  obtain ⟨m, rfl⟩ := h2
  have hm2 : ¬ 2 ∣ m := by
    intro h
    have he := clow8_primeFactors_mul Nat.prime_two (by omega : 0 < m) h
    rw [he] at hcard
    have := (cno_primorial_le_of_card (show 0 < m by omega)).2.2.2.1 hcard
    omega
  have hcm : 3 ≤ m.primeFactors.card := by
    have := clow8_card_mul Nat.prime_two (by omega : 0 < m) hm2
    omega
  have hm : m < 165 := by omega
  have h3 : 3 ∣ m := by
    by_contra h
    have c1 := clow8_card_mul Nat.prime_three (by omega : 0 < m) h
    have c2 := clow8_card_mul Nat.prime_two (by omega : 0 < 3 * m) (by omega)
    have := (cno_primorial_le_of_card (show 0 < 2 * (3 * m) by omega)).2.2.2.2.1 (by omega)
    omega
  obtain ⟨k, rfl⟩ := h3
  have hk3 : ¬ 3 ∣ k := by
    intro h
    have he := clow8_primeFactors_mul Nat.prime_three (by omega : 0 < k) h
    rw [he] at hcm
    have c2 := clow8_card_mul Nat.prime_two (by omega : 0 < k) (by omega)
    have := (cno_primorial_le_of_card (show 0 < 2 * k by omega)).2.2.2.1 (by omega)
    omega
  have hck : 2 ≤ k.primeFactors.card := by
    have := clow8_card_mul Nat.prime_three (by omega : 0 < k) hk3
    omega
  have h5 : 5 ∣ k := by
    by_contra h
    have c1 := clow8_card_mul Nat.prime_five (by omega : 0 < k) h
    have c2 := clow8_card_mul Nat.prime_three (by omega : 0 < 5 * k) (by omega)
    have c3 := clow8_card_mul Nat.prime_two (by omega : 0 < 3 * (5 * k)) (by omega)
    have := (cno_primorial_le_of_card (show 0 < 2 * (3 * (5 * k)) by omega)).2.2.2.2.1
      (by omega)
    omega
  obtain ⟨j, rfl⟩ := h5
  omega

/-- No primitive character has conductor `≡ 2 (mod 4)`: for `n ≡ 2 (mod 4)` every character
mod `n` factors through `n / 2`. -/
theorem clow8_conductor_le {n : ℕ} (hn : n % 4 = 2) (χ : DirichletCharacter ℂ n) :
    χ.conductor ≤ n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hm : m % 2 = 1 := by omega
  have : NeZero m := ⟨by omega⟩
  have : NeZero (2 * m) := ⟨by omega⟩
  have hd : m ∣ 2 * m := Dvd.intro_left 2 rfl
  have hinj : Function.Injective (ZMod.unitsMap hd) := by
    have hs := ZMod.unitsMap_surjective hd
    have hcard : Fintype.card (ZMod (2 * m))ˣ = Fintype.card (ZMod m)ˣ := by
      rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
        Nat.totient_mul (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hm)), Nat.totient_two, one_mul]
    exact ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hs, hcard⟩).1
  have hF : χ.FactorsThrough m := by
    refine (factorsThrough_iff_ker_unitsMap (χ := χ) hd).mpr ?_
    rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
    exact bot_le
  have : χ.conductor ≤ m := Nat.sInf_le ((mem_conductorSet_iff χ).mpr hF)
  omega

/-! ### `ψ₁` on `(240, 1536]` -/

theorem clow8_cert_240 : 2 ^ 40863 ≤ (lcmProd 240).2 ∧ 2 ^ 2754 ≤ (lcmProd 240).1 ^ 8 := by
  decide +kernel

theorem clow8_psiOne_mul_240 {x : ℝ} (hx : 240 < x) : 238.615 * x - 28944 ≤ x * psiOne x :=
  psiOneGrid_mul clow8_cert_240.1 clow8_cert_240.2 (by norm_num) (by norm_num)
    (by push_cast; exact hx)

/-- `ψ₁(x) ≥ x/2 - 2.6` on `(240, 1536]`. -/
theorem clow8_psiOne_half {x : ℝ} (hx : 240 < x) (hx' : x ≤ 1536) : x / 2 - 2.6 ≤ psiOne x := by
  rcases le_or_gt x 256 with h | h
  · have h1 := clow8_psiOne_mul_240 hx
    have hx0 : (0 : ℝ) < x := by linarith
    refine le_of_mul_le_mul_left ?_ hx0
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr h)]
  · exact psiOne_lower_grid h hx'

/-- Chord bound for `1/x` on `[a, b]`. -/
theorem clow8_inv_chord {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    1 / x ≤ 1 / a + 1 / b - x / (a * b) := by
  have hx : 0 < x := by linarith
  have hb : 0 < b := by linarith
  have key : 1 / a + 1 / b - x / (a * b) - 1 / x = (x - a) * (b - x) / (a * b * x) := by
    field_simp
    ring
  have : 0 ≤ (x - a) * (b - x) / (a * b * x) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

/-! ### The upper bound and the main theorem -/

theorem clow8_sqrt_le {L s : ℝ} (hL : 0 ≤ L) (hs : s ^ 2 = 8 * L ^ 2) : s ≤ 2.8285 * L := by
  by_contra hc
  push Not at hc
  have hp : 0 < (s - 2.8285 * L) * (s + 2.8285 * L) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- The GRH upper bound simplified (`c = 8`): for `L ≥ 5.48`, `s = √(8L²)` and
`0 ≤ lq ≤ L`, the right-hand side of `re_smoothPsi_le_of_zeroSum_le_of_logDeriv` is at most
`(2.8285 L + 2)(⅔ lq + 1.097) - 0.336`. -/
theorem clow8_upper {L s lq : ℝ} (hL : 5.48 ≤ L) (_hs0 : 0 ≤ s) (hs : s ^ 2 = 8 * L ^ 2)
    (hlq0 : 0 ≤ lq) (hlq : lq ≤ L) :
    (s + 2 + 3 / (8 * L ^ 2)) * (2 / 3 * lq + 1.097) + 0.5708 - 1
        + (Real.log (8 * L ^ 2) + 13 / 6) / (8 * L ^ 2)
      ≤ (2.8285 * L + 2) * (2 / 3 * lq + 1.097) - 0.336 := by
  have h2u := Real.log_two_lt_d9
  have hsr := clow8_sqrt_le (by linarith) hs
  have hx : (240 : ℝ) ≤ 8 * L ^ 2 := by nlinarith
  have hx0 : (0 : ℝ) < 8 * L ^ 2 := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 3 / (8 * L ^ 2) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hux : u * (8 * L ^ 2) = 3 := by rw [hu]; field_simp
  have hu1 : u ≤ 3 / 240 := by
    rw [hu]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have huL : u * L ≤ 0.0685 := by
    have h50 : 0 ≤ 8 * L ^ 2 - 43.8 * L := by nlinarith
    have := mul_nonneg hu0 h50
    nlinarith
  have hulq : u * lq ≤ u * L := mul_le_mul_of_nonneg_left hlq hu0
  have hR : (Real.log (8 * L ^ 2) + 13 / 6) / (8 * L ^ 2) ≤ 0.033 := by
    rw [div_le_iff₀ hx0]
    have hlog := clow_log_le_two_pow hx0 8
    push_cast at hlog
    linarith
  rw [← hu]
  have hY : 0 ≤ 2 / 3 * lq + 1.097 := by linarith
  have hmul : (s + 2 + u) * (2 / 3 * lq + 1.097) ≤ (2.8285 * L + 2 + u) * (2 / 3 * lq + 1.097) :=
    mul_le_mul_of_nonneg_right (by linarith) hY
  have hexp : (2.8285 * L + 2 + u) * (2 / 3 * lq + 1.097)
      = (2.8285 * L + 2) * (2 / 3 * lq + 1.097) + 2 / 3 * (u * lq) + 1.097 * u := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- (§7.3) **GRH ⟹ character form of Bach's bound with `c = 8`** (sorry-free). -/
theorem bachBoundChar_of_GRH_c8 (hGRH : DirichletLZerosOnLine) : BachBoundChar 8 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hn241, hL⟩ := clow8_log_ge hn χ hχ hcon
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have hn0 : 0 < n := by omega
  have hL0 : 0 ≤ Real.log n := by linarith
  have hx240 : (240 : ℝ) < 8 * Real.log n ^ 2 := by
    linarith [sq_nonneg (Real.log n - 5.484)]
  have hx0 : (0 : ℝ) < 8 * Real.log n ^ 2 := by linarith
  have hx1 : (1 : ℝ) ≤ 8 * Real.log n ^ 2 := by linarith
  have hs0 := Real.sqrt_nonneg (8 * Real.log n ^ 2)
  have hsq := Real.sq_sqrt hx0.le
  have hsr := clow8_sqrt_le hL0 hsq
  have hlx2 : 2 ≤ Real.log (8 * Real.log n ^ 2) := by
    have h1 : Real.log ((2 : ℝ) ^ 7) ≤ Real.log (8 * Real.log n ^ 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlog0 : 0 ≤ Real.log (8 * Real.log n ^ 2) := by linarith
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hne1 : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, changeLevel_one]
  have hq0' : (0 : ℝ) < (χ.conductor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hq0 : 0 ≤ Real.log χ.conductor := Real.log_natCast_nonneg _
  have hq : Real.log χ.conductor ≤ Real.log n :=
    Real.log_le_log hq0' (by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level)
  have hT := zeroSum_le_sharp32 hGRH χ.primitiveCharacter hprim hne1
  have hD := norm_logDeriv_LFunction_two_le_sharp χ.primitiveCharacter
  have hre := re_smoothPsi_le_of_zeroSum_le_of_logDeriv hGRH χ.primitiveCharacter hprim hne1
    hT hD hx1 hlx2
  have hup := clow8_upper (L := Real.log n) (s := √(8 * Real.log n ^ 2))
    (lq := Real.log χ.conductor) (by linarith) hs0 hsq hq0 hq
  have hpre : 0 ≤ 2.8285 * Real.log n + 2 := by linarith
  have hUq : (smoothPsi χ.primitiveCharacter (8 * Real.log n ^ 2)).re
      ≤ (2.8285 * Real.log n + 2) * (2 / 3 * Real.log χ.conductor + 1.097) - 0.336 := by
    linarith
  have hU : (smoothPsi χ.primitiveCharacter (8 * Real.log n ^ 2)).re
      ≤ (2.8285 * Real.log n + 2) * (2 / 3 * Real.log n + 1.097) - 0.336 := by
    have := mul_le_mul_of_nonneg_left
      (show 2 / 3 * Real.log χ.conductor + 1.097 ≤ 2 / 3 * Real.log n + 1.097 by linarith) hpre
    linarith
  have hlow := re_smoothPsi_primitive_lower χ (x := 8 * Real.log n ^ 2) hx0 hcon
  rcases le_or_gt (8 * Real.log n ^ 2) 1536 with h1536 | h1536
  · have hψ := clow8_psiOne_half (x := 8 * Real.log n ^ 2) hx240 h1536
    rcases lt_or_ge n 2310 with hsmall | hbig
    · have hEω := noncoprimeSum_le_omega_mul_log hn0 (x := 8 * Real.log n ^ 2) hx1
      rcases Nat.lt_or_ge n.primeFactors.card 4 with hc3 | hc4
      · -- at most three prime factors
        have hcard' : (n.primeFactors.card : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.mp hc3
        have hE' : noncoprimeSum n (8 * Real.log n ^ 2) ≤ 3 * Real.log (8 * Real.log n ^ 2) :=
          hEω.trans (mul_le_mul_of_nonneg_right hcard' hlog0)
        have hlog := clow_log_le_two_pow hx0 8
        push_cast at hlog
        linarith [sq_nonneg (Real.log n - 5.484)]
      · -- exactly four prime factors
        have hcard : n.primeFactors.card ≤ 4 := by
          by_contra hc
          have := (cno_primorial_le_of_card hn0).2.2.2.2.1 (by omega)
          omega
        have hcard' : (n.primeFactors.card : ℝ) ≤ 4 := by exact_mod_cast hcard
        have hE' : noncoprimeSum n (8 * Real.log n ^ 2) ≤ 4 * Real.log (8 * Real.log n ^ 2) :=
          hEω.trans (mul_le_mul_of_nonneg_right hcard' hlog0)
        have hlog := clow_log_le_300 hx0
        rcases clow8_omega4 hn241 hc4 with ⟨hmod, h330⟩ | h420
        · -- `n ≡ 2 (mod 4)`, `n ≥ 330`: the conductor is at most `n / 2`
          have hL' : 5.798 ≤ Real.log n :=
            clow_log_ge_of_pow (N := 330) (k := 4283) (j := 512) h330 (by norm_num)
              (by decide +kernel) (by norm_num)
          have hc2 := clow8_conductor_le hmod χ
          have hc2' : (χ.conductor : ℝ) ≤ (n : ℝ) / 2 :=
            le_trans (by exact_mod_cast hc2) Nat.cast_div_le
          have hq2 : Real.log χ.conductor ≤ Real.log n - Real.log 2 := by
            have := Real.log_le_log hq0' hc2'
            rwa [Real.log_div (by positivity) (by norm_num)] at this
          have hU2 : (smoothPsi χ.primitiveCharacter (8 * Real.log n ^ 2)).re
              ≤ (2.8285 * Real.log n + 2) * (2 / 3 * (Real.log n - 0.6931) + 1.097) - 0.336 := by
            have := mul_le_mul_of_nonneg_left
              (show 2 / 3 * Real.log χ.conductor + 1.097
                ≤ 2 / 3 * (Real.log n - 0.6931) + 1.097 by linarith) hpre
            linarith
          linarith [sq_nonneg (Real.log n - 5.798)]
        · have hL' : 6.039 ≤ Real.log n :=
            clow_log_ge_of_pow (N := 420) (k := 4461) (j := 512) h420 (by norm_num)
              (by decide +kernel) (by norm_num)
          rcases le_or_gt (8 * Real.log n ^ 2) 304 with h304 | h304
          · -- `n ≥ 420`, `x ≤ 304`: the grid cell `K = 288` with a chord for `1/x`
            have hx291 : (291.5 : ℝ) ≤ 8 * Real.log n ^ 2 := by
              linarith [sq_nonneg (Real.log n - 6.039)]
            have hψ' := psiOne_lower_grid_288 (x := 8 * Real.log n ^ 2) (by linarith)
            have hch := clow8_inv_chord (a := 291.5) (b := 304) (by norm_num) hx291 h304
            have hch' : 42761 / (8 * Real.log n ^ 2)
                ≤ 42761 * (1 / 291.5 + 1 / 304 - 8 * Real.log n ^ 2 / (291.5 * 304)) := by
              rw [div_eq_mul_one_div]
              exact mul_le_mul_of_nonneg_left hch (by norm_num)
            linarith [sq_nonneg (Real.log n - 6.039)]
          · have hL'' : 6.164 ≤ Real.log n := by nlinarith
            linarith [sq_nonneg (Real.log n - 6.164)]
    · -- `n ≥ 2310`
      have hL' : 7.62 ≤ Real.log n :=
        clow_log_ge_of_pow (N := 2310) (k := 11) (j := 1) hbig (by norm_num)
          (by decide +kernel) (by norm_num)
      have hE := noncoprimeSum_le_of_ge_420_of_lt_65536 (n := n) hn0
        (x := 8 * Real.log n ^ 2) (by linarith [sq_nonneg (Real.log n - 7.62)]) (by linarith)
      linarith [sq_nonneg (Real.log n - 7.62)]
  · have a1 : (8 * Real.log n ^ 2 - 3) * 0.6931471803 ≤ (8 * Real.log n ^ 2 - 3) * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2l.le (by linarith)
    rcases le_or_gt (8 * Real.log n ^ 2) 2048 with h2048 | h2048
    · -- `1536 < x ≤ 2048`
      have hL' : 13.85 ≤ Real.log n := by nlinarith
      have hE := noncoprimeSum_le_of_ge_420_of_lt_65536 (n := n) hn0
        (x := 8 * Real.log n ^ 2) (by linarith) (by linarith)
      have hψ := psiOne_lower_1024 (x := 8 * Real.log n ^ 2) (by linarith)
      have hg : 239571 * 0.6931471803 / 2048 ≤ 239571 * Real.log 2 / (8 * Real.log n ^ 2) := by
        exact div_le_div₀ (by positivity) (by linarith) hx0 h2048
      have hlog : Real.log (8 * Real.log n ^ 2) ≤ 11 * Real.log 2 := by
        have h1 : Real.log (8 * Real.log n ^ 2) ≤ Real.log ((2 : ℝ) ^ 11) :=
          Real.log_le_log hx0 (by linarith)
        rw [Real.log_pow] at h1
        push_cast at h1
        exact h1
      linarith [sq_nonneg (Real.log n - 13.85)]
    · have hE := noncoprimeSum_le_small (n := n) hn0 (8 * Real.log n ^ 2)
      rcases le_or_gt (8 * Real.log n ^ 2) 4096 with h4096 | h4096
      · -- `2048 < x ≤ 4096`
        have hL' : 15.99 ≤ Real.log n := by nlinarith
        have hψ := psiOne_lower_2048_of_le (x := 8 * Real.log n ^ 2) (X := 4096) h2048 h4096
        have hg : 946453 * 0.6931471803 / 4096 ≤ 946453 * Real.log 2 / 4096 := by linarith
        have hlog : Real.log (8 * Real.log n ^ 2) ≤ 12 * Real.log 2 := by
          have h1 : Real.log (8 * Real.log n ^ 2) ≤ Real.log ((2 : ℝ) ^ 12) :=
            Real.log_le_log hx0 (by linarith)
          rw [Real.log_pow] at h1
          push_cast at h1
          exact h1
        linarith [sq_nonneg (Real.log n - 15.99)]
      · -- `x > 4096`
        have hL' : 22.62 ≤ Real.log n := by nlinarith
        have hψ := psiOne_lower_integral (x := 8 * Real.log n ^ 2) hx1
        have hlog := clow_log_le_two_pow hx0 12
        push_cast at hlog
        linarith [sq_nonneg (Real.log n - 22.62)]

/-- **Main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's bound with the
explicit constant `c = 8`. -/
theorem grh_implies_bach_c8 : GRHImpliesBach 8 :=
  fun hGRH => bachBound_of_bachBoundChar (bachBoundChar_of_GRH_c8 hGRH)

end DetPrimality.Bach
