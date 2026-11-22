import DetPrimality.CompositeInterface
import DetPrimality.Bach.CompositeReduction
import DetPrimality.Bach.SharpZeroSum
import DetPrimality.Bach.SharpExplicit
import DetPrimality.Bach.ConstPsiOne
import DetPrimality.Bach.ConstPsiOneSharp
import DetPrimality.Bach.ConstPsiOneGrid

/-!
# GRH ⟹ Bach's Theorem 2 form (composite moduli) with `c = 4`

Main results: `bachBoundCharComposite_of_GRH_c4 : BachBoundCharComposite 4` (under GRH) and
`grh_implies_bach_composite_c4 : GRHImpliesBachComposite 4`.

Let `n > 2` be composite, `χ ≠ 1` mod `n`, `L = log n`, `x = 4 L²` (so `√x = 2L`), and assume
`χ a = 1` for all `1 ≤ a < x`.  By `CompositeReduction.lean`:

* `x² ≤ n`, hence `n ≥ 463371`, `L ≥ 13.04524`, `x > 680` (`compred_log_ge_c4`);
* `ψ₁(x) ≤ Re ψ̃(x, χ*)` with **no** non-coprime correction (`compred_psiOne_le`).

Upper bound (GRH; `re_smoothPsi_le_of_zeroSum_le_of_logDeriv`, `zeroSum_le_sharp32`,
`norm_logDeriv_LFunction_two_le_sharp`), simplified in `ccomp4_upper`:

  `Re ψ̃(x, χ*) ≤ W(L) := (2L + 2)(⅔ L + 1.097) - 0.37`.

The contradiction is `W(L) < ψ₁(4L²)` (`ccomp4_final`), proved on ranges of `x = 4L²`; in each
range the claim is reduced to a quadratic inequality in `L`, closed by a tangent
`L² ≥ 2 m L - m²` and `linarith` (`log x ≤ k log 2 + x/2^k - 1` for a suitable `k`):

| range of `x`          | `ψ₁` bound                              | margin    |
|-----------------------|-----------------------------------------|-----------|
| `680 < x ≤ 1536`      | `psiOne_lower_grid` (`x/2 - 2.6`)       | ≈ 63      |
| `1536 < x ≤ 2048`     | `psiOne_lower_1024` (gain at `2048`)    | ≈ 17.8    |
| `2048 < x ≤ 24576`    | `psiOne_lower_2048_of_le`, 11 intervals | ≥ 4.7     |
| `x > 24576`           | `psiOne_lower_integral`                 | ≥ 35.8    |

The true margin is smallest (`≈ 8`) near `x ≈ 11500`: there `ψ₁(x) ≈ (log 2 / 2) x + 656031/x`
is the Chebyshev-type bound with the `lcmProd 2048` certificate, and the intervals
`(8704, 15616]` have to be short.  With these inputs `c = 4` is essentially optimal: the leading
terms are `(log 2 / 2) c L²` against `⅔ √c L²`, which needs `c > 3.70` (and `c ≥ 3.9` or so once
the linear term is included at realistic sizes).
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- Tangent bound `log x ≤ k log 2 + x / 2^k - 1` for `x > 0`. -/
theorem ccomp_log_le_two_pow {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.log x ≤ k * Real.log 2 + x / 2 ^ k - 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 2 ^ k by positivity)
  rw [Real.log_div hx.ne' (by positivity), Real.log_pow] at h1
  linarith

theorem ccomp_le_of_sq_lt {L lo X0 : ℝ} (hL : 0 ≤ L) (hlo : 4 * lo ^ 2 ≤ X0)
    (h : X0 < 4 * L ^ 2) : lo ≤ L := by
  by_contra hc
  push Not at hc
  nlinarith [mul_pos (sub_pos.mpr hc) (show 0 < lo + L by linarith)]

theorem ccomp_le_of_sq_le {L hi X : ℝ} (hhi : 0 ≤ hi) (hX : X ≤ 4 * hi ^ 2)
    (h : 4 * L ^ 2 ≤ X) : L ≤ hi := by
  by_contra hc
  push Not at hc
  nlinarith [mul_pos (sub_pos.mpr hc) (show 0 < L + hi by linarith)]

/-- The GRH upper bound simplified (`c = 4`): for `L ≥ 13.04`, `√(4L²) = 2L` and `log q ≤ L`,
the right-hand side of `re_smoothPsi_le_of_zeroSum_le_of_logDeriv` (with `A = 2/3`,
`B = 1.097`, `D = 0.5708`) is at most `(2L + 2)(⅔L + 1.097) - 0.37`. -/
theorem ccomp4_upper {L lq : ℝ} (hL : 13.04 ≤ L) (hlq : lq ≤ L) :
    (2 * L + 2 + 3 / (4 * L ^ 2)) * (2 / 3 * lq + 1.097) + 0.5708 - 1
        + (Real.log (4 * L ^ 2) + 13 / 6) / (4 * L ^ 2)
      ≤ (2 * L + 2) * (2 / 3 * L + 1.097) - 0.37 := by
  have h2u := Real.log_two_lt_d9
  have hx : (680 : ℝ) ≤ 4 * L ^ 2 := by nlinarith
  have hx0 : (0 : ℝ) < 4 * L ^ 2 := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 3 / (4 * L ^ 2) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hux : u * (4 * L ^ 2) = 3 := by rw [hu]; field_simp
  have hu1 : u ≤ 3 / 680 := by
    rw [hu]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have huL : u * L ≤ 0.0577 := by
    have h52 : 0 ≤ 4 * L ^ 2 - 52 * L := by nlinarith
    have := mul_nonneg hu0 h52
    nlinarith
  have hR : (Real.log (4 * L ^ 2) + 13 / 6) / (4 * L ^ 2) ≤ 0.013 := by
    rw [div_le_iff₀ hx0]
    have hlog := ccomp_log_le_two_pow hx0 9
    push_cast at hlog
    linarith
  rw [← hu]
  have hpre : 0 ≤ 2 * L + 2 + u := by linarith
  have hmul : (2 * L + 2 + u) * (2 / 3 * lq + 1.097) ≤ (2 * L + 2 + u) * (2 / 3 * L + 1.097) :=
    mul_le_mul_of_nonneg_left (by linarith) hpre
  have hexp : (2 * L + 2 + u) * (2 / 3 * L + 1.097)
      = (2 * L + 2) * (2 / 3 * L + 1.097) + 2 / 3 * (u * L) + 1.097 * u := by ring
  linarith

/-- `W(L) < ψ₁(4L²)` for `680 < 4L² ≤ 2048`. -/
theorem ccomp4_low {L : ℝ} (hL : 13.04 ≤ L) (hx' : 4 * L ^ 2 ≤ 2048) :
    (2 * L + 2) * (2 / 3 * L + 1.097) - 0.37 < psiOne (4 * L ^ 2) := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have hL0 : 0 ≤ L := by linarith
  have hx680 : (680 : ℝ) < 4 * L ^ 2 := by linarith [sq_nonneg (L - 13.04)]
  have hx0 : (0 : ℝ) < 4 * L ^ 2 := by linarith
  rcases le_or_gt (4 * L ^ 2) 1536 with h | h
  · -- `680 < x ≤ 1536`
    have hψ := psiOne_lower_grid (x := 4 * L ^ 2) (by linarith) h
    linarith [sq_nonneg (L - 13.04)]
  · -- `1536 < x ≤ 2048`
    have hlo : 19.59 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h
    have hhi : L ≤ 22.63 := ccomp_le_of_sq_le (by norm_num) (by norm_num) hx'
    have hψ := psiOne_lower_1024 (x := 4 * L ^ 2) (by linarith)
    have hg : 239571 * Real.log 2 / 2048 ≤ 239571 * Real.log 2 / (4 * L ^ 2) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (by linarith)) hx0 hx'
    have a1 : (4 * L ^ 2 - 3) * 0.6931471803 ≤ (4 * L ^ 2 - 3) * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2l.le (by linarith)
    have hlog := ccomp_log_le_two_pow hx0 11
    push_cast at hlog
    linarith [sq_nonneg (L - 21.11)]

set_option maxHeartbeats 1000000 in
/-- `W(L) < ψ₁(4L²)` for `2048 < 4L² ≤ 24576` (eleven intervals, `psiOne_lower_2048_of_le`). -/
theorem ccomp4_mid {L : ℝ} (hL : 13.04 ≤ L) (hx : 2048 < 4 * L ^ 2) (hx' : 4 * L ^ 2 ≤ 24576) :
    (2 * L + 2) * (2 / 3 * L + 1.097) - 0.37 < psiOne (4 * L ^ 2) := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have hL0 : 0 ≤ L := by linarith
  have hx0 : (0 : ℝ) < 4 * L ^ 2 := by linarith
  have a1 : (4 * L ^ 2 - 3) * 0.6931471803 ≤ (4 * L ^ 2 - 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2l.le (by linarith)
  rcases le_or_gt (4 * L ^ 2) 8704 with h8704 | h8704
  · -- `2048 < x ≤ 8704`, margin ≈ 4.8
    have hlo : 22.62 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) hx
    have hhi : L ≤ 46.65 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h8704
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 8704) (by linarith) h8704
    have hlog := ccomp_log_le_two_pow hx0 11
    push_cast at hlog
    linarith [sq_nonneg (L - 34.63)]
  rcases le_or_gt (4 * L ^ 2) 9728 with h9728 | h9728
  · -- `8704 < x ≤ 9728`, margin ≈ 6.1
    have hlo : 46.64 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h8704
    have hhi : L ≤ 49.32 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h9728
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 9728) (by linarith) h9728
    have hlog := ccomp_log_le_two_pow hx0 13
    push_cast at hlog
    linarith [sq_nonneg (L - 47.98)]
  rcases le_or_gt (4 * L ^ 2) 10496 with h10496 | h10496
  · -- `9728 < x ≤ 10496`, margin ≈ 5.2
    have hlo : 49.31 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h9728
    have hhi : L ≤ 51.23 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h10496
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 10496) (by linarith) h10496
    have hlog := ccomp_log_le_two_pow hx0 13
    push_cast at hlog
    linarith [sq_nonneg (L - 50.27)]
  rcases le_or_gt (4 * L ^ 2) 11008 with h11008 | h11008
  · -- `10496 < x ≤ 11008`, margin ≈ 5.7
    have hlo : 51.22 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h10496
    have hhi : L ≤ 52.46 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h11008
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 11008) (by linarith) h11008
    have hlog := ccomp_log_le_two_pow hx0 13
    push_cast at hlog
    linarith [sq_nonneg (L - 51.84)]
  rcases le_or_gt (4 * L ^ 2) 11520 with h11520 | h11520
  · -- `11008 < x ≤ 11520`, margin ≈ 5.4
    have hlo : 52.45 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h11008
    have hhi : L ≤ 53.67 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h11520
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 11520) (by linarith) h11520
    have hlog := ccomp_log_le_two_pow hx0 13
    push_cast at hlog
    linarith [sq_nonneg (L - 53.06)]
  rcases le_or_gt (4 * L ^ 2) 12032 with h12032 | h12032
  · -- `11520 < x ≤ 12032`, margin ≈ 5.5
    have hlo : 53.66 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h11520
    have hhi : L ≤ 54.85 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h12032
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 12032) (by linarith) h12032
    have hlog := ccomp_log_le_two_pow hx0 14
    push_cast at hlog
    linarith [sq_nonneg (L - 54.25)]
  rcases le_or_gt (4 * L ^ 2) 12800 with h12800 | h12800
  · -- `12032 < x ≤ 12800`, margin ≈ 4.7
    have hlo : 54.84 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h12032
    have hhi : L ≤ 56.57 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h12800
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 12800) (by linarith) h12800
    have hlog := ccomp_log_le_two_pow hx0 14
    push_cast at hlog
    linarith [sq_nonneg (L - 55.7)]
  rcases le_or_gt (4 * L ^ 2) 13824 with h13824 | h13824
  · -- `12800 < x ≤ 13824`, margin ≈ 5.0
    have hlo : 56.56 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h12800
    have hhi : L ≤ 58.79 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h13824
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 13824) (by linarith) h13824
    have hlog := ccomp_log_le_two_pow hx0 14
    push_cast at hlog
    linarith [sq_nonneg (L - 57.67)]
  rcases le_or_gt (4 * L ^ 2) 15616 with h15616 | h15616
  · -- `13824 < x ≤ 15616`, margin ≈ 5.1
    have hlo : 58.78 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h13824
    have hhi : L ≤ 62.49 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h15616
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 15616) (by linarith) h15616
    have hlog := ccomp_log_le_two_pow hx0 14
    push_cast at hlog
    linarith [sq_nonneg (L - 60.63)]
  rcases le_or_gt (4 * L ^ 2) 20480 with h20480 | h20480
  · -- `15616 < x ≤ 20480`, margin ≈ 4.8
    have hlo : 62.48 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h15616
    have hhi : L ≤ 71.56 := ccomp_le_of_sq_le (by norm_num) (by norm_num) h20480
    have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 20480) (by linarith) h20480
    have hlog := ccomp_log_le_two_pow hx0 14
    push_cast at hlog
    linarith [sq_nonneg (L - 67.01)]
  -- `20480 < x ≤ 24576`, margin ≈ 32.0
  have hlo : 71.55 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) h20480
  have hhi : L ≤ 78.39 := ccomp_le_of_sq_le (by norm_num) (by norm_num) hx'
  have hψ := psiOne_lower_2048_of_le (x := 4 * L ^ 2) (X := 24576) (by linarith) hx'
  have hlog := ccomp_log_le_two_pow hx0 14
  push_cast at hlog
  linarith [sq_nonneg (L - 74.96)]

/-- `W(L) < ψ₁(4L²)` for `4L² > 24576` (`psiOne_lower_integral`). -/
theorem ccomp4_high {L : ℝ} (hL : 13.04 ≤ L) (hx : 24576 < 4 * L ^ 2) :
    (2 * L + 2) * (2 / 3 * L + 1.097) - 0.37 < psiOne (4 * L ^ 2) := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have hL0 : 0 ≤ L := by linarith
  have hx0 : (0 : ℝ) < 4 * L ^ 2 := by linarith
  have a1 : (4 * L ^ 2 - 3) * 0.6931471803 ≤ (4 * L ^ 2 - 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2l.le (by linarith)
  have hlo : 78.38 ≤ L := ccomp_le_of_sq_lt hL0 (by norm_num) hx
  have hψ := psiOne_lower_integral (x := 4 * L ^ 2) (by linarith)
  have hlog := ccomp_log_le_two_pow hx0 15
  push_cast at hlog
  linarith [sq_nonneg (L - 78.38)]

/-- The final numerical inequality for `c = 4`: `W(L) < ψ₁(4L²)` for all `L ≥ 13.04`. -/
theorem ccomp4_final {L : ℝ} (hL : 13.04 ≤ L) :
    (2 * L + 2) * (2 / 3 * L + 1.097) - 0.37 < psiOne (4 * L ^ 2) := by
  rcases le_or_gt (4 * L ^ 2) 2048 with h1 | h1
  · exact ccomp4_low hL h1
  rcases le_or_gt (4 * L ^ 2) 24576 with h2 | h2
  · exact ccomp4_mid hL h1 h2
  · exact ccomp4_high hL h2

/-- **GRH ⟹ Bach's Theorem 2 form for composite moduli with `c = 4`** (sorry-free). -/
theorem bachBoundCharComposite_of_GRH_c4 (hGRH : DirichletLZerosOnLine) :
    BachBoundCharComposite 4 := by
  intro n hn hnp χ hχ
  by_contra hcon
  push Not at hcon
  have hbig := compred_bootstrap_hyp hn hnp χ (c := 4) (by norm_num) hcon
  obtain ⟨-, hL⟩ := compred_log_ge_c4 hn hbig
  have h2l := Real.log_two_gt_d9
  have hL' : 13.04 ≤ Real.log n := by linarith
  have hx680 : (680 : ℝ) < 4 * Real.log n ^ 2 := by linarith [sq_nonneg (Real.log n - 13.04)]
  have hx0 : (0 : ℝ) < 4 * Real.log n ^ 2 := by linarith
  have hx1 : (1 : ℝ) ≤ 4 * Real.log n ^ 2 := by linarith
  have hs : √(4 * Real.log n ^ 2) = 2 * Real.log n := by
    rw [show 4 * Real.log n ^ 2 = (2 * Real.log n) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  have hlx2 : 2 ≤ Real.log (4 * Real.log n ^ 2) := by
    have h1 : Real.log ((2 : ℝ) ^ 9) ≤ Real.log (4 * Real.log n ^ 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have : NeZero n := ⟨by omega⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨hprim, hne1, -, hq⟩ := compred_primitive_facts (by omega) χ hχ
  have hT := zeroSum_le_sharp32 hGRH χ.primitiveCharacter hprim hne1
  have hD := norm_logDeriv_LFunction_two_le_sharp χ.primitiveCharacter
  have hre := re_smoothPsi_le_of_zeroSum_le_of_logDeriv hGRH χ.primitiveCharacter hprim hne1
    hT hD hx1 hlx2
  rw [hs] at hre
  have hup := ccomp4_upper (L := Real.log n) (lq := Real.log χ.conductor) hL' hq
  have hlow := compred_psiOne_le (by omega) χ hx0 hcon
  have hfin := ccomp4_final hL'
  linarith

/-- **Main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's Theorem 2 form
for composite moduli with the explicit constant `c = 4`. -/
theorem grh_implies_bach_composite_c4 : GRHImpliesBachComposite 4 :=
  fun hGRH => bachBoundCharComposite_of_GRH_c4 hGRH

end DetPrimality.Bach
