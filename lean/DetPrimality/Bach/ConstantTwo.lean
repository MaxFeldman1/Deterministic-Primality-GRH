import DetPrimality.CompositeInterface
import DetPrimality.Bach.CompositeReduction
import DetPrimality.Bach.ZeroSumGain
import DetPrimality.Bach.SharpExplicit
import DetPrimality.Bach.ChebyshevThirty

/-!
# GRH ⟹ Bach's Theorem 2 form (composite moduli) with `c = 73/50 = 1.46` (hence `3/2` and `2`)

Main results (all under GRH for Dirichlet L-functions, sorry-free):

* `bachBoundCharComposite_of_GRH_c146 : BachBoundCharComposite (73 / 50)`;
* `bachBoundCharComposite_of_GRH_c32 : BachBoundCharComposite (3 / 2)`;
* `bachBoundCharComposite_of_GRH_c2 : BachBoundCharComposite 2` (Bach's own constant), and
  `grh_implies_bach_composite_c2 : GRHImpliesBachComposite 2`.

Let `n > 2` be composite, `χ ≠ 1` mod `n`, `L = log n`, `c = 73/50`, `x = c L²`, and assume
`χ a = 1` for all `1 ≤ a < x`.

* Composite reduction (`CompositeReduction.lean`): `x² ≤ n`, which bootstraps to
  `n ≥ 20840`, `L ≥ 9.94368`, `x ≥ 144` (`ctwo_log_ge`); and `ψ₁(x) ≤ Re ψ̃(x, χ*)`.
* Zero sum with hypothesis gain (`ZeroSumGain.lean`, new certificate at `K = 143`):
  `T(χ*) ≤ (5/9) log q - 1.9523` (`ctwo_zeroSum_le_gain_144`).
* Explicit formula (`SharpExplicit.lean`), simplified in `ctwo_upper`
  (`√x ≤ 1.208305 L`, `D = 0.5708`):
  `Re ψ̃(x, χ*) ≤ W(L) := (1.208305 L + 2)(5/9 L - 1.9523) - 0.262`.
* Chebyshev-30 (`ChebyshevThirty.lean`): `ψ₁(x) ≥ 0.460645 x - (3/2) log x + 3.273 - (30 log x + 265)/x`.

With `log x ≤ L/8 + 4.0052` the difference `ψ₁(x) - W(L)` is at least
`0.00126 L² + 1.06 L - 1.52 > 0` (`ctwo_lower`); the margin at the bottom `L ≈ 9.94` is `≈ 9`.

The constant: the leading terms are `0.460645 c L²` against `(5/9) √c L²`, so this combination
of inputs needs `c > (5/9 / 0.460645)² = 1.45457…`; `c = 1.46` is essentially the limit.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- Monotonicity of the composite Bach bound in the constant. -/
theorem ctwo_mono {c c' : ℝ} (h : c ≤ c') (hB : BachBoundCharComposite c) :
    BachBoundCharComposite c' := by
  intro n hn hnp χ hχ
  obtain ⟨a, ha1, hac, hχa⟩ := hB n hn hnp χ hχ
  exact ⟨a, ha1, lt_of_lt_of_le hac (mul_le_mul_of_nonneg_right h (sq_nonneg _)), hχa⟩

/-- Tangent bound `log x ≤ k log 2 + x / 2^k - 1` for `x > 0`. -/
theorem ctwo_log_le_two_pow {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.log x ≤ k * Real.log 2 + x / 2 ^ k - 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 2 ^ k by positivity)
  rw [Real.log_div hx.ne' (by positivity), Real.log_pow] at h1
  linarith

/-! ## Bootstrap: `((73/50) L²)² ≤ n ⟹ L ≥ 9.94368` -/

theorem ctwo_log_ge {n : ℕ} (hn : 2 < n)
    (h : ((73/50) * Real.log n ^ 2) ^ 2 ≤ n) : 20840 ≤ n ∧ 9.94368 ≤ Real.log n := by
  have h0 : 3 ≤ n := hn
  obtain ⟨-, h1⟩ := compred_boot_step (c := (73/50)) (N := 3) (k := 811) (j := 512) (M := 4)
    (lb := 1.09793) (by norm_num) h h0 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h2⟩ := compred_boot_step (c := (73/50)) (N := 4) (k := 1024) (j := 512) (M := 8)
    (lb := 1.38629) (by norm_num) h h1 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h3⟩ := compred_boot_step (c := (73/50)) (N := 8) (k := 1536) (j := 512) (M := 40)
    (lb := 2.07944) (by norm_num) h h2 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h4⟩ := compred_boot_step (c := (73/50)) (N := 40) (k := 2724) (j := 512) (M := 395)
    (lb := 3.68775) (by norm_num) h h3 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h5⟩ := compred_boot_step (c := (73/50)) (N := 395) (k := 4416) (j := 512) (M := 2723)
    (lb := 5.97839) (by norm_num) h h4 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h6⟩ := compred_boot_step (c := (73/50)) (N := 2723) (k := 5842) (j := 512) (M := 8341)
    (lb := 7.90891) (by norm_num) h h5 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h7⟩ := compred_boot_step (c := (73/50)) (N := 8341) (k := 6669) (j := 512) (M := 14164)
    (lb := 9.02851) (by norm_num) h h6 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h8⟩ := compred_boot_step (c := (73/50)) (N := 14164) (k := 7060) (j := 512) (M := 17789)
    (lb := 9.55784) (by norm_num) h h7 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h9⟩ := compred_boot_step (c := (73/50)) (N := 17789) (k := 7228) (j := 512) (M := 19544)
    (lb := 9.78528) (by norm_num) h h8 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h10⟩ := compred_boot_step (c := (73/50)) (N := 19544) (k := 7298) (j := 512) (M := 20312)
    (lb := 9.88005) (by norm_num) h h9 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h11⟩ := compred_boot_step (c := (73/50)) (N := 20312) (k := 7326) (j := 512) (M := 20626)
    (lb := 9.91796) (by norm_num) h h10 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h12⟩ := compred_boot_step (c := (73/50)) (N := 20626) (k := 7338) (j := 512) (M := 20761)
    (lb := 9.93420) (by norm_num) h h11 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h13⟩ := compred_boot_step (c := (73/50)) (N := 20761) (k := 7342) (j := 512) (M := 20806)
    (lb := 9.93962) (by norm_num) h h12 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h14⟩ := compred_boot_step (c := (73/50)) (N := 20806) (k := 7344) (j := 512) (M := 20829)
    (lb := 9.94232) (by norm_num) h h13 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h15⟩ := compred_boot_step (c := (73/50)) (N := 20829) (k := 7345) (j := 512) (M := 20840)
    (lb := 9.94368) (by norm_num) h h14 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨h15, compred_log_ge_of_pow (N := 20840) (k := 7345) (j := 512) h15 (by norm_num)
    (by decide +kernel) (by norm_num)⟩

/-! ## Zero sum with gain at `x ≥ 144` -/

set_option maxRecDepth 100000 in
theorem ctwo_cert54_144 : 2 ^ 3496185 ≤ (zsg_acc zsg_c54 143).2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ctwo_cert2_144 : 2 ^ 851606 ≤ (zsg_acc zsg_c2 143).2 := by decide +kernel

/-- `x ≥ 144`, no witness below `x`: `T(χ) ≤ (5/9) log q - 1.9523`. -/
theorem ctwo_zeroSum_le_gain_144 (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 144 ≤ x)
    (hx1 : ∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ (m : ZMod q) = 1) :
    zeroSum χ ≤ 5 / 9 * Real.log q - 1.9523 := by
  have h := zeroSum_le_gain_of_certs hGRH χ hχ hχ1 ctwo_cert54_144 ctwo_cert2_144 (x := x)
    (by norm_num; linarith) hx1
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

/-! ## The numerical inequalities -/

/-- The GRH upper bound simplified (`c = 73/50`): for `L ≥ 9.94`, `0 ≤ s ≤ 1.208305 L`
(`s = √x`) and `log q ≤ L`, the right-hand side of `re_smoothPsi_le_of_zeroSum_le_of_logDeriv`
(with `A = 5/9`, `B = -1.9523`, `D = 0.5708`) is at most
`(1.208305 L + 2)(5/9 L - 1.9523) - 0.262`. -/
theorem ctwo_upper {L lq s : ℝ} (hL : 9.94 ≤ L) (hlq : lq ≤ L) (hs0 : 0 ≤ s)
    (hs : s ≤ 1.208305 * L) :
    (s + 2 + 3 / (73 / 50 * L ^ 2)) * (5 / 9 * lq + -1.9523) + 0.5708 - 1
        + (Real.log (73 / 50 * L ^ 2) + 13 / 6) / (73 / 50 * L ^ 2)
      ≤ (1.208305 * L + 2) * (5 / 9 * L - 1.9523) - 0.262 := by
  have h2u := Real.log_two_lt_d9
  have hL0 : 0 ≤ L := by linarith
  have hx : (144 : ℝ) ≤ 73 / 50 * L ^ 2 := by nlinarith
  have hx0 : (0 : ℝ) < 73 / 50 * L ^ 2 := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 3 / (73 / 50 * L ^ 2) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hux : u * (73 / 50 * L ^ 2) = 3 := by rw [hu]; field_simp
  have huL : u * L ≤ 0.2068 := by
    have := mul_nonneg (mul_nonneg hu0 hL0) (sub_nonneg.mpr hL)
    nlinarith
  have hR : (Real.log (73 / 50 * L ^ 2) + 13 / 6) / (73 / 50 * L ^ 2) ≤ 0.052 := by
    rw [div_le_iff₀ hx0]
    have hlog := ctwo_log_le_two_pow hx0 7
    push_cast at hlog
    linarith
  rw [← hu]
  have hpre : 0 ≤ s + 2 + u := by linarith
  have hmul1 : (s + 2 + u) * (5 / 9 * lq + -1.9523) ≤ (s + 2 + u) * (5 / 9 * L + -1.9523) :=
    mul_le_mul_of_nonneg_left (by linarith) hpre
  have hmul2 : (s + 2 + u) * (5 / 9 * L + -1.9523)
      ≤ (1.208305 * L + 2 + u) * (5 / 9 * L + -1.9523) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hexp : (1.208305 * L + 2 + u) * (5 / 9 * L + -1.9523)
      = (1.208305 * L + 2) * (5 / 9 * L - 1.9523) + 5 / 9 * (u * L) - 1.9523 * u := by ring
  linarith

/-- The final numerical inequality for `c = 73/50`: `W(L) < ψ₁((73/50) L²)` for `L ≥ 9.94`. -/
theorem ctwo_lower {L : ℝ} (hL : 9.94 ≤ L) :
    (1.208305 * L + 2) * (5 / 9 * L - 1.9523) - 0.262 < psiOne (73 / 50 * L ^ 2) := by
  have h2u := Real.log_two_lt_d9
  have hL0 : 0 < L := by linarith
  have hx : (144 : ℝ) ≤ 73 / 50 * L ^ 2 := by nlinarith
  have hx0 : (0 : ℝ) < 73 / 50 * L ^ 2 := by linarith
  have hψ := psiOne_lower_cheb30_sharp (x := 73 / 50 * L ^ 2) (by linarith)
  -- `log x ≤ L/8 + 4.0052`
  have hlogx : Real.log (73 / 50 * L ^ 2) ≤ L / 8 + 4.0052 := by
    have h1 : Real.log (73 / 50 * L ^ 2) = Real.log (73 / 50) + 2 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have h2 : Real.log (73 / 50 : ℝ) ≤ 73 / 50 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h3 := ctwo_log_le_two_pow hL0 4
    push_cast at h3
    rw [h1]
    linarith
  have hQ : (30 * Real.log (73 / 50 * L ^ 2) + 265) / (73 / 50 * L ^ 2) ≤ 2.95 := by
    rw [div_le_iff₀ hx0]
    nlinarith [sq_nonneg (L - 9.94)]
  nlinarith [sq_nonneg L]

/-! ## Assembly -/

/-- **GRH ⟹ Bach's Theorem 2 form for composite moduli with `c = 73/50 = 1.46`**. -/
theorem bachBoundCharComposite_of_GRH_c146 (hGRH : DirichletLZerosOnLine) :
    BachBoundCharComposite (73 / 50) := by
  intro n hn hnp χ hχ
  by_contra hcon
  push Not at hcon
  have hbig := compred_bootstrap_hyp hn hnp χ (c := 73 / 50) (by norm_num) hcon
  obtain ⟨-, hL⟩ := ctwo_log_ge hn hbig
  have h2l := Real.log_two_gt_d9
  have hL' : 9.94 ≤ Real.log n := by linarith
  have hx144 : (144 : ℝ) ≤ 73 / 50 * Real.log n ^ 2 := by nlinarith
  have hx0 : (0 : ℝ) < 73 / 50 * Real.log n ^ 2 := by linarith
  have hx1 : (1 : ℝ) ≤ 73 / 50 * Real.log n ^ 2 := by linarith
  have hs : √(73 / 50 * Real.log n ^ 2) ≤ 1.208305 * Real.log n := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
  have hlx2 : 2 ≤ Real.log (73 / 50 * Real.log n ^ 2) := by
    have h1 : Real.log ((2 : ℝ) ^ 7) ≤ Real.log (73 / 50 * Real.log n ^ 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have : NeZero n := ⟨by omega⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨hprim, hne1, -, hq⟩ := compred_primitive_facts (by omega) χ hχ
  have hT0 := ctwo_zeroSum_le_gain_144 hGRH χ.primitiveCharacter hprim hne1 hx144
    (fun m hm hmx => compred_primitive_eq_one χ hcon hm hmx)
  have hT : zeroSum χ.primitiveCharacter ≤ 5 / 9 * Real.log χ.conductor + -1.9523 := by
    linarith
  have hD := norm_logDeriv_LFunction_two_le_sharp χ.primitiveCharacter
  have hre := re_smoothPsi_le_of_zeroSum_le_of_logDeriv hGRH χ.primitiveCharacter hprim hne1
    hT hD hx1 hlx2
  have hup := ctwo_upper (L := Real.log n) (lq := Real.log χ.conductor)
    (s := √(73 / 50 * Real.log n ^ 2)) hL' hq (Real.sqrt_nonneg _) hs
  have hlow := compred_psiOne_le (by omega) χ hx0 hcon
  have hfin := ctwo_lower hL'
  linarith

/-- GRH ⟹ composite Bach bound with `c = 3/2`. -/
theorem bachBoundCharComposite_of_GRH_c32 (hGRH : DirichletLZerosOnLine) :
    BachBoundCharComposite (3 / 2) :=
  ctwo_mono (by norm_num) (bachBoundCharComposite_of_GRH_c146 hGRH)

/-- **GRH ⟹ Bach's Theorem 2 form for composite moduli with Bach's constant `c = 2`**. -/
theorem bachBoundCharComposite_of_GRH_c2 (hGRH : DirichletLZerosOnLine) :
    BachBoundCharComposite 2 :=
  ctwo_mono (by norm_num) (bachBoundCharComposite_of_GRH_c146 hGRH)

/-- GRH implies the composite Theorem 2 form with `c = 73/50`. -/
theorem grh_implies_bach_composite_c146 : GRHImpliesBachComposite (73 / 50) :=
  fun hGRH => bachBoundCharComposite_of_GRH_c146 hGRH

/-- GRH implies the composite Theorem 2 form with `c = 3/2`. -/
theorem grh_implies_bach_composite_c32 : GRHImpliesBachComposite (3 / 2) :=
  fun hGRH => bachBoundCharComposite_of_GRH_c32 hGRH

/-- **Main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's Theorem 2 form
for composite moduli with Bach's constant `c = 2`. -/
theorem grh_implies_bach_composite_c2 : GRHImpliesBachComposite 2 :=
  fun hGRH => bachBoundCharComposite_of_GRH_c2 hGRH

end DetPrimality.Bach
