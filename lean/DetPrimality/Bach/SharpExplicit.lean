import DetPrimality.Bach.Assembly

/-!
# Sharper passage from `zeroSum` to `smoothPsi`

`norm_smoothPsi_le_of_inputs` (`Assembly.lean`) proves
`‖ψ̃(x, χ)‖ ≤ (√x + 5)(log q + 2) + log x + 5`.  This file keeps `zeroSum χ` symbolic and sharpens
every other constant:

* prefactor `√x + 5 → √x + 2 + 3/x` (under GRH, `|2 - ρ| = |ρ + 1|` and `|ρ| ≤ |ρ + 1|`, so
  `3/(|ρ+1||2-ρ|x) ≤ (3/x)/(|ρ||ρ+1|)`);
* `|L'/L(2, χ)| ≤ 3/4` instead of `1` (or any `D` supplied as a hypothesis);
* (one-sided, `re_smoothPsi_le_*`) the explicit-formula residual `I_Γ(x) = I[G - G(2)](x)` is
  *real* and satisfies `I_Γ(x) ≤ max (1 - log x) (-1 + (log x + 13/6)/x)`, so that for the upper
  bound of `Re ψ̃` the term `log x + 4` is replaced by `-1 + (log x + 13/6)/x` (when `log x ≥ 2`).

All helper names are prefixed `sharpex_`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## `|L'/L(2, χ)| ≤ 3/4` -/

/-- `|L'/L(2, χ)| ≤ ∑ Λ(n)/n² ≤ 3/4` for every Dirichlet character. -/
theorem sharpex_norm_logDeriv_LFunction_two_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖deriv (LFunction χ) 2 / LFunction χ 2‖ ≤ 3 / 4 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have hsum : Summable fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) hs).norm
  have h1 := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs, neg_div] at h1
  rw [← norm_neg]
  refine (HasSum.norm_le_of_bounded h1 hsum.hasSum fun n => ?_).trans
    Numerics.tsum_vonMangoldt_term_two_le_three_quarters
  refine LSeries.norm_term_le 2 (g := fun n => (Λ n : ℂ)) ?_
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

/-- `‖L'/L(2) · (1 - 1/x)‖ ≤ D` as soon as `‖L'/L(2)‖ ≤ D` and `x ≥ 1`. -/
theorem sharpex_norm_logDeriv_mul_le {z : ℂ} {D : ℝ} (hD : ‖z‖ ≤ D) {x : ℝ} (hx : 1 ≤ x) :
    ‖z * (1 - 1 / (x : ℂ))‖ ≤ D := by
  have hxpos : 0 < x := by linarith
  have h1 : ‖(1 - 1 / (x : ℂ))‖ ≤ 1 := by
    have : (1 - 1 / (x : ℂ)) = ((1 - 1 / x : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have : 1 / x ≤ 1 := by rw [div_le_one hxpos]; exact hx
    have : 0 ≤ 1 / x := by positivity
    constructor <;> linarith
  rw [norm_mul]
  calc ‖z‖ * ‖(1 - 1 / (x : ℂ))‖ ≤ D * 1 :=
        mul_le_mul hD h1 (norm_nonneg _) ((norm_nonneg _).trans hD)
    _ = D := mul_one D

/-! ## The sum over zeros -/

/-- Under GRH, the zero sum of the explicit formula is at most `(√x + 2 + 3/x) · T(χ)`. -/
theorem sharpex_norm_tsum_zeros_le (hI : BachInputs) (hGRH : DirichletLZerosOnLine) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    ‖∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) *
        ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x))‖
      ≤ (√x + 2 + 3 / x) * zeroSum χ := by
  have hxpos : 0 < x := by linarith
  have hsx : 0 ≤ √x := Real.sqrt_nonneg x
  set F : ℂ → ℂ := fun ρ => (zeroOrd χ ρ : ℂ) *
    ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x)) with hFdef
  have hF : ∀ ρ, ‖F ρ‖ ≤ (√x + 2 + 3 / x) * ((zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)) := by
    intro ρ
    by_cases h0 : zeroOrd χ ρ = 0
    · simp [hFdef, h0]
    · obtain ⟨ha, hab, h2, -, -⟩ := zero_facts hGRH χ h0
      have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h0
      have hb : 0 < ‖ρ + 1‖ := lt_of_lt_of_le ha hab
      have hcpow : ‖(x : ℂ) ^ ρ‖ = √x := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hρ, Real.sqrt_eq_rpow]
      have h1 : ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ = √x / (‖ρ‖ * ‖ρ + 1‖) := by
        rw [norm_div, norm_mul, hcpow]
      have h2' : ‖(2 : ℂ) / (ρ * (2 - ρ))‖ = 2 / (‖ρ‖ * ‖ρ + 1‖) := by
        rw [norm_div, norm_mul, h2]; simp
      have h3 : ‖(3 : ℂ) / ((ρ + 1) * (2 - ρ) * x)‖ = 3 / (‖ρ + 1‖ * ‖ρ + 1‖ * x) := by
        rw [norm_div, norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_of_nonneg hxpos.le]
        simp
      have h4 : 3 / (‖ρ + 1‖ * ‖ρ + 1‖ * x) ≤ 3 / x / (‖ρ‖ * ‖ρ + 1‖) := by
        rw [div_div]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have := mul_le_mul_of_nonneg_right hab hb.le
        nlinarith [mul_le_mul_of_nonneg_left this hxpos.le]
      have hnorm : ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ))
            + 3 / ((ρ + 1) * (2 - ρ) * x)‖ ≤ (√x + 2 + 3 / x) / (‖ρ‖ * ‖ρ + 1‖) := by
        calc _ ≤ ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ + ‖(2 : ℂ) / (ρ * (2 - ρ))‖
              + ‖(3 : ℂ) / ((ρ + 1) * (2 - ρ) * x)‖ :=
              (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
          _ ≤ √x / (‖ρ‖ * ‖ρ + 1‖) + 2 / (‖ρ‖ * ‖ρ + 1‖) + 3 / x / (‖ρ‖ * ‖ρ + 1‖) := by
              rw [h1, h2', h3]; linarith
          _ = (√x + 2 + 3 / x) / (‖ρ‖ * ‖ρ + 1‖) := by ring
      calc ‖F ρ‖ = (zeroOrd χ ρ : ℝ) * ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ))
            + 3 / ((ρ + 1) * (2 - ρ) * x)‖ := by
            simp only [hFdef, norm_mul, Complex.norm_natCast]
        _ ≤ (zeroOrd χ ρ : ℝ) * ((√x + 2 + 3 / x) / (‖ρ‖ * ‖ρ + 1‖)) := by gcongr
        _ = _ := by ring
  have hsummL := summable_zeroSum_of_inputs hI hGRH χ hχ hχ1
  have hsummF : Summable fun ρ => ‖F ρ‖ :=
    Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) hF (hsummL.mul_left _)
  calc ‖∑' ρ, F ρ‖ ≤ ∑' ρ, ‖F ρ‖ := norm_tsum_le_tsum_norm hsummF
    _ ≤ ∑' ρ : ℂ, (√x + 2 + 3 / x) * ((zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)) :=
        hsummF.tsum_le_tsum hF (hsummL.mul_left _)
    _ = (√x + 2 + 3 / x) * zeroSum χ := tsum_mul_left

/-! ## Two-sided bound (norm) -/

/-- Sharp "Theorem A", with the bound `D` for `|L'/L(2, χ)|` as a hypothesis and `zeroSum`
symbolic. -/
theorem norm_smoothPsi_le_zeroSum_of_logDeriv (hI : BachInputs) (hGRH : DirichletLZerosOnLine)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {D : ℝ}
    (hD : ‖deriv (LFunction χ) 2 / LFunction χ 2‖ ≤ D) {x : ℝ} (hx : 1 ≤ x) :
    ‖smoothPsi χ x‖ ≤ (√x + 2 + 3 / x) * zeroSum χ + Real.log x + 4 + D := by
  have htsum := sharpex_norm_tsum_zeros_le hI hGRH χ hχ hχ1 hx
  have hE := hI.explicit χ hχ hχ1 hx
  have hA := sharpex_norm_logDeriv_mul_le hD hx
  set S : ℂ := ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) *
    ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x)) with hSdef
  have hsplit : smoothPsi χ x =
      (smoothPsi χ x + deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ)) + S)
        - deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ)) - S := by ring
  calc ‖smoothPsi χ x‖
      ≤ ‖smoothPsi χ x + deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ)) + S‖
        + ‖deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ))‖ + ‖S‖ := by
        conv_lhs => rw [hsplit]
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- Sharp "Theorem A" (sorry-free inputs, `D = 3/4`): under GRH, for primitive `χ ≠ 1` and
`x ≥ 1`, `‖ψ̃(x, χ)‖ ≤ (√x + 2 + 3/x) T(χ) + log x + 4 + 3/4`. -/
theorem norm_smoothPsi_le_zeroSum (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖smoothPsi χ x‖ ≤ (√x + 2 + 3 / x) * zeroSum χ + Real.log x + 4 + 3 / 4 :=
  norm_smoothPsi_le_zeroSum_of_logDeriv bachInputs hGRH χ hχ hχ1
    (sharpex_norm_logDeriv_LFunction_two_le χ) hx

/-- Monotonicity in the zero sum: `(√x + 2 + 3/x) T ≤ (√x + 2 + 3/x)(A log q + B)`. -/
theorem sharpex_prefactor_mul_le {x T A B lq : ℝ} (hx : 1 ≤ x) (hT : T ≤ A * lq + B) :
    (√x + 2 + 3 / x) * T ≤ (√x + 2 + 3 / x) * (A * lq + B) := by
  have hxpos : 0 < x := by linarith
  have h3 : 0 ≤ 3 / x := by positivity
  exact mul_le_mul_of_nonneg_left hT (by linarith [Real.sqrt_nonneg x])

/-- Convenience corollary: a bound `T(χ) ≤ A log q + B` and a bound `D` for `|L'/L(2)|` as
hypotheses. -/
theorem norm_smoothPsi_le_of_zeroSum_le_of_logDeriv (hGRH : DirichletLZerosOnLine) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {A B D : ℝ}
    (hT : zeroSum χ ≤ A * Real.log q + B)
    (hD : ‖deriv (LFunction χ) 2 / LFunction χ 2‖ ≤ D) {x : ℝ} (hx : 1 ≤ x) :
    ‖smoothPsi χ x‖ ≤ (√x + 2 + 3 / x) * (A * Real.log q + B) + Real.log x + 4 + D := by
  have h := norm_smoothPsi_le_zeroSum_of_logDeriv bachInputs hGRH χ hχ hχ1 hD hx
  have hmul := sharpex_prefactor_mul_le hx hT
  linarith

/-- Convenience corollary (`D = 3/4`): a bound `T(χ) ≤ A log q + B` as hypothesis. -/
theorem norm_smoothPsi_le_of_zeroSum_le (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {A B : ℝ}
    (hT : zeroSum χ ≤ A * Real.log q + B) {x : ℝ} (hx : 1 ≤ x) :
    ‖smoothPsi χ x‖ ≤ (√x + 2 + 3 / x) * (A * Real.log q + B) + Real.log x + 4 + 3 / 4 :=
  norm_smoothPsi_le_of_zeroSum_le_of_logDeriv hGRH χ hχ hχ1 hT
    (sharpex_norm_logDeriv_LFunction_two_le χ) hx

/-! ## The explicit formula as an identity, and the sign of the Γ-residual -/

/-- The smoothed explicit formula as an *identity*: the residual is exactly the Γ-integral
`I[G - G(2)](x)` (this is the `key` step of `explicit_formula_bound_of_hadamard`). -/
theorem sharpex_explicit_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    smoothPsi χ x + deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ))
        + ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) *
            ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x))
      = perronI (fun s => Gfun χ s - Gfun χ 2) x := by
  have hx0 : 0 < x := by linarith
  have hH := hadamardLogDeriv_of_growth χ hχ hχ1 (growth_completedLFunction χ hχ1)
  have hS := summable_zeroOrd_div_normSq_proof χ hχ hχ1 (growth_completedLFunction χ hχ1)
  obtain ⟨hZi, hZ⟩ := zero_part χ hχ1 hH hS hx
  obtain ⟨hGi, -⟩ := gamma_part χ hx
  set c0 : ℂ := -(deriv (LFunction χ) 2 / LFunction χ 2) with hc0
  set Z : ℂ → ℂ := fun s => ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ)) with hZdef
  have hAi : VerticalIntegrable (fun s => (c0 + (Gfun χ s - Gfun χ 2)) / (s * (s + 1))) 2 := by
    have h := Integrable.add (verticalIntegrable_const_kernel c0) hGi
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have h1 : smoothPsi χ x = perronI (fun s => (c0 + (Gfun χ s - Gfun χ 2)) - Z s) x := by
    rw [smoothPsi_eq_perronI χ hx]
    apply perronI_congr_line
    intro y
    exact neg_logDeriv_decomp χ hχ1 hH hS (by simp)
  rw [perronI_sub hAi hZi hx0, perronI_add (verticalIntegrable_const_kernel c0) hGi hx0,
    perronI_const, perronI_one hx, hZ] at h1
  rw [h1, hc0]
  simp only [zeroTerm]
  ring

/-- Telescoping: `∑_j 2/((2j+2+a)(2j+4+a)) = 1/(2+a)`. -/
theorem sharpex_hasSum_telescope (a : ℕ) :
    HasSum (fun j : ℕ => 2 / ((2 * (j : ℝ) + 2 + a) * (2 * (j : ℝ) + 4 + a)))
      (1 / (2 + (a : ℝ))) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity)]
  have hps : ∀ n : ℕ, ∑ j ∈ Finset.range n, 2 / ((2 * (j : ℝ) + 2 + a) * (2 * (j : ℝ) + 4 + a))
      = 1 / (2 + (a : ℝ)) - 1 / (2 * (n : ℝ) + (2 + a)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : (2 * (n : ℝ) + 2 + a) ≠ 0 := by positivity
      have h2 : (2 * (n : ℝ) + 4 + a) ≠ 0 := by positivity
      have h3 : (2 * (n : ℝ) + (2 + a)) ≠ 0 := by positivity
      have h4 : (2 * ((n + 1 : ℕ) : ℝ) + (2 + a)) ≠ 0 := by positivity
      have h5 : (2 + (a : ℝ)) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  rw [show (fun n : ℕ => ∑ j ∈ Finset.range n,
        2 / ((2 * (j : ℝ) + 2 + a) * (2 * (j : ℝ) + 4 + a)))
      = fun n : ℕ => 1 / (2 + (a : ℝ)) - 1 / (2 * (n : ℝ) + (2 + a)) from funext hps]
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + (2 + a))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have h := (tendsto_const_nhds (x := 1 / (2 + (a : ℝ)))).sub h0
  rw [sub_zero] at h
  exact h

/-- One-sided bound for the tail terms `m = 2(j+1)+a ≥ 2` of the Γ-series. -/
theorem sharpex_rterm_le (a j : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    rterm (2 * (j + 1) + a) x ≤ -(2 / ((2 * (j : ℝ) + 2 + a) * (2 * (j : ℝ) + 4 + a)))
      + 3 / (2 * x) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
  have hx0 : 0 < x := by linarith
  have hm2 : 2 ≤ 2 * (j + 1) + a := by omega
  rw [rterm_of_two_le hm2]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hMe : ((2 * (j + 1) + a : ℕ) : ℝ) = 2 * (j : ℝ) + 2 + a := by push_cast; ring
  rw [hMe]
  set M : ℝ := 2 * (j : ℝ) + 2 + a with hMdef
  have hM : 2 * (j : ℝ) + 2 ≤ M := by rw [hMdef]; linarith
  have hM1 : 0 < M - 1 := by linarith
  have hP : 0 < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
  have hxp : 0 < x ^ (-M) := Real.rpow_pos_of_pos hx0 _
  have hC0 : 0 ≤ x ^ (-M) / (M * (M - 1)) := by positivity
  have hB : 3 / ((M - 1) * (M + 2) * x) ≤ 3 / (2 * x) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    rw [show 3 / (2 * x) * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
        = 3 / (2 * (((j : ℝ) + 1) * ((j : ℝ) + 2)) * x) by field_simp]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    apply mul_le_mul_of_nonneg_right _ hx0.le
    nlinarith [mul_le_mul hM hM (by linarith) (by linarith)]
  have e1 : -2 / (M * (M + 2)) = -(2 / (M * (M + 2))) := neg_div _ _
  have e2 : 2 * (j : ℝ) + 4 + a = M + 2 := by rw [hMdef]; ring
  rw [e1, e2]
  linarith

/-- The Γ-residual of the explicit formula is real. -/
theorem sharpex_gamma_im {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    (perronI (fun s => Gfun χ s - Gfun χ 2) x).im = 0 := by
  have hS := hasSum_perronI_gamma χ hx
  simp only [perronI_gterm _ hx] at hS
  have hIm := Complex.hasSum_im hS
  simp only [Complex.ofReal_im] at hIm
  exact hIm.unique hasSum_zero

/-- **Sign of the Γ-residual.**  `I_Γ(x) ≤ 1 - log x` (even `χ`) or
`I_Γ(x) ≤ -1 + (log x + 13/6)/x` (odd `χ`). -/
theorem sharpex_gamma_re_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) :
    (perronI (fun s => Gfun χ s - Gfun χ 2) x).re
      ≤ max (1 - Real.log x) (-1 + (Real.log x + 13 / 6) / x) := by
  have hx0 : 0 < x := by linarith
  have hS := hasSum_perronI_gamma χ hx
  simp only [perronI_gterm _ hx] at hS
  have hR := Complex.hasSum_re hS
  simp only [Complex.ofReal_re] at hR
  rw [← hR.tsum_eq, hR.summable.tsum_eq_zero_add]
  have htail : Summable fun j : ℕ => rterm (2 * (j + 1) + gammaShift χ) x :=
    (summable_nat_add_iff (f := fun k : ℕ => rterm (2 * k + gammaShift χ) x) 1).mpr hR.summable
  have hc := sharpex_hasSum_telescope (gammaShift χ)
  have ht := hasSum_telescope
  have hmaj := hc.neg.add (ht.mul_left (3 / (2 * x)))
  have hup : ∑' j : ℕ, rterm (2 * (j + 1) + gammaShift χ) x
      ≤ -(1 / (2 + (gammaShift χ : ℝ))) + 3 / (2 * x) * 1 := by
    rw [← hmaj.tsum_eq]
    exact htail.tsum_le_tsum (fun j => sharpex_rterm_le _ j hx) hmaj.summable
  generalize ∑' j : ℕ, rterm (2 * (j + 1) + gammaShift χ) x = T at hup
  rcases gammaShift_cases χ with h0 | h1
  · rw [show 2 * 0 + gammaShift χ = 0 by omega, rterm_zero]
    rw [h0] at hup
    refine le_trans ?_ (le_max_left _ _)
    norm_num at hup
    linarith
  · rw [show 2 * 0 + gammaShift χ = 1 by omega, rterm_one]
    rw [h1] at hup
    refine le_trans ?_ (le_max_right _ _)
    have e : -1 + (Real.log x + 13 / 6) / x
        = -2 / 3 + Real.log x / x + 2 / (3 * x) + (-(1 / 3) + 3 / (2 * x)) := by
      field_simp
      ring
    rw [e]
    norm_num at hup
    linarith

/-! ## One-sided bound (real part) -/

/-- One-sided sharp "Theorem A", with the bound `D` for `|L'/L(2, χ)|` as hypothesis: the
explicit-formula residual `log x + 4` is replaced by the signed Γ-residual. -/
theorem re_smoothPsi_le_zeroSum_of_logDeriv (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {D : ℝ}
    (hD : ‖deriv (LFunction χ) 2 / LFunction χ 2‖ ≤ D) {x : ℝ} (hx : 1 ≤ x) :
    (smoothPsi χ x).re ≤ (√x + 2 + 3 / x) * zeroSum χ + D
      + max (1 - Real.log x) (-1 + (Real.log x + 13 / 6) / x) := by
  have htsum := sharpex_norm_tsum_zeros_le bachInputs hGRH χ hχ hχ1 hx
  have hA := sharpex_norm_logDeriv_mul_le hD hx
  have hid := sharpex_explicit_identity χ hχ hχ1 hx
  have hG := sharpex_gamma_re_le χ hx
  set S : ℂ := ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) *
    ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x)) with hSdef
  set A : ℂ := deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ)) with hAdef
  have hsplit : smoothPsi χ x = perronI (fun s => Gfun χ s - Gfun χ 2) x - A - S := by
    rw [← hid]; ring
  have hre : (smoothPsi χ x).re
      = (perronI (fun s => Gfun χ s - Gfun χ 2) x).re - A.re - S.re := by
    rw [hsplit, Complex.sub_re, Complex.sub_re]
  have hA' := (abs_le.mp (Complex.abs_re_le_norm A)).1
  have hS' := (abs_le.mp (Complex.abs_re_le_norm S)).1
  rw [hre]
  linarith

/-- One-sided sharp "Theorem A" (`D = 3/4`, `log x ≥ 2`):
`Re ψ̃(x, χ) ≤ (√x + 2 + 3/x) T(χ) - 1/4 + (log x + 13/6)/x`. -/
theorem re_smoothPsi_le_zeroSum (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x)
    (hlx : 2 ≤ Real.log x) :
    (smoothPsi χ x).re ≤ (√x + 2 + 3 / x) * zeroSum χ - 1 / 4 + (Real.log x + 13 / 6) / x := by
  have h := re_smoothPsi_le_zeroSum_of_logDeriv hGRH χ hχ hχ1
    (sharpex_norm_logDeriv_LFunction_two_le χ) hx
  have hxpos : 0 < x := by linarith
  have hpos : 0 ≤ (Real.log x + 13 / 6) / x := by positivity
  have hmax : max (1 - Real.log x) (-1 + (Real.log x + 13 / 6) / x)
      = -1 + (Real.log x + 13 / 6) / x := max_eq_right (by linarith)
  rw [hmax] at h
  linarith

/-- One-sided convenience corollary: bounds `T(χ) ≤ A log q + B` and `|L'/L(2)| ≤ D` as
hypotheses, `log x ≥ 2`. -/
theorem re_smoothPsi_le_of_zeroSum_le_of_logDeriv (hGRH : DirichletLZerosOnLine) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {A B D : ℝ}
    (hT : zeroSum χ ≤ A * Real.log q + B)
    (hD : ‖deriv (LFunction χ) 2 / LFunction χ 2‖ ≤ D) {x : ℝ} (hx : 1 ≤ x)
    (hlx : 2 ≤ Real.log x) :
    (smoothPsi χ x).re
      ≤ (√x + 2 + 3 / x) * (A * Real.log q + B) + D - 1 + (Real.log x + 13 / 6) / x := by
  have h := re_smoothPsi_le_zeroSum_of_logDeriv hGRH χ hχ hχ1 hD hx
  have hxpos : 0 < x := by linarith
  have hpos : 0 ≤ (Real.log x + 13 / 6) / x := by positivity
  have hmax : max (1 - Real.log x) (-1 + (Real.log x + 13 / 6) / x)
      = -1 + (Real.log x + 13 / 6) / x := max_eq_right (by linarith)
  rw [hmax] at h
  have hmul := sharpex_prefactor_mul_le hx hT
  linarith

/-- One-sided convenience corollary (`D = 3/4`): a bound `T(χ) ≤ A log q + B` as hypothesis. -/
theorem re_smoothPsi_le_of_zeroSum_le (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {A B : ℝ}
    (hT : zeroSum χ ≤ A * Real.log q + B) {x : ℝ} (hx : 1 ≤ x) (hlx : 2 ≤ Real.log x) :
    (smoothPsi χ x).re
      ≤ (√x + 2 + 3 / x) * (A * Real.log q + B) - 1 / 4 + (Real.log x + 13 / 6) / x := by
  have h := re_smoothPsi_le_of_zeroSum_le_of_logDeriv hGRH χ hχ hχ1 hT
    (sharpex_norm_logDeriv_LFunction_two_le χ) hx hlx
  linarith

end DetPrimality.Bach
