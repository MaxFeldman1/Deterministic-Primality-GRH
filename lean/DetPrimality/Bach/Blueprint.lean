import Mathlib
import DetPrimality.Interfaces

/-!
# Layer 2: GRH ⟹ Bach's bound (blueprint skeleton)

Lean counterpart of `blueprint/BACH_BLUEPRINT.md`.  Section numbers `§k` refer to that file.
Main result: `DetPrimality.Bach.grh_implies_bach : GRHImpliesBach 1024`.

Status legend in docstrings:  **DEEP** = sorried analytic input, **NUM** = sorried numerical
fact, **ELEM** = sorried elementary lemma, no tag = fully proved here.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## §1 Definitions -/

/-- Multiplicity of `ρ` as a *nontrivial* zero of `L(s, χ)` (zero outside the open critical
strip).  For primitive `χ ≠ 1` these are exactly the zeros of the completed L-function. -/
noncomputable def zeroOrd {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  if 0 < ρ.re ∧ ρ.re < 1 then analyticOrderNatAt (LFunction χ) ρ else 0

/-- Bach's smoothed sum `∑_{m < x} Λ(m) χ(m) (1 - m/x)`. -/
noncomputable def smoothPsi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ m ∈ Finset.range ⌈x⌉₊, (Λ m : ℂ) * χ (m : ZMod N) * (1 - (m : ℂ) / (x : ℂ))

/-- `ψ₁(x) = ∑_{m < x} Λ(m) (1 - m/x)`. -/
noncomputable def psiOne (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range ⌈x⌉₊, Λ m * (1 - (m : ℝ) / x)

/-- `∑_{m < x, gcd(m,n) > 1} Λ(m)`. -/
noncomputable def noncoprimeSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ (Finset.range ⌈x⌉₊).filter (fun m => ¬ Nat.Coprime m n), Λ m

/-- The zero sum `T(χ) = ∑_ρ 1/|ρ(ρ+1)|` (with multiplicity). -/
noncomputable def zeroSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)

/-! ## §2 Deep analytic inputs (unconditional) -/

/-- **DEEP** (§2.1, Hadamard / Jensen).  `∑_ρ 1/|ρ|² < ∞` over nontrivial zeros of a primitive
nonprincipal `L(s, χ)`.  Missing: Jensen-type zero counting `N(T+1) - N(T) ≪ log(q(T+2))` (or the
order-1 Hadamard factorisation) for `completedLFunction χ`; neither is in Mathlib. -/
theorem summable_zeroOrd_div_normSq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2 := by
  sorry

/-- **DEEP** (§2.2, Hadamard partial fractions + functional equation).  For `Re s > 1`,
`Re (Λ'/Λ)(s, χ) = -½ log q + ∑_ρ Re 1/(s - ρ)` where `Λ = gammaFactor · L` is Mathlib's
completed L-function.  Missing: Hadamard factorisation of the entire order-1 function
`completedLFunction χ`, plus the computation `Re B(χ) = -½ log q - ∑ Re 1/ρ` from
`IsPrimitive.completedLFunction_one_sub`. -/
theorem re_logDeriv_eq_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    (deriv (LFunction χ) s / LFunction χ s + deriv (gammaFactor χ) s / gammaFactor χ s).re
      = -(Real.log q) / 2 + ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (s - ρ)).re := by
  sorry

/-- **DEEP** (§3, smoothed explicit formula, exact up to the Γ-term).  For primitive `χ ≠ 1`
and `x ≥ 1`:
`S(x) + (L'/L)(2)(1 - 1/x) + ∑_ρ [x^ρ/(ρ(ρ+1)) - 2/(ρ(2-ρ)) + 3/((ρ+1)(2-ρ)x)] = I_Γ(x)`
with `|I_Γ(x)| ≤ log x + 4` the (explicit) contribution of the trivial zeros.
Missing: Perron formula for the kernel `1/(s(s+1))` (from `mellinInv_mellin_eq`), the
difference form of the Hadamard partial fraction, the digamma series, termwise integration. -/
theorem explicit_formula_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖smoothPsi χ x + deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ))
        + ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) *
            ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x))‖
      ≤ Real.log x + 4 := by
  sorry

/-! ## §4 Numerical inputs -/

/-- **NUM** (§4.1a).  `∑ Λ(n)/n² = -ζ'/ζ(2) = 0.5699… ≤ 1`.  Missing: a purely numerical
estimate, e.g. `Λ(n) ≤ log n` and `log 2/4 + log 3/9 + ∫₃^∞ log t / t² dt = 0.995 < 1`
(or sharper: `∑_p log p/(p²-1)`). -/
theorem tsum_vonMangoldt_term_two_le :
    ∑' n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ ≤ 1 := by
  sorry

/-- (§4.1) `|L'/L(2, χ)| ≤ ∑ Λ(n)/n² ≤ 1` for every Dirichlet character. -/
theorem norm_logDeriv_LFunction_two_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖deriv (LFunction χ) 2 / LFunction χ 2‖ ≤ 1 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have hsum : Summable fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) hs).norm
  have h1 := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs, neg_div] at h1
  rw [← norm_neg]
  refine (HasSum.norm_le_of_bounded h1 hsum.hasSum fun n => ?_).trans
    tsum_vonMangoldt_term_two_le
  refine LSeries.norm_term_le 2 (g := fun n => (Λ n : ℂ)) ?_
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

/-- (§4.2a) `Γ_ℝ'/Γ_ℝ(s) = -½ log π + ½ ψ(s/2)` for `Re s > 0`. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    deriv Gammaℝ s / Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2 := by
  have hs2 : ∀ m : ℕ, s / 2 ≠ -m := fun m h => by
    have h1 := congrArg Complex.re h
    have h2 : (s / 2).re = s.re / 2 := by simp
    have h3 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [h2] at h1
    simp at h1
    linarith
  have hΓ : HasDerivAt (fun z : ℂ => Gamma (z / 2)) (deriv Gamma (s / 2) * (1 / 2)) s := by
    have h1 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := (hasDerivAt_id s).div_const 2
    exact (differentiableAt_Gamma _ hs2).hasDerivAt.comp s h1
  have hπ : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h1 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s := ((hasDerivAt_id s).neg).div_const 2
    exact h1.const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have hG : HasDerivAt Gammaℝ (((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2))
      * Gamma (s / 2) + (Real.pi : ℂ) ^ (-s / 2) * (deriv Gamma (s / 2) * (1 / 2))) s :=
    hπ.mul hΓ
  rw [hG.deriv, Gammaℝ_def, digamma_def, logDeriv_apply, Complex.ofReal_log Real.pi_pos.le]
  have h1 : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff, Real.pi_ne_zero]
  have h2 : Gamma (s / 2) ≠ 0 := Gamma_ne_zero hs2
  field_simp

/-- (§4.2) `Re (Γ_ℝ'/Γ_ℝ)(2 + a) ≤ 0` for `a ∈ {0,1}`: the values are
`-(log π + γ)/2 ≈ -0.861` (even) and `(2 - log π - 2 log 2 - γ)/2 ≈ -0.554` (odd). -/
theorem re_logDeriv_gammaFactor_two_nonpos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (deriv (gammaFactor χ) 2 / gammaFactor χ 2).re ≤ 0 := by
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hπ1 : 1 < Real.log Real.pi := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
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

/-! ## §5 Consequences of GRH -/

/-- Under GRH every nontrivial zero counted by `zeroOrd` has real part `1/2`. -/
theorem re_eq_half_of_zeroOrd_ne_zero (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) : ρ.re = 1 / 2 := by
  unfold zeroOrd at h
  split_ifs at h with hstrip
  · have h0 : LFunction χ ρ = 0 := by
      have h' : analyticOrderAt (LFunction χ) ρ ≠ 0 := by
        intro h'
        apply h
        simp [analyticOrderNatAt, h']
      exact apply_eq_zero_of_analyticOrderAt_ne_zero h'
    exact hGRH N χ ρ hstrip.1 hstrip.2 h0
  · exact absurd rfl h

/-- Geometry of a zero on the critical line (used for all termwise estimates). -/
theorem zero_facts (hGRH : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h : zeroOrd χ ρ ≠ 0) :
    0 < ‖ρ‖ ∧ ‖ρ‖ ≤ ‖ρ + 1‖ ∧ ‖2 - ρ‖ = ‖ρ + 1‖ ∧ ‖ρ + 1‖ ^ 2 ≤ 9 * ‖ρ‖ ^ 2 ∧
      (1 / (2 - ρ)).re = (3 / 2) / ‖ρ + 1‖ ^ 2 := by
  have hρ := re_eq_half_of_zeroOrd_ne_zero hGRH χ h
  have ha2 : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hρ]; ring
  have hb2 : ‖ρ + 1‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hρ]; ring
  have hconj : 2 - ρ = (starRingEnd ℂ) (ρ + 1) := by
    apply Complex.ext <;> simp [hρ]; norm_num
  have h2 : ‖2 - ρ‖ = ‖ρ + 1‖ := by rw [hconj, Complex.norm_conj]
  refine ⟨?_, ?_, h2, ?_, ?_⟩
  · exact norm_pos_iff.mpr (fun h0 => by simp [h0] at hρ)
  · exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by rw [ha2, hb2]; linarith)
  · rw [ha2, hb2]; nlinarith [sq_nonneg ρ.im]
  · rw [one_div, Complex.inv_re, ← Complex.sq_norm, h2]
    congr 1
    simp [hρ]; norm_num

/-- Under GRH the series defining `zeroSum` converges (from `summable_zeroOrd_div_normSq`). -/
theorem summable_zeroSum (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖) := by
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    (summable_zeroOrd_div_normSq χ hχ hχ1)
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  · obtain ⟨ha, hab, -, -, -⟩ := zero_facts hGRH χ h0
    gcongr
    rw [sq]
    gcongr

/-- (§5.1) Under GRH, `T(χ) = ∑_ρ 1/|ρ(ρ+1)| ≤ log q + 2`. -/
theorem zeroSum_le (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    zeroSum χ ≤ Real.log q + 2 := by
  have hsum := summable_zeroOrd_div_normSq χ hχ hχ1
  have hre := re_logDeriv_eq_tsum χ hχ hχ1 (s := 2) (by norm_num)
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
  have hL := norm_logDeriv_LFunction_two_le χ
  have hG := re_logDeriv_gammaFactor_two_nonpos χ
  have hreL := Complex.re_le_norm (deriv (LFunction χ) 2 / LFunction χ 2)
  calc zeroSum χ ≤ ∑' ρ : ℂ, 2 * ((zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re) :=
        (summable_zeroSum hGRH χ hχ hχ1).tsum_le_tsum key (hsummR.mul_left 2)
    _ = 2 * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re := tsum_mul_left
    _ = 2 * ((deriv (LFunction χ) 2 / LFunction χ 2
          + deriv (gammaFactor χ) 2 / gammaFactor χ 2).re + Real.log q / 2) := by
        rw [hre]; ring
    _ ≤ Real.log q + 2 := by rw [Complex.add_re]; linarith

/-- (§5.2, "Theorem A") Under GRH, for primitive `χ ≠ 1` mod `q` and `x ≥ 1`:
`|∑_{m<x} Λ(m)χ(m)(1-m/x)| ≤ (√x + 5)(log q + 2) + log x + 5`. -/
theorem norm_smoothPsi_le (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖smoothPsi χ x‖ ≤ (√x + 5) * (Real.log q + 2) + Real.log x + 5 := by
  have hxpos : 0 < x := by linarith
  have hsx : 0 ≤ √x := Real.sqrt_nonneg x
  set F : ℂ → ℂ := fun ρ => (zeroOrd χ ρ : ℂ) *
    ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x)) with hFdef
  have hF : ∀ ρ, ‖F ρ‖ ≤ (√x + 5) * ((zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)) := by
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
      have h4 : 3 / (‖ρ + 1‖ * ‖ρ + 1‖ * x) ≤ 3 / (‖ρ‖ * ‖ρ + 1‖) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [mul_pos hb hb, mul_le_mul_of_nonneg_right hab hb.le]
      have hnorm : ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ))
            + 3 / ((ρ + 1) * (2 - ρ) * x)‖ ≤ (√x + 5) / (‖ρ‖ * ‖ρ + 1‖) := by
        calc _ ≤ ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ + ‖(2 : ℂ) / (ρ * (2 - ρ))‖
              + ‖(3 : ℂ) / ((ρ + 1) * (2 - ρ) * x)‖ :=
              (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
          _ ≤ √x / (‖ρ‖ * ‖ρ + 1‖) + 2 / (‖ρ‖ * ‖ρ + 1‖) + 3 / (‖ρ‖ * ‖ρ + 1‖) := by
              rw [h1, h2', h3]; linarith
          _ = (√x + 5) / (‖ρ‖ * ‖ρ + 1‖) := by ring
      calc ‖F ρ‖ = (zeroOrd χ ρ : ℝ) * ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ))
            + 3 / ((ρ + 1) * (2 - ρ) * x)‖ := by
            simp only [hFdef, norm_mul, Complex.norm_natCast]
        _ ≤ (zeroOrd χ ρ : ℝ) * ((√x + 5) / (‖ρ‖ * ‖ρ + 1‖)) := by gcongr
        _ = _ := by ring
  have hsummL := summable_zeroSum hGRH χ hχ hχ1
  have hsummF : Summable fun ρ => ‖F ρ‖ :=
    Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) hF (hsummL.mul_left _)
  have htsum : ‖∑' ρ, F ρ‖ ≤ (√x + 5) * zeroSum χ := by
    calc ‖∑' ρ, F ρ‖ ≤ ∑' ρ, ‖F ρ‖ := norm_tsum_le_tsum_norm hsummF
      _ ≤ ∑' ρ : ℂ, (√x + 5) * ((zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)) :=
          hsummF.tsum_le_tsum hF (hsummL.mul_left _)
      _ = (√x + 5) * zeroSum χ := tsum_mul_left
  have hT := zeroSum_le hGRH χ hχ hχ1
  have hE := explicit_formula_bound χ hχ hχ1 hx
  have hL := norm_logDeriv_LFunction_two_le χ
  have hA : ‖deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ))‖ ≤ 1 := by
    have h1 : ‖(1 - 1 / (x : ℂ))‖ ≤ 1 := by
      have : (1 - 1 / (x : ℂ)) = ((1 - 1 / x : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have : 1 / x ≤ 1 := by rw [div_le_one hxpos]; exact hx
      have : 0 ≤ 1 / x := by positivity
      constructor <;> linarith
    rw [norm_mul]
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul hL h1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hsplit : smoothPsi χ x =
      (smoothPsi χ x + deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ)) + ∑' ρ, F ρ)
        - deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ)) - ∑' ρ, F ρ := by ring
  have hmul : (√x + 5) * zeroSum χ ≤ (√x + 5) * (Real.log q + 2) :=
    mul_le_mul_of_nonneg_left hT (by linarith)
  calc ‖smoothPsi χ x‖
      ≤ ‖smoothPsi χ x + deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ)) + ∑' ρ, F ρ‖
        + ‖deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ))‖ + ‖∑' ρ, F ρ‖ := by
        conv_lhs => rw [hsplit]
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-! ## §6 Elementary prime-number inputs -/

/-- (§6.1) Chebyshev-type lower bound `ψ₁(x) ≥ ψ(x/2)/2 ≥ ((x/2-1) log 2 - log(x/2+2))/2`. -/
theorem psiOne_lower {x : ℝ} (hx : 0 < x) :
    ((x / 2 - 1) * Real.log 2 - Real.log (x / 2 + 2)) / 2 ≤ psiOne x := by
  have hψ := Chebyshev.psi_ge' (x := x / 2) (by positivity)
  suffices Chebyshev.psi (x / 2) / 2 ≤ psiOne x by linarith
  unfold Chebyshev.psi psiOne
  rw [Finset.sum_div]
  have hmem : ∀ m ∈ Finset.Ioc 0 ⌊x / 2⌋₊, (m : ℝ) ≤ x / 2 := fun m hm =>
    (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp hm).2
  have hsub : Finset.Ioc 0 ⌊x / 2⌋₊ ⊆ Finset.range ⌈x⌉₊ := by
    intro m hm
    rw [Finset.mem_range, Nat.lt_ceil]
    linarith [hmem m hm]
  calc ∑ m ∈ Finset.Ioc 0 ⌊x / 2⌋₊, Λ m / 2
      ≤ ∑ m ∈ Finset.Ioc 0 ⌊x / 2⌋₊, Λ m * (1 - (m : ℝ) / x) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have h1 : (m : ℝ) / x ≤ 1 / 2 := by rw [div_le_iff₀ hx]; linarith [hmem m hm]
        have h2 : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
        nlinarith
    _ ≤ ∑ m ∈ Finset.range ⌈x⌉₊, Λ m * (1 - (m : ℝ) / x) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => ?_
        have h1 : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
        have h2 : (m : ℝ) / x ≤ 1 := by rw [div_le_one hx]; linarith
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by linarith)

/-- (§6.2) Prime powers not coprime to `n`:
`∑_{m<x, (m,n)>1} Λ(m) ≤ log n + (ψ(x) - θ(x)) ≤ log n + 3 (log 4 + 4) √x`. -/
theorem noncoprimeSum_le {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 1 ≤ x) :
    noncoprimeSum n x ≤ Real.log n + 3 * (Real.log 4 + 4) * √x := by
  have hx0 : 0 ≤ x := by linarith
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
        (fun m => ¬ Nat.Prime m), Λ m ≤ 3 * (Real.log 4 + 4) * √x := by
    have h0 : (0 : ℕ) ∉ (Finset.Ioc 0 ⌊x⌋₊).filter (fun m => ¬ Nat.Prime m) := by simp
    calc _ ≤ ∑ m ∈ insert 0 ((Finset.Ioc 0 ⌊x⌋₊).filter (fun m => ¬ Nat.Prime m)), Λ m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_)
            (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
          obtain ⟨hm1, hmp⟩ := Finset.mem_filter.mp hm
          have hmx : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm1).1)
          rcases Nat.eq_zero_or_pos m with rfl | hpos
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
              ⟨Finset.mem_Ioc.mpr ⟨hpos, Nat.le_floor hmx.le⟩, hmp⟩)
      _ = Chebyshev.psi x - Chebyshev.theta x := by
          rw [Finset.sum_insert h0, Chebyshev.psi_sub_theta_eq_sum_not_prime]
          simp
      _ ≤ Chebyshev.psi (x ^ (2 : ℝ)⁻¹) + Chebyshev.psi (x ^ (3 : ℝ)⁻¹)
            + Chebyshev.psi (x ^ (5 : ℝ)⁻¹) := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
      _ ≤ Chebyshev.psi (√x) + Chebyshev.psi (√x) + Chebyshev.psi (√x) := by
          have hs : √x = x ^ (2 : ℝ)⁻¹ := by rw [Real.sqrt_eq_rpow, one_div]
          rw [hs]
          have h3 : Chebyshev.psi (x ^ (3 : ℝ)⁻¹) ≤ Chebyshev.psi (x ^ (2 : ℝ)⁻¹) :=
            Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hx
              (by norm_num : (3 : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹))
          have h5 : Chebyshev.psi (x ^ (5 : ℝ)⁻¹) ≤ Chebyshev.psi (x ^ (2 : ℝ)⁻¹) :=
            Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hx
              (by norm_num : (5 : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹))
          linarith
      _ ≤ 3 * (Real.log 4 + 4) * √x := by
          have := Chebyshev.psi_le_const_mul_self (Real.sqrt_nonneg x)
          linarith
  linarith

/-- (§6.3) Reduction to the primitive character: if `χ(a) = 1` for all units `a < x`, then
`Re S(x, χ*) ≥ ψ₁(x) - 2 ∑_{m<x,(m,n)>1} Λ(m)`. -/
theorem re_smoothPsi_primitive_lower {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) {x : ℝ}
    (hx : 0 < x)
    (h : ∀ a : ℕ, (a : ℝ) < x → IsUnit (a : ZMod n) → χ (a : ZMod n) = 1) :
    psiOne x - 2 * noncoprimeSum n x ≤ (smoothPsi χ.primitiveCharacter x).re := by
  unfold psiOne noncoprimeSum smoothPsi
  rw [Complex.re_sum, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro m hm
  have hmx : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
  have hw0 : 0 ≤ 1 - (m : ℝ) / x := by rw [sub_nonneg, div_le_one hx]; linarith
  have hw1 : 1 - (m : ℝ) / x ≤ 1 := by
    have : 0 ≤ (m : ℝ) / x := by positivity
    linarith
  have hΛ : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  have hre : ((Λ m : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor)
      * (1 - (m : ℂ) / (x : ℂ))).re
      = Λ m * (1 - (m : ℝ) / x) * (χ.primitiveCharacter (m : ZMod χ.conductor)).re := by
    have : (Λ m : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor) * (1 - (m : ℂ) / (x : ℂ))
        = ((Λ m * (1 - (m : ℝ) / x) : ℝ) : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [hre]
  by_cases hc : Nat.Coprime m n
  · have h1 : χ.primitiveCharacter (m : ZMod χ.conductor) = 1 := by
      have h2 := χ.primitiveCharacter_apply_of_isCoprime (a := (m : ℤ))
        (Nat.isCoprime_iff_coprime.mpr hc)
      rw [Int.cast_natCast, Int.cast_natCast] at h2
      rw [h2]
      exact h m hmx ((ZMod.isUnit_iff_coprime m n).mpr hc)
    simp [hc, h1]
  · have hnorm : -1 ≤ (χ.primitiveCharacter (m : ZMod χ.conductor)).re := by
      have h1 := Complex.abs_re_le_norm (χ.primitiveCharacter (m : ZMod χ.conductor))
      have h2 := DirichletCharacter.norm_le_one χ.primitiveCharacter (m : ZMod χ.conductor)
      linarith [neg_abs_le ((χ.primitiveCharacter (m : ZMod χ.conductor)).re)]
    simp only [hc, not_false_eq_true, if_true]
    nlinarith [mul_nonneg hΛ hw0, mul_le_mul_of_nonneg_left hw1 hΛ,
      mul_le_mul_of_nonneg_left hnorm (mul_nonneg hΛ hw0)]

/-! ## §7 Assembly -/

/-- (§7.1) Small moduli are trivial: if no unit `a < 1024 (log n)²` has `χ a ≠ 1`, then
`n > 2¹³` and so `log n ≥ 9`. -/
theorem nine_le_log_of_no_small_witness {n : ℕ} (hn : 2 < n) (χ : DirichletCharacter ℂ n)
    (hχ : χ ≠ 1)
    (h : ∀ a : ℕ, (a : ℝ) < 1024 * (Real.log n) ^ 2 → IsUnit (a : ZMod n) → χ (a : ZMod n) = 1) :
    9 ≤ Real.log n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod n)ˣ, χ u ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hχ (MulChar.ext fun a => by rw [hc a, MulChar.one_apply_coe])
  have hval : ¬ (((u : ZMod n).val : ℝ) < 1024 * Real.log n ^ 2) := fun hlt => hu (by
    have h1 := h (u : ZMod n).val hlt (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    rwa [ZMod.natCast_zmod_val] at h1)
  have hlt : ((u : ZMod n).val : ℝ) < n := by exact_mod_cast ZMod.val_lt _
  have hbig : 1024 * Real.log n ^ 2 < n := by linarith [not_lt.mp hval]
  have h2 := Real.log_two_gt_d9
  have hn0 : (0 : ℝ) < n := by positivity
  have hL1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  have hn1 : (1024 : ℝ) < n := by nlinarith
  have hL2 : 10 * Real.log 2 ≤ Real.log n := by
    have h3 : Real.log ((2 : ℝ) ^ (10 : ℕ)) ≤ Real.log n :=
      Real.log_le_log (by positivity) (by norm_num; exact_mod_cast hn1.le)
    rw [Real.log_pow] at h3
    push_cast at h3
    exact h3
  have hn2 : (8192 : ℝ) < n := by nlinarith
  have hL3 : 13 * Real.log 2 ≤ Real.log n := by
    have h3 : Real.log ((2 : ℝ) ^ (13 : ℕ)) ≤ Real.log n :=
      Real.log_le_log (by positivity) (by norm_num; exact_mod_cast hn2.le)
    rw [Real.log_pow] at h3
    push_cast at h3
    exact h3
  linarith

/-- (§7.2) The final numerical inequality, in the variable `L = log n ≥ 9`, `√x = 32 L`. -/
theorem final_numeric {L : ℝ} (hL : 9 ≤ L) :
    (32 * L + 5) * (L + 2) + Real.log (1024 * L ^ 2) + 5
      < ((1024 * L ^ 2 / 2 - 1) * Real.log 2 - Real.log (1024 * L ^ 2 / 2 + 2)) / 2
        - 2 * (L + 3 * (Real.log 4 + 4) * (32 * L)) := by
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hy : Real.log (1024 * L ^ 2) ≤ 2 * (32 * L) - 2 := by
    have h1 : Real.log (32 * L) ≤ 32 * L - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [show 1024 * L ^ 2 = (32 * L) ^ (2 : ℕ) by ring, Real.log_pow]
    push_cast; linarith
  have hy2 : Real.log (1024 * L ^ 2 / 2 + 2) ≤ Real.log (1024 * L ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hsq : 9 * L ≤ L ^ 2 := by nlinarith
  have a1 : (512 * L ^ 2 - 1) * 0.6931471803 ≤ (512 * L ^ 2 - 1) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2l.le (by nlinarith)
  have a2 : L * Real.log 2 ≤ L * 0.6931471808 :=
    mul_le_mul_of_nonneg_left h2u.le (by linarith)
  rw [h4]
  nlinarith

/-- (§7.3) **GRH ⟹ character form of Bach's bound with `c = 1024`.** -/
theorem bachBoundChar_of_GRH (hGRH : DirichletLZerosOnLine) : BachBoundChar 1024 := by
  intro n hn χ hχ
  by_contra hcon
  push Not at hcon
  have : NeZero n := ⟨by omega⟩
  have hL := nine_le_log_of_no_small_witness hn χ hχ hcon
  have hx1 : (1 : ℝ) ≤ 1024 * Real.log n ^ 2 := by nlinarith
  have hsqrt : √(1024 * Real.log n ^ 2) = 32 * Real.log n := by
    rw [show 1024 * Real.log n ^ 2 = (32 * Real.log n) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hne1 : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, changeLevel_one]
  have hq : Real.log χ.conductor ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level)
  have hA := norm_smoothPsi_le hGRH χ.primitiveCharacter hprim hne1 hx1
  have hlow := re_smoothPsi_primitive_lower χ (x := 1024 * Real.log n ^ 2) (by linarith) hcon
  have hE := noncoprimeSum_le (n := n) (by omega) hx1
  have hψ := psiOne_lower (x := 1024 * Real.log n ^ 2) (by linarith)
  have hre := Complex.re_le_norm (smoothPsi χ.primitiveCharacter (1024 * Real.log n ^ 2))
  have hfin := final_numeric hL
  rw [hsqrt] at hA hE
  have hmul : (32 * Real.log n + 5) * (Real.log χ.conductor + 2)
      ≤ (32 * Real.log n + 5) * (Real.log n + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- (§7.4) Character form ⟹ subgroup form (duality for the finite abelian group `(ℤ/n)ˣ/H`). -/
theorem bachBound_of_bachBoundChar {c : ℝ} (h : BachBoundChar c) : BachBound c := by
  intro n hn H hH
  have : NeZero n := ⟨by omega⟩
  obtain ⟨g, hg⟩ : ∃ g : (ZMod n)ˣ, g ∉ H := by
    by_contra hc
    push Not at hc
    exact hH (eq_top_iff.mpr fun x _ => hc x)
  have hne : (QuotientGroup.mk' H g) ≠ 1 := by
    rwa [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hexp : NeZero (Monoid.exponent ((ZMod n)ˣ ⧸ H)) := 
    ⟨Monoid.exponent_ne_zero.mpr ⟨Nat.card ((ZMod n)ˣ ⧸ H), Nat.card_pos, fun g => pow_card_eq_one'⟩⟩
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ hne
  set χ : DirichletCharacter ℂ n := MulChar.ofUnitHom (φ.comp (QuotientGroup.mk' H)) with hχdef
  have hval : ∀ u : (ZMod n)ˣ, χ (u : ZMod n) = ((φ (QuotientGroup.mk' H u) : ℂˣ) : ℂ) := by
    intro u
    rw [hχdef, MulChar.ofUnitHom_coe]
    rfl
  have hχ : χ ≠ 1 := by
    intro h1
    apply hφ
    have h2 := hval g
    rw [h1, MulChar.one_apply_coe] at h2
    exact Units.ext h2.symm
  obtain ⟨a, ha, hau, haχ⟩ := h n hn χ hχ
  refine ⟨hau.unit, ?_, ?_⟩
  · intro hmem
    apply haχ
    have h2 := hval hau.unit
    rw [IsUnit.unit_spec] at h2
    rw [h2, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hmem]
    simp
  · calc (((hau.unit : ZMod n).val : ℕ) : ℝ) ≤ a := by
          rw [IsUnit.unit_spec, ZMod.val_natCast]
          exact_mod_cast Nat.mod_le a n
      _ < _ := ha

/-- **Main theorem of Layer 2**: GRH for Dirichlet L-functions implies Bach's bound with the
explicit constant `c = 1024`. -/
theorem grh_implies_bach : GRHImpliesBach 1024 :=
  fun hGRH => bachBound_of_bachBoundChar (bachBoundChar_of_GRH hGRH)

end DetPrimality.Bach
