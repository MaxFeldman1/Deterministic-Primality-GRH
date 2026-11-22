import DetPrimality.Bach.Blueprint
import DetPrimality.Bach.Handoffs
import DetPrimality.Bach.Growth
import DetPrimality.Bach.ZeroCount
import DetPrimality.Bach.HadamardGeneral
import DetPrimality.Bach.HadamardL
import DetPrimality.Bach.ExplicitMain
import DetPrimality.Bach.Numerics

/-!
# Layer 2, round 2: sorry-free assembly of GRH ⟹ Bach

`Blueprint.lean` proves `grh_implies_bach : GRHImpliesBach 1024` from four sorried inputs
(§2.1, §2.2, §3, §4.1a).  `Handoffs.lean` (and hence every round-2 file) imports `Blueprint.lean`,
so those sorries cannot be filled in place.  Instead this file

1. packages the four inputs as a `Prop` `BachInputs`;
2. re-proves the downstream assembly (§4.1, §5.1, §5.2, §7.3) as `…_of_inputs`, parameterised
   by `hI : BachInputs` (the proofs are copied verbatim from `Blueprint.lean`, with the sorried
   lemmas replaced by the fields of `hI`; all sorry-free lemmas of `Blueprint.lean` are reused);
3. proves `bachInputs : BachInputs` from the round-2 files (`Growth`, `HadamardL`,
   `ExplicitMain`, `Numerics`), and
4. concludes `grh_implies_bach_v2 : GRHImpliesBach 1024` with no `sorryAx`.

The old chain (`blueprintInputs`, from the Blueprint sorries) is also shown to fit the interface.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The four deep/numerical inputs of the blueprint (the statements of the four sorried lemmas
of `Blueprint.lean`, verbatim). -/
structure BachInputs : Prop where
  /-- §2.1 -/
  summable : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2
  /-- §2.2 -/
  reLogDeriv : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
    ∀ {s : ℂ}, 1 < s.re →
    (deriv (LFunction χ) s / LFunction χ s + deriv (gammaFactor χ) s / gammaFactor χ s).re
      = -(Real.log q) / 2 + ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (s - ρ)).re
  /-- §3 -/
  explicit : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
    ∀ {x : ℝ}, 1 ≤ x →
    ‖smoothPsi χ x + deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ))
        + ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) *
            ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x))‖
      ≤ Real.log x + 4
  /-- §4.1a -/
  vonMangoldt : ∑' n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ ≤ 1

/-- The old (round-1) chain: the four inputs as sorried in `Blueprint.lean`. -/
theorem blueprintInputs : BachInputs where
  summable χ hχ hχ1 := summable_zeroOrd_div_normSq χ hχ hχ1
  reLogDeriv χ hχ hχ1 _ hs := re_logDeriv_eq_tsum χ hχ hχ1 hs
  explicit χ hχ hχ1 _ hx := explicit_formula_bound χ hχ hχ1 hx
  vonMangoldt := tsum_vonMangoldt_term_two_le

/-- **Round 2: all four inputs, sorry-free.**
* §2.1 from `growth_completedLFunction` (`Growth.lean`) + `summable_zeroOrd_div_normSq_proof`
  (`HadamardL.lean`; Jensen);
* §2.2 from `re_logDeriv_eq_tsum_of_growth` (`HadamardL.lean`; genus-1 Hadamard partial
  fractions + functional equation);
* §3 from `explicit_formula_bound_of_hadamard` (`ExplicitMain.lean`);
* §4.1a from `Numerics.tsum_vonMangoldt_term_two_le_proof`. -/
theorem bachInputs : BachInputs where
  summable χ hχ hχ1 :=
    summable_zeroOrd_div_normSq_proof χ hχ hχ1 (growth_completedLFunction χ hχ1)
  reLogDeriv χ hχ hχ1 _ hs :=
    re_logDeriv_eq_tsum_of_growth χ hχ hχ1 (growth_completedLFunction χ hχ1) hs
  explicit χ hχ hχ1 _ hx :=
    explicit_formula_bound_of_hadamard χ hχ hχ1
      (hadamardLogDeriv_of_growth χ hχ hχ1 (growth_completedLFunction χ hχ1))
      (summable_zeroOrd_div_normSq_proof χ hχ hχ1 (growth_completedLFunction χ hχ1)) hx
  vonMangoldt := Numerics.tsum_vonMangoldt_term_two_le_proof

/-! ## Downstream assembly, parameterised by `BachInputs` -/

section OfInputs

variable (hI : BachInputs)
include hI

/-- (§4.1) `|L'/L(2, χ)| ≤ ∑ Λ(n)/n² ≤ 1` for every Dirichlet character. -/
theorem norm_logDeriv_LFunction_two_le_of_inputs {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖deriv (LFunction χ) 2 / LFunction χ 2‖ ≤ 1 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have hsum : Summable fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) hs).norm
  have h1 := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs, neg_div] at h1
  rw [← norm_neg]
  refine (HasSum.norm_le_of_bounded h1 hsum.hasSum fun n => ?_).trans hI.vonMangoldt
  refine LSeries.norm_term_le 2 (g := fun n => (Λ n : ℂ)) ?_
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem summable_zeroSum_of_inputs (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖) := by
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    (hI.summable χ hχ hχ1)
  by_cases h0 : zeroOrd χ ρ = 0
  · simp [h0]
  · obtain ⟨ha, hab, -, -, -⟩ := zero_facts hGRH χ h0
    gcongr
    rw [sq]
    gcongr

/-- (§5.1) Under GRH, `T(χ) = ∑_ρ 1/|ρ(ρ+1)| ≤ log q + 2`. -/
theorem zeroSum_le_of_inputs (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    zeroSum χ ≤ Real.log q + 2 := by
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
  have hL := norm_logDeriv_LFunction_two_le_of_inputs hI χ
  have hG := re_logDeriv_gammaFactor_two_nonpos χ
  have hreL := Complex.re_le_norm (deriv (LFunction χ) 2 / LFunction χ 2)
  calc zeroSum χ ≤ ∑' ρ : ℂ, 2 * ((zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re) :=
        (summable_zeroSum_of_inputs hI hGRH χ hχ hχ1).tsum_le_tsum key (hsummR.mul_left 2)
    _ = 2 * ∑' ρ : ℂ, (zeroOrd χ ρ : ℝ) * (1 / (2 - ρ)).re := tsum_mul_left
    _ = 2 * ((deriv (LFunction χ) 2 / LFunction χ 2
          + deriv (gammaFactor χ) 2 / gammaFactor χ 2).re + Real.log q / 2) := by
        rw [hre]; ring
    _ ≤ Real.log q + 2 := by rw [Complex.add_re]; linarith

/-- (§5.2, "Theorem A") Under GRH, for primitive `χ ≠ 1` mod `q` and `x ≥ 1`:
`|∑_{m<x} Λ(m)χ(m)(1-m/x)| ≤ (√x + 5)(log q + 2) + log x + 5`. -/
theorem norm_smoothPsi_le_of_inputs (hGRH : DirichletLZerosOnLine) {q : ℕ} [NeZero q]
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
  have hsummL := summable_zeroSum_of_inputs hI hGRH χ hχ hχ1
  have hsummF : Summable fun ρ => ‖F ρ‖ :=
    Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) hF (hsummL.mul_left _)
  have htsum : ‖∑' ρ, F ρ‖ ≤ (√x + 5) * zeroSum χ := by
    calc ‖∑' ρ, F ρ‖ ≤ ∑' ρ, ‖F ρ‖ := norm_tsum_le_tsum_norm hsummF
      _ ≤ ∑' ρ : ℂ, (√x + 5) * ((zeroOrd χ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)) :=
          hsummF.tsum_le_tsum hF (hsummL.mul_left _)
      _ = (√x + 5) * zeroSum χ := tsum_mul_left
  have hT := zeroSum_le_of_inputs hI hGRH χ hχ hχ1
  have hE := hI.explicit χ hχ hχ1 hx
  have hL := norm_logDeriv_LFunction_two_le_of_inputs hI χ
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

/-- (§7.3) GRH ⟹ character form of Bach's bound with `c = 1024`, given `BachInputs`. -/
theorem bachBoundChar_of_GRH_of_inputs (hGRH : DirichletLZerosOnLine) : BachBoundChar 1024 := by
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
  have hA := norm_smoothPsi_le_of_inputs hI hGRH χ.primitiveCharacter hprim hne1 hx1
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

/-- GRH ⟹ Bach's bound with `c = 1024`, given the four inputs. -/
theorem grh_implies_bach_of_inputs : GRHImpliesBach 1024 :=
  fun hGRH => bachBound_of_bachBoundChar (bachBoundChar_of_GRH_of_inputs hI hGRH)

end OfInputs

/-- **Round 2 main theorem (sorry-free).** -/
theorem bachBoundChar_of_GRH_v2 (hGRH : DirichletLZerosOnLine) : BachBoundChar 1024 :=
  bachBoundChar_of_GRH_of_inputs bachInputs hGRH

/-- **Round 2 main theorem (sorry-free)**: GRH for Dirichlet L-functions implies Bach's bound
with the explicit constant `c = 1024`. -/
theorem grh_implies_bach_v2 : GRHImpliesBach 1024 :=
  grh_implies_bach_of_inputs bachInputs

end DetPrimality.Bach
