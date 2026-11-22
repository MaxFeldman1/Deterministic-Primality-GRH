import Mathlib
import DetPrimality.Bach.LLSAssembly
import DetPrimality.Bach.LLSZetaLower
import DetPrimality.Bach.LLSPerronMain
import DetPrimality.Bach.LLSGain

/-!
# LLS Theorem 1.1(2) for arbitrary (in particular prime) moduli

The proof of `llsAsm_bachBound_one` never uses compositeness: if `χ ≠ 1` mod `n` is `1` at every
`1 ≤ a < log² n` then all those `a` are automatically coprime to `n` (non-units have `χ a = 0`),
which is all LLS Part 2 needs.  So the statement holds for every `n ≥ 3000`
(`llsPrime_bachBound_one_all`).  We specialise to composite `n` (`llsPrime_composite`, re-deriving
`llsAsm_bachBound_one`) and to primes `p` (`llsPrime_prime`), where additionally `a < p`
(`llsPrime_log_sq_lt`), so the witness is a unit: LLS Corollary 1.1.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- **LLS Theorem 1.1(2) for all moduli `n ≥ 3000`** (from the four LLS inputs). -/
theorem llsPrime_bachBound_one_all (hGRH : DirichletLZerosOnLine)
    (hZ : LLSZetaLower (1 / 20)) (hU : LLSChiUpper) (hG : LLSZeroSumGain) (hW : LLSWeightedLower) :
    ∀ n : ℕ, 3000 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1 := by
  intro n hn χ hχ
  by_contra hcon
  have hcon' : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < Real.log n ^ 2 → χ (a : ZMod n) = 1 := by
    intro a ha hax
    by_contra h
    exact hcon ⟨a, ha, hax, h⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 8 ≤ Real.log n :=
    llsAsm_log_3000.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hL0 : 0 ≤ Real.log n := by linarith
  have hX : (64 : ℝ) ≤ Real.log n ^ 2 := by nlinarith
  obtain ⟨-, hprim, hne1, hc0, -, -, hq, -, -, hS, -, hWre⟩ :=
    llsElem_no_witness_facts (by omega) χ hχ hcon'
  have : NeZero χ.conductor := ⟨hc0⟩
  have hsqrt : √(Real.log n ^ 2) = Real.log n := Real.sqrt_sq hL0
  have hlogX : Real.log (Real.log n ^ 2) = 2 * Real.log (Real.log n) := by
    rw [Real.log_pow]; norm_num
  have hcpos : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero hc0
  have hu : Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi :=
    Real.log_div hcpos.ne' Real.pi_ne_zero
  have h2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  have hG' := hG hGRH χ.conductor χ.primitiveCharacter hprim hne1 (Real.log n ^ 2) hX
  have hU' := hU hGRH χ.conductor χ.primitiveCharacter hprim hne1 (Real.log n ^ 2) (by linarith)
  have hZ' := hZ hGRH (Real.log n ^ 2) hX
  have hW' := hW (Real.log n ^ 2) hX
  rw [hsqrt, hWre] at hG'
  rw [hsqrt, hS, hlogX] at hU'
  rw [hsqrt, hlogX, h2pi] at hZ'
  rw [hlogX] at hW'
  refine llsAsm_real_contra (L := Real.log n) (ℓ := Real.log (Real.log n))
    (p := Real.log Real.pi) (l2 := Real.log 2) (Z := zeroSumSq χ.primitiveCharacter)
    (u := Real.log ((χ.conductor : ℝ) / Real.pi)) (S := logPsiZeta (Real.log n ^ 2))
    hL (llsAsm_loglog_ge hL) szs_log_pi_gt.le llsAsm_log_pi_le
    (by linarith [Real.log_two_lt_d9]) (by rw [hu]; linarith) (by linarith) ?_ hZ'
  calc logPsiZeta (Real.log n ^ 2) ≤ _ := hU'
    _ = _ := by ring

/-- Sanity check: the composite case re-derives the statement of `llsAsm_bachBound_one`. -/
theorem llsPrime_composite (hGRH : DirichletLZerosOnLine)
    (hZ : LLSZetaLower (1 / 20)) (hU : LLSChiUpper) (hG : LLSZeroSumGain) (hW : LLSWeightedLower) :
    ∀ n : ℕ, 3000 ≤ n → ¬ n.Prime → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1 :=
  fun n hn _ => llsPrime_bachBound_one_all hGRH hZ hU hG hW n hn

/-- **Under GRH alone**: every `χ ≠ 1` mod `n ≥ 3000` has a witness `1 ≤ a < log² n`. -/
theorem llsPrime_bachBound_one_all_of_GRH (hGRH : DirichletLZerosOnLine) :
    ∀ n : ℕ, 3000 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1 :=
  llsPrime_bachBound_one_all hGRH llsZL_main llsPer_chiUpper llsGain_main llsElem_weightedLower

/-- `log² x < x` for `x ≥ 256`. -/
theorem llsPrime_log_sq_lt {x : ℝ} (hx : 256 ≤ x) : Real.log x ^ 2 < x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have hs16 : 16 ≤ √x := by
    by_contra h
    push Not at h
    nlinarith
  have ht0 : 0 ≤ √(√x) := Real.sqrt_nonneg _
  have htt : √(√x) * √(√x) = √x := Real.mul_self_sqrt hs0
  have ht4 : 4 ≤ √(√x) := by
    by_contra h
    push Not at h
    nlinarith
  have hlog : Real.log x = 4 * Real.log (√(√x)) := by
    rw [Real.log_sqrt hs0, Real.log_sqrt hx0]; ring
  have h1 : Real.log (√(√x)) ≤ √(√x) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h0 : 0 ≤ Real.log (√(√x)) := Real.log_nonneg (by linarith)
  rw [hlog]
  nlinarith

/-- **LLS Corollary 1.1, character form**: under GRH, for a prime `p ≥ 3000` every `χ ≠ 1` mod `p`
has a witness `1 ≤ a < log² p` (so `a < p`, a unit) with `χ a ≠ 1`. -/
theorem llsPrime_prime (hGRH : DirichletLZerosOnLine) (p : ℕ) (hp : p.Prime) (hp3 : 3000 ≤ p)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < Real.log p ^ 2 ∧ a < p ∧ IsUnit (a : ZMod p) ∧
      χ (a : ZMod p) ≠ 1 := by
  obtain ⟨a, ha1, hab, hχa⟩ := llsPrime_bachBound_one_all_of_GRH hGRH p hp3 χ hχ
  have hlt : (a : ℝ) < p := hab.trans (llsPrime_log_sq_lt (by exact_mod_cast (by omega : 256 ≤ p)))
  have hlt' : a < p := by exact_mod_cast hlt
  refine ⟨a, ha1, hab, hlt', ?_, hχa⟩
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt ha1 hlt'))

end DetPrimality.Bach

#print axioms DetPrimality.Bach.llsPrime_bachBound_one_all
#print axioms DetPrimality.Bach.llsPrime_bachBound_one_all_of_GRH
#print axioms DetPrimality.Bach.llsPrime_prime
