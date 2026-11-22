import Mathlib
import DetPrimality.Bach.LLSAssembly
import DetPrimality.Miller.Composite
import DetPrimality.Miller.LLSSmall

/-!
# The deterministic Miller test with `c = 1` (Lamzouri–Li–Soundararajan)

`llsAsm_millerDet_one_correct`: under GRH and the four LLS inputs of `Bach/LLSDefs.lean`,
`millerDet 1 n = true ↔ n.Prime` for every `n`.  For `n < 3000` this is the kernel-checked table
`llsElem_millerDet_one_small`; for `n ≥ 3000` it follows from `Bach.llsAsm_bachBound_one` and a
pointwise version of `millerDet_eq_false_of_not_prime_of_composite`.
-/

namespace DetPrimality.Miller

/-- Pointwise form of `millerDet_eq_false_of_not_prime_of_composite`: the character bound is only
needed at the modulus `n` itself. -/
theorem llsAsm_millerDet_eq_false_pointwise {c : ℚ} (hc : 0 ≤ c) {n : ℕ} (hn : 2 < n)
    (hodd : n % 2 = 1) (hnp : ¬ n.Prime)
    (hB : ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < (c : ℝ) * Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1) :
    millerDet c n = false := by
  rw [Bool.eq_false_iff, Ne, millerDet_iff_all c hn hodd]
  intro hall
  obtain ⟨H, hH, hliar⟩ := exists_proper_subgroup_strongLiars hn hodd hnp
  have : NeZero n := ⟨by omega⟩
  obtain ⟨χ, hχ, hχH⟩ := millerComp_exists_char hH
  obtain ⟨a, ha1, hab, haχ⟩ := hB χ hχ
  have hlt : a < millerBound c n := by
    have := millerBound_ge hc n
    exact_mod_cast hab.trans_le this
  rcases lt_or_ge a n with han | han
  · have ha2 : 2 ≤ a := by
      rcases Nat.lt_or_ge a 2 with h | h
      · exfalso
        have h1a : a = 1 := by omega
        subst h1a
        exact haχ (by simp)
      · exact h
    have hs := hall a ha2 hlt han
    have hu := millerComp_isUnit_of_sprp (by omega) hs
    apply haχ
    have hmem : hu.unit ∈ H := by
      apply hliar
      rw [isStrongLiar_iff_sprp (by omega), IsUnit.unit_spec, ZMod.val_natCast,
        Nat.mod_eq_of_lt han]
      exact hs
    have := hχH hu.unit hmem
    rwa [IsUnit.unit_spec] at this
  · have hp := Nat.minFac_prime (n := n) (by omega)
    have hpn : n.minFac < n := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
    have hs := hall n.minFac hp.two_le (by omega) hpn
    have hu := millerComp_isUnit_of_sprp (by omega) hs
    rw [ZMod.isUnit_iff_coprime] at hu
    have h1' := Nat.Coprime.eq_one_of_dvd hu (Nat.minFac_dvd n)
    have := hp.two_le
    omega

/-- What LLS gives, in the shape of `BachBoundCharComposite 1` restricted to `n ≥ 3000`
(at the rational constant used by the algorithm). -/
theorem llsAsm_bachBoundCharComposite_one_ge_3000 (hGRH : DirichletLZerosOnLine)
    (hZ : Bach.LLSZetaLower (1 / 20)) (hU : Bach.LLSChiUpper) (hG : Bach.LLSZeroSumGain)
    (hW : Bach.LLSWeightedLower) :
    ∀ n : ℕ, 3000 ≤ n → ¬ n.Prime → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < ((1 : ℚ) : ℝ) * Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1 := by
  intro n hn hnp χ hχ
  obtain ⟨a, ha, hab, hχa⟩ := Bach.llsAsm_bachBound_one hGRH hZ hU hG hW n hn hnp χ hχ
  exact ⟨a, ha, by push_cast; linarith, hχa⟩

/-- **Deterministic Miller test with `c = 1`** (LLS Theorem 1.1(2)): correct for every `n`,
under GRH and the four LLS inputs. -/
theorem llsAsm_millerDet_one_correct (hGRH : DirichletLZerosOnLine)
    (hZ : Bach.LLSZetaLower (1 / 20)) (hU : Bach.LLSChiUpper) (hG : Bach.LLSZeroSumGain)
    (hW : Bach.LLSWeightedLower) (n : ℕ) : millerDet 1 n = true ↔ n.Prime := by
  rcases lt_or_ge n 3000 with hsmall | hbig
  · exact llsElem_millerDet_one_small n hsmall
  constructor
  · intro h
    by_contra hnp
    have hfalse : millerDet 1 n = false := by
      by_cases h3 : n % 2 = 0
      · have h1 : ¬ n < 2 := by omega
        have h2 : n ≠ 2 := by omega
        simp [millerDet, h1, h2, h3]
      · exact llsAsm_millerDet_eq_false_pointwise (by norm_num) (by omega) (by omega) hnp
          (llsAsm_bachBoundCharComposite_one_ge_3000 hGRH hZ hU hG hW n hbig hnp)
    rw [hfalse] at h
    exact Bool.false_ne_true h
  · exact millerDet_of_prime 1

/-- Version with the unconditional input `llsElem_weightedLower` discharged. -/
theorem llsAsm_millerDet_one_correct' (hGRH : DirichletLZerosOnLine)
    (hZ : Bach.LLSZetaLower (1 / 20)) (hU : Bach.LLSChiUpper) (hG : Bach.LLSZeroSumGain)
    (n : ℕ) : millerDet 1 n = true ↔ n.Prime :=
  llsAsm_millerDet_one_correct hGRH hZ hU hG Bach.llsElem_weightedLower n

end DetPrimality.Miller

#print axioms DetPrimality.Miller.llsAsm_bachBoundCharComposite_one_ge_3000
#print axioms DetPrimality.Miller.llsAsm_millerDet_one_correct
#print axioms DetPrimality.Miller.llsAsm_millerDet_one_correct'
