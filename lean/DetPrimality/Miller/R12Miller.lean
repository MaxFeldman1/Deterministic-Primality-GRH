import Mathlib
import DetPrimality.Bach.R12M4
import DetPrimality.Miller.Composite

/-!
# The deterministic Miller test with `c < 1` (miller4.md, Corollary)

Inputs: GRH, the Round-11 Props, and Lemma M (`hLiar`, the statement of
`Miller.liar4_exists_subgroup` in `Miller/LiarIndex.lean`): for odd composite `n ≠ 9` the strong
liars lie in a subgroup of index `≥ 4`.

* `r12_millerDet_eq_false_pointwise`: if the strong liars mod `n` lie in a subgroup of index `≥ 4`
  and `Bach.R12Bound c n` holds, then `millerDet c n = false` (odd composite `n > 2`).
* `r12_millerDet_correct` (`c = 7/10`, `n ≥ 10¹¹`), `r12_millerDet_correct_66` (`c = 33/50`,
  `n ≥ 10¹²`), `r12_millerDet_correct_65` (`c = 13/20`, `n ≥ 10¹³`):
  `millerDet c n = true ↔ n.Prime`.
-/

namespace DetPrimality.Miller

/-- Subgroup version of `llsAsm_millerDet_eq_false_pointwise`. -/
theorem r12_millerDet_eq_false_pointwise {c : ℚ} (hc : 0 ≤ c) {n : ℕ} (hn : 2 < n)
    (hodd : n % 2 = 1) (hnp : ¬ n.Prime)
    (hH : ∃ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index ∧ ∀ x, IsStrongLiar n x → x ∈ H)
    (hB : Bach.R12Bound (c : ℝ) n) : millerDet c n = false := by
  rw [Bool.eq_false_iff, Ne, millerDet_iff_all c hn hodd]
  intro hall
  obtain ⟨H, hH4, hliar⟩ := hH
  obtain ⟨a, ha1, hab, haH⟩ := hB H hH4
  have hlt : a < millerBound c n := by
    have := millerBound_ge hc n
    exact_mod_cast hab.trans_le this
  rcases lt_or_ge a n with han | han
  · have ha2 : 2 ≤ a := by
      rcases Nat.lt_or_ge a 2 with h | h
      · exfalso
        have h1a : a = 1 := by omega
        subst h1a
        rcases haH with h1 | ⟨u, hu, huH⟩
        · exact h1 (by simp)
        · have hu1 : u = 1 := Units.ext (by rw [hu]; simp)
          exact huH (hu1 ▸ H.one_mem)
      · exact h
    have hs := hall a ha2 hlt han
    have hu := millerComp_isUnit_of_sprp (by omega) hs
    have hmem : hu.unit ∈ H := by
      apply hliar
      rw [isStrongLiar_iff_sprp (by omega), IsUnit.unit_spec, ZMod.val_natCast,
        Nat.mod_eq_of_lt han]
      exact hs
    rcases haH with h1 | ⟨u, hu', huH⟩
    · exact h1 hu
    · have hu1 : u = hu.unit := Units.ext (by rw [hu', IsUnit.unit_spec])
      exact huH (hu1 ▸ hmem)
  · have hp := Nat.minFac_prime (n := n) (by omega)
    have hpn : n.minFac < n := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
    have hs := hall n.minFac hp.two_le (by omega) hpn
    have hu := millerComp_isUnit_of_sprp (by omega) hs
    rw [ZMod.isUnit_iff_coprime] at hu
    have h1' := Nat.Coprime.eq_one_of_dvd hu (Nat.minFac_dvd n)
    have := hp.two_le
    omega

/-- Correctness of `millerDet c` at `n ≥ 10`, from Lemma M and the subgroup bound at `n`. -/
theorem r12_millerDet_correct_of_bound {c : ℚ} (hc : 0 ≤ c)
    (hLiar : ∀ {n : ℕ}, 2 < n → n % 2 = 1 → ¬ n.Prime → n ≠ 9 →
      ∃ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index ∧ ∀ x, IsStrongLiar n x → x ∈ H)
    {n : ℕ} (hn : 10 ≤ n) (hB : Bach.R12Bound (c : ℝ) n) : millerDet c n = true ↔ n.Prime := by
  constructor
  · intro h
    by_contra hnp
    have hfalse : millerDet c n = false := by
      by_cases h3 : n % 2 = 0
      · have h1 : ¬ n < 2 := by omega
        have h2 : n ≠ 2 := by omega
        simp [millerDet, h1, h2, h3]
      · exact r12_millerDet_eq_false_pointwise hc (by omega) (by omega) hnp
          (hLiar (by omega) (by omega) hnp (by omega)) hB
    rw [hfalse] at h
    exact Bool.false_ne_true h
  · exact millerDet_of_prime c

/-- **Deterministic Miller test with `c = 7/10`**: correct for every `n ≥ 10¹¹`, under GRH, the
Round-11 Props and Lemma M. -/
theorem r12_millerDet_correct (hGRH : DirichletLZerosOnLine) (hZ : Bach.R11ZetaZ)
    (hA : Bach.R11ZetaExplicit) (hC : Bach.R11ChiExplicit) (hG : Bach.R11ZeroSumGain)
    (hLiar : ∀ {n : ℕ}, 2 < n → n % 2 = 1 → ¬ n.Prime → n ≠ 9 →
      ∃ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index ∧ ∀ x, IsStrongLiar n x → x ∈ H)
    (n : ℕ) (hn : (10 : ℝ) ^ 11 ≤ n) : millerDet (7 / 10) n = true ↔ n.Prime := by
  have hn' : 10 ^ 11 ≤ n := by exact_mod_cast hn
  have e : ((7 / 10 : ℚ) : ℝ) = 0.7 := by norm_num
  refine r12_millerDet_correct_of_bound (by norm_num) hLiar (by omega) ?_
  rw [e]
  exact (Bach.r12_subgroup_table hGRH hZ hA hC hG).2.2.1 n hn

/-- The same with `c = 33/50 = 0.66`, `n ≥ 10¹²`. -/
theorem r12_millerDet_correct_66 (hGRH : DirichletLZerosOnLine) (hZ : Bach.R11ZetaZ)
    (hA : Bach.R11ZetaExplicit) (hC : Bach.R11ChiExplicit) (hG : Bach.R11ZeroSumGain)
    (hLiar : ∀ {n : ℕ}, 2 < n → n % 2 = 1 → ¬ n.Prime → n ≠ 9 →
      ∃ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index ∧ ∀ x, IsStrongLiar n x → x ∈ H)
    (n : ℕ) (hn : (10 : ℝ) ^ 12 ≤ n) : millerDet (33 / 50) n = true ↔ n.Prime := by
  have hn' : 10 ^ 12 ≤ n := by exact_mod_cast hn
  have e : ((33 / 50 : ℚ) : ℝ) = 0.66 := by norm_num
  refine r12_millerDet_correct_of_bound (by norm_num) hLiar (by omega) ?_
  rw [e]
  exact (Bach.r12_subgroup_table hGRH hZ hA hC hG).2.2.2.2.1 n hn

/-- The same with `c = 13/20 = 0.65`, `n ≥ 10¹³`. -/
theorem r12_millerDet_correct_65 (hGRH : DirichletLZerosOnLine) (hZ : Bach.R11ZetaZ)
    (hA : Bach.R11ZetaExplicit) (hC : Bach.R11ChiExplicit) (hG : Bach.R11ZeroSumGain)
    (hLiar : ∀ {n : ℕ}, 2 < n → n % 2 = 1 → ¬ n.Prime → n ≠ 9 →
      ∃ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index ∧ ∀ x, IsStrongLiar n x → x ∈ H)
    (n : ℕ) (hn : (10 : ℝ) ^ 13 ≤ n) : millerDet (13 / 20) n = true ↔ n.Prime := by
  have hn' : 10 ^ 13 ≤ n := by exact_mod_cast hn
  have e : ((13 / 20 : ℚ) : ℝ) = 0.65 := by norm_num
  refine r12_millerDet_correct_of_bound (by norm_num) hLiar (by omega) ?_
  rw [e]
  exact (Bach.r12_subgroup_table hGRH hZ hA hC hG).2.2.2.2.2 n hn

end DetPrimality.Miller

#print axioms DetPrimality.Miller.r12_millerDet_eq_false_pointwise
#print axioms DetPrimality.Miller.r12_millerDet_correct
#print axioms DetPrimality.Miller.r12_millerDet_correct_66
#print axioms DetPrimality.Miller.r12_millerDet_correct_65
