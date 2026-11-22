import Mathlib
import DetPrimality.Bach.LLSPrime
import DetPrimality.Miller.Composite
import DetPrimality.Miller.LLSSmall
import DetPrimality.TonelliShanks.Basic

/-!
# Deterministic Tonelli–Shanks with `c = 1` (LLS Corollary 1.1)

* `llsPrime_findNonResidue_isSome`, `llsPrime_sqrtModDet_correct_pointwise`,
  `llsPrime_sqrtModDet_isSome_iff_pointwise`: pointwise versions of the results of
  `TonelliShanks/Basic.lean`, needing only a non-residue inside the search window
  `a < nonResidueBound c p + 2` for the given `p`.
* `llsPrime_exists_nonresidue`: under GRH, a prime `p ≥ 3000` has a quadratic non-residue
  `a < log² p` (LLS Corollary 1.1).
* `llsPrime_small`: kernel-checked table for the odd primes `p < 3000`.
* `llsPrime_sqrtModDet_correct`, `llsPrime_sqrtModDet_isSome_iff`: the end results for `c = 1`.
-/

namespace DetPrimality
namespace TonelliShanks

/-! ### Pointwise versions -/

/-- Pointwise form of `findNonResidue_isSome`: the search window is `2 ≤ a < B(p) + 2`. -/
theorem llsPrime_findNonResidue_isSome {c : ℚ} (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (h : ∃ a : ℕ, a < nonResidueBound c p + 2 ∧ ¬ IsSquare (a : ZMod p)) :
    ∃ z, findNonResidue c p = some z := by
  obtain ⟨a, haB, hns⟩ := h
  have ha2 : 2 ≤ a := by
    by_contra h
    push Not at h
    interval_cases a
    · exact hns ⟨0, by simp⟩
    · exact hns ⟨1, by simp⟩
  cases hf : findNonResidue c p with
  | some z => exact ⟨z, rfl⟩
  | none =>
    exfalso
    rw [findNonResidue, List.find?_eq_none] at hf
    exact hf a (List.mem_range'_1.2 ⟨ha2, by omega⟩) ((isNonResidueB_iff p hp a).2 hns)

/-- Pointwise form of `sqrtModDet_correct`. -/
theorem llsPrime_sqrtModDet_correct_pointwise {c : ℚ} (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (h : ∃ a : ℕ, a < nonResidueBound c p + 2 ∧ ¬ IsSquare (a : ZMod p)) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, sqrtModDet c p n = some r ∧ ((r : ZMod p)) ^ 2 = n := by
  intro hn
  by_cases h0 : n % p = 0
  · refine ⟨0, by simp [sqrtModDet, h0], ?_⟩
    rw [natCast_eq_zero_of_mod h0]
    simp
  · have hn0 : (n : ZMod p) ≠ 0 := by
      intro h
      apply h0
      have := (ZMod.natCast_eq_natCast_iff' n 0 p).1 (by rw [h, Nat.cast_zero])
      simpa using this
    obtain ⟨z, hz⟩ := llsPrime_findNonResidue_isSome p hp h
    obtain ⟨r, hr, hr2⟩ := tonelliShanks_correct p hp n z (findNonResidue_spec hp hz) hn0 hn
    refine ⟨r, ?_, hr2⟩
    have hc' : r * r % p = n % p := by
      rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_mul, ← sq, hr2]
    unfold sqrtModDet
    rw [if_neg h0]
    simp only [hz, hr]
    rw [if_pos hc']

/-- Pointwise form of `sqrtModDet_isSome_iff`. -/
theorem llsPrime_sqrtModDet_isSome_iff_pointwise {c : ℚ} (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (h : ∃ a : ℕ, a < nonResidueBound c p + 2 ∧ ¬ IsSquare (a : ZMod p)) (n : ℕ) :
    (sqrtModDet c p n).isSome ↔ IsSquare (n : ZMod p) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
    exact ⟨r, by rw [← sqrtModDet_sound hr, sq]⟩
  · intro hn
    obtain ⟨r, hr, -⟩ := llsPrime_sqrtModDet_correct_pointwise p hp h n hn
    simp [hr]

/-! ### Large primes: LLS Corollary 1.1 -/

/-- **LLS Corollary 1.1**: under GRH, a prime `p ≥ 3000` has a quadratic non-residue
`1 ≤ a < log² p`. -/
theorem llsPrime_exists_nonresidue (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp3 : 3000 ≤ p) :
    ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < Real.log p ^ 2 ∧ ¬ IsSquare (a : ZMod p) := by
  have hp2 : p ≠ 2 := by omega
  set H : Subgroup (ZMod p)ˣ := (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range with hH
  have hmem : ∀ u : (ZMod p)ˣ, IsSquare (u : ZMod p) → u ∈ H := by
    intro u
    simp only [hH, MonoidHom.mem_range, powMonoidHom_apply]
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    refine ⟨Units.mk0 y hy0, ?_⟩
    ext
    simp [sq, hy]
  have hmem' : ∀ u : (ZMod p)ˣ, u ∈ H → IsSquare (u : ZMod p) := by
    intro u
    simp only [hH, MonoidHom.mem_range, powMonoidHom_apply]
    rintro ⟨v, rfl⟩
    exact ⟨v, by simp [sq]⟩
  have hne : H ≠ ⊤ := by
    obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p)
      (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx ⟨0, by simp⟩
    intro htop
    have hxH : Units.mk0 x hx0 ∈ H := by rw [htop]; exact Subgroup.mem_top _
    exact hx (by simpa using hmem' _ hxH)
  have : NeZero p := ⟨by omega⟩
  obtain ⟨χ, hχ, hχH⟩ := Miller.millerComp_exists_char hne
  obtain ⟨a, ha1, hab, -, hu, hχa⟩ := Bach.llsPrime_prime hGRH p Fact.out hp3 χ hχ
  refine ⟨a, ha1, hab, fun hsq => hχa ?_⟩
  have := hχH hu.unit (hmem _ (by rwa [IsUnit.unit_spec]))
  rwa [IsUnit.unit_spec] at this

/-! ### Small primes: a kernel-checked table -/

/-- Some `2 ≤ a < 22` inside the search window (checked via `log2 p + 1 ≤ size p`) is a
quadratic non-residue mod `p` by Euler's criterion. -/
def llsPrime_nrCheck (p : ℕ) : Bool :=
  (List.range' 2 20).any (fun a =>
    decide ((a - 2) * 1000000 < 480454 * (Miller.llsElem_log2F p p + 1) ^ 2) &&
      a ^ (p / 2) % p == p - 1)

theorem llsPrime_table :
    (List.range 3000).all
      (fun p => !Miller.llsElem_primeB p || decide (p = 2) || llsPrime_nrCheck p) = true := by
  decide +kernel

/-- Every odd prime `p < 3000` has a non-residue in the search window of `sqrtModDet 1`. -/
theorem llsPrime_small (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hp3 : p < 3000) :
    ∃ a : ℕ, a < nonResidueBound 1 p + 2 ∧ ¬ IsSquare (a : ZMod p) := by
  have hpr : p.Prime := Fact.out
  have h := List.all_eq_true.mp llsPrime_table p (List.mem_range.mpr hp3)
  rw [(Miller.llsElem_primeB_iff hp3).mpr hpr] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h hp
  simp only [llsPrime_nrCheck, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨a, -, hlt, hnr⟩ := h
  refine ⟨a, ?_, ?_⟩
  · rw [Miller.llsElem_log2F_eq p p le_rfl] at hlt
    have hsz : Nat.log2 p + 1 ≤ Nat.size p :=
      Nat.lt_size.mpr (Nat.log2_self_le hpr.pos.ne')
    have h1 : (a - 2) * 1000000 < 480454 * Nat.size p ^ 2 :=
      hlt.trans_le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz 2))
    have h2 : a - 2 < nonResidueBound 1 p := by
      unfold nonResidueBound
      rw [Nat.lt_ceil]
      have h3 : (((a - 2 : ℕ) : ℚ)) * 1000000 < 480454 * (Nat.size p : ℚ) ^ 2 := by
        exact_mod_cast h1
      unfold log2SqUpper
      linarith
    omega
  · rw [← isNonResidueB_iff p hp, isNonResidueB, powMod_eq]
    exact hnr

/-! ### Main results -/

/-- Under GRH, every odd prime `p` has a non-residue in the search window of `sqrtModDet 1`. -/
theorem llsPrime_exists_nonresidue_window (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) : ∃ a : ℕ, a < nonResidueBound 1 p + 2 ∧ ¬ IsSquare (a : ZMod p) := by
  rcases lt_or_ge p 3000 with hs | hb
  · exact llsPrime_small p hp hs
  · obtain ⟨a, -, hab, hns⟩ := llsPrime_exists_nonresidue hGRH p hb
    have hle := le_nonResidueBound (c := 1) one_pos (p := p) (by omega)
    have : (a : ℝ) < nonResidueBound 1 p := by
      push_cast at hle
      linarith
    have : a < nonResidueBound 1 p := by exact_mod_cast this
    exact ⟨a, by omega, hns⟩

/-- **Deterministic Tonelli–Shanks with `c = 1`** (completeness, under GRH). -/
theorem llsPrime_sqrtModDet_correct (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 1 p n = some r ∧ (r : ZMod p) ^ 2 = n :=
  llsPrime_sqrtModDet_correct_pointwise p hp (llsPrime_exists_nonresidue_window hGRH p hp) n

/-- Under GRH, `sqrtModDet 1 p n` returns something iff `n` is a square mod the odd prime `p`. -/
theorem llsPrime_sqrtModDet_isSome_iff (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    (TonelliShanks.sqrtModDet 1 p n).isSome ↔ IsSquare (n : ZMod p) :=
  llsPrime_sqrtModDet_isSome_iff_pointwise p hp (llsPrime_exists_nonresidue_window hGRH p hp) n

end TonelliShanks
end DetPrimality

#print axioms DetPrimality.TonelliShanks.llsPrime_exists_nonresidue
#print axioms DetPrimality.TonelliShanks.llsPrime_small
#print axioms DetPrimality.TonelliShanks.llsPrime_sqrtModDet_correct
#print axioms DetPrimality.TonelliShanks.llsPrime_sqrtModDet_isSome_iff
