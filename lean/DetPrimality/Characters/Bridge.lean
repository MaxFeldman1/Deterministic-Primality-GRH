import Mathlib
import DetPrimality.Interfaces

/-!
# Characters ↔ subgroups: `BachBoundChar c ↔ BachBound c`

The analytic side naturally proves `BachBoundChar` (a statement about nontrivial Dirichlet
characters). The algorithmic side needs `BachBound` (a statement about proper subgroups of
`(ZMod n)ˣ`). This file proves they are equivalent, using that characters of the finite abelian
group `G ⧸ H` separate points (`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`).

We also derive the least-quadratic-nonresidue bound used by Tonelli–Shanks.
-/

namespace DetPrimality

open Real

/-- A proper subgroup `H` of `(ZMod n)ˣ` is contained in the kernel of some nontrivial
Dirichlet character mod `n`. -/
theorem exists_dirichletCharacter_trivial_on (n : ℕ) [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ n, χ ≠ 1 ∧ ∀ u : (ZMod n)ˣ, u ∈ H → χ (u : ZMod n) = 1 := by
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hH)
  have hq : (QuotientGroup.mk g : (ZMod n)ˣ ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have : NeZero ((Monoid.exponent ((ZMod n)ˣ ⧸ H) : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (Monoid.exponent_ne_zero_of_finite (G := (ZMod n)ˣ ⧸ H))⟩
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    ((ZMod n)ˣ ⧸ H) ℂ hq
  let ψ : (ZMod n)ˣ →* ℂˣ := φ.comp (QuotientGroup.mk' H)
  refine ⟨MulChar.ofUnitHom ψ, ?_, ?_⟩
  · intro h1
    apply hφ
    have := congrArg (fun χ : DirichletCharacter ℂ n => χ (g : ZMod n)) h1
    simp only [MulChar.ofUnitHom_coe, MulChar.one_apply_coe] at this
    exact Units.ext (by simpa [ψ] using this)
  · intro u hu
    rw [MulChar.ofUnitHom_coe]
    have : ψ u = 1 := by
      simp [ψ, (QuotientGroup.eq_one_iff u).mpr hu]
    rw [this, Units.val_one]

/-- **Bridge**: the character form of Bach's bound implies the subgroup form. -/
theorem bachBound_of_bachBoundChar (c : ℝ) : BachBoundChar c → BachBound c := by
  intro hc n hn H hH
  have : NeZero n := ⟨by omega⟩
  obtain ⟨χ, hχ1, hχH⟩ := exists_dirichletCharacter_trivial_on n H hH
  obtain ⟨a, ha_lt, ha_unit, ha_ne⟩ := hc n hn χ hχ1
  refine ⟨ha_unit.unit, ?_, ?_⟩
  · intro hmem
    apply ha_ne
    have := hχH _ hmem
    rwa [IsUnit.unit_spec] at this
  · rw [IsUnit.unit_spec, ZMod.val_natCast]
    exact lt_of_le_of_lt (by exact_mod_cast Nat.mod_le a n) ha_lt

/-- Converse: the subgroup form implies the character form (take `H = ker χ`). -/
theorem bachBoundChar_of_bachBound (c : ℝ) : BachBound c → BachBoundChar c := by
  intro hc n hn χ hχ
  have : NeZero n := ⟨by omega⟩
  let H : Subgroup (ZMod n)ˣ := (MulChar.toUnitHom χ).ker
  have hH : H ≠ ⊤ := by
    intro htop
    apply hχ
    refine MulChar.ext fun u => ?_
    have hu : u ∈ H := htop ▸ Subgroup.mem_top u
    rw [MulChar.one_apply_coe, ← MulChar.coe_toUnitHom, (MonoidHom.mem_ker).mp hu,
      Units.val_one]
  obtain ⟨u, huH, hu_lt⟩ := hc n hn H hH
  refine ⟨(u : ZMod n).val, hu_lt, ?_, ?_⟩
  · rw [ZMod.natCast_zmod_val]; exact u.isUnit
  · rw [ZMod.natCast_zmod_val]
    intro h1
    apply huH
    rw [MonoidHom.mem_ker]
    exact Units.ext (by rw [MulChar.coe_toUnitHom, h1, Units.val_one])

theorem bachBound_iff_bachBoundChar (c : ℝ) : BachBound c ↔ BachBoundChar c :=
  ⟨bachBoundChar_of_bachBound c, bachBound_of_bachBoundChar c⟩

/-- The squares form a proper subgroup of `(ZMod p)ˣ` for an odd prime `p`. -/
theorem squares_ne_top (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range ≠ ⊤ := by
  have h2 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  have : Fact (2 < p) := ⟨h2⟩
  intro htop
  have hsurj : Function.Surjective (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ) :=
    MonoidHom.range_eq_top.mp htop
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  have : (-1 : (ZMod p)ˣ) = 1 := hinj (by simp)
  apply ZMod.neg_one_ne_one (n := p)
  simpa using congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) this

/-- **Least quadratic nonresidue** (used by Tonelli–Shanks): from `BachBound c`, every odd prime
`p` has a quadratic nonresidue `a < c (log p)^2`. -/
theorem exists_nonresidue_lt_of_bachBound (c : ℝ) (hc : BachBound c) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) :
    ∃ a : ℕ, (a : ℝ) < c * (Real.log p) ^ 2 ∧ legendreSym p a = -1 := by
  have h2 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  obtain ⟨u, huH, hu_lt⟩ := hc p h2 _ (squares_ne_top p hp)
  refine ⟨(u : ZMod p).val, hu_lt, ?_⟩
  have := legendreSym.eq_neg_one_iff' (p := p) (a := (u : ZMod p).val)
  rw [this, ZMod.natCast_zmod_val]
  rintro ⟨r, hr⟩
  apply huH
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
  simp [hr, sq]

/-- Same, starting from the character form. -/
theorem exists_nonresidue_lt_of_bachBoundChar (c : ℝ) (hc : BachBoundChar c) (p : ℕ)
    [Fact p.Prime] (hp : p ≠ 2) :
    ∃ a : ℕ, (a : ℝ) < c * (Real.log p) ^ 2 ∧ legendreSym p a = -1 :=
  exists_nonresidue_lt_of_bachBound c (bachBound_of_bachBoundChar c hc) p hp

end DetPrimality
