import Mathlib
import DetPrimality.CompositeInterface
import DetPrimality.Miller.Basic

/-!
# Deterministic Miller test from Bach's Theorem 2 form (composite moduli)

`millerDet_correct_of_composite`: `millerDet c n = true ↔ n.Prime` assuming only
`BachBoundCharComposite c` (for composite `n` and `χ ≠ 1` mod `n` some `1 ≤ a < c log² n` has
`χ a ≠ 1`, where `a` may share a factor with `n`).

For odd composite `n > 2` take the proper subgroup `H ⊇ {strong liars}` and a character `χ ≠ 1`
trivial on `H`; let `a` be the witness of `BachBoundCharComposite`.

* `a < n`: then `a ≥ 2` (as `χ 1 = 1`) and `a < millerBound c n`.  If `sprp n a` held, `a` would
  be a unit (`millerComp_isUnit_of_sprp`), hence a strong liar, hence in `H`, so `χ a = 1`.
* `a ≥ n`: then `millerBound c n > n`, so the test runs over all `2 ≤ b < n`, in particular over
  the least prime factor of `n`, which is not a unit and so fails `sprp`.
-/

namespace DetPrimality.Miller

/-- A strong probable prime base is a unit mod `n` (since `a^k = ±1` with `k ≥ 1`). -/
theorem millerComp_isUnit_of_sprp {n : ℕ} (hn : 1 < n) {a : ℕ} (h : sprp n a = true) :
    IsUnit (a : ZMod n) := by
  have hd : oddPart (n - 1) ≠ 0 := by
    have := oddPart_odd (m := n - 1) (by omega)
    omega
  rcases (sprp_iff hn a).mp h with h1 | ⟨r, -, h1⟩
  · exact (isUnit_pow_iff hd).mp (by rw [h1]; exact isUnit_one)
  · exact (isUnit_pow_iff (mul_ne_zero hd (pow_ne_zero r two_ne_zero))).mp
      (by rw [h1]; exact isUnit_one.neg)

/-- A base sharing a factor with `n` is a Miller witness. -/
theorem millerComp_sprp_eq_false_of_not_coprime {n : ℕ} (hn : 1 < n) {a : ℕ}
    (h : ¬ Nat.Coprime a n) : sprp n a = false := by
  rw [Bool.eq_false_iff]
  intro hs
  exact h ((ZMod.isUnit_iff_coprime a n).mp (millerComp_isUnit_of_sprp hn hs))

/-- Every proper subgroup of `(ZMod n)ˣ` is contained in the kernel of a nontrivial Dirichlet
character mod `n`. -/
theorem millerComp_exists_char {n : ℕ} [NeZero n] {H : Subgroup (ZMod n)ˣ} (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ n, χ ≠ 1 ∧ ∀ u : (ZMod n)ˣ, u ∈ H → χ (u : ZMod n) = 1 := by
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
  refine ⟨χ, ?_, ?_⟩
  · intro h1
    apply hφ
    have h2 := hval g
    rw [h1, MulChar.one_apply_coe] at h2
    exact Units.ext h2.symm
  · intro u hu
    rw [hval u, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hu]
    simp

/-- Under `BachBoundCharComposite c`, composites (and `0, 1`) are rejected. -/
theorem millerDet_eq_false_of_not_prime_of_composite {c : ℚ} (hc : 0 ≤ c)
    (hB : BachBoundCharComposite (c : ℝ)) {n : ℕ} (hnp : ¬ n.Prime) : millerDet c n = false := by
  by_cases h1 : n < 2
  · simp [millerDet, h1]
  have h2 : n ≠ 2 := by rintro rfl; exact hnp Nat.prime_two
  by_cases h3 : n % 2 = 0
  · simp [millerDet, h1, h2, h3]
  have hn : 2 < n := by omega
  have hodd : n % 2 = 1 := by omega
  rw [Bool.eq_false_iff, Ne, millerDet_iff_all c hn hodd]
  intro hall
  obtain ⟨H, hH, hliar⟩ := exists_proper_subgroup_strongLiars hn hodd hnp
  have : NeZero n := ⟨by omega⟩
  obtain ⟨χ, hχ, hχH⟩ := millerComp_exists_char hH
  obtain ⟨a, ha1, hab, haχ⟩ := hB n hn hnp χ hχ
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

/-- **Main theorem (composite form).** Under `BachBoundCharComposite c` (Bach's Theorem 2 form,
`c = 2` under GRH), the deterministic Miller test is correct. -/
theorem millerDet_correct_of_composite (c : ℚ) (hc : 0 < c)
    (hB : BachBoundCharComposite (c : ℝ)) (n : ℕ) : millerDet c n = true ↔ n.Prime := by
  constructor
  · intro h
    by_contra hnp
    rw [millerDet_eq_false_of_not_prime_of_composite hc.le hB hnp] at h
    exact Bool.false_ne_true h
  · exact millerDet_of_prime c

end DetPrimality.Miller
