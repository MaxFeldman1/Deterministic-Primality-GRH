import Mathlib
import DetPrimality.Bach.R11AsmCore

/-!
# Round 12 (miller4.md), part 1: positivity over the character group of `G/H`

`H ≤ (ZMod n)ˣ`, `S = r12S H` the Dirichlet characters mod `n` trivial on `H`, `T = S \ {1}`.

* `r12_sum_pv_nonneg` (Lemma M11): `0 ≤ 1 + ∑_{χ ∈ T} Re χ̃(m)` for **every** `m : ℕ` (also when
  `gcd(m, n) > 1`), `χ̃` the primitive character inducing `χ`.  Proof: `χ ↦ χ̃(m)` vanishes off the
  subgroup `U = {χ : gcd(m, cond χ) = 1}` (Mathlib's `subgroupOfCoprimeConductor`) and is
  multiplicative on it, so its sum over the group `S` is `0` or `|S ∩ U|`.
* `r12_index_le_card`: `[G : H] ≤ |S|`.
* `r12_sum_ge` (Lemma M12): if `χ̃(m) = 1` for `χ ∈ T`, `1 ≤ m < X`, then
  `(1 + |T|) ∑_{m<X} Λ(m)√m log³(x/m) ≤ A₃(x) + ∑_{χ ∈ T} Re Φ_χ̃(x)`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## An abstract character-sum lemma -/

/-- If `f` vanishes off a subgroup `U` and is multiplicative on `U`, its sum over a (finite)
subgroup `S` has non-negative real part (it is `0` or `|S ∩ U|`). -/
theorem r12_group_sum_re_nonneg {G : Type*} [CommGroup G] (S U : Subgroup G) (Sf : Finset G)
    (hSf : ∀ g, g ∈ Sf ↔ g ∈ S) (f : G → ℂ) (h0 : ∀ g, g ∉ U → f g = 0)
    (hmul : ∀ g h, g ∈ U → h ∈ U → f (g * h) = f g * f h) :
    0 ≤ (∑ g ∈ Sf, f g).re := by
  by_cases hex : ∃ ψ, ψ ∈ S ∧ ψ ∈ U ∧ f ψ ≠ 1
  · obtain ⟨ψ, hψS, hψU, hψ1⟩ := hex
    have hfm : ∀ g, f (g * ψ) = f g * f ψ := by
      intro g
      by_cases hg : g ∈ U
      · exact hmul g ψ hg hψU
      · have : g * ψ ∉ U := fun hc => hg ((Subgroup.mul_mem_cancel_right U hψU).mp hc)
        rw [h0 _ this, h0 g hg, zero_mul]
    have hsum : ∑ g ∈ Sf, f (g * ψ) = ∑ g ∈ Sf, f g :=
      Finset.sum_equiv (Equiv.mulRight ψ)
        (fun g => by rw [hSf, hSf]; simp [Subgroup.mul_mem_cancel_right S hψS])
        (fun g _ => by simp)
    simp_rw [hfm, ← Finset.sum_mul] at hsum
    rcases mul_right_eq_self₀.mp hsum with h | h
    · exact absurd h hψ1
    · rw [h]; simp
  · have hall : ∀ ψ, ψ ∈ S → ψ ∈ U → f ψ = 1 := fun ψ h1 h2 => by
      by_contra h3
      exact hex ⟨ψ, h1, h2, h3⟩
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun g hg => ?_
    by_cases hgU : g ∈ U
    · rw [hall g ((hSf g).mp hg) hgU]; simp
    · rw [h0 g hgU]; simp

/-! ## Values of the primitive character at natural numbers -/

/-- `χ̃(m)`: the value at `m` of the primitive character inducing `χ`. -/
noncomputable def r12_pv {n : ℕ} (χ : DirichletCharacter ℂ n) (m : ℕ) : ℂ :=
  χ.primitiveCharacter (m : ZMod χ.conductor)

theorem r12_pv_eq_zero {n : ℕ} (χ : DirichletCharacter ℂ n) {m : ℕ}
    (h : ¬ m.Coprime χ.conductor) : r12_pv χ m = 0 :=
  MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime m _).mp hu))

theorem r12_pv_one {n : ℕ} [NeZero n] (m : ℕ) : r12_pv (1 : DirichletCharacter ℂ n) m = 1 := by
  unfold r12_pv
  have hc : (1 : DirichletCharacter ℂ n).conductor = 1 := conductor_one
  have hu : IsUnit ((m : ℕ) : ZMod (1 : DirichletCharacter ℂ n).conductor) := by
    rw [ZMod.isUnit_iff_coprime, hc]; exact Nat.coprime_one_right m
  rw [primitiveCharacter_one]
  exact MulChar.one_apply hu

theorem r12_pv_changeLevel {n d : ℕ} [NeZero n] (hd : d ∣ n) (θ : DirichletCharacter ℂ d)
    {m : ℕ} (hm : m.Coprime d) : r12_pv (changeLevel hd θ) m = θ (m : ZMod d) := by
  unfold r12_pv
  have hmZ : IsCoprime (m : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr hm
  have h1 := primitiveCharacter_changeLevel_apply hd θ (m : ℤ)
  have h2 := θ.primitiveCharacter_apply_of_isCoprime hmZ
  simp only [Int.cast_natCast] at h1 h2
  rw [h1, h2]

theorem r12_pv_mul {n : ℕ} [NeZero n] (χ ψ : DirichletCharacter ℂ n) {m : ℕ}
    (hχ : m.Coprime χ.conductor) (hψ : m.Coprime ψ.conductor) :
    r12_pv (χ * ψ) m = r12_pv χ m * r12_pv ψ m := by
  have hd : χ.conductor.lcm ψ.conductor ∣ n :=
    Nat.lcm_dvd χ.conductor_dvd_level ψ.conductor_dvd_level
  have hmd : m.Coprime (χ.conductor.lcm ψ.conductor) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_right hχ hψ)
  have hmZ : IsCoprime (m : ℤ) ((χ.conductor.lcm ψ.conductor : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hmd
  have e : χ * ψ = changeLevel hd
      (changeLevel (Nat.dvd_lcm_left χ.conductor ψ.conductor) χ.primitiveCharacter
        * changeLevel (Nat.dvd_lcm_right χ.conductor ψ.conductor) ψ.primitiveCharacter) := by
    rw [map_mul, ← changeLevel_trans, ← changeLevel_trans, changeLevel_primitiveCharacter,
      changeLevel_primitiveCharacter]
  have h3 := changeLevel_eq_cast_of_dvd' χ.primitiveCharacter
    (Nat.dvd_lcm_left χ.conductor ψ.conductor) hmZ
  have h4 := changeLevel_eq_cast_of_dvd' ψ.primitiveCharacter
    (Nat.dvd_lcm_right χ.conductor ψ.conductor) hmZ
  simp only [Int.cast_natCast] at h3 h4
  rw [e, r12_pv_changeLevel hd _ hmd, MulChar.mul_apply, h3, h4]
  rfl

/-! ## The characters trivial on `H` -/

open Classical in
/-- The Dirichlet characters mod `n` that are trivial on `H`. -/
noncomputable def r12S {n : ℕ} (H : Subgroup (ZMod n)ˣ) : Finset (DirichletCharacter ℂ n) :=
  Finset.univ.filter (fun χ => ∀ u ∈ H, χ (u : ZMod n) = 1)

open Classical in
/-- The non-principal Dirichlet characters mod `n` that are trivial on `H`. -/
noncomputable def r12T {n : ℕ} (H : Subgroup (ZMod n)ˣ) : Finset (DirichletCharacter ℂ n) :=
  (r12S H).erase 1

theorem r12_mem_S {n : ℕ} {H : Subgroup (ZMod n)ˣ} {χ : DirichletCharacter ℂ n} :
    χ ∈ r12S H ↔ ∀ u ∈ H, χ (u : ZMod n) = 1 := by
  simp only [r12S, Finset.mem_filter, Finset.mem_univ, true_and]

theorem r12_one_mem_S {n : ℕ} (H : Subgroup (ZMod n)ˣ) : (1 : DirichletCharacter ℂ n) ∈ r12S H :=
  r12_mem_S.mpr fun u _ => MulChar.one_apply_coe u

open Classical in
theorem r12_mem_T {n : ℕ} {H : Subgroup (ZMod n)ˣ} {χ : DirichletCharacter ℂ n} :
    χ ∈ r12T H ↔ χ ≠ 1 ∧ ∀ u ∈ H, χ (u : ZMod n) = 1 := by
  unfold r12T
  rw [Finset.mem_erase, r12_mem_S]

open Classical in
theorem r12_sum_S {n : ℕ} (H : Subgroup (ZMod n)ˣ) (f : DirichletCharacter ℂ n → ℂ) :
    ∑ χ ∈ r12S H, f χ = f 1 + ∑ χ ∈ r12T H, f χ := by
  unfold r12T
  exact (Finset.add_sum_erase _ _ (r12_one_mem_S H)).symm

open Classical in
theorem r12_card_T {n : ℕ} (H : Subgroup (ZMod n)ˣ) : (r12T H).card + 1 = (r12S H).card := by
  unfold r12T
  exact Finset.card_erase_add_one (r12_one_mem_S H)

/-- **Lemma M11.** `∑_{χ ∈ S} χ̃(m)` has non-negative real part, for every `m`. -/
theorem r12_sum_pv_nonneg {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) (m : ℕ) :
    0 ≤ 1 + ∑ χ ∈ r12T H, (r12_pv χ m).re := by
  have key := r12_group_sum_re_nonneg (annihilator ℂ (H : Set (ZMod n)ˣ))
    (subgroupOfCoprimeConductor (R := ℂ) (n := n) m) (r12S H)
    (fun χ => by simp [r12_mem_S, mem_annihilator_iff]) (fun χ => r12_pv χ m)
    (fun χ hχ => r12_pv_eq_zero χ hχ) (fun χ ψ hχ hψ => r12_pv_mul χ ψ hχ hψ)
  rw [r12_sum_S, Complex.add_re, Complex.re_sum, r12_pv_one] at key
  simpa using key

/-- There are at least `[G : H]` characters trivial on `H`. -/
theorem r12_index_le_card {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) :
    H.index ≤ (r12S H).card := by
  have hexp : NeZero (Monoid.exponent ((ZMod n)ˣ ⧸ H)) :=
    ⟨Monoid.exponent_ne_zero.mpr
      ⟨Nat.card ((ZMod n)ˣ ⧸ H), Nat.card_pos, fun g => pow_card_eq_one'⟩⟩
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ
  have e : Nat.card {χ : DirichletCharacter ℂ n // χ ∈ r12S H} = (r12S H).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Subgroup.index, ← hcard, ← e]
  let F : ((ZMod n)ˣ ⧸ H →* ℂˣ) → {χ : DirichletCharacter ℂ n // χ ∈ r12S H} := fun φ =>
    ⟨MulChar.ofUnitHom (φ.comp (QuotientGroup.mk' H)), by
      rw [r12_mem_S]
      intro u hu
      rw [MulChar.ofUnitHom_coe]
      change ((φ (QuotientGroup.mk' H u) : ℂˣ) : ℂ) = 1
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hu]
      simp⟩
  refine Nat.card_le_card_of_injective F ?_
  intro φ φ' h
  have h1 : MulChar.ofUnitHom (φ.comp (QuotientGroup.mk' H)) =
      (MulChar.ofUnitHom (φ'.comp (QuotientGroup.mk' H)) : DirichletCharacter ℂ n) :=
    congrArg Subtype.val h
  rw [MulChar.ofUnitHom_eq, MulChar.ofUnitHom_eq] at h1
  exact QuotientGroup.monoidHom_ext H (MulChar.equivToUnitHom.symm.injective h1)

theorem r12_three_le_card {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) (h4 : 4 ≤ H.index) :
    3 ≤ (r12T H).card := by
  have h1 := r12_index_le_card H
  have h2 := r12_card_T H
  omega

/-! ## Lemma M12 -/

theorem r12_Phi_re {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    (r11Phi χ x).re = ∑ m ∈ Finset.range ⌈x⌉₊,
      Λ m * (χ (m : ZMod q)).re * (√(m : ℝ) * Real.log (x / m) ^ 3) := by
  unfold r11Phi
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero]

theorem r12_term_nonneg {x : ℝ} {m : ℕ} (hpos : 0 < m) (hlt : (m : ℝ) < x) :
    0 ≤ Real.log (x / m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
  exact Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)

/-- **Lemma M12**: the basic positivity inequality for the `|T|` non-principal characters. -/
theorem r12_sum_ge {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) {X x : ℝ} (hXx : X ≤ x)
    (h1 : ∀ χ ∈ r12T H, ∀ m : ℕ, 1 ≤ m → (m : ℝ) < X → r12_pv χ m = 1) :
    (1 + ((r12T H).card : ℝ)) * ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (x / m) ^ 3
      ≤ r11A 3 x + ∑ χ ∈ r12T H, (r11Phi χ.primitiveCharacter x).re := by
  have hsum : r11A 3 x + ∑ χ ∈ r12T H, (r11Phi χ.primitiveCharacter x).re
      = ∑ m ∈ Finset.range ⌈x⌉₊, Λ m * (1 + ∑ χ ∈ r12T H, (r12_pv χ m).re)
          * (√(m : ℝ) * Real.log (x / m) ^ 3) := by
    have e1 : ∑ χ ∈ r12T H, (r11Phi χ.primitiveCharacter x).re
        = ∑ m ∈ Finset.range ⌈x⌉₊, ∑ χ ∈ r12T H,
            Λ m * (r12_pv χ m).re * (√(m : ℝ) * Real.log (x / m) ^ 3) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun χ _ => r12_Phi_re _ x
    rw [e1]; unfold r11A
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e2 : ∑ χ ∈ r12T H, Λ m * (r12_pv χ m).re * (√(m : ℝ) * Real.log (x / m) ^ 3)
        = Λ m * (∑ χ ∈ r12T H, (r12_pv χ m).re) * (√(m : ℝ) * Real.log (x / m) ^ 3) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e2]; ring
  have hleft : (1 + ((r12T H).card : ℝ))
        * ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (x / m) ^ 3
      = ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * (1 + ∑ χ ∈ r12T H, (r12_pv χ m).re)
          * (√(m : ℝ) * Real.log (x / m) ^ 3) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp
    · have hlt : (m : ℝ) < X := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
      have e3 : ∑ χ ∈ r12T H, (r12_pv χ m).re = ((r12T H).card : ℝ) := by
        have e4 : ∀ χ ∈ r12T H, (r12_pv χ m).re = 1 := fun χ hχ => by
          rw [h1 χ hχ m hpos hlt, Complex.one_re]
        rw [Finset.sum_congr rfl e4]
        simp
      rw [e3]; ring
  rw [hsum, hleft]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.ceil_mono hXx))
    fun m hm _ => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  · have hlt : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
    have hlog := r12_term_nonneg hpos hlt
    have hχ := r12_sum_pv_nonneg H m
    have := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    positivity

/-- `∑_{m<X} Λ(m)√m log³(x/m) ≤ A₃(x)` for `X ≤ x`. -/
theorem r12_S_le_A3 {X x : ℝ} (hXx : X ≤ x) :
    ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (x / m) ^ 3 ≤ r11A 3 x := by
  unfold r11A
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.ceil_mono hXx))
    fun m hm _ => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  · have hlt : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
    have hlog := r12_term_nonneg hpos hlt
    have := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    positivity

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r12_sum_pv_nonneg
#print axioms DetPrimality.Bach.r12_sum_ge
#print axioms DetPrimality.Bach.r12_three_le_card
