import Mathlib
import DetPrimality.CompositeInterface
import DetPrimality.Bach.Blueprint

/-!
# Reduction lemmas for Bach's Theorem 2 form (composite moduli)

Let `n > 2` be composite, `χ` a character mod `n` and `x > 0` such that `χ a = 1` for all
`1 ≤ a < x`.  Then every `1 ≤ a < x` is coprime to `n` (`compred_coprime`), so

* `x² ≤ n` (the least prime factor `p` of `n` is `≥ x` and `p² ≤ n`), `compred_sq_le`;
* `χ* m = 1` for `1 ≤ m < x`, `compred_primitive_eq_one`;
* `noncoprimeSum n x = 0`, `compred_noncoprimeSum_eq_zero`;
* `ψ₁(x) ≤ Re ψ̃(x, χ*)`, `compred_psiOne_le`.

All four are packaged in `composite_no_witness_facts`; `composite_no_witness_setup` is the form
used by assemblies (negation of the conclusion of `BachBoundCharComposite c`).

Bootstrap: with `x = c L²`, `L = log n`, the inequality `(c L²)² ≤ n` forces `L ≥ L₀(c)`:

| `c`   | `n ≥`    | `L ≥`      |
|-------|----------|------------|
| `2`   | `57782`  | `10.96309` |
| `5/2` | `115323` | `11.65489` |
| `3`   | `199589` | `12.20318` |
| `4`   | `463371` | `13.04524` |

(`compred_log_ge_c2`, `_c25`, `_c3`, `_c4`; each is a chain of `compred_boot_step`s with
certificates `2^k ≤ N^512`.)
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

/-- If `χ a = 1` for all `1 ≤ a < x` then all such `a` are coprime to `n`. -/
theorem compred_coprime {n : ℕ} (χ : DirichletCharacter ℂ n) {x : ℝ}
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < x → χ (a : ZMod n) = 1) {a : ℕ} (ha : 1 ≤ a)
    (hax : (a : ℝ) < x) : Nat.Coprime a n := by
  by_contra hc
  have hnu : ¬ IsUnit (a : ZMod n) := fun hu => hc ((ZMod.isUnit_iff_coprime a n).mp hu)
  have h1 := h a ha hax
  rw [MulChar.map_nonunit χ hnu] at h1
  exact zero_ne_one h1

/-- The least prime factor of a composite `n` is `≥ x`, hence `x² ≤ n`. -/
theorem compred_sq_le {n : ℕ} (hn : 2 < n) (hnp : ¬ n.Prime) (χ : DirichletCharacter ℂ n)
    {x : ℝ} (hx : 0 ≤ x) (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < x → χ (a : ZMod n) = 1) :
    x ≤ n.minFac ∧ x ^ 2 ≤ n := by
  have hp := Nat.minFac_prime (n := n) (by omega)
  have hxp : x ≤ n.minFac := by
    by_contra hc
    push Not at hc
    have hcop := compred_coprime χ h hp.one_lt.le hc
    have h1 := Nat.Coprime.eq_one_of_dvd hcop (Nat.minFac_dvd n)
    exact hp.one_lt.ne' h1
  refine ⟨hxp, ?_⟩
  have h2 : (n.minFac : ℝ) ^ 2 ≤ n := by
    exact_mod_cast Nat.minFac_sq_le_self (by omega) hnp
  exact (pow_le_pow_left₀ hx hxp 2).trans h2

theorem compred_primitive_eq_one {n : ℕ} (χ : DirichletCharacter ℂ n) {x : ℝ}
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < x → χ (a : ZMod n) = 1) {m : ℕ} (hm : 1 ≤ m)
    (hmx : (m : ℝ) < x) : χ.primitiveCharacter (m : ZMod χ.conductor) = 1 := by
  have hc := compred_coprime χ h hm hmx
  have h2 := χ.primitiveCharacter_apply_of_isCoprime (a := (m : ℤ))
    (Nat.isCoprime_iff_coprime.mpr hc)
  rw [Int.cast_natCast, Int.cast_natCast] at h2
  rw [h2]
  exact h m hm hmx

theorem compred_noncoprimeSum_eq_zero {n : ℕ} (χ : DirichletCharacter ℂ n) {x : ℝ}
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < x → χ (a : ZMod n) = 1) : noncoprimeSum n x = 0 := by
  unfold noncoprimeSum
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
  have hmx : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hm1)
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  · exact absurd (compred_coprime χ h hpos hmx) hm2

theorem compred_psiOne_le {n : ℕ} (hn : 1 < n) (χ : DirichletCharacter ℂ n) {x : ℝ}
    (hx : 0 < x) (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < x → χ (a : ZMod n) = 1) :
    psiOne x ≤ (smoothPsi χ.primitiveCharacter x).re := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨hn⟩
  have hlow := re_smoothPsi_primitive_lower χ hx (fun a hax hu => by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · exact absurd hu (by simp)
    · exact h a hpos hax)
  rw [compred_noncoprimeSum_eq_zero χ h] at hlow
  linarith

/-- **Composite reduction.**  If `n > 2` is composite and `χ a = 1` for all `1 ≤ a < x`, then
`x² ≤ n`, the primitive character is `1` below `x`, the non-coprime correction vanishes and
`ψ₁(x) ≤ Re ψ̃(x, χ*)`. -/
theorem composite_no_witness_facts {n : ℕ} (hn : 2 < n) (hnp : ¬ n.Prime)
    (χ : DirichletCharacter ℂ n) {x : ℝ} (hx : 0 < x)
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < x → χ (a : ZMod n) = 1) :
    x ^ 2 ≤ n ∧
      (∀ m : ℕ, 1 ≤ m → (m : ℝ) < x → χ.primitiveCharacter (m : ZMod χ.conductor) = 1) ∧
      noncoprimeSum n x = 0 ∧ psiOne x ≤ (smoothPsi χ.primitiveCharacter x).re :=
  ⟨(compred_sq_le hn hnp χ hx.le h).2, fun _ hm hmx => compred_primitive_eq_one χ h hm hmx,
    compred_noncoprimeSum_eq_zero χ h, compred_psiOne_le (by omega) χ hx h⟩

/-- The primitive character inducing `χ ≠ 1` is primitive, nontrivial, and has
`log (conductor) ≤ log n`. -/
theorem compred_primitive_facts {n : ℕ} (hn : 0 < n) (χ : DirichletCharacter ℂ n) (hχ : χ ≠ 1) :
    χ.primitiveCharacter.IsPrimitive ∧ χ.primitiveCharacter ≠ 1 ∧
      0 ≤ Real.log χ.conductor ∧ Real.log χ.conductor ≤ Real.log n := by
  have : NeZero n := ⟨hn.ne'⟩
  refine ⟨χ.primitiveCharacter_isPrimitive, ?_, Real.log_natCast_nonneg _, ?_⟩
  · intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, changeLevel_one]
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by exact_mod_cast Nat.le_of_dvd hn χ.conductor_dvd_level)

/-! ## The bootstrap `(c L²)² ≤ n ⟹ L ≥ L₀` -/

/-- `log n ≥ lb` from `n ≥ N` and a certificate `2^k ≤ N^j` with `lb ≤ (k/j) · 0.6931471803`. -/
theorem compred_log_ge_of_pow {n N k j : ℕ} {lb : ℝ} (hN : N ≤ n) (hj : 0 < j)
    (hpow : 2 ^ k ≤ N ^ j) (hlb : lb * (j : ℝ) ≤ (k : ℝ) * 0.6931471803) :
    lb ≤ Real.log n := by
  have h2 := Real.log_two_gt_d9
  have hp : (2 : ℝ) ^ k ≤ (n : ℝ) ^ j := by
    exact_mod_cast hpow.trans (Nat.pow_le_pow_left hN j)
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((n : ℝ) ^ j) := Real.log_le_log (by positivity) hp
  rw [Real.log_pow, Real.log_pow] at h1
  have hk : (k : ℝ) * 0.6931471803 ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2.le (Nat.cast_nonneg k)
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have : lb * (j : ℝ) ≤ Real.log n * (j : ℝ) := by linarith
  exact le_of_mul_le_mul_right this hj'

/-- One bootstrap step: from `n ≥ N`, a certificate `2^k ≤ N^j` and `(c (log n)²)² ≤ n` we get
`log n ≥ lb` and `n ≥ M` as soon as `lb ≤ (k/j) · 0.6931471803` and `M < (c lb²)² + 1`. -/
theorem compred_boot_step {n N k j M : ℕ} {c lb : ℝ} (hc : 0 ≤ c)
    (hbig : (c * Real.log n ^ 2) ^ 2 ≤ n) (hN : N ≤ n) (hj : 0 < j) (hpow : 2 ^ k ≤ N ^ j)
    (hlb0 : 0 ≤ lb) (hlb : lb * (j : ℝ) ≤ (k : ℝ) * 0.6931471803)
    (hM : (M : ℝ) < (c * lb ^ 2) ^ 2 + 1) :
    lb ≤ Real.log n ∧ M ≤ n := by
  have hL := compred_log_ge_of_pow hN hj hpow hlb
  refine ⟨hL, ?_⟩
  have h1 : (c * lb ^ 2) ^ 2 ≤ (c * Real.log n ^ 2) ^ 2 := by gcongr
  have hlt : (M : ℝ) < (n : ℝ) + 1 := by linarith
  have : M < n + 1 := by exact_mod_cast hlt
  omega

/-- The hypothesis of the bootstrap from the composite reduction: with `x = c (log n)²`. -/
theorem compred_bootstrap_hyp {n : ℕ} (hn : 2 < n) (hnp : ¬ n.Prime)
    (χ : DirichletCharacter ℂ n) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < c * Real.log n ^ 2 → χ (a : ZMod n) = 1) :
    (c * Real.log n ^ 2) ^ 2 ≤ n :=
  (compred_sq_le hn hnp χ (by positivity) h).2

theorem compred_log_ge_c2 {n : ℕ} (hn : 2 < n)
    (h : (2 * Real.log n ^ 2) ^ 2 ≤ n) : 57782 ≤ n ∧ 10.96309 ≤ Real.log n := by
  have h0 : 3 ≤ n := hn
  obtain ⟨-, h1⟩ := compred_boot_step (c := 2) (N := 3) (k := 811) (j := 512) (M := 6)
    (lb := 1.09793) (by norm_num) h h0 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h2⟩ := compred_boot_step (c := 2) (N := 6) (k := 1323) (j := 512) (M := 42)
    (lb := 1.79108) (by norm_num) h h1 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h3⟩ := compred_boot_step (c := 2) (N := 42) (k := 2760) (j := 512) (M := 780)
    (lb := 3.73649) (by norm_num) h h2 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h4⟩ := compred_boot_step (c := 2) (N := 780) (k := 4918) (j := 512) (M := 7861)
    (lb := 6.65800) (by norm_num) h h3 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h5⟩ := compred_boot_step (c := 2) (N := 7861) (k := 6625) (j := 512) (M := 25884)
    (lb := 8.96894) (by norm_num) h h4 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h6⟩ := compred_boot_step (c := 2) (N := 25884) (k := 7505) (j := 512) (M := 42627)
    (lb := 10.16029) (by norm_num) h h5 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h7⟩ := compred_boot_step (c := 2) (N := 42627) (k := 7874) (j := 512) (M := 51650)
    (lb := 10.65984) (by norm_num) h h6 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h8⟩ := compred_boot_step (c := 2) (N := 51650) (k := 8016) (j := 512) (M := 55477)
    (lb := 10.85208) (by norm_num) h h7 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h9⟩ := compred_boot_step (c := 2) (N := 55477) (k := 8068) (j := 512) (M := 56931)
    (lb := 10.92248) (by norm_num) h h8 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h10⟩ := compred_boot_step (c := 2) (N := 56931) (k := 8088) (j := 512) (M := 57497)
    (lb := 10.94955) (by norm_num) h h9 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h11⟩ := compred_boot_step (c := 2) (N := 57497) (k := 8095) (j := 512) (M := 57697)
    (lb := 10.95903) (by norm_num) h h10 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h12⟩ := compred_boot_step (c := 2) (N := 57697) (k := 8097) (j := 512) (M := 57754)
    (lb := 10.96174) (by norm_num) h h11 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h13⟩ := compred_boot_step (c := 2) (N := 57754) (k := 8098) (j := 512) (M := 57782)
    (lb := 10.96309) (by norm_num) h h12 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨h13, compred_log_ge_of_pow (N := 57782) (k := 8098) (j := 512) h13 (by norm_num)
    (by decide +kernel) (by norm_num)⟩

theorem compred_log_ge_c25 {n : ℕ} (hn : 2 < n)
    (h : ((5/2) * Real.log n ^ 2) ^ 2 ≤ n) : 115323 ≤ n ∧ 11.65489 ≤ Real.log n := by
  have h0 : 3 ≤ n := hn
  obtain ⟨-, h1⟩ := compred_boot_step (c := (5/2)) (N := 3) (k := 811) (j := 512) (M := 10)
    (lb := 1.09793) (by norm_num) h h0 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h2⟩ := compred_boot_step (c := (5/2)) (N := 10) (k := 1700) (j := 512) (M := 176)
    (lb := 2.30146) (by norm_num) h h1 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h3⟩ := compred_boot_step (c := (5/2)) (N := 176) (k := 3819) (j := 512) (M := 4466)
    (lb := 5.17017) (by norm_num) h h2 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h4⟩ := compred_boot_step (c := (5/2)) (N := 4466) (k := 6207) (j := 512) (M := 31163)
    (lb := 8.40305) (by norm_num) h h3 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h5⟩ := compred_boot_step (c := (5/2)) (N := 31163) (k := 7642) (j := 512) (M := 71603)
    (lb := 10.34576) (by norm_num) h h4 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h6⟩ := compred_boot_step (c := (5/2)) (N := 71603) (k := 8257) (j := 512) (M := 97587)
    (lb := 11.17835) (by norm_num) h h5 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h7⟩ := compred_boot_step (c := (5/2)) (N := 97587) (k := 8486) (j := 512) (M := 108872)
    (lb := 11.48837) (by norm_num) h h6 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h8⟩ := compred_boot_step (c := (5/2)) (N := 108872) (k := 8566) (j := 512) (M := 113036)
    (lb := 11.59667) (by norm_num) h h7 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h9⟩ := compred_boot_step (c := (5/2)) (N := 113036) (k := 8594) (j := 512) (M := 114521)
    (lb := 11.63458) (by norm_num) h h8 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h10⟩ := compred_boot_step (c := (5/2)) (N := 114521) (k := 8604) (j := 512) (M := 115055)
    (lb := 11.64812) (by norm_num) h h9 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h11⟩ := compred_boot_step (c := (5/2)) (N := 115055) (k := 8607) (j := 512) (M := 115215)
    (lb := 11.65218) (by norm_num) h h10 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h12⟩ := compred_boot_step (c := (5/2)) (N := 115215) (k := 8608) (j := 512) (M := 115269)
    (lb := 11.65353) (by norm_num) h h11 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h13⟩ := compred_boot_step (c := (5/2)) (N := 115269) (k := 8609) (j := 512) (M := 115323)
    (lb := 11.65489) (by norm_num) h h12 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨h13, compred_log_ge_of_pow (N := 115323) (k := 8609) (j := 512) h13 (by norm_num)
    (by decide +kernel) (by norm_num)⟩

theorem compred_log_ge_c3 {n : ℕ} (hn : 2 < n)
    (h : (3 * Real.log n ^ 2) ^ 2 ≤ n) : 199589 ≤ n ∧ 12.20318 ≤ Real.log n := by
  have h0 : 3 ≤ n := hn
  obtain ⟨-, h1⟩ := compred_boot_step (c := 3) (N := 3) (k := 811) (j := 512) (M := 14)
    (lb := 1.09793) (by norm_num) h h0 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h2⟩ := compred_boot_step (c := 3) (N := 14) (k := 1949) (j := 512) (M := 437)
    (lb := 2.63856) (by norm_num) h h1 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h3⟩ := compred_boot_step (c := 3) (N := 437) (k := 4491) (j := 512) (M := 12298)
    (lb := 6.07992) (by norm_num) h h2 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h4⟩ := compred_boot_step (c := 3) (N := 12298) (k := 6956) (j := 512) (M := 70779)
    (lb := 9.41705) (by norm_num) h h3 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h5⟩ := compred_boot_step (c := 3) (N := 70779) (k := 8248) (j := 512) (M := 139913)
    (lb := 11.16616) (by norm_num) h h4 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h6⟩ := compred_boot_step (c := 3) (N := 139913) (k := 8752) (j := 512) (M := 177376)
    (lb := 11.84848) (by norm_num) h h5 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h7⟩ := compred_boot_step (c := 3) (N := 177376) (k := 8927) (j := 512) (M := 191994)
    (lb := 12.08540) (by norm_num) h h6 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h8⟩ := compred_boot_step (c := 3) (N := 191994) (k := 8985) (j := 512) (M := 197032)
    (lb := 12.16392) (by norm_num) h h7 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h9⟩ := compred_boot_step (c := 3) (N := 197032) (k := 9005) (j := 512) (M := 198792)
    (lb := 12.19099) (by norm_num) h h8 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h10⟩ := compred_boot_step (c := 3) (N := 198792) (k := 9011) (j := 512) (M := 199322)
    (lb := 12.19911) (by norm_num) h h9 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h11⟩ := compred_boot_step (c := 3) (N := 199322) (k := 9013) (j := 512) (M := 199500)
    (lb := 12.20182) (by norm_num) h h10 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h12⟩ := compred_boot_step (c := 3) (N := 199500) (k := 9014) (j := 512) (M := 199589)
    (lb := 12.20318) (by norm_num) h h11 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨h12, compred_log_ge_of_pow (N := 199589) (k := 9014) (j := 512) h12 (by norm_num)
    (by decide +kernel) (by norm_num)⟩

theorem compred_log_ge_c4 {n : ℕ} (hn : 2 < n)
    (h : (4 * Real.log n ^ 2) ^ 2 ≤ n) : 463371 ≤ n ∧ 13.04524 ≤ Real.log n := by
  have h0 : 3 ≤ n := hn
  obtain ⟨-, h1⟩ := compred_boot_step (c := 4) (N := 3) (k := 811) (j := 512) (M := 24)
    (lb := 1.09793) (by norm_num) h h0 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h2⟩ := compred_boot_step (c := 4) (N := 24) (k := 2347) (j := 512) (M := 1631)
    (lb := 3.17737) (by norm_num) h h1 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h3⟩ := compred_boot_step (c := 4) (N := 1631) (k := 5463) (j := 512) (M := 47871)
    (lb := 7.39582) (by norm_num) h h2 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h4⟩ := compred_boot_step (c := 4) (N := 47871) (k := 7959) (j := 512) (M := 215663)
    (lb := 10.77491) (by norm_num) h h3 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h5⟩ := compred_boot_step (c := 4) (N := 215663) (k := 9071) (j := 512) (M := 363883)
    (lb := 12.28034) (by norm_num) h h4 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h6⟩ := compred_boot_step (c := 4) (N := 363883) (k := 9458) (j := 512) (M := 430069)
    (lb := 12.80426) (by norm_num) h h5 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h7⟩ := compred_boot_step (c := 4) (N := 430069) (k := 9581) (j := 512) (M := 452882)
    (lb := 12.97078) (by norm_num) h h6 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h8⟩ := compred_boot_step (c := 4) (N := 452882) (k := 9619) (j := 512) (M := 460110)
    (lb := 13.02223) (by norm_num) h h7 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h9⟩ := compred_boot_step (c := 4) (N := 460110) (k := 9631) (j := 512) (M := 462410)
    (lb := 13.03847) (by norm_num) h h8 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h10⟩ := compred_boot_step (c := 4) (N := 462410) (k := 9635) (j := 512) (M := 463179)
    (lb := 13.04389) (by norm_num) h h9 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨-, h11⟩ := compred_boot_step (c := 4) (N := 463179) (k := 9636) (j := 512) (M := 463371)
    (lb := 13.04524) (by norm_num) h h10 (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨h11, compred_log_ge_of_pow (N := 463371) (k := 9636) (j := 512) h11 (by norm_num)
    (by decide +kernel) (by norm_num)⟩

end DetPrimality.Bach
