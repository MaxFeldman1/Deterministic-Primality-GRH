import Mathlib
import DetPrimality.Interfaces
import DetPrimality.LogTwo

/-!
# Deterministic square roots modulo a prime, assuming Bach's bound

* `powMod`              : fast modular exponentiation (binary), proved `= b ^ e % m`.
* `exists_nonresidue_lt`: `BachBound c` ⇒ least quadratic non-residue mod an odd prime `p`
                          is `< c (log p)^2`.
* `findNonResidue`      : executable search over `a = 2, …, B(p)+1`, `B(p) = ⌈c⌉₊ * (size p)^2`.
* `tonelliShanks`       : executable Tonelli–Shanks given a non-residue.
* `sqrtModDet`          : the combined deterministic algorithm, with
  `sqrtModDet_correct` (completeness under `BachBound`) and
  `sqrtModDet_sound` / `sqrtModDet_eq_none_of_not_isSquare` (unconditional soundness).
-/

namespace DetPrimality
namespace TonelliShanks

/-! ### Fast modular exponentiation -/

/-- `powMod b e m = b ^ e % m`, computed by binary exponentiation. -/
def powMod (b e m : ℕ) : ℕ :=
  if e = 0 then 1 % m
  else
    let h := powMod b (e / 2) m
    if e % 2 = 0 then h * h % m else h * h % m * b % m
termination_by e
decreasing_by omega

theorem powMod_eq (b e m : ℕ) : powMod b e m = b ^ e % m := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [powMod]
    dsimp only
    split_ifs with h0 h2
    · simp [h0]
    · rw [ih (e / 2) (by omega), ← Nat.mul_mod, ← pow_add]
      have : e / 2 + e / 2 = e := by omega
      rw [this]
    · rw [ih (e / 2) (by omega), ← Nat.mul_mod, ← pow_add, Nat.mod_mul_mod, ← pow_succ]
      have : e / 2 + e / 2 + 1 = e := by omega
      rw [this]

theorem cast_powMod (b e p : ℕ) : ((powMod b e p : ℕ) : ZMod p) = (b : ZMod p) ^ e := by
  rw [powMod_eq, ZMod.natCast_mod, Nat.cast_pow]

/-! ### Small `ZMod` helpers -/

theorem mod_eq_one_iff {p : ℕ} (hp : 1 < p) (x : ℕ) : x % p = 1 ↔ (x : ZMod p) = 1 := by
  have := ZMod.natCast_eq_natCast_iff' x 1 p
  rw [Nat.cast_one] at this
  rw [this, Nat.mod_eq_of_lt hp]

theorem mod_eq_pred_iff {p : ℕ} (hp : 1 < p) (x : ℕ) : x % p = p - 1 ↔ (x : ZMod p) = -1 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have h1 : (-1 : ZMod (k + 1)).val = k := ZMod.val_neg_one k
  constructor
  · intro h
    apply ZMod.val_injective (k + 1)
    rw [h1, ZMod.val_natCast]
    simpa using h
  · intro h
    rw [← ZMod.val_natCast, h, h1]
    simp

theorem natCast_eq_zero_of_mod {p n : ℕ} (h : n % p = 0) : (n : ZMod p) = 0 := by
  rw [← ZMod.natCast_mod, h, Nat.cast_zero]

/-- Euler's criterion in the form used by the algorithm: for `p` an odd prime,
`a ^ (p/2) = -1` iff `a` is a non-square (this also covers `a = 0`). -/
theorem pow_half_eq_neg_one_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) :
    a ^ (p / 2) = -1 ↔ ¬ IsSquare a := by
  have hp3 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  have : Fact (2 < p) := ⟨hp3⟩
  by_cases ha : a = 0
  · subst ha
    have h0 : (0 : ZMod p) ^ (p / 2) = 0 := zero_pow (by omega)
    rw [h0]
    refine iff_of_false ?_ (not_not.mpr ⟨0, by simp⟩)
    intro h
    have : (1 : ZMod p) = 0 := by rw [← neg_eq_zero, ← h]
    exact one_ne_zero this
  · rw [ZMod.euler_criterion p ha]
    rcases ZMod.pow_div_two_eq_neg_one_or_one p ha with h | h
    · rw [h]; exact iff_of_false (Ne.symm ZMod.neg_one_ne_one) (by simp)
    · rw [h]; exact iff_of_true rfl ZMod.neg_one_ne_one

/-! ### Least non-residue from Bach's bound -/

/-- **Least quadratic non-residue under `BachBound c`.** For an odd prime `p` there is a
non-square `a` mod `p` with `a < c (log p)^2`. (The squares form a proper subgroup of
`(ZMod p)ˣ`.) -/
theorem exists_nonresidue_lt {c : ℝ} (hB : BachBound c) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ a : ℕ, (a : ℝ) < c * Real.log p ^ 2 ∧ ¬ IsSquare (a : ZMod p) := by
  have hp3 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  set H : Subgroup (ZMod p)ˣ := (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range with hH
  have hmem : ∀ u : (ZMod p)ˣ, u ∈ H ↔ IsSquare (u : ZMod p) := by
    intro u
    simp only [hH, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, by simp [sq]⟩
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      refine ⟨Units.mk0 y hy0, ?_⟩
      ext
      simp [sq, hy]
  have hne : H ≠ ⊤ := by
    obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p)
      (by rw [ZMod.ringChar_zmod_n]; exact hp)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx ⟨0, by simp⟩
    intro htop
    have hxH : Units.mk0 x hx0 ∈ H := by rw [htop]; exact Subgroup.mem_top _
    rw [hmem] at hxH
    exact hx (by simpa using hxH)
  obtain ⟨a, haH, hlt⟩ := hB p hp3 H hne
  refine ⟨(a : ZMod p).val, hlt, ?_⟩
  rw [ZMod.natCast_zmod_val]
  intro hsq
  exact haH ((hmem a).2 hsq)

/-! ### Computable bound and search -/

theorem log_lt_size {p : ℕ} (hp : 0 < p) : Real.log p < Nat.size p := by
  have h2 : (p : ℝ) < 2 ^ Nat.size p := by exact_mod_cast Nat.lt_size_self p
  have hlog : Real.log p < Nat.size p * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_lt_log (by exact_mod_cast hp) h2
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    norm_num at this
    linarith
  have : (Nat.size p : ℝ) * Real.log 2 ≤ Nat.size p :=
    mul_le_of_le_one_right (Nat.cast_nonneg _) hl2.le
  linarith

/-- Computable search bound `≥ c (log p)^2`: with `Nat.size p` the bit length of `p`,
`ln p < size p · ln 2`, so `⌈c · 0.480454 · (size p)²⌉` suffices (`DetPrimality.log2SqUpper`). -/
def nonResidueBound (c : ℚ) (p : ℕ) : ℕ := ⌈c * log2SqUpper * ((Nat.size p : ℕ) : ℚ) ^ 2⌉₊

theorem le_nonResidueBound {c : ℚ} (hc : 0 < c) {p : ℕ} (_hp : 0 < p) :
    (c : ℝ) * Real.log p ^ 2 ≤ nonResidueBound c p :=
  mul_log_sq_le_ceil hc.le (Nat.lt_size_self p)

/-- Euler test: `a` is a non-residue mod the odd prime `p` iff `a^(p/2) ≡ -1`. -/
def isNonResidueB (p a : ℕ) : Bool := powMod a (p / 2) p == p - 1

theorem isNonResidueB_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ℕ) :
    isNonResidueB p a = true ↔ ¬ IsSquare (a : ZMod p) := by
  have h1 : 1 < p := (Fact.out : p.Prime).one_lt
  rw [isNonResidueB, beq_iff_eq, powMod_eq, mod_eq_pred_iff h1, Nat.cast_pow,
    pow_half_eq_neg_one_iff p hp]

/-- Search `a = 2, 3, …, B(p)+1` for a quadratic non-residue mod `p`. -/
def findNonResidue (c : ℚ) (p : ℕ) : Option ℕ :=
  (List.range' 2 (nonResidueBound c p)).find? (isNonResidueB p)

theorem findNonResidue_spec {c : ℚ} {p z : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h : findNonResidue c p = some z) : ¬ IsSquare (z : ZMod p) :=
  (isNonResidueB_iff p hp z).1 (List.find?_some h)

theorem findNonResidue_isSome {c : ℚ} (hB : BachBound (c : ℝ)) (hc : 0 < c) (p : ℕ)
    [Fact p.Prime] (hp : p ≠ 2) : ∃ z, findNonResidue c p = some z := by
  obtain ⟨a, hlt, hns⟩ := exists_nonresidue_lt hB p hp
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hle := le_nonResidueBound hc hp0
  have haB : a < nonResidueBound c p := by exact_mod_cast lt_of_lt_of_le hlt hle
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

/-! ### Tonelli–Shanks -/

/-- `oddPart m = (s, q)` with `m = q * 2^s`, `q` odd (for `m ≠ 0`). -/
def oddPart (m : ℕ) : ℕ × ℕ :=
  if h : m ≠ 0 ∧ m % 2 = 0 then
    let r := oddPart (m / 2)
    (r.1 + 1, r.2)
  else (0, m)
termination_by m
decreasing_by omega

theorem oddPart_spec (m : ℕ) (hm : m ≠ 0) :
    (oddPart m).2 * 2 ^ (oddPart m).1 = m ∧ (oddPart m).2 % 2 = 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [oddPart]
    split_ifs with h
    · obtain ⟨ih1, ih2⟩ := ih (m / 2) (by omega) (by omega)
      dsimp only
      refine ⟨?_, ih2⟩
      rw [pow_succ, ← mul_assoc, ih1]
      omega
    · dsimp only
      exact ⟨by simp, by omega⟩

/-- Main Tonelli–Shanks loop with state `(M, c, t, R)`. Invariant (in `ZMod p`):
`c^(2^(M-1)) = -1`, `t^(2^(M-1)) = 1`, `R^2 = n t`. -/
def tsLoop (p : ℕ) (M c t R : ℕ) : Option ℕ :=
  if t % p = 1 then some (R % p)
  else
    match (List.range M).find? (fun i => powMod t (2 ^ i) p == 1) with
    | none => none
    | some i =>
      if _hi : i < M then
        let b := powMod c (2 ^ (M - i - 1)) p
        tsLoop p i (b * b % p) (t * b * b % p) (R * b % p)
      else none
termination_by M
decreasing_by omega

theorem tsLoop_spec (p : ℕ) [Fact p.Prime] (n : ZMod p) :
    ∀ M c t R : ℕ, 1 ≤ M → (c : ZMod p) ^ 2 ^ (M - 1) = -1 → (t : ZMod p) ^ 2 ^ (M - 1) = 1 →
      (R : ZMod p) ^ 2 = n * t → ∃ r, tsLoop p M c t R = some r ∧ (r : ZMod p) ^ 2 = n := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro c t R hM hc ht hR
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases ht1 : t % p = 1
  · refine ⟨R % p, ?_, ?_⟩
    · rw [tsLoop, if_pos ht1]
    · rw [ZMod.natCast_mod, hR, (mod_eq_one_iff hp1 t).1 ht1, mul_one]
  · have htne : (t : ZMod p) ≠ 1 := fun h => ht1 ((mod_eq_one_iff hp1 t).2 h)
    have hfi : ∀ i, (powMod t (2 ^ i) p == 1) = true ↔ (t : ZMod p) ^ 2 ^ i = 1 := by
      intro i
      rw [beq_iff_eq, powMod_eq, mod_eq_one_iff hp1, Nat.cast_pow]
    obtain ⟨i, hi⟩ : ∃ i, (List.range M).find? (fun i => powMod t (2 ^ i) p == 1) = some i := by
      cases h : (List.range M).find? (fun i => powMod t (2 ^ i) p == 1) with
      | some i => exact ⟨i, rfl⟩
      | none =>
        rw [List.find?_eq_none] at h
        exact absurd ((hfi (M - 1)).2 ht) (h (M - 1) (List.mem_range.2 (by omega)))
    obtain ⟨hfi_i, hiM, hmin⟩ := List.find?_range_eq_some.1 hi
    rw [List.mem_range] at hiM
    have hti : (t : ZMod p) ^ 2 ^ i = 1 := (hfi i).1 hfi_i
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := by
      rcases i with _ | k
      · exact (htne (by simpa using hti)).elim
      · exact ⟨k, rfl⟩
    have htk : (t : ZMod p) ^ 2 ^ k ≠ 1 := by
      intro h
      have h1 := hmin k (by omega)
      have h2 : (powMod t (2 ^ k) p == 1) = true := (hfi k).2 h
      simp [h2] at h1
    have htk' : (t : ZMod p) ^ 2 ^ k = -1 := by
      have hsq : (t : ZMod p) ^ 2 ^ k * (t : ZMod p) ^ 2 ^ k = 1 := by
        rw [← pow_add, ← two_mul, ← pow_succ']
        exact hti
      exact (mul_self_eq_one_iff.1 hsq).resolve_left htk
    set b := powMod c (2 ^ (M - (k + 1) - 1)) p with hb
    have hbc : (b : ZMod p) ^ 2 ^ (k + 1) = -1 := by
      rw [hb, cast_powMod, ← pow_mul, ← pow_add,
        show M - (k + 1) - 1 + (k + 1) = M - 1 by omega, hc]
    have hc' : ((b * b % p : ℕ) : ZMod p) ^ 2 ^ (k + 1 - 1) = -1 := by
      simp only [ZMod.natCast_mod, Nat.cast_mul]
      rw [show k + 1 - 1 = k by omega, ← sq, ← pow_mul, ← pow_succ']
      exact hbc
    have ht' : ((t * b * b % p : ℕ) : ZMod p) ^ 2 ^ (k + 1 - 1) = 1 := by
      simp only [ZMod.natCast_mod, Nat.cast_mul]
      rw [show k + 1 - 1 = k by omega, mul_assoc, mul_pow, ← sq, ← pow_mul, ← pow_succ',
        htk', hbc]
      norm_num
    have hR' : ((R * b % p : ℕ) : ZMod p) ^ 2 = n * ((t * b * b % p : ℕ) : ZMod p) := by
      simp only [ZMod.natCast_mod, Nat.cast_mul]
      rw [mul_pow, hR]
      ring
    obtain ⟨r, hr1, hr2⟩ :=
      ih (k + 1) hiM (b * b % p) (t * b * b % p) (R * b % p) (by omega) hc' ht' hR'
    refine ⟨r, ?_, hr2⟩
    rw [tsLoop, if_neg ht1, hi]
    dsimp only
    rw [dif_pos hiM]
    exact hr1

/-- Tonelli–Shanks: given a non-residue `z` mod `p`, compute a square root of `n` mod `p`. -/
def tonelliShanks (p n z : ℕ) : Option ℕ :=
  tsLoop p (oddPart (p - 1)).1 (powMod z (oddPart (p - 1)).2 p)
    (powMod n (oddPart (p - 1)).2 p) (powMod n (((oddPart (p - 1)).2 + 1) / 2) p)

theorem tonelliShanks_correct (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n z : ℕ)
    (hz : ¬ IsSquare (z : ZMod p)) (hn0 : (n : ZMod p) ≠ 0) (hn : IsSquare (n : ZMod p)) :
    ∃ r, tonelliShanks p n z = some r ∧ (r : ZMod p) ^ 2 = n := by
  have hp3 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  have hodd : p % 2 = 1 := Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp)
  obtain ⟨h1, h2⟩ := oddPart_spec (p - 1) (by omega)
  unfold tonelliShanks
  set s := (oddPart (p - 1)).1 with hs
  set q := (oddPart (p - 1)).2 with hq
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, pow_zero, mul_one] at h1
      omega
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hhalf : p / 2 = q * 2 ^ k := by
    rw [hk, pow_succ] at h1
    have h3 : 2 * (q * 2 ^ k) = p - 1 := by rw [← h1]; ring
    generalize q * 2 ^ k = m at h3 ⊢
    omega
  have hez := (pow_half_eq_neg_one_iff p hp z).2 hz
  have hen : (n : ZMod p) ^ (p / 2) = 1 := (ZMod.euler_criterion p hn0).1 hn
  apply tsLoop_spec p (n : ZMod p) s _ _ _ hs1
  · rw [cast_powMod, ← pow_mul, hk, Nat.add_sub_cancel, ← hhalf, hez]
  · rw [cast_powMod, ← pow_mul, hk, Nat.add_sub_cancel, ← hhalf, hen]
  · rw [cast_powMod, cast_powMod, ← pow_mul, show (q + 1) / 2 * 2 = q + 1 by omega, pow_succ']

/-! ### The combined deterministic algorithm -/

/-- Deterministic square root mod `p`: find a non-residue below `B(p)`, run Tonelli–Shanks,
and verify the answer. Returns `none` iff no square root exists (for odd prime `p`, under
`BachBound c`). -/
def sqrtModDet (c : ℚ) (p n : ℕ) : Option ℕ :=
  if n % p = 0 then some 0
  else
    match findNonResidue c p with
    | none => none
    | some z =>
      match tonelliShanks p n z with
      | none => none
      | some r => if r * r % p = n % p then some r else none

/-- Unconditional soundness: any output is a square root. -/
theorem sqrtModDet_sound {c : ℚ} {p n r : ℕ} (h : sqrtModDet c p n = some r) :
    (r : ZMod p) ^ 2 = n := by
  unfold sqrtModDet at h
  by_cases h0 : n % p = 0
  · rw [if_pos h0] at h
    obtain rfl := (Option.some.inj h).symm
    rw [natCast_eq_zero_of_mod h0]
    simp
  · rw [if_neg h0] at h
    cases hz : findNonResidue c p with
    | none => simp [hz] at h
    | some z =>
      cases hr : tonelliShanks p n z with
      | none => simp [hz, hr] at h
      | some r' =>
        simp only [hz, hr] at h
        split_ifs at h with hc
        obtain rfl := Option.some.inj h
        rw [sq, ← Nat.cast_mul, (ZMod.natCast_eq_natCast_iff' _ _ _).2 hc]

/-- **Main theorem (completeness).** Under `BachBound c`, `sqrtModDet` finds a square root of
every square mod an odd prime. -/
theorem sqrtModDet_correct {c : ℚ} (hB : BachBound (c : ℝ)) (hc : 0 < c) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
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
    obtain ⟨z, hz⟩ := findNonResidue_isSome hB hc p hp
    obtain ⟨r, hr, hr2⟩ := tonelliShanks_correct p hp n z (findNonResidue_spec hp hz) hn0 hn
    refine ⟨r, ?_, hr2⟩
    have hc' : r * r % p = n % p := by
      rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_mul, ← sq, hr2]
    unfold sqrtModDet
    rw [if_neg h0]
    simp only [hz, hr]
    rw [if_pos hc']

/-- Converse: on a non-square the algorithm returns `none` (unconditionally). -/
theorem sqrtModDet_eq_none_of_not_isSquare {c : ℚ} {p n : ℕ} (hn : ¬ IsSquare (n : ZMod p)) :
    sqrtModDet c p n = none := by
  cases h : sqrtModDet c p n with
  | none => rfl
  | some r => exact (hn ⟨r, by rw [← sqrtModDet_sound h, sq]⟩).elim

/-- Under `BachBound c`, for an odd prime `p`: `sqrtModDet` succeeds iff `n` is a square. -/
theorem sqrtModDet_isSome_iff {c : ℚ} (hB : BachBound (c : ℝ)) (hc : 0 < c) (p : ℕ)
    [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    (sqrtModDet c p n).isSome ↔ IsSquare (n : ZMod p) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
    exact ⟨r, by rw [← sqrtModDet_sound hr, sq]⟩
  · intro hn
    obtain ⟨r, hr, -⟩ := sqrtModDet_correct hB hc p hp n hn
    simp [hr]

end TonelliShanks
end DetPrimality
