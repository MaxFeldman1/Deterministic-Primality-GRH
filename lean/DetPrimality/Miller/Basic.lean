import Mathlib
import DetPrimality.Interfaces

/-!
# Deterministic Miller test, correct under `BachBound c` (Layers 3 + 4)

* `powMod` : executable binary modular exponentiation, `powMod_eq : powMod a e n = a ^ e % n`.
* `twoVal`, `oddPart` : `m = 2 ^ twoVal m * oddPart m`, `oddPart m` odd for `m ≠ 0`.
* `sprp n a` : strong-probable-prime test to base `a` (executable).
* `IsStrongLiar n x` : the same condition for a unit `x : (ZMod n)ˣ`.
* Layer 3 (`exists_proper_subgroup_strongLiars`): for odd composite `n > 2` the strong liars
  lie in a proper subgroup of `(ZMod n)ˣ`.
* Layer 4 (`millerDet_correct`): `millerDet c n = true ↔ n.Prime`, assuming `BachBound c`;
  `millerDet_of_prime` (primes always pass) is unconditional.
-/

namespace DetPrimality.Miller

/-! ## Fast modular exponentiation -/

/-- Binary modular exponentiation: `powMod a e n = a ^ e % n` (see `powMod_eq`). -/
def powMod (a e n : ℕ) : ℕ :=
  if h : e = 0 then 1 % n
  else
    let b := powMod a (e / 2) n
    if e % 2 = 0 then b * b % n else b * b % n * a % n
termination_by e
decreasing_by omega

theorem powMod_eq (a e n : ℕ) : powMod a e n = a ^ e % n := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [powMod]
    dsimp only
    split_ifs with h0 h2
    · simp [h0]
    · rw [ih (e / 2) (by omega), ← Nat.mul_mod, ← pow_add]
      congr 2; omega
    · rw [ih (e / 2) (by omega), ← Nat.mul_mod, Nat.mod_mul_mod, ← pow_add, ← pow_succ]
      congr 2; omega

/-! ## Writing `m = 2^s * d` with `d` odd -/

/-- `oddDecomp m = (s, d)` with `m = 2^s * d` and `d` odd when `m ≠ 0`. -/
def oddDecomp (m : ℕ) : ℕ × ℕ :=
  if h : m ≠ 0 ∧ m % 2 = 0 then
    let p := oddDecomp (m / 2)
    (p.1 + 1, p.2)
  else (0, m)
termination_by m
decreasing_by omega

theorem oddDecomp_spec (m : ℕ) :
    2 ^ (oddDecomp m).1 * (oddDecomp m).2 = m ∧ (m ≠ 0 → (oddDecomp m).2 % 2 = 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [oddDecomp]
    dsimp only
    split_ifs with h
    · obtain ⟨h1, h2⟩ := ih (m / 2) (by omega)
      refine ⟨?_, fun _ => h2 (by omega)⟩
      calc 2 ^ ((oddDecomp (m / 2)).1 + 1) * (oddDecomp (m / 2)).2
          = 2 * (2 ^ (oddDecomp (m / 2)).1 * (oddDecomp (m / 2)).2) := by ring
        _ = m := by rw [h1]; omega
    · refine ⟨by simp, fun hm => ?_⟩
      simp only
      omega

/-- The 2-adic valuation of `m` (0 for `m = 0`). -/
def twoVal (m : ℕ) : ℕ := (oddDecomp m).1

/-- The odd part of `m`. -/
def oddPart (m : ℕ) : ℕ := (oddDecomp m).2

theorem twoVal_spec (m : ℕ) : 2 ^ twoVal m * oddPart m = m := (oddDecomp_spec m).1

theorem oddPart_odd {m : ℕ} (hm : m ≠ 0) : oddPart m % 2 = 1 := (oddDecomp_spec m).2 hm

/-! ## Strong probable primes -/

/-- Strong probable prime test of `n` to base `a`: writing `n - 1 = 2^s d` with `d` odd,
`a^d ≡ 1 (mod n)` or `a^(d 2^r) ≡ -1 (mod n)` for some `r < s`. Executable. -/
def sprp (n a : ℕ) : Bool :=
  let s := twoVal (n - 1)
  let d := oddPart (n - 1)
  powMod a d n == 1 || (List.range s).any (fun r => powMod a (d * 2 ^ r) n == n - 1)

theorem mod_eq_one_iff {n m : ℕ} (hn : 1 < n) : m % n = 1 ↔ (m : ZMod n) = 1 := by
  have h := ZMod.natCast_eq_natCast_iff' m 1 n
  rw [Nat.cast_one, Nat.mod_eq_of_lt hn] at h
  exact h.symm

theorem mod_eq_neg_one_iff {n m : ℕ} (hn : 1 < n) : m % n = n - 1 ↔ (m : ZMod n) = -1 := by
  have h := ZMod.natCast_eq_natCast_iff' m (n - 1) n
  have h2 : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [h2, Nat.mod_eq_of_lt (by omega : n - 1 < n)] at h
  exact h.symm

theorem sprp_iff {n : ℕ} (hn : 1 < n) (a : ℕ) :
    sprp n a = true ↔ (a : ZMod n) ^ oddPart (n - 1) = 1 ∨
      ∃ r < twoVal (n - 1), (a : ZMod n) ^ (oddPart (n - 1) * 2 ^ r) = -1 := by
  simp only [sprp, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range, powMod_eq,
    mod_eq_one_iff hn, mod_eq_neg_one_iff hn, Nat.cast_pow]

/-- Strong-liar condition for a unit of `ZMod n`. -/
def IsStrongLiar (n : ℕ) (x : (ZMod n)ˣ) : Prop :=
  x ^ oddPart (n - 1) = 1 ∨ ∃ r < twoVal (n - 1), x ^ (oddPart (n - 1) * 2 ^ r) = -1

theorem isStrongLiar_iff_sprp {n : ℕ} (hn : 1 < n) (x : (ZMod n)ˣ) :
    IsStrongLiar n x ↔ sprp n (x : ZMod n).val = true := by
  have : NeZero n := ⟨by omega⟩
  rw [sprp_iff hn, ZMod.natCast_zmod_val]
  simp only [IsStrongLiar, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, Units.val_neg]

/-! ## Layer 3: strong liars lie in a proper subgroup -/

/-- `{x | x^k = ±1}` as a subgroup of `(ZMod n)ˣ`. -/
def pmSubgroup (n k : ℕ) : Subgroup (ZMod n)ˣ where
  carrier := {x | x ^ k = 1 ∨ x ^ k = -1}
  one_mem' := by simp
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb) <;> simp [mul_pow, ha, hb]
  inv_mem' := by
    rintro a (ha | ha) <;> simp [inv_pow, ha]

theorem mem_pmSubgroup {n k : ℕ} {x : (ZMod n)ˣ} :
    x ∈ pmSubgroup n k ↔ x ^ k = 1 ∨ x ^ k = -1 := Iff.rfl

/-- CRT step: if `n = m₁ m₂` with coprime `m₁, m₂ > 2` and some unit has `x^k = -1`, then
`{x | x^k = ±1}` is a proper subgroup. -/
theorem exists_not_mem_pmSubgroup {n m1 m2 : ℕ} (hn : n = m1 * m2) (hcop : m1.Coprime m2)
    (h1 : 2 < m1) (h2 : 2 < m2) (k : ℕ) (x : (ZMod n)ˣ) (hx : x ^ k = -1) :
    ∃ y : (ZMod n)ˣ, y ∉ pmSubgroup n k := by
  subst hn
  have : Fact (2 < m1) := ⟨h1⟩
  have : Fact (2 < m2) := ⟨h2⟩
  set e := ZMod.chineseRemainder hcop
  have hxk : (x : ZMod (m1 * m2)) ^ k = -1 := by
    have := congrArg Units.val hx
    simpa using this
  have hfst : (e x).1 ^ k = -1 := by
    have : e ((x : ZMod (m1 * m2)) ^ k) = e (-1) := by rw [hxk]
    rw [map_pow, map_neg, map_one] at this
    exact congrArg Prod.fst this
  have hu : IsUnit (e.symm ((e x).1, 1)) := by
    rw [← isUnit_map_iff e, RingEquiv.apply_symm_apply, Prod.isUnit_iff]
    exact ⟨(x.isUnit.map e).map (RingHom.fst _ _), isUnit_one⟩
  refine ⟨hu.unit, ?_⟩
  have hy : e ((hu.unit : ZMod (m1 * m2)) ^ k) = (-1, 1) := by
    rw [IsUnit.unit_spec, map_pow, RingEquiv.apply_symm_apply, Prod.pow_mk, one_pow, hfst]
  rintro (h | h)
  · have h' := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h'
    rw [h', map_one] at hy
    exact ZMod.neg_one_ne_one (congrArg Prod.fst hy).symm
  · have h' := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h'
    rw [h', map_neg, map_one] at hy
    exact ZMod.neg_one_ne_one (congrArg Prod.snd hy)

/-- Prime-power step: in `(ZMod (p^k))ˣ`, `k ≥ 2`, the unit `1 + p^(k-1)` has
`(1 + p^(k-1))^(p^k - 1) ≠ 1` (since `p ∤ p^k - 1`). -/
theorem exists_pow_ne_one_primePow {n p k : ℕ} (hn : n = p ^ k) (hp : p.Prime) (hk : 2 ≤ k) :
    ∃ y : (ZMod n)ˣ, y ^ (n - 1) ≠ 1 := by
  subst hn
  set t : ZMod (p ^ k) := ((p ^ (k - 1) : ℕ) : ZMod (p ^ k)) with ht
  have ht2 : t * t = 0 := by
    rw [ht, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ← pow_add]
    exact pow_dvd_pow p (by omega)
  have hpow : ∀ m : ℕ, (1 + t) ^ m = 1 + (m : ZMod (p ^ k)) * t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih]
      calc (1 + (m : ZMod (p ^ k)) * t) * (1 + t)
          = 1 + ((m : ZMod (p ^ k)) + 1) * t + (m : ZMod (p ^ k)) * (t * t) := by ring
        _ = 1 + ((m + 1 : ℕ) : ZMod (p ^ k)) * t := by rw [ht2]; push_cast; ring
  have hu : IsUnit (1 + t) :=
    isUnit_iff_exists_inv.mpr ⟨1 - t, by
      rw [show (1 + t) * (1 - t) = 1 - t * t by ring, ht2, sub_zero]⟩
  refine ⟨hu.unit, fun h => ?_⟩
  have h' := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one, hpow] at h'
  have h0 : ((p ^ k - 1 : ℕ) : ZMod (p ^ k)) * t = 0 := by linear_combination h'
  rw [ht, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  have h0' : p * p ^ (k - 1) ∣ (p ^ k - 1) * p ^ (k - 1) := by
    rwa [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hdvd : p ∣ p ^ k - 1 := Nat.dvd_of_mul_dvd_mul_right (pow_pos hp.pos _) h0'
  have hp1 : p ∣ p ^ k := dvd_pow_self p (by omega)
  have : p ∣ 1 := (Nat.dvd_add_right hdvd).mp (by rwa [Nat.sub_add_cancel (by omega)])
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **Layer 3.** For odd composite `n > 2`, all strong liars lie in a proper subgroup of
`(ZMod n)ˣ`. -/
theorem exists_proper_subgroup_strongLiars {n : ℕ} (hn : 2 < n) (hodd : n % 2 = 1)
    (hnp : ¬ n.Prime) :
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧ ∀ x, IsStrongLiar n x → x ∈ H := by
  classical
  have hsd := twoVal_spec (n - 1)
  have hd1 : oddPart (n - 1) % 2 = 1 := oddPart_odd (by omega)
  set s := twoVal (n - 1) with hs_def
  set d := oddPart (n - 1) with hd_def
  have hs1 : 1 ≤ s := by
    by_contra h
    have h0 : s = 0 := by omega
    rw [h0, pow_zero, one_mul] at hsd
    omega
  have hn0 : n ≠ 0 := by omega
  set p := n.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime (by omega)
  set k := n.factorization p with hk_def
  have hfac : p ^ k * (n / p ^ k) = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hk : 1 ≤ k := hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    have hp2 : p = 2 := by omega
    have : 2 ∣ n := hp2 ▸ Nat.minFac_dvd n
    omega
  by_cases hm2 : n / p ^ k = 1
  · -- prime power case: use the Fermat subgroup `{x | x^(n-1) = 1}`
    have hnpk : n = p ^ k := by rw [hm2, mul_one] at hfac; exact hfac.symm
    have hk2 : 2 ≤ k := by
      by_contra h
      have h1 : k = 1 := by omega
      rw [h1, pow_one] at hnpk
      exact hnp (hnpk ▸ hp)
    refine ⟨(powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker, ?_, ?_⟩
    · obtain ⟨y, hy⟩ := exists_pow_ne_one_primePow hnpk hp hk2
      intro htop
      apply hy
      have : y ∈ (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker := by
        rw [htop]; exact Subgroup.mem_top y
      simpa [MonoidHom.mem_ker] using this
    · intro x hx
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hn1 : n - 1 = d * 2 ^ s := by rw [← hsd]; ring
      rw [hn1]
      rcases hx with hx | ⟨r, hr, hx⟩
      · rw [pow_mul, hx, one_pow]
      · have he : d * 2 ^ s = d * 2 ^ r * 2 ^ (s - r) := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hr.le]
        rw [he, pow_mul, hx]
        exact Even.neg_one_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  · -- not a prime power: `n = m₁ m₂` coprime, use `{x | x^(d 2^j) = ±1}`
    have hm2pos : n / p ^ k ≠ 0 := by
      intro h; rw [h, mul_zero] at hfac; omega
    have hm2odd : (n / p ^ k) % 2 = 1 := by
      have : Odd n := Nat.odd_iff.mpr hodd
      rw [← hfac, Nat.odd_mul] at this
      exact Nat.odd_iff.mp this.2
    have hm1 : 2 < p ^ k := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    have hcop : (p ^ k).Coprime (n / p ^ k) := (Nat.coprime_ordCompl hp hn0).pow_left k
    let P : ℕ → Prop := fun r => ∃ x : (ZMod n)ˣ, x ^ (d * 2 ^ r) = -1
    have hP0 : P 0 := ⟨-1, by
      rw [pow_zero, mul_one]; exact Odd.neg_one_pow (Nat.odd_iff.mpr hd1)⟩
    set j := Nat.findGreatest P (s - 1) with hj_def
    have hPj : P j := Nat.findGreatest_spec (Nat.zero_le _) hP0
    have hjs : j < s := by
      have := Nat.findGreatest_le (P := P) (s - 1); omega
    refine ⟨pmSubgroup n (d * 2 ^ j), ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hPj
      have hm2gt : 2 < n / p ^ k := by
        generalize n / p ^ k = m at hm2 hm2odd hm2pos ⊢
        omega
      obtain ⟨y, hy⟩ := exists_not_mem_pmSubgroup hfac.symm hcop hm1 hm2gt _ x hx
      intro htop
      apply hy
      rw [htop]
      exact Subgroup.mem_top y
    · intro x hx
      rw [mem_pmSubgroup]
      rcases hx with hx | ⟨r, hr, hx⟩
      · left; rw [pow_mul, hx, one_pow]
      · have hrj : r ≤ j := Nat.le_findGreatest (by omega) ⟨x, hx⟩
        rcases hrj.lt_or_eq with hlt | heq
        · left
          have he : d * 2 ^ j = d * 2 ^ r * 2 ^ (j - r) := by
            rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
          rw [he, pow_mul, hx]
          exact Even.neg_one_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩)
        · right; rw [← heq]; exact hx

/-! ## Primes always pass -/

theorem pow_two_pow_eq_one {R : Type*} [CommRing R] [NoZeroDivisors R] (x : R) (s : ℕ)
    (h : x ^ 2 ^ s = 1) : x = 1 ∨ ∃ r < s, x ^ 2 ^ r = -1 := by
  induction s with
  | zero => left; simpa using h
  | succ s ih =>
    have h' : x ^ 2 ^ s * x ^ 2 ^ s = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']; exact h
    rcases mul_self_eq_one_iff.mp h' with h1 | h1
    · rcases ih h1 with h2 | ⟨r, hr, h2⟩
      · left; exact h2
      · right; exact ⟨r, by omega, h2⟩
    · right; exact ⟨s, by omega, h1⟩

/-- Every base `0 < a < p` is a strong probable prime base for an odd prime `p`. -/
theorem sprp_of_prime {p : ℕ} (hp : p.Prime) (a : ℕ) (ha : 0 < a) (hap : a < p) :
    sprp p a = true := by
  have := Fact.mk hp
  rw [sprp_iff hp.one_lt]
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt ha hap
  have hferm := ZMod.pow_card_sub_one_eq_one ha0
  have hsd := twoVal_spec (p - 1)
  rw [← hsd, mul_comm, pow_mul] at hferm
  rcases pow_two_pow_eq_one _ _ hferm with h | ⟨r, hr, h⟩
  · left; exact h
  · right; exact ⟨r, hr, by rw [pow_mul]; exact h⟩

/-! ## Layer 4: the deterministic test -/

/-- Computable loop bound: `millerBound c n ≥ c (log n)^2` (see `millerBound_ge`). -/
def millerBound (c : ℚ) (n : ℕ) : ℕ := ⌈c⌉₊ * (Nat.log2 n + 1) ^ 2

/-- Deterministic Miller test: `n` prime iff `sprp n a` for all `2 ≤ a < min (millerBound c n) n`
(for odd `n > 2`). -/
def millerDet (c : ℚ) (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else (List.range' 2 (min (millerBound c n) n - 2)).all (fun a => sprp n a)

theorem millerBound_ge {c : ℚ} (hc : 0 ≤ c) (n : ℕ) :
    (c : ℝ) * Real.log n ^ 2 ≤ (millerBound c n : ℝ) := by
  have hL : Real.log n ≤ ((Nat.log2 n + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, Real.log_zero]; positivity
    have h1 : (n : ℝ) < 2 ^ (Nat.log2 n + 1) := by exact_mod_cast Nat.lt_log2_self (n := n)
    have h2 : Real.log n < ((Nat.log2 n + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast h1)
    have h3 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
    have h4 : (0 : ℝ) ≤ ((Nat.log2 n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hsq : Real.log n ^ 2 ≤ ((Nat.log2 n + 1 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ h0 hL 2
  have hceil : (c : ℝ) ≤ ((⌈c⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_ceil c
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  unfold millerBound
  rw [Nat.cast_mul, Nat.cast_pow]
  calc (c : ℝ) * Real.log n ^ 2 ≤ c * ((Nat.log2 n + 1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hc'
    _ ≤ ((⌈c⌉₊ : ℕ) : ℝ) * ((Nat.log2 n + 1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hceil (sq_nonneg _)

theorem millerDet_iff_all (c : ℚ) {n : ℕ} (h2 : 2 < n) (hodd : n % 2 = 1) :
    millerDet c n = true ↔ ∀ a, 2 ≤ a → a < millerBound c n → a < n → sprp n a = true := by
  have h1 : ¬ n < 2 := by omega
  have h2' : n ≠ 2 := by omega
  have h3 : n % 2 ≠ 0 := by omega
  simp only [millerDet, h1, h2', h3, if_false, List.all_eq_true, List.mem_range'_1]
  constructor
  · intro h a ha hb hn; exact h a ⟨ha, by omega⟩
  · rintro h a ⟨ha, hb⟩; exact h a ha (by omega) (by omega)

/-- **Primes always pass** (unconditional). -/
theorem millerDet_of_prime (c : ℚ) {n : ℕ} (hp : n.Prime) : millerDet c n = true := by
  by_cases h2 : n = 2
  · subst h2; simp [millerDet]
  have hodd : n % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
  have hn2 : 2 < n := by have := hp.two_le; omega
  rw [millerDet_iff_all c hn2 hodd]
  intro a ha _ han
  exact sprp_of_prime hp a (by omega) han

/-- Under `BachBound c`, composites (and `0, 1`) are rejected. -/
theorem millerDet_eq_false_of_not_prime {c : ℚ} (hc : 0 ≤ c) (hB : BachBound (c : ℝ)) {n : ℕ}
    (hnp : ¬ n.Prime) : millerDet c n = false := by
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
  obtain ⟨a, haH, hab⟩ := hB n hn H hH
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨by omega⟩
  have hval_lt : (a : ZMod n).val < millerBound c n := by
    have := millerBound_ge hc n
    exact_mod_cast hab.trans_le this
  have hva0 : (a : ZMod n).val ≠ 0 := by
    rw [Ne, ZMod.val_eq_zero]; exact a.ne_zero
  have hva1 : (a : ZMod n).val ≠ 1 := by
    rw [Ne, ZMod.val_eq_one (by omega)]
    intro h
    apply haH
    have : a = 1 := Units.ext h
    rw [this]; exact H.one_mem
  apply haH
  apply hliar
  rw [isStrongLiar_iff_sprp (by omega)]
  exact hall _ (by omega) hval_lt (ZMod.val_lt _)

/-- **Main theorem.** Under `BachBound c` (e.g. Bach's `c = 2` under GRH), the deterministic
Miller test is correct. -/
theorem millerDet_correct (c : ℚ) (hc : 0 < c) (hB : BachBound (c : ℝ)) (n : ℕ) :
    millerDet c n = true ↔ n.Prime := by
  constructor
  · intro h
    by_contra hnp
    rw [millerDet_eq_false_of_not_prime hc.le hB hnp] at h
    exact Bool.false_ne_true h
  · exact millerDet_of_prime c

end DetPrimality.Miller
