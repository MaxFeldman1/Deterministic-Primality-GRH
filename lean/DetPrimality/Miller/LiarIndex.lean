import Mathlib
import DetPrimality.Miller.Basic

/-!
# Strong liars lie in a subgroup of index `≥ 4` (odd composite `n ≠ 9`)

Write `n - 1 = 2^s d`, `d` odd.

* `n = p^k`, `k ≥ 2`: `H = {x | x^(n-1) = 1}`. If `[G:H] ≤ 3` then `y^(6(n-1)) = 1` for all units
  `y`; this fails for `y = 1 + p^(k-1)` (`p ≥ 5`) and for a lift of `4 mod 27` (`p = 3`, `k ≥ 3`).
* otherwise `n = m₁ m₂` coprime, `m_i > 2`: `H = {x | x^e = ±1}`, `e = 2^j d`, `j` maximal with
  `-1` an `e`-th power. With `K = {x | x^e ≡ ±1 mod m₁}` we have `H < K`; if `K ≠ ⊤` the chain
  `H < K < G` gives index `≥ 4`. If `K = ⊤` for both orderings then all units mod `m_i` have
  `u^e = ±1`, which forces `m₁, m₂` prime with `m_i - 1 ∣ m₁ m₂ - 1`, so `m₁ = m₂`: contradiction.
-/

namespace DetPrimality.Miller

/-- A chain `H < K < ⊤` in a finite group forces `[G : H] ≥ 4`. -/
theorem liar4_four_le_index_of_chain {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) (h1 : ¬ K ≤ H) (h2 : K ≠ ⊤) : 4 ≤ H.index := by
  have hmul := Subgroup.relIndex_mul_index hHK
  have hH0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have ha1 : H.relIndex K ≠ 1 := fun h => h1 (Subgroup.relIndex_eq_one.mp h)
  have hb1 : K.index ≠ 1 := fun h => h2 (Subgroup.index_eq_one.mp h)
  have ha0 : H.relIndex K ≠ 0 := by
    intro h; rw [h, zero_mul] at hmul; exact hH0 hmul.symm
  have hb0 : K.index ≠ 0 := by
    intro h; rw [h, mul_zero] at hmul; exact hH0 hmul.symm
  rw [← hmul]
  exact Nat.mul_le_mul (by omega : 2 ≤ H.relIndex K) (by omega : 2 ≤ K.index)

/-- In `(ZMod (p^k))ˣ`, `k ≥ 2`, the unit `1 + p^(k-1)` has `y^M ≠ 1` whenever `p ∤ M`. -/
theorem liar4_exists_pow_ne_one {n p k M : ℕ} (hn : n = p ^ k) (hp : p.Prime) (hk : 2 ≤ k)
    (hM : ¬ p ∣ M) : ∃ y : (ZMod n)ˣ, y ^ M ≠ 1 := by
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
  refine ⟨hu.unit, fun h => hM ?_⟩
  have h' := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one, hpow] at h'
  have h0 : (M : ZMod (p ^ k)) * t = 0 := by linear_combination h'
  rw [ht, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
  have h0' : p * p ^ (k - 1) ∣ M * p ^ (k - 1) := by
    rwa [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  exact Nat.dvd_of_mul_dvd_mul_right (pow_pos hp.pos _) h0'

/-- The unit `4` of `ZMod 27` (of order `9`). -/
def liar4_u4 : (ZMod 27)ˣ := ⟨4, 7, by decide, by decide⟩

theorem liar4_u4_pow_nine : liar4_u4 ^ 9 = 1 := by decide +kernel

theorem liar4_u4_pow_three : liar4_u4 ^ 3 ≠ 1 := by decide +kernel

/-- If `27 ∣ n` and `M ≡ 3 (mod 9)` then some unit of `ZMod n` has `y^M ≠ 1`. -/
theorem liar4_exists_pow_ne_one_three {n t M : ℕ} (hn : n = 27 * t) (ht : t ≠ 0)
    (hM : M % 9 = 3) : ∃ y : (ZMod n)ˣ, y ^ M ≠ 1 := by
  have : NeZero n := ⟨by omega⟩
  have hdvd : 27 ∣ n := ⟨t, hn⟩
  obtain ⟨y, hy⟩ := ZMod.unitsMap_surjective hdvd liar4_u4
  refine ⟨y, fun h => liar4_u4_pow_three ?_⟩
  have h2 : liar4_u4 ^ M = 1 := by rw [← hy, ← map_pow, h, map_one]
  have hM' : M = 9 * (M / 9) + 3 := by omega
  rw [hM', pow_add, pow_mul, liar4_u4_pow_nine, one_pow, one_mul] at h2
  exact h2

/-- If every unit mod a prime `p` has `u^M = 1` then `p - 1 ∣ M`. -/
theorem liar4_sub_one_dvd {p M : ℕ} (hp : p.Prime) (h : ∀ u : (ZMod p)ˣ, u ^ M = 1) :
    p - 1 ∣ M := by
  haveI := Fact.mk hp
  have h1 := Monoid.exponent_dvd_of_forall_pow_eq_one h
  rwa [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units] at h1

theorem liar4_two_prime_arith {a b : ℕ} (ha : 2 < a) (hb : 2 < b) (h1 : a - 1 ∣ a * b - 1)
    (h2 : b - 1 ∣ a * b - 1) : a = b := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp only [add_tsub_cancel_right] at h1 h2
  have e1 : (a + 1) * (b + 1) - 1 = a * (b + 1) + b := by
    have : (a + 1) * (b + 1) = a * (b + 1) + b + 1 := by ring
    omega
  have e2 : (a + 1) * (b + 1) - 1 = b * (a + 1) + a := by
    have : (a + 1) * (b + 1) = b * (a + 1) + a + 1 := by ring
    omega
  rw [e1] at h1
  rw [e2] at h2
  have h1' : a ∣ b := (Nat.dvd_add_right (dvd_mul_right a _)).mp h1
  have h2' : b ∣ a := (Nat.dvd_add_right (dvd_mul_right b _)).mp h2
  rw [Nat.dvd_antisymm h1' h2']

/-- Chain step: `n = m₁ m₂` coprime, `m_i > 2`, `-1` an `k`-th power. If `{x | x^k = ±1}` has
index `< 4` in `(ZMod n)ˣ`, then every unit of `ZMod m₁` has `u^k = ±1`. -/
theorem liar4_forall_pm_of_index_lt {n m1 m2 : ℕ} (hn : n = m1 * m2) (hcop : m1.Coprime m2)
    (h1 : 2 < m1) (h2 : 2 < m2) (k : ℕ) (b : (ZMod n)ˣ) (hb : b ^ k = -1)
    (hidx : ¬ 4 ≤ (pmSubgroup n k).index) (u : (ZMod m1)ˣ) : u ^ k = 1 ∨ u ^ k = -1 := by
  subst hn
  by_contra hu
  apply hidx
  have : Fact (2 < m1) := ⟨h1⟩
  have : Fact (2 < m2) := ⟨h2⟩
  have : NeZero (m1 * m2) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  set e := ZMod.chineseRemainder hcop
  let ψ : (ZMod (m1 * m2))ˣ →* (ZMod m1)ˣ :=
    Units.map (((RingHom.fst (ZMod m1) (ZMod m2)).comp
      (e : ZMod (m1 * m2) →+* ZMod m1 × ZMod m2) : ZMod (m1 * m2) →+* ZMod m1) :
        ZMod (m1 * m2) →* ZMod m1)
  have hψ : ∀ x, ((ψ x : (ZMod m1)ˣ) : ZMod m1) = (e x).1 := fun x => rfl
  have hψneg : ψ (-1) = -1 := Units.ext (by rw [hψ]; simp)
  have hbk : (b : ZMod (m1 * m2)) ^ k = -1 := by
    have := congrArg Units.val hb
    simpa using this
  have hfst : (e b).1 ^ k = -1 := by
    have : e ((b : ZMod (m1 * m2)) ^ k) = e (-1) := by rw [hbk]
    rw [map_pow, map_neg, map_one] at this
    exact congrArg Prod.fst this
  refine liar4_four_le_index_of_chain (K := (pmSubgroup m1 k).comap ψ) ?_ ?_ ?_
  · intro x hx
    rw [Subgroup.mem_comap, mem_pmSubgroup, ← map_pow]
    rcases mem_pmSubgroup.mp hx with hx | hx
    · left; rw [hx, map_one]
    · right; rw [hx, hψneg]
  · have hz : IsUnit (e.symm ((e b).1, 1)) := by
      rw [← isUnit_map_iff e, RingEquiv.apply_symm_apply, Prod.isUnit_iff]
      exact ⟨(b.isUnit.map e).map (RingHom.fst _ _), isUnit_one⟩
    intro hle
    have hzK : hz.unit ∈ (pmSubgroup m1 k).comap ψ := by
      rw [Subgroup.mem_comap, mem_pmSubgroup]
      right
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hψ, IsUnit.unit_spec, RingEquiv.apply_symm_apply,
        Units.val_neg, Units.val_one]
      exact hfst
    have hy : e ((hz.unit : ZMod (m1 * m2)) ^ k) = (-1, 1) := by
      rw [IsUnit.unit_spec, map_pow, RingEquiv.apply_symm_apply, Prod.pow_mk, one_pow, hfst]
    rcases mem_pmSubgroup.mp (hle hzK) with h | h
    · have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h'
      rw [h', map_one] at hy
      exact ZMod.neg_one_ne_one (congrArg Prod.fst hy).symm
    · have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h'
      rw [h', map_neg, map_one] at hy
      exact ZMod.neg_one_ne_one (congrArg Prod.snd hy)
  · have hy : IsUnit (e.symm ((u : ZMod m1), 1)) := by
      rw [← isUnit_map_iff e, RingEquiv.apply_symm_apply, Prod.isUnit_iff]
      exact ⟨u.isUnit, isUnit_one⟩
    intro htop
    have hmem : hy.unit ∈ (pmSubgroup m1 k).comap ψ := by rw [htop]; trivial
    rw [Subgroup.mem_comap, mem_pmSubgroup] at hmem
    have hψy : ψ hy.unit = u :=
      Units.ext (by rw [hψ, IsUnit.unit_spec, RingEquiv.apply_symm_apply])
    rw [hψy] at hmem
    exact hu hmem

/-- If `N > 2` is odd, coprime to `M`, `-1` is a `k`-th power mod `N`, every unit has
`u^k = ±1` and `u^M = 1`, then `N` is prime. -/
theorem liar4_prime_of_forall_pm {N k M : ℕ} (hN : 2 < N) (hodd : N % 2 = 1)
    (hcop : N.Coprime M) (x : (ZMod N)ˣ) (hx : x ^ k = -1)
    (hall : ∀ u : (ZMod N)ˣ, u ^ k = 1 ∨ u ^ k = -1) (hM : ∀ u : (ZMod N)ˣ, u ^ M = 1) :
    N.Prime := by
  by_contra hnp
  have hN0 : N ≠ 0 := by omega
  set p := N.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime (by omega)
  set a := N.factorization p with ha_def
  have hfac : p ^ a * (N / p ^ a) = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have ha : 1 ≤ a := hp.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N)
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    have hp2 : p = 2 := by omega
    have : 2 ∣ N := hp2 ▸ Nat.minFac_dvd N
    omega
  by_cases hm2 : N / p ^ a = 1
  · have hNpa : N = p ^ a := by rw [hm2, mul_one] at hfac; exact hfac.symm
    have ha2 : 2 ≤ a := by
      by_contra h
      have h1 : a = 1 := by omega
      rw [h1, pow_one] at hNpa
      exact hnp (hNpa ▸ hp)
    have hpM : ¬ p ∣ M := by
      intro h
      have h1 : p ∣ Nat.gcd N M := Nat.dvd_gcd (Nat.minFac_dvd N) h
      rw [Nat.Coprime.gcd_eq_one hcop] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    obtain ⟨y, hy⟩ := liar4_exists_pow_ne_one hNpa hp ha2 hpM
    exact hy (hM y)
  · have hm2pos : N / p ^ a ≠ 0 := by
      intro h; rw [h, mul_zero] at hfac; omega
    have hm2odd : (N / p ^ a) % 2 = 1 := by
      have : Odd N := Nat.odd_iff.mpr hodd
      rw [← hfac, Nat.odd_mul] at this
      exact Nat.odd_iff.mp this.2
    have hm1 : 2 < p ^ a := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    have hcop' : (p ^ a).Coprime (N / p ^ a) := (Nat.coprime_ordCompl hp hN0).pow_left a
    have hm2gt : 2 < N / p ^ a := by
      generalize N / p ^ a = m at hm2 hm2odd hm2pos ⊢
      omega
    obtain ⟨y, hy⟩ := exists_not_mem_pmSubgroup hfac.symm hcop' hm1 hm2gt k x hx
    exact hy (mem_pmSubgroup.mpr (hall y))

/-- **Index-4 form of Layer 3.** For odd composite `n > 2`, `n ≠ 9`, all strong liars lie in a
subgroup of `(ZMod n)ˣ` of index at least `4`. -/
theorem liar4_exists_subgroup {n : ℕ} (hn : 2 < n) (hodd : n % 2 = 1) (hnp : ¬ n.Prime)
    (h9 : n ≠ 9) :
    ∃ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index ∧ ∀ x, IsStrongLiar n x → x ∈ H := by
  classical
  have : NeZero n := ⟨by omega⟩
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
  have hcopn : n.Coprime (n - 1) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    apply Nat.dvd_one.mp
    have h1 := Nat.gcd_dvd_left n (n - 1)
    have h2 := Nat.gcd_dvd_right n (n - 1)
    exact (Nat.dvd_add_right h2).mp (by rwa [Nat.sub_add_cancel (by omega)])
  by_cases hm2 : n / p ^ k = 1
  · -- prime power case: the Fermat subgroup `{x | x^(n-1) = 1}`
    have hnpk : n = p ^ k := by rw [hm2, mul_one] at hfac; exact hfac.symm
    have hk2 : 2 ≤ k := by
      by_contra h
      have h1 : k = 1 := by omega
      rw [h1, pow_one] at hnpk
      exact hnp (hnpk ▸ hp)
    refine ⟨(powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker, ?_, ?_⟩
    · by_contra hidx
      have hH0 : (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker.index ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      have h6 : ∀ y : (ZMod n)ˣ, y ^ (6 * (n - 1)) = 1 := by
        intro y
        have hy := Subgroup.pow_index_mem (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker y
        have hdvd : (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker.index ∣ 6 := by
          obtain h | h | h : (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker.index = 1 ∨
              (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker.index = 2 ∨
              (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker.index = 3 := by omega
          all_goals rw [h]; decide
        obtain ⟨c, hc⟩ := hdvd
        have h6mem : y ^ 6 ∈ (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker := by
          rw [hc, pow_mul]; exact Subgroup.pow_mem _ hy c
        rw [MonoidHom.mem_ker, powMonoidHom_apply] at h6mem
        rw [pow_mul]; exact h6mem
      by_cases hp3' : p = 3
      · have hk3 : 3 ≤ k := by
          by_contra h
          have h2 : k = 2 := by omega
          rw [h2, hp3'] at hnpk
          exact h9 (by rw [hnpk]; norm_num)
        have hn27 : n = 27 * 3 ^ (k - 3) := by
          rw [hnpk, hp3', show (27 : ℕ) = 3 ^ 3 by norm_num, ← pow_add]
          congr 1; omega
        have ht : 3 ^ (k - 3) ≠ 0 := by positivity
        obtain ⟨y, hy⟩ := liar4_exists_pow_ne_one_three (M := 6 * (n - 1)) hn27 ht (by omega)
        exact hy (h6 y)
      · have hp6 : ¬ p ∣ 6 * (n - 1) := by
          intro h
          rcases hp.dvd_mul.mp h with h | h
          · rw [show (6 : ℕ) = 2 * 3 by norm_num] at h
            rcases hp.dvd_mul.mp h with h | h
            · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h; omega
            · exact hp3' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
          · have h1 : p ∣ Nat.gcd n (n - 1) := Nat.dvd_gcd (Nat.minFac_dvd n) h
            rw [Nat.Coprime.gcd_eq_one hcopn] at h1
            exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
        obtain ⟨y, hy⟩ := liar4_exists_pow_ne_one hnpk hp hk2 hp6
        exact hy (h6 y)
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
    have hoddn : Odd (p ^ k * (n / p ^ k)) := by rw [hfac]; exact Nat.odd_iff.mpr hodd
    rw [Nat.odd_mul] at hoddn
    have hm1odd : (p ^ k) % 2 = 1 := Nat.odd_iff.mp hoddn.1
    have hm2odd : (n / p ^ k) % 2 = 1 := Nat.odd_iff.mp hoddn.2
    have hm1 : 2 < p ^ k := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
    have hcop : (p ^ k).Coprime (n / p ^ k) := (Nat.coprime_ordCompl hp hn0).pow_left k
    have hm2gt : 2 < n / p ^ k := by
      generalize n / p ^ k = m at hm2 hm2odd hm2pos ⊢
      omega
    let P : ℕ → Prop := fun r => ∃ x : (ZMod n)ˣ, x ^ (d * 2 ^ r) = -1
    have hP0 : P 0 := ⟨-1, by
      rw [pow_zero, mul_one]; exact Odd.neg_one_pow (Nat.odd_iff.mpr hd1)⟩
    set j := Nat.findGreatest P (s - 1) with hj_def
    have hPj : P j := Nat.findGreatest_spec (Nat.zero_le _) hP0
    have hjs : j < s := by
      have := Nat.findGreatest_le (P := P) (s - 1); omega
    refine ⟨pmSubgroup n (d * 2 ^ j), ?_, ?_⟩
    · obtain ⟨b, hb⟩ := hPj
      by_contra hidx
      have hall1 := liar4_forall_pm_of_index_lt hfac.symm hcop hm1 hm2gt _ b hb hidx
      have hall2 := liar4_forall_pm_of_index_lt (hfac.symm.trans (mul_comm _ _)) hcop.symm
        hm2gt hm1 _ b hb hidx
      have hn1 : n - 1 = d * 2 ^ j * 2 ^ (s - j) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hjs.le, ← hsd]; ring
      have hpow : ∀ (N : ℕ) (u : (ZMod N)ˣ), (u ^ (d * 2 ^ j) = 1 ∨ u ^ (d * 2 ^ j) = -1) →
          u ^ (n - 1) = 1 := by
        intro N u hu
        rw [hn1, pow_mul]
        rcases hu with hu | hu
        · rw [hu, one_pow]
        · rw [hu]
          exact Even.neg_one_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have hmap : ∀ {N : ℕ} (h : N ∣ n), (ZMod.unitsMap h b) ^ (d * 2 ^ j) = -1 := by
        intro N h
        rw [← map_pow, hb]
        exact Units.ext (by simp [ZMod.unitsMap_def])
      have hdvd1 : p ^ k ∣ n := Dvd.intro _ hfac
      have hdvd2 : n / p ^ k ∣ n := Dvd.intro_left _ hfac
      have hP1 : (p ^ k).Prime :=
        liar4_prime_of_forall_pm hm1 hm1odd (Nat.Coprime.coprime_dvd_left hdvd1 hcopn)
          (ZMod.unitsMap hdvd1 b) (hmap hdvd1) hall1 (fun u => hpow _ u (hall1 u))
      have hP2 : (n / p ^ k).Prime :=
        liar4_prime_of_forall_pm hm2gt hm2odd (Nat.Coprime.coprime_dvd_left hdvd2 hcopn)
          (ZMod.unitsMap hdvd2 b) (hmap hdvd2) hall2 (fun u => hpow _ u (hall2 u))
      have hd1' := liar4_sub_one_dvd hP1 (fun u => hpow _ u (hall1 u))
      have hd2' := liar4_sub_one_dvd hP2 (fun u => hpow _ u (hall2 u))
      have hn' : n - 1 = p ^ k * (n / p ^ k) - 1 := by rw [hfac]
      rw [hn'] at hd1' hd2'
      have heq := liar4_two_prime_arith hm1 hm2gt hd1' hd2'
      rw [← heq, Nat.coprime_self] at hcop
      omega
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

/-- The Dirichlet characters mod `n` trivial on `H` are at least `[G : H]` in number. -/
theorem liar4_index_le_card_chars {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) :
    H.index ≤ Nat.card {χ : DirichletCharacter ℂ n //
      ∀ u : (ZMod n)ˣ, u ∈ H → χ (u : ZMod n) = 1} := by
  have hexp : NeZero (Monoid.exponent ((ZMod n)ˣ ⧸ H)) :=
    ⟨Monoid.exponent_ne_zero.mpr ⟨Nat.card ((ZMod n)ˣ ⧸ H), Nat.card_pos, fun g => pow_card_eq_one'⟩⟩
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ
  rw [Subgroup.index, ← hcard]
  let F : ((ZMod n)ˣ ⧸ H →* ℂˣ) → {χ : DirichletCharacter ℂ n //
      ∀ u : (ZMod n)ˣ, u ∈ H → χ (u : ZMod n) = 1} := fun φ =>
    ⟨MulChar.ofUnitHom (φ.comp (QuotientGroup.mk' H)), by
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

/-- **Character form.** For odd composite `n > 2`, `n ≠ 9`, the strong liars lie in a subgroup `H`
such that at least `4` Dirichlet characters mod `n` are trivial on `H`. -/
theorem liar4_exists_subgroup_char {n : ℕ} (hn : 2 < n) (hodd : n % 2 = 1) (hnp : ¬ n.Prime)
    (h9 : n ≠ 9) :
    ∃ H : Subgroup (ZMod n)ˣ, (∀ x, IsStrongLiar n x → x ∈ H) ∧
      4 ≤ Nat.card {χ : DirichletCharacter ℂ n //
        ∀ u : (ZMod n)ˣ, u ∈ H → χ (u : ZMod n) = 1} := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨H, h4, hH⟩ := liar4_exists_subgroup hn hodd hnp h9
  exact ⟨H, hH, h4.trans (liar4_index_le_card_chars H)⟩

end DetPrimality.Miller

#print axioms DetPrimality.Miller.liar4_exists_subgroup
#print axioms DetPrimality.Miller.liar4_exists_subgroup_char
