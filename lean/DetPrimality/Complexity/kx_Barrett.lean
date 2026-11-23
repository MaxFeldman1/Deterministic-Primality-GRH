import Mathlib
import DetPrimality.Complexity.cx_Bits
import DetPrimality.Complexity.kx_Karatsuba

/-!
# Barrett reduction on bit lists with Karatsuba products, with explicit bit cost

Cost model exactly as in `cx_Bits.lean` / `kx_Karatsuba.lean` (one unit = one constant-size bit
step; values are computed by Boolean operations on bit lists only).

* `kx_div m n` – schoolbook shift-subtract division (quotient and remainder); only used once per
  modulus, for the precomputation.
* `kx_mu n` – the Barrett constant `μ = ⌊4^b / n⌋`, `b = |n|`, by `kx_div` (cost
  `4 b² + 13 b + 6`, charged once by the caller).
* `kx_barrett mu x y n` – modular multiplication:
  `p = x·y` (Karatsuba), `q = ⌊p·μ / 4^b⌋` (Karatsuba, then dropping `2b` bits; kept to `b`
  bits), `t = q·n` (Karatsuba), `r = p - t`, one conditional subtraction of `n`, and a final
  comparison `r < n`.  The program is **safe for every `mu`**: if `p - t` borrows or the final
  comparison fails, it falls back to the shift-subtract remainder `cx_mod`, so the value is
  always `x·y mod n` (`kx_barrett_val`).  When `mu` is the Barrett constant of `n` and
  `x, y < n`, the fallbacks are never taken and the cost is at most `220 · 3^k` for `b ≤ 2^k`
  (`kx_barrett_cost`): two Karatsuba products of size `b`, one of size `2b`, and `O(b)`
  correction steps, all charged.
-/

namespace DetPrimality.Complexity

/-! ## Schoolbook division (for the precomputation) -/

/-- The bit list of `4 ^ |n|` (two zero cells per cell of `n`, then a one). -/
def kx_pow4 : List Bool → List Bool × ℕ
  | [] => ([true], 1)
  | _ :: n =>
    let r := kx_pow4 n
    (false :: false :: r.1, r.2 + 2)

theorem kx_pow4_spec (n : List Bool) :
    cx_val (kx_pow4 n).1 = 4 ^ n.length ∧ (kx_pow4 n).1.length = 2 * n.length + 1 ∧
    (kx_pow4 n).2 = 2 * n.length + 1 := by
  induction n with
  | nil => simp [kx_pow4]
  | cons b n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · simp only [kx_pow4, cx_val_cons, h1, List.length_cons, pow_succ, Bool.toNat_false]; ring
    · simp only [kx_pow4, List.length_cons, h2]; omega
    · simp only [kx_pow4, List.length_cons, h3]; omega

/-- Shift-subtract division, most significant bit of the dividend first:
`((quotient, remainder), cost)`; the remainder has width `|n|`, the quotient width `|m|`. -/
def kx_div : List Bool → List Bool → (List Bool × List Bool) × ℕ
  | [], n =>
    let t := cx_trunc n []
    (([], t.1), t.2)
  | a :: m, n =>
    let r := kx_div m n
    let d := cx_sub (a :: r.1.2) n false
    let t := cx_trunc n (if d.1.2 then a :: r.1.2 else d.1.1)
    (((!d.1.2) :: r.1.1, t.1), r.2 + d.2 + t.2 + 1)

theorem kx_div_rem_length (m n : List Bool) : (kx_div m n).1.2.length = n.length := by
  cases m <;> simp [kx_div, cx_trunc_length]

theorem kx_div_cost (m n : List Bool) :
    (kx_div m n).2 = (n.length + 1) + m.length * (2 * n.length + 4) := by
  induction m with
  | nil => simp [kx_div, cx_trunc_cost]
  | cons a m ih =>
    simp only [kx_div, cx_trunc_cost, (cx_sub_spec _ _ _).2.2, List.length_cons,
      kx_div_rem_length, ih]
    have : max (n.length + 1) n.length = n.length + 1 := by omega
    rw [this]; ring

theorem kx_div_spec (m n : List Bool) (hn : 0 < cx_val n) :
    cx_val m = cx_val (kx_div m n).1.1 * cx_val n + cx_val (kx_div m n).1.2 ∧
    cx_val (kx_div m n).1.2 < cx_val n := by
  induction m with
  | nil =>
    refine ⟨by simp [kx_div, cx_trunc_val n [] (by simp)], ?_⟩
    simpa [kx_div, cx_trunc_val n [] (by simp)] using hn
  | cons a m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hnlt := cx_val_lt n
    have hb := Bool.toNat_lt a
    obtain ⟨hs1, hs2, -⟩ := cx_sub_spec (a :: (kx_div m n).1.2) n false
    have hdlt := cx_val_lt (cx_sub (a :: (kx_div m n).1.2) n false).1.1
    have hL : max (n.length + 1) n.length = n.length + 1 := by omega
    rw [hs2, List.length_cons, kx_div_rem_length, hL, pow_succ] at hdlt
    rw [hs2, List.length_cons, kx_div_rem_length, hL, cx_val_cons, pow_succ] at hs1
    simp only [Bool.toNat_false, add_zero] at hs1
    simp only [kx_div, cx_val_cons]
    cases hbr : (cx_sub (a :: (kx_div m n).1.2) n false).1.2 with
    | true =>
      rw [hbr] at hs1
      simp only [Bool.toNat_true, mul_one] at hs1
      simp only [if_true, Bool.not_true, Bool.toNat_false, zero_add]
      rw [cx_trunc_val _ _ (by rw [cx_val_cons]; omega), cx_val_cons]
      refine ⟨by rw [ih1]; ring, by omega⟩
    | false =>
      rw [hbr] at hs1
      simp only [Bool.toNat_false, mul_zero, add_zero] at hs1
      simp only [Bool.false_eq_true, if_false, Bool.not_false, Bool.toNat_true]
      rw [cx_trunc_val _ _ (by omega)]
      refine ⟨by rw [ih1]; linarith, by omega⟩

/-- `mu` is the Barrett constant `⌊4^|n| / n⌋` of `n`. -/
def kx_IsMu (n mu : List Bool) : Prop :=
  cx_val mu * cx_val n ≤ 4 ^ n.length ∧ 4 ^ n.length < (cx_val mu + 1) * cx_val n

/-- Precomputation of the Barrett constant `⌊4^|n| / n⌋` by schoolbook division. -/
def kx_mu (n : List Bool) : List Bool × ℕ :=
  let d := kx_pow4 n
  let q := kx_div d.1 n
  (q.1.1, d.2 + q.2)

theorem kx_mu_isMu (n : List Bool) (hn : 0 < cx_val n) : kx_IsMu n (kx_mu n).1 := by
  obtain ⟨h1, h2⟩ := kx_div_spec (kx_pow4 n).1 n hn
  rw [(kx_pow4_spec n).1] at h1
  simp only [kx_IsMu, kx_mu]
  constructor
  · omega
  · rw [h1, Nat.add_mul, one_mul]; omega

theorem kx_mu_cost (n : List Bool) : (kx_mu n).2 = 4 * n.length ^ 2 + 13 * n.length + 6 := by
  simp only [kx_mu, kx_div_cost, (kx_pow4_spec n).2.1, (kx_pow4_spec n).2.2]
  ring

/-! ## Comparison facts about `cx_sub` -/

theorem kx_sub_cases (x y : List Bool) :
    ((cx_sub x y false).1.2 = true → cx_val x < cx_val y) ∧
    ((cx_sub x y false).1.2 = false → cx_val x = cx_val y + cx_val (cx_sub x y false).1.1) := by
  obtain ⟨h1, h2, -⟩ := cx_sub_spec x y false
  have hd := cx_val_lt (cx_sub x y false).1.1
  rw [h2] at h1 hd
  have hx : cx_val x < 2 ^ max x.length y.length :=
    lt_of_lt_of_le (cx_val_lt x) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  generalize 2 ^ max x.length y.length = P at *
  simp only [Bool.toNat_false, add_zero] at h1
  constructor
  · intro hb
    rw [hb] at h1
    simp only [Bool.toNat_true, mul_one] at h1
    omega
  · intro hb
    rw [hb] at h1
    simp only [Bool.toNat_false, mul_zero, add_zero] at h1
    omega

/-- Conditional subtraction: `d - n` if `d ≥ n`, else `d`. -/
def kx_csub (d n : List Bool) : List Bool × ℕ :=
  let e := cx_sub d n false
  (if e.1.2 then d else e.1.1, e.2)

theorem kx_csub_spec (d n : List Bool) :
    (kx_csub d n).2 = max d.length n.length + 1 ∧
    (n.length ≤ d.length → (kx_csub d n).1.length = d.length) ∧
    (∃ c, cx_val d = c * cx_val n + cx_val (kx_csub d n).1) ∧
    (cx_val d < 2 * cx_val n → cx_val (kx_csub d n).1 < cx_val n) := by
  obtain ⟨c1, c2⟩ := kx_sub_cases d n
  obtain ⟨-, l2, l3⟩ := cx_sub_spec d n false
  simp only [kx_csub]
  refine ⟨l3, ?_, ?_, ?_⟩
  · intro h
    split_ifs
    · rfl
    · rw [l2]; omega
  · cases hb : (cx_sub d n false).1.2 with
    | true => exact ⟨0, by simp⟩
    | false => exact ⟨1, by simp only [Bool.false_eq_true, if_false]; have := c2 hb; omega⟩
  · intro h
    cases hb : (cx_sub d n false).1.2 with
    | true => simpa using c1 hb
    | false => simp only [Bool.false_eq_true, if_false]; have := c2 hb; omega

/-! ## Barrett reduction -/

/-- Quotient estimate: `p = x·y`, `q = ⌊p·μ / 2^|p|⌋` kept to `|n|` bits, `t = q·n`.
Returns `((p, t), cost)`. -/
def kx_bq (mu x y n : List Bool) : (List Bool × List Bool) × ℕ :=
  let p := kx_kar x y
  let mu' := cx_trunc p.1 mu
  let w := kx_kar p.1 mu'.1
  let dq := kx_drop p.1 w.1
  let q := cx_trunc n dq.1
  let t := kx_kar q.1 n
  ((p.1, t.1), p.2 + mu'.2 + w.2 + dq.2 + q.2 + t.2)

/-- Final correction: `r = p - t`, one conditional subtraction, check `r < n`; fallbacks to
`cx_mod` keep the value correct for arbitrary `t`. -/
def kx_bfin (p t n : List Bool) : List Bool × ℕ :=
  let d := cx_sub p t false
  if d.1.2 then
    let r := cx_mod p n
    (r.1, d.2 + r.2 + 1)
  else
    let r := kx_csub d.1.1 n
    let g := cx_sub r.1 n false
    if g.1.2 then
      let f := cx_trunc n r.1
      (f.1, d.2 + r.2 + g.2 + f.2 + 1)
    else
      let f := cx_mod r.1 n
      (f.1, d.2 + r.2 + g.2 + f.2 + 1)

/-- **Barrett modular multiplication** with Karatsuba products. -/
def kx_barrett (mu x y n : List Bool) : List Bool × ℕ :=
  let a := kx_bq mu x y n
  let f := kx_bfin a.1.1 a.1.2 n
  (f.1, a.2 + f.2)

theorem kx_bfin_length (p t n : List Bool) : (kx_bfin p t n).1.length = n.length := by
  simp only [kx_bfin]
  split_ifs <;> simp only [cx_mod_length, cx_trunc_length]

theorem kx_bfin_val (p t n : List Bool) (hn : 0 < cx_val n) (ht : ∃ c, cx_val t = c * cx_val n) :
    cx_val (kx_bfin p t n).1 = cx_val p % cx_val n := by
  obtain ⟨c, hc⟩ := ht
  obtain ⟨-, d2⟩ := kx_sub_cases p t
  obtain ⟨-, -, ⟨c', hc'⟩, -⟩ := kx_csub_spec (cx_sub p t false).1.1 n
  obtain ⟨g1, -⟩ := kx_sub_cases (kx_csub (cx_sub p t false).1.1 n).1 n
  simp only [kx_bfin]
  split_ifs with h1 h2
  · exact cx_mod_val p n hn
  · have h1' : (cx_sub p t false).1.2 = false := by simpa using h1
    have e := d2 h1'
    have hr := g1 h2
    have hp : cx_val p = cx_val (kx_csub (cx_sub p t false).1.1 n).1 + (c + c') * cx_val n := by
      rw [e, hc, hc']; ring
    dsimp only
    rw [cx_trunc_val _ _ (lt_trans hr (cx_val_lt n)), hp, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hr]
  · have h1' : (cx_sub p t false).1.2 = false := by simpa using h1
    have e := d2 h1'
    have hp : cx_val p = cx_val (kx_csub (cx_sub p t false).1.1 n).1 + (c + c') * cx_val n := by
      rw [e, hc, hc']; ring
    dsimp only
    rw [cx_mod_val _ _ hn, hp, Nat.add_mul_mod_self_right]

/-- Cost of the correction when the quotient estimate is good (no fallback). -/
theorem kx_bfin_cost_fast (p t n : List Bool) (hl : t.length = p.length)
    (hnl : n.length ≤ p.length) (h1 : cx_val t ≤ cx_val p)
    (h2 : cx_val p < cx_val t + 2 * cx_val n) :
    (kx_bfin p t n).2 = 3 * (p.length + 1) + (n.length + 1) + 1 := by
  obtain ⟨d1, d2⟩ := kx_sub_cases p t
  obtain ⟨-, dl, dc⟩ := cx_sub_spec p t false
  have hd : (cx_sub p t false).1.2 = false := by
    cases h : (cx_sub p t false).1.2 with
    | false => rfl
    | true => have := d1 h; omega
  have e := d2 hd
  rw [hl, max_self] at dl dc
  obtain ⟨rc, rl, -, rv⟩ := kx_csub_spec (cx_sub p t false).1.1 n
  have rl' := rl (by omega)
  have rv' := rv (by omega)
  obtain ⟨-, g2⟩ := kx_sub_cases (kx_csub (cx_sub p t false).1.1 n).1 n
  obtain ⟨-, -, gc⟩ := cx_sub_spec (kx_csub (cx_sub p t false).1.1 n).1 n false
  have hg : (cx_sub (kx_csub (cx_sub p t false).1.1 n).1 n false).1.2 = true := by
    cases h : (cx_sub (kx_csub (cx_sub p t false).1.1 n).1 n false).1.2 with
    | true => rfl
    | false => have := g2 h; omega
  simp only [kx_bfin, hd, hg, Bool.false_eq_true, if_false, if_true, cx_trunc_cost]
  rw [dc, rc, gc, rl', dl]
  omega

/-- Cost of the correction in general (including the fallbacks). -/
theorem kx_bfin_cost_weak (p t n : List Bool) (hl : t.length = p.length)
    (hnl : n.length ≤ p.length) :
    (kx_bfin p t n).2
      ≤ 3 * (p.length + 1) + (n.length + 1) + 1 + p.length * (2 * n.length + 4) := by
  obtain ⟨-, dl, dc⟩ := cx_sub_spec p t false
  rw [hl, max_self] at dl dc
  obtain ⟨rc, rl, -, -⟩ := kx_csub_spec (cx_sub p t false).1.1 n
  have rl' := rl (by omega)
  obtain ⟨-, -, gc⟩ := cx_sub_spec (kx_csub (cx_sub p t false).1.1 n).1 n false
  simp only [kx_bfin]
  split_ifs
  · dsimp only
    rw [dc, cx_mod_cost]; omega
  · dsimp only
    rw [dc, rc, gc, rl', dl, cx_trunc_cost]; omega
  · dsimp only
    rw [dc, rc, gc, cx_mod_cost, rl', dl]; omega

theorem kx_bq_spec (mu x y n : List Bool) :
    cx_val (kx_bq mu x y n).1.1 = cx_val x * cx_val y ∧
    (kx_bq mu x y n).1.1.length = x.length + y.length ∧
    (kx_bq mu x y n).1.2.length = n.length + n.length ∧
    ∃ c, cx_val (kx_bq mu x y n).1.2 = c * cx_val n := by
  simp only [kx_bq]
  refine ⟨kx_kar_val x y, kx_kar_length x y, ?_, ⟨_, kx_kar_val _ _⟩⟩
  rw [kx_kar_length, cx_trunc_length]

theorem kx_barrett_length (mu x y n : List Bool) : (kx_barrett mu x y n).1.length = n.length := by
  simp only [kx_barrett, kx_bfin_length]

/-- **Barrett multiplication is correct for every `mu`** (thanks to the fallbacks). -/
theorem kx_barrett_val (mu x y n : List Bool) (hn : 0 < cx_val n) :
    cx_val (kx_barrett mu x y n).1 = cx_val x * cx_val y % cx_val n := by
  obtain ⟨h1, -, -, h4⟩ := kx_bq_spec mu x y n
  simp only [kx_barrett]
  rw [kx_bfin_val _ _ _ hn h4, h1]

/-- Cost of the quotient estimate: two Karatsuba products of size `b`, one of size `2b`. -/
theorem kx_bq_cost (k : ℕ) (mu x y n : List Bool) (hx : x.length = n.length)
    (hy : y.length = n.length) (hk : n.length ≤ 2 ^ k) :
    (kx_bq mu x y n).2 + 92 * 2 ^ k + 27 ≤ 220 * 3 ^ k + 5 * n.length := by
  have hpow2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hpow3 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
  have c1 := kx_kar_cost k x y (by omega) (by omega)
  have l1 := kx_kar_length x y
  simp only [kx_bq]
  generalize kx_kar x y = p at *
  have c2 := cx_trunc_cost p.1 mu
  have l2 := cx_trunc_length p.1 mu
  generalize cx_trunc p.1 mu = mu' at *
  have c3 := kx_kar_cost (k + 1) p.1 mu'.1 (by omega) (by omega)
  rw [hpow2, hpow3] at c3
  generalize kx_kar p.1 mu'.1 = w at *
  have c4 := kx_drop_cost p.1 w.1
  generalize kx_drop p.1 w.1 = dq at *
  have c5 := cx_trunc_cost n dq.1
  have l5 := cx_trunc_length n dq.1
  generalize cx_trunc n dq.1 = q at *
  have c6 := kx_kar_cost k q.1 n l5 (by omega)
  omega

theorem kx_barrett_arith (N μ P B : ℕ) (hN : 0 < N) (h1 : μ * N ≤ B) (h2 : B < (μ + 1) * N)
    (hP : P < B) : P * μ / B * N ≤ P ∧ P < (P * μ / B + 2) * N := by
  have hB : 0 < B := by omega
  have hq1 : P * μ / B * B ≤ P * μ := Nat.div_mul_le_self _ _
  have hq2 : P * μ < (P * μ / B + 1) * B := by
    linarith [Nat.div_add_mod (P * μ) B, Nat.mod_lt (P * μ) hB]
  generalize P * μ / B = q at *
  constructor
  · have : q * N * B ≤ P * B := by
      calc q * N * B = q * B * N := by ring
        _ ≤ P * μ * N := Nat.mul_le_mul_right _ hq1
        _ = P * (μ * N) := by ring
        _ ≤ P * B := Nat.mul_le_mul_left _ h1
    exact Nat.le_of_mul_le_mul_right this hB
  · by_contra hcon
    rw [not_lt] at hcon
    have hP0 : 0 < P := by nlinarith
    have f1 : (q + 2) * N * B ≤ P * B := Nat.mul_le_mul_right _ hcon
    have f2 : P * B < P * ((μ + 1) * N) := Nat.mul_lt_mul_of_pos_left h2 hP0
    have f3 : P * μ * N < (q + 1) * B * N := Nat.mul_lt_mul_of_pos_right hq2 hN
    have f4 : P * N < B * N := Nat.mul_lt_mul_of_pos_right hP hN
    nlinarith

/-- With the true Barrett constant and reduced operands the quotient estimate is good:
`t ≤ p < t + 2 n`. -/
theorem kx_bq_fast (mu x y n : List Bool) (hx : x.length = n.length) (hy : y.length = n.length)
    (hxv : cx_val x < cx_val n) (hyv : cx_val y < cx_val n) (hmu : kx_IsMu n mu) :
    cx_val (kx_bq mu x y n).1.2 ≤ cx_val (kx_bq mu x y n).1.1 ∧
    cx_val (kx_bq mu x y n).1.1 < cx_val (kx_bq mu x y n).1.2 + 2 * cx_val n := by
  obtain ⟨m1, m2⟩ := hmu
  have hnlt := cx_val_lt n
  have h4 : (4 : ℕ) ^ n.length = 2 ^ n.length * 2 ^ n.length := by
    rw [← mul_pow]; norm_num
  have h4' : (2 : ℕ) ^ (n.length + n.length) = 4 ^ n.length := by
    rw [h4, pow_add]
  have hPlt : cx_val x * cx_val y < cx_val n * cx_val n :=
    Nat.mul_lt_mul'' hxv hyv
  have hNN : cx_val n * cx_val n < 4 ^ n.length := by
    rw [h4]; exact Nat.mul_lt_mul'' hnlt hnlt
  have hpv := kx_kar_val x y
  have hpl := kx_kar_length x y
  rw [hx, hy] at hpl
  simp only [kx_bq, kx_kar_val]
  generalize kx_kar x y = p at *
  have hmv := cx_trunc_val p.1 mu
  rw [hpl, h4'] at hmv
  generalize cx_trunc p.1 mu = mu' at *
  have hdv := kx_drop_val p.1 (kx_kar p.1 mu'.1).1
  rw [kx_kar_val, hpl, h4', hpv] at hdv
  generalize kx_drop p.1 (kx_kar p.1 mu'.1).1 = dq at *
  have hqv := cx_trunc_val n dq.1
  generalize cx_trunc n dq.1 = q at *
  by_cases hP0 : cx_val x * cx_val y = 0
  · rw [hP0, Nat.zero_mul, Nat.zero_div] at hdv
    rw [hqv (by rw [hdv]; exact Nat.pos_of_ne_zero (by positivity)), hdv, hP0]
    omega
  · have hx1 : 1 ≤ cx_val x := by
      rcases Nat.eq_zero_or_pos (cx_val x) with h | h
      · rw [h] at hP0; simp at hP0
      · exact h
    have hmulN : cx_val mu * 2 ≤ cx_val mu * cx_val n := Nat.mul_le_mul_left _ (by omega)
    have hmu4 : cx_val mu < 4 ^ n.length := by omega
    rw [hmv hmu4] at hdv
    obtain ⟨a1, a2⟩ := kx_barrett_arith (cx_val n) (cx_val mu) (cx_val x * cx_val y)
      (4 ^ n.length) (by omega) m1 m2 (by omega)
    rw [← hdv] at a1 a2
    have hqN : cx_val dq.1 < cx_val n := by
      by_contra hcon
      rw [not_lt] at hcon
      have := Nat.mul_le_mul_right (cx_val n) hcon
      omega
    rw [hqv (by omega)]
    constructor
    · exact a1
    · rw [Nat.add_mul] at a2; omega

/-- **Barrett cost (good case).** If `mu` is the Barrett constant of the `b`-bit modulus `n`,
`x, y < n` are `b`-bit operands and `b ≤ 2^k`, the whole modular multiplication costs at most
`220 · 3^k` bit steps. -/
theorem kx_barrett_cost (k : ℕ) (mu x y n : List Bool) (hx : x.length = n.length)
    (hy : y.length = n.length) (hxv : cx_val x < cx_val n) (hyv : cx_val y < cx_val n)
    (hmu : kx_IsMu n mu) (hk : n.length ≤ 2 ^ k) :
    (kx_barrett mu x y n).2 ≤ 220 * 3 ^ k := by
  obtain ⟨f1, f2⟩ := kx_bq_fast mu x y n hx hy hxv hyv hmu
  obtain ⟨-, l1, l2, -⟩ := kx_bq_spec mu x y n
  have c := kx_bq_cost k mu x y n hx hy hk
  simp only [kx_barrett]
  rw [kx_bfin_cost_fast _ _ _ (by omega) (by omega) f1 f2, l1]
  omega

/-- Barrett cost without any assumption on `mu` (fallbacks included): quadratic. -/
theorem kx_barrett_cost_weak (k : ℕ) (mu x y n : List Bool) (hx : x.length = n.length)
    (hy : y.length = n.length) (hk : n.length ≤ 2 ^ k) :
    (kx_barrett mu x y n).2 ≤ 220 * 3 ^ k + 4 * n.length ^ 2 + 8 * n.length := by
  obtain ⟨-, l1, l2, -⟩ := kx_bq_spec mu x y n
  have c := kx_bq_cost k mu x y n hx hy hk
  have w := kx_bfin_cost_weak (kx_bq mu x y n).1.1 (kx_bq mu x y n).1.2 n (by omega) (by omega)
  rw [l1, hx, hy] at w
  have e : (n.length + n.length) * (2 * n.length + 4) = 4 * n.length ^ 2 + 8 * n.length := by
    ring
  rw [e] at w
  simp only [kx_barrett]
  omega

end DetPrimality.Complexity

#print axioms DetPrimality.Complexity.kx_barrett_val
#print axioms DetPrimality.Complexity.kx_barrett_cost
#print axioms DetPrimality.Complexity.kx_mu_isMu
