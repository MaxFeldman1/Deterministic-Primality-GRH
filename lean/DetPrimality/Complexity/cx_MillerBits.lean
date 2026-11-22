import Mathlib
import DetPrimality.Complexity.cx_Fast
import DetPrimality.Complexity.cx_Bits

/-!
# Running time of the deterministic Miller test, Tier 2: bit operations

The whole test is re-implemented on little-endian bit lists (`List Bool`), parametrised by an
abstract modular multiplier `mm : cx_ModMul` with cost function `mm.M`, and every step is charged.

## Cost model

* **Bit steps.** As in `cx_Bits.lean`: each iteration of a primitive bit loop (`cx_add`, `cx_sub`,
  `cx_trunc`, `cx_eq`, `cx_inc`, `cx_decompB`) reads O(1) bits, writes at most one bit, and costs
  `1`.
* **Modular multiplications.** A call `mm.run x y n` is charged the cost it reports, which by
  the interface is at most `mm.M n.length` on normalised operands (`x.length = y.length =
  n.length`, values `< n`).  `cx_schoolbook` instantiates this with schoolbook multiplication
  followed by shift-subtract remainder, `M b = 9 b² + 16 b + 2` (all bit steps counted).
* **Control.** Every iteration of every outer loop (the exponent-bit loop of `cx_powB`, the
  squaring loop `cx_sqLoopB`, the base loop `cx_loopB`) and every branch of the top-level
  function is charged an additional `1` for its O(1) control decisions (inspecting an exponent
  bit, testing a Boolean flag, decrementing a unary counter).
* **Overhead that is charged:** building the width-`b` constants `1` and `2` (`cx_trunc`),
  `n - 1` (clearing the low bit of the odd `n`, charged inside the top-level `+1`), the
  decomposition `n - 1 = 2^s d` by stripping low zero bits (`cx_decompB`), the comparison
  `a < n` (`cx_sub`) and the increment `a ← a + 1` (`cx_inc`) for every base, the comparison with
  `1` after the exponentiation and with `n - 1` before every squaring (`cx_eq`).
* **Assumed / not charged:**
  1. the input is given as its normalised binary expansion `cx_bits n`
     (length `Nat.log2 n + 1` for `n ≠ 0`);
  2. loop counters (`s ≤ b`, and the base budget) are *unary* naturals; decrement/zero-test is
     part of the `1` charged per loop iteration;
  3. the base budget `millerBound 1 n - 2 = ⌈0.480454 · b²⌉ - 2`, a function of the bit length
     `b = Nat.log2 n + 1` only, is supplied to the bit-level program as a unary counter; the
     arithmetic computing it from `b` (on numbers of `O(log b)` bits) is **not** charged.
     The cut-off `a < n` of `min (millerBound 1 n) n` *is* performed and charged at bit level.

## Main results

* `cx_millerDetB_fst : (cx_millerDetB mm (millerBound 1 n - 2) (cx_bits n)).1 = cx_millerDetFast n`
* `cx_millerDetB_cost : (cx_millerDetB mm (millerBound 1 n - 2) (cx_bits n)).2
    ≤ L ^ 3 * mm.M L + 4 * L ^ 4` with `L = Nat.log2 n + 1`, for every `n` and every multiplier;
* `cx_millerDetBits_cost : (cx_millerDetBits n).2 ≤ 31 * (Nat.log2 n + 1) ^ 5` (schoolbook).
-/

namespace DetPrimality.Complexity

open DetPrimality DetPrimality.Miller

/-- A modular multiplier on bit lists together with a cost bound `M` (as a function of the bit
width).  It is only required to work on normalised operands: `x`, `y` of the same width as the
modulus `n`, and with values `< n`. -/
structure cx_ModMul where
  /-- `run x y n = (x * y mod n, cost)`. -/
  run : List Bool → List Bool → List Bool → List Bool × ℕ
  /-- Cost bound in terms of the bit width of the modulus. -/
  M : ℕ → ℕ
  run_val : ∀ x y n, x.length = n.length → y.length = n.length →
    cx_val x < cx_val n → cx_val y < cx_val n →
    cx_val (run x y n).1 = cx_val x * cx_val y % cx_val n
  run_length : ∀ x y n, x.length = n.length → y.length = n.length →
    cx_val x < cx_val n → cx_val y < cx_val n → (run x y n).1.length = n.length
  run_cost : ∀ x y n, x.length = n.length → y.length = n.length →
    cx_val x < cx_val n → cx_val y < cx_val n → (run x y n).2 ≤ M n.length

/-- Schoolbook multiplication followed by shift-subtract remainder: `M b = 9 b² + 16 b + 2`. -/
def cx_schoolbook : cx_ModMul where
  run := cx_mulmod
  M := fun b => 9 * b ^ 2 + 16 * b + 2
  run_val := fun x y n _ _ hx _ => cx_mulmod_val x y n (by omega)
  run_length := fun x y n _ _ _ _ => cx_mulmod_length x y n
  run_cost := fun x y n hx hy _ _ => cx_mulmod_cost x y n hx hy

/-! ## Modular exponentiation on bit lists -/

/-- Square-and-multiply; the exponent is a little-endian bit list, so the recursion mirrors
`Miller.powMod` (`e / 2` = tail, `e % 2` = head). -/
def cx_powB (mm : cx_ModMul) (n one a : List Bool) : List Bool → List Bool × ℕ
  | [] => (one, 1)
  | b :: e =>
    let r := cx_powB mm n one a e
    let q := mm.run r.1 r.1 n
    if b then
      let t := mm.run q.1 a n
      (t.1, r.2 + q.2 + t.2 + 1)
    else (q.1, r.2 + q.2 + 1)

theorem cx_powB_spec (mm : cx_ModMul) (n one a : List Bool) (hn1 : 1 < cx_val n)
    (hone : one.length = n.length) (honev : cx_val one = 1)
    (ha : a.length = n.length) (hav : cx_val a < cx_val n) (e : List Bool) :
    cx_val (cx_powB mm n one a e).1 = cx_val a ^ cx_val e % cx_val n ∧
    (cx_powB mm n one a e).1.length = n.length ∧
    (cx_powB mm n one a e).2 ≤ 1 + e.length * (2 * mm.M n.length + 1) := by
  induction e with
  | nil =>
    refine ⟨?_, hone, ?_⟩
    · simp [cx_powB, honev, Nat.mod_eq_of_lt hn1]
    · simp [cx_powB]
  | cons b e ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hr : cx_val (cx_powB mm n one a e).1 < cx_val n := by
      rw [h1]; exact Nat.mod_lt _ (by omega)
    have hq1 := mm.run_val _ _ n h2 h2 hr hr
    have hq2 := mm.run_length _ _ n h2 h2 hr hr
    have hq3 := mm.run_cost _ _ n h2 h2 hr hr
    have hqv : cx_val (mm.run (cx_powB mm n one a e).1 (cx_powB mm n one a e).1 n).1
        < cx_val n := by
      rw [hq1]; exact Nat.mod_lt _ (by omega)
    cases b with
    | false =>
      simp only [cx_powB, Bool.false_eq_true, if_false]
      refine ⟨?_, hq2, ?_⟩
      · rw [hq1, h1, ← Nat.mul_mod, ← pow_add, cx_val_cons, Bool.toNat_false, zero_add, two_mul]
      · rw [List.length_cons, Nat.add_mul, one_mul]; omega
    | true =>
      have ht1 := mm.run_val _ _ n hq2 ha hqv hav
      have ht2 := mm.run_length _ _ n hq2 ha hqv hav
      have ht3 := mm.run_cost _ _ n hq2 ha hqv hav
      simp only [cx_powB, eq_self, if_true]
      refine ⟨?_, ht2, ?_⟩
      · rw [ht1, hq1, h1, ← Nat.mul_mod, Nat.mod_mul_mod, ← pow_add, ← pow_succ]
        congr 2
        simp only [cx_val_cons, Bool.toNat_true]
        omega
      · rw [List.length_cons, Nat.add_mul, one_mul]; omega

/-! ## The squaring loop -/

/-- Bit-level `cx_sqLoop`: compare with `n - 1`, then square; at most `k - 1` squarings. -/
def cx_sqLoopB (mm : cx_ModMul) (n nm1 : List Bool) : ℕ → List Bool → Bool × ℕ
  | 0, _ => (false, 1)
  | k + 1, x =>
    let c := cx_eq x nm1
    if c.1 then (true, c.2 + 1)
    else if k = 0 then (false, c.2 + 1)
    else
      let q := mm.run x x n
      let r := cx_sqLoopB mm n nm1 k q.1
      (r.1, c.2 + q.2 + r.2 + 1)

theorem cx_sqLoopB_spec (mm : cx_ModMul) (n nm1 : List Bool) (hn1 : 1 < cx_val n)
    (hnm1 : nm1.length = n.length) (hnm1v : cx_val nm1 = cx_val n - 1)
    (k : ℕ) (x : List Bool) (hx : x.length = n.length) (hxv : cx_val x < cx_val n) :
    (cx_sqLoopB mm n nm1 k x).1 = cx_sqLoop (cx_val n) k (cx_val x) ∧
    (cx_sqLoopB mm n nm1 k x).2 ≤ 1 + k * (mm.M n.length + n.length + 2) := by
  induction k generalizing x with
  | zero => simp [cx_sqLoopB, cx_sqLoop]
  | succ k ih =>
    have hiff : (cx_eq x nm1).1 = true ↔ cx_val x = cx_val n - 1 := by
      rw [cx_eq_iff x nm1 (by omega), hnm1v]
    have hcc := cx_eq_cost x nm1
    simp only [cx_sqLoopB, cx_sqLoop]
    by_cases h : (cx_eq x nm1).1 = true
    · rw [if_pos h, if_pos (hiff.mp h)]
      refine ⟨rfl, ?_⟩
      dsimp only
      rw [Nat.add_mul, one_mul]; omega
    · rw [if_neg h, if_neg (fun e => h (hiff.mpr e))]
      by_cases hk : k = 0
      · rw [if_pos hk, if_pos hk]
        refine ⟨rfl, ?_⟩
        dsimp only
        rw [Nat.add_mul, one_mul]; omega
      · rw [if_neg hk, if_neg hk]
        have hq1 := mm.run_val x x n hx hx hxv hxv
        have hq2 := mm.run_length x x n hx hx hxv hxv
        have hq3 := mm.run_cost x x n hx hx hxv hxv
        obtain ⟨i1, i2⟩ := ih (mm.run x x n).1 hq2 (by rw [hq1]; exact Nat.mod_lt _ (by omega))
        rw [hq1] at i1
        refine ⟨i1, ?_⟩
        dsimp only
        rw [Nat.add_mul, one_mul]; omega

/-! ## Decomposition `m = 2^s d` by stripping low zero bits -/

/-- Returns `((s, bits of d), cost)`; `s` is a unary counter. -/
def cx_decompB : List Bool → (ℕ × List Bool) × ℕ
  | [] => ((0, []), 1)
  | true :: l => ((0, true :: l), 1)
  | false :: l =>
    let r := cx_decompB l
    ((r.1.1 + 1, r.1.2), r.2 + 1)

theorem cx_oddDecomp_even {m : ℕ} (h0 : m ≠ 0) :
    oddDecomp (2 * m) = ((oddDecomp m).1 + 1, (oddDecomp m).2) := by
  rw [oddDecomp, dif_pos (by omega)]
  simp

theorem cx_oddDecomp_odd (m : ℕ) : oddDecomp (1 + 2 * m) = (0, 1 + 2 * m) := by
  rw [oddDecomp, dif_neg (by omega)]

theorem cx_decompB_spec (m : List Bool) (h : cx_val m ≠ 0) :
    (cx_decompB m).1.1 = (oddDecomp (cx_val m)).1 ∧
    cx_val (cx_decompB m).1.2 = (oddDecomp (cx_val m)).2 := by
  induction m with
  | nil => simp at h
  | cons b l ih =>
    cases b with
    | true => simp [cx_decompB, cx_oddDecomp_odd]
    | false =>
      have hV : cx_val l ≠ 0 := by simpa using h
      obtain ⟨i1, i2⟩ := ih hV
      simp [cx_decompB, cx_oddDecomp_even hV, i1, i2]

theorem cx_decompB_len (m : List Bool) :
    (cx_decompB m).1.1 + (cx_decompB m).1.2.length = m.length ∧
    (cx_decompB m).2 ≤ m.length + 1 := by
  induction m with
  | nil => simp [cx_decompB]
  | cons b l ih =>
    cases b with
    | true => simp [cx_decompB]
    | false =>
      obtain ⟨i1, i2⟩ := ih
      simp only [cx_decompB, List.length_cons]
      omega

/-! ## Strong probable prime test on bit lists -/

/-- Bit-level `cx_sprpFast`: `n` modulus, `one` the width-`b` constant 1, `nm1 = n - 1`,
`d` the odd part of `n - 1` and `s` its 2-adic valuation (unary). -/
def cx_sprpB (mm : cx_ModMul) (n one nm1 d : List Bool) (s : ℕ) (a : List Bool) : Bool × ℕ :=
  let x := cx_powB mm n one a d
  let c := cx_eq x.1 one
  if c.1 then (true, x.2 + c.2 + 1)
  else
    let r := cx_sqLoopB mm n nm1 s x.1
    (r.1, x.2 + c.2 + r.2 + 1)

theorem cx_sprpB_spec (mm : cx_ModMul) (n one nm1 d : List Bool) (s : ℕ) (hn1 : 1 < cx_val n)
    (hone : one.length = n.length) (honev : cx_val one = 1)
    (hnm1 : nm1.length = n.length) (hnm1v : cx_val nm1 = cx_val n - 1)
    (hs : s = (oddDecomp (cx_val n - 1)).1) (hd : cx_val d = (oddDecomp (cx_val n - 1)).2)
    (hsd : s + d.length ≤ n.length)
    (a : List Bool) (ha : a.length = n.length) (hav : cx_val a < cx_val n) :
    (cx_sprpB mm n one nm1 d s a).1 = cx_sprpFast (cx_val n) (cx_val a) ∧
    (cx_sprpB mm n one nm1 d s a).2
      ≤ n.length * (2 * mm.M n.length + n.length + 2) + n.length + 4 := by
  obtain ⟨p1, p2, p3⟩ := cx_powB_spec mm n one a hn1 hone honev ha hav d
  have hpv : cx_val (cx_powB mm n one a d).1 < cx_val n := by
    rw [p1]; exact Nat.mod_lt _ (by omega)
  have hiff : (cx_eq (cx_powB mm n one a d).1 one).1 = true
      ↔ cx_val (cx_powB mm n one a d).1 = 1 := by
    rw [cx_eq_iff _ _ (by omega), honev]
  have hcc := cx_eq_cost (cx_powB mm n one a d).1 one
  obtain ⟨q1, q2⟩ := cx_sqLoopB_spec mm n nm1 hn1 hnm1 hnm1v s _ p2 hpv
  have e0 : 0 ≤ s * (2 * mm.M n.length + n.length + 2) := Nat.zero_le _
  have e1 : d.length * (2 * mm.M n.length + 1)
      ≤ d.length * (2 * mm.M n.length + n.length + 2) := Nat.mul_le_mul_left _ (by omega)
  have e2 : s * (mm.M n.length + n.length + 2)
      ≤ s * (2 * mm.M n.length + n.length + 2) := Nat.mul_le_mul_left _ (by omega)
  have e3 : (d.length + s) * (2 * mm.M n.length + n.length + 2)
      ≤ n.length * (2 * mm.M n.length + n.length + 2) := Nat.mul_le_mul_right _ (by omega)
  have hfast : cx_sprpFast (cx_val n) (cx_val a)
      = if cx_val (cx_powB mm n one a d).1 = 1 then true
        else cx_sqLoop (cx_val n) s (cx_val (cx_powB mm n one a d).1) := by
    simp only [cx_sprpFast, powMod_eq, ← hd, ← hs, p1]
  rw [hfast]
  simp only [cx_sprpB]
  by_cases h : (cx_eq (cx_powB mm n one a d).1 one).1 = true
  · rw [if_pos h, if_pos (hiff.mp h)]
    refine ⟨rfl, ?_⟩
    dsimp only
    linarith
  · rw [if_neg h, if_neg (fun e => h (hiff.mpr e))]
    refine ⟨q1, ?_⟩
    dsimp only
    linarith

/-! ## The base loop -/

theorem cx_lt_iff (x y : List Bool) (h : x.length = y.length) :
    (cx_sub x y false).1.2 = true ↔ cx_val x < cx_val y := by
  obtain ⟨h1, h2, -⟩ := cx_sub_spec x y false
  have hd := cx_val_lt (cx_sub x y false).1.1
  have hx := cx_val_lt x
  rw [h2, h, max_self] at hd
  rw [h2, h, max_self] at h1
  rw [h] at hx
  cases hbr : (cx_sub x y false).1.2 <;> rw [hbr] at h1 <;> simp at h1 ⊢ <;> omega

/-- Base loop: `k` is the remaining (unary) budget, `a` the current base (width `b`).
Stops with `true` when the budget is exhausted or `a ≥ n`; with `false` at the first witness. -/
def cx_loopB (mm : cx_ModMul) (n one nm1 d : List Bool) (s : ℕ) : ℕ → List Bool → Bool × ℕ
  | 0, _ => (true, 1)
  | k + 1, a =>
    let c := cx_sub a n false
    if c.1.2 then
      let t := cx_sprpB mm n one nm1 d s a
      if t.1 then
        let a' := cx_inc a
        let r := cx_loopB mm n one nm1 d s k a'.1
        (r.1, c.2 + t.2 + a'.2 + r.2 + 1)
      else (false, c.2 + t.2 + 1)
    else (true, c.2 + 1)

theorem cx_loopB_spec (mm : cx_ModMul) (n one nm1 d : List Bool) (s : ℕ) (hn1 : 1 < cx_val n)
    (hone : one.length = n.length) (honev : cx_val one = 1)
    (hnm1 : nm1.length = n.length) (hnm1v : cx_val nm1 = cx_val n - 1)
    (hs : s = (oddDecomp (cx_val n - 1)).1) (hd : cx_val d = (oddDecomp (cx_val n - 1)).2)
    (hsd : s + d.length ≤ n.length)
    (k : ℕ) (a : List Bool) (ha : a.length = n.length) :
    (cx_loopB mm n one nm1 d s k a).1
      = (List.range' (cx_val a) (min (cx_val a + k) (cx_val n) - cx_val a)).all
          (fun b => cx_sprpFast (cx_val n) b) ∧
    (cx_loopB mm n one nm1 d s k a).2
      ≤ 1 + k * (n.length * (2 * mm.M n.length + n.length + 2) + 3 * n.length + 8) := by
  induction k generalizing a with
  | zero =>
    simp [cx_loopB]
  | succ k ih =>
    have hlt_iff := cx_lt_iff a n ha
    have hc2 : (cx_sub a n false).2 = n.length + 1 := by
      rw [(cx_sub_spec a n false).2.2, ha, max_self]
    simp only [cx_loopB]
    by_cases hlt : cx_val a < cx_val n
    · have hb : (cx_sub a n false).1.2 = true := hlt_iff.mpr hlt
      rw [if_pos hb]
      obtain ⟨t1, t2⟩ := cx_sprpB_spec mm n one nm1 d s hn1 hone honev hnm1 hnm1v hs hd hsd
        a ha hlt
      have hrange : List.range' (cx_val a) (min (cx_val a + (k + 1)) (cx_val n) - cx_val a)
          = cx_val a :: List.range' (cx_val a + 1)
              (min (cx_val a + 1 + k) (cx_val n) - (cx_val a + 1)) := by
        have : min (cx_val a + (k + 1)) (cx_val n) - cx_val a
            = (min (cx_val a + 1 + k) (cx_val n) - (cx_val a + 1)) + 1 := by omega
        rw [this, List.range'_succ]
      rw [hrange, List.all_cons]
      by_cases ht : (cx_sprpB mm n one nm1 d s a).1 = true
      · rw [if_pos ht]
        have hinc_len := cx_inc_length a
        have hinc_val := cx_inc_val a (by have := cx_val_lt n; rw [ha]; omega)
        have hinc_cost := cx_inc_cost a
        obtain ⟨i1, i2⟩ := ih (cx_inc a).1 (by rw [hinc_len, ha])
        rw [hinc_val] at i1
        refine ⟨?_, ?_⟩
        · dsimp only
          rw [i1, ← t1, ht, Bool.true_and]
        · dsimp only
          rw [Nat.add_mul, one_mul]
          omega
      · rw [if_neg ht]
        have ht' : (cx_sprpB mm n one nm1 d s a).1 = false := by simpa using ht
        refine ⟨?_, ?_⟩
        · dsimp only
          rw [← t1, ht', Bool.false_and]
        · dsimp only
          rw [Nat.add_mul, one_mul]
          omega
    · have hb : ¬ (cx_sub a n false).1.2 = true := fun e => hlt (hlt_iff.mp e)
      rw [if_neg hb]
      refine ⟨?_, ?_⟩
      · have : min (cx_val a + (k + 1)) (cx_val n) - cx_val a = 0 := by omega
        simp [this]
      · dsimp only
        rw [Nat.add_mul, one_mul]
        omega

/-! ## The complete test -/

/-- Main branch (odd `n ≥ 3` of width `≥ 2`): set up the constants, decompose `n - 1`, run the
base loop starting at `a = 2` with budget `cnt`. -/
def cx_millerMainB (mm : cx_ModMul) (cnt : ℕ) (n nm1 : List Bool) : Bool × ℕ :=
  let one := cx_trunc n [true]
  let two := cx_trunc n [false, true]
  let sd := cx_decompB nm1
  let r := cx_loopB mm n one.1 nm1 sd.1.2 sd.1.1 cnt two.1
  (r.1, one.2 + two.2 + sd.2 + r.2 + 1)

/-- The deterministic Miller test on the bit list of `n`, with base budget `cnt` (unary).
The first six cases dispose of `n < 2`, `n = 2` and even `n` by inspecting at most three cells. -/
def cx_millerDetB (mm : cx_ModMul) (cnt : ℕ) : List Bool → Bool × ℕ
  | [] => (false, 1)
  | [false] => (false, 2)
  | false :: false :: _ => (false, 3)
  | [false, true] => (true, 3)
  | false :: true :: _ :: _ => (false, 3)
  | [true] => (false, 2)
  | true :: b :: t => cx_millerMainB mm cnt (true :: b :: t) (false :: b :: t)

theorem cx_millerMainB_spec (mm : cx_ModMul) (cnt : ℕ) (n nm1 : List Bool)
    (hlen : 2 ≤ n.length) (h3 : 3 ≤ cx_val n)
    (hnm1 : nm1.length = n.length) (hnm1v : cx_val nm1 = cx_val n - 1) :
    (cx_millerMainB mm cnt n nm1).1
      = (List.range' 2 (min (2 + cnt) (cx_val n) - 2)).all (fun b => cx_sprpFast (cx_val n) b) ∧
    (cx_millerMainB mm cnt n nm1).2
      ≤ cnt * (n.length * (2 * mm.M n.length + n.length + 2) + 3 * n.length + 8)
        + 3 * n.length + 5 := by
  have hpow : 4 ≤ 2 ^ n.length :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) hlen)
  have v1 : cx_val [true] = 1 := by simp
  have v2 : cx_val [false, true] = 2 := by simp
  have hone_v : cx_val (cx_trunc n [true]).1 = 1 := by
    rw [cx_trunc_val n [true] (by omega), v1]
  have htwo_v : cx_val (cx_trunc n [false, true]).1 = 2 := by
    rw [cx_trunc_val n [false, true] (by omega), v2]
  obtain ⟨hs, hd⟩ := cx_decompB_spec nm1 (by omega)
  rw [hnm1v] at hs hd
  obtain ⟨hsd, hdc⟩ := cx_decompB_len nm1
  obtain ⟨l1, l2⟩ := cx_loopB_spec mm n (cx_trunc n [true]).1 nm1 (cx_decompB nm1).1.2
    (cx_decompB nm1).1.1 (by omega) (cx_trunc_length _ _) hone_v hnm1 hnm1v hs hd (by omega)
    cnt (cx_trunc n [false, true]).1 (cx_trunc_length _ _)
  rw [htwo_v] at l1
  have c1 := cx_trunc_cost n [true]
  have c2 := cx_trunc_cost n [false, true]
  simp only [cx_millerMainB]
  refine ⟨l1, ?_⟩
  omega

theorem cx_arith (w M cnt T : ℕ) (hw : 2 ≤ w) (hc : 2 * cnt ≤ w ^ 2)
    (hT : T ≤ cnt * (w * (2 * M + w + 2) + 3 * w + 8) + 3 * w + 5) :
    T ≤ w ^ 3 * M + 4 * w ^ 4 := by
  have hP := Nat.mul_le_mul_right (w * (2 * M + w + 2) + 3 * w + 8) hc
  have e4 : 16 ≤ w ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hw 4)
  have e3 : 8 * w ≤ w ^ 4 := by
    have := Nat.mul_le_mul_right w (Nat.pow_le_pow_left hw 3)
    calc 8 * w = 2 ^ 3 * w := by norm_num
      _ ≤ w ^ 3 * w := this
      _ = w ^ 4 := by ring
  have e2 : 4 * w ^ 2 ≤ w ^ 4 := by
    have := Nat.mul_le_mul_right (w ^ 2) (Nat.pow_le_pow_left hw 2)
    calc 4 * w ^ 2 = 2 ^ 2 * w ^ 2 := by norm_num
      _ ≤ w ^ 2 * w ^ 2 := this
      _ = w ^ 4 := by ring
  have e1 : 2 * w ^ 3 ≤ w ^ 4 := by
    have := Nat.mul_le_mul_right (w ^ 3) hw
    calc 2 * w ^ 3 ≤ w * w ^ 3 := this
      _ = w ^ 4 := by ring
  nlinarith

/-- Value and cost of the bit-level test, for every `n` and every modular multiplier. -/
theorem cx_millerDetB_spec (mm : cx_ModMul) (n : ℕ) :
    (cx_millerDetB mm (millerBound 1 n - 2) (cx_bits n)).1 = cx_millerDetFast n ∧
    (cx_millerDetB mm (millerBound 1 n - 2) (cx_bits n)).2
      ≤ (Nat.log2 n + 1) ^ 3 * mm.M (Nat.log2 n + 1) + 4 * (Nat.log2 n + 1) ^ 4 := by
  have hL4 : 4 ≤ (Nat.log2 n + 1) ^ 3 * mm.M (Nat.log2 n + 1) + 4 * (Nat.log2 n + 1) ^ 4 := by
    have := Nat.one_le_pow 4 (Nat.log2 n + 1) (by omega)
    omega
  by_cases h3 : n < 3
  · interval_cases n
    · exact ⟨by simp [cx_bits_zero, cx_millerDetB, cx_millerDetFast],
        le_trans (show _ ≤ 4 by simp [cx_bits_zero, cx_millerDetB]) hL4⟩
    · exact ⟨by simp [cx_bits_one, cx_millerDetB, cx_millerDetFast],
        le_trans (show _ ≤ 4 by simp [cx_bits_one, cx_millerDetB]) hL4⟩
    · exact ⟨by simp [cx_bits_two, cx_millerDetB, cx_millerDetFast],
        le_trans (show _ ≤ 4 by simp [cx_bits_two, cx_millerDetB]) hL4⟩
  by_cases hodd : n % 2 = 1
  · -- main case: odd `n ≥ 3`
    have e0 : (n % 2 == 1) = true := by rw [beq_iff_eq]; exact hodd
    obtain ⟨b, t, hbt⟩ : ∃ b t, cx_bits n = true :: b :: t :=
      ⟨_, _, by rw [cx_bits_cons (show n ≠ 0 by omega), cx_bits_cons (show n / 2 ≠ 0 by omega),
        e0]⟩
    have hval := cx_val_bits n
    have hlen := cx_bits_length (show n ≠ 0 by omega)
    rw [hbt] at hval hlen
    rw [hbt]
    simp only [cx_millerDetB]
    obtain ⟨m1, m2⟩ := cx_millerMainB_spec mm (millerBound 1 n - 2) (true :: b :: t)
      (false :: b :: t) (by simp) (by omega) (by simp)
      (by simp only [cx_val_cons, Bool.toNat_true, Bool.toNat_false]; omega)
    rw [hval] at m1
    rw [hlen] at m2
    have hw : 2 ≤ Nat.log2 n + 1 := by
      simp only [List.length_cons] at hlen; omega
    have hc : 2 * (millerBound 1 n - 2) ≤ (Nat.log2 n + 1) ^ 2 := by
      have := cx_two_mul_millerBound_le n; omega
    refine ⟨?_, cx_arith _ _ _ _ hw hc m2⟩
    rw [m1]
    unfold cx_millerDetFast
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have : min (2 + (millerBound 1 n - 2)) n - 2 = min (millerBound 1 n) n - 2 := by omega
    rw [this]
  · -- even `n ≥ 4`
    have e0 : (n % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; exact hodd
    have hf : cx_millerDetFast n = false := by
      unfold cx_millerDetFast
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [hf, cx_bits_cons (show n ≠ 0 by omega), cx_bits_cons (show n / 2 ≠ 0 by omega),
      cx_bits_cons (show n / 2 / 2 ≠ 0 by omega), e0]
    rcases Nat.mod_two_eq_zero_or_one (n / 2) with h | h
    · have e1 : (n / 2 % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; omega
      rw [e1]
      simp only [cx_millerDetB]
      exact ⟨trivial, le_trans (by norm_num) hL4⟩
    · have e1 : (n / 2 % 2 == 1) = true := by rw [beq_iff_eq]; exact h
      rw [e1]
      simp only [cx_millerDetB]
      exact ⟨trivial, le_trans (by norm_num) hL4⟩

/-- **Value.** The bit-level program computes `cx_millerDetFast n` (hence `millerDet 1 n`). -/
theorem cx_millerDetB_fst (mm : cx_ModMul) (n : ℕ) :
    (cx_millerDetB mm (millerBound 1 n - 2) (cx_bits n)).1 = cx_millerDetFast n :=
  (cx_millerDetB_spec mm n).1

/-- **Generic bit-cost bound.** With `L = log₂ n + 1` and any modular multiplier of cost `M`:
total cost `≤ L³ · M(L) + 4 L⁴` for every `n`.  (`L³` modular multiplications, `4 L⁴` for all
comparisons, increments, the decomposition of `n - 1` and loop control.) -/
theorem cx_millerDetB_cost (mm : cx_ModMul) (n : ℕ) :
    (cx_millerDetB mm (millerBound 1 n - 2) (cx_bits n)).2
      ≤ (Nat.log2 n + 1) ^ 3 * mm.M (Nat.log2 n + 1) + 4 * (Nat.log2 n + 1) ^ 4 :=
  (cx_millerDetB_spec mm n).2

/-- The deterministic Miller test at bit level with schoolbook arithmetic: `(answer, cost)`. -/
def cx_millerDetBits (n : ℕ) : Bool × ℕ :=
  cx_millerDetB cx_schoolbook (millerBound 1 n - 2) (cx_bits n)

theorem cx_millerDetBits_fst (n : ℕ) : (cx_millerDetBits n).1 = millerDet 1 n := by
  rw [cx_millerDetBits, cx_millerDetB_fst, cx_millerDetFast_eq]

/-- **Tier 2 bound.** With schoolbook multiplication and division, the deterministic Miller test
uses at most `31 · (log₂ n + 1)⁵` bit steps, for every `n`. -/
theorem cx_millerDetBits_cost (n : ℕ) : (cx_millerDetBits n).2 ≤ 31 * (Nat.log2 n + 1) ^ 5 := by
  have h := cx_millerDetB_cost cx_schoolbook n
  have hM : cx_schoolbook.M (Nat.log2 n + 1)
      = 9 * (Nat.log2 n + 1) ^ 2 + 16 * (Nat.log2 n + 1) + 2 := rfl
  rw [hM] at h
  unfold cx_millerDetBits
  generalize Nat.log2 n + 1 = w at h ⊢
  generalize (cx_millerDetB cx_schoolbook (millerBound 1 n - 2) (cx_bits n)).2 = T at h ⊢
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simpa using h
  have h4 : w ^ 4 ≤ w ^ 5 := Nat.pow_le_pow_right hw (by norm_num)
  have h3 : w ^ 3 ≤ w ^ 5 := Nat.pow_le_pow_right hw (by norm_num)
  nlinarith

end DetPrimality.Complexity
