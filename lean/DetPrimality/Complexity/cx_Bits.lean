import Mathlib

/-!
# Bit-level arithmetic with explicit cost: schoolbook multiplication and shift-subtract remainder

Numbers are little-endian bit lists `List Bool` (`cx_val`), least significant bit first.

## Cost model (bit operations)

Every function in this file returns a pair `(result, cost)`.  The primitive loops are
`cx_add` (ripple-carry adder), `cx_sub` (ripple-borrow subtractor, also used as comparator),
`cx_trunc` (copy/zero-pad to a fixed width), `cx_eq` (equality scan), `cx_inc` (increment).
Each is a structural recursion on bit lists whose every recursive step

* inspects at most one cons cell of each operand list and one carry/borrow bit,
* evaluates a fixed Boolean formula on these (at most 3) bits (a full adder / full subtractor),
* emits at most one output cons cell,

and adds exactly `1` to the cost.  Hence **one unit of cost = one such constant-size bit step**
(a full-adder-like gate group together with the pointer move on the lists); the final `nil` step
of each loop is also charged `1`.  Composite functions (`cx_mul`, `cx_mod`, `cx_mulmod`) add up
the costs of the primitives they call plus `1` per iteration of their own outer loop (the
inspection of the multiplier bit / the selection after the trial subtraction).  No operation on
`ℕ` is used to compute any value: `ℕ` appears only as the cost counter and in specifications.

Main results:
* `cx_mulmod x y n` = schoolbook product (`cx_mul`, shift-and-add) followed by schoolbook
  shift-subtract remainder (`cx_mod`), result normalised to width `n.length`;
* `cx_mulmod_val : 0 < cx_val n → cx_val (cx_mulmod x y n).1 = cx_val x * cx_val y % cx_val n`;
* `cx_mulmod_cost : x.length = n.length → y.length = n.length →
    (cx_mulmod x y n).2 ≤ 9 * n.length ^ 2 + 16 * n.length + 2`.
-/

namespace DetPrimality.Complexity

/-! ## Bit lists -/

/-- Value of a little-endian bit list. -/
def cx_val : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * cx_val l

@[simp] theorem cx_val_nil : cx_val [] = 0 := rfl
@[simp] theorem cx_val_cons (b : Bool) (l : List Bool) :
    cx_val (b :: l) = b.toNat + 2 * cx_val l := rfl

theorem cx_val_lt (l : List Bool) : cx_val l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have := Bool.toNat_lt b
    simp only [cx_val_cons, List.length_cons, pow_succ]
    omega

/-- The (normalised) little-endian binary expansion of `n`. -/
def cx_bits (n : ℕ) : List Bool :=
  if h : n = 0 then [] else (n % 2 == 1) :: cx_bits (n / 2)
termination_by n
decreasing_by omega

theorem cx_val_bits (n : ℕ) : cx_val (cx_bits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [cx_bits]
    split_ifs with h
    · simp [h]
    · rw [cx_val_cons, ih (n / 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> (simp [h2]; omega)

theorem cx_bits_length {n : ℕ} (hn : n ≠ 0) : (cx_bits n).length = Nat.log2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [cx_bits, dif_neg hn, List.length_cons]
    by_cases h2 : 2 ≤ n
    · rw [Nat.log2_def n, if_pos h2, ih (n / 2) (by omega) (by omega)]
    · have h0 : n / 2 = 0 := by omega
      rw [Nat.log2_def n, if_neg h2, h0, cx_bits]
      simp

theorem cx_bits_cons {n : ℕ} (hn : n ≠ 0) : cx_bits n = (n % 2 == 1) :: cx_bits (n / 2) := by
  rw [cx_bits, dif_neg hn]

theorem cx_bits_zero : cx_bits 0 = [] := by
  rw [cx_bits]; simp

theorem cx_bits_one : cx_bits 1 = [true] := by
  rw [cx_bits_cons (show (1 : ℕ) ≠ 0 by norm_num)]; simp [cx_bits_zero]

theorem cx_bits_two : cx_bits 2 = [false, true] := by
  rw [cx_bits_cons (show (2 : ℕ) ≠ 0 by norm_num)]; simp [cx_bits_one]

/-! ## Primitive loops -/

/-- Ripple-carry addition with carry-in; one full-adder step per unit of cost. -/
def cx_add : List Bool → List Bool → Bool → List Bool × ℕ
  | [], [], c => ([c], 1)
  | a :: x, [], c =>
    let r := cx_add x [] (a && c)
    ((a ^^ c) :: r.1, r.2 + 1)
  | [], b :: y, c =>
    let r := cx_add [] y (b && c)
    ((b ^^ c) :: r.1, r.2 + 1)
  | a :: x, b :: y, c =>
    let r := cx_add x y ((a && b) || (c && (a ^^ b)))
    ((a ^^ (b ^^ c)) :: r.1, r.2 + 1)
termination_by x y => x.length + y.length

theorem cx_add_spec (x y : List Bool) (c : Bool) :
    cx_val (cx_add x y c).1 = cx_val x + cx_val y + c.toNat ∧
    (cx_add x y c).1.length = max x.length y.length + 1 ∧
    (cx_add x y c).2 = max x.length y.length + 1 := by
  induction x generalizing y c with
  | nil =>
    induction y generalizing c with
    | nil => simp [cx_add]
    | cons b y ih =>
      obtain ⟨h1, h2, h3⟩ := ih (b && c)
      simp only [cx_add, cx_val_cons, cx_val_nil, List.length_cons, List.length_nil,
        Nat.zero_max] at h1 h2 h3 ⊢
      refine ⟨?_, ?_, ?_⟩ <;> cases b <;> cases c <;> simp_all <;> omega
  | cons a x ih =>
    cases y with
    | nil =>
      obtain ⟨h1, h2, h3⟩ := ih [] (a && c)
      simp only [cx_add, cx_val_cons, cx_val_nil, List.length_cons, List.length_nil,
        Nat.max_zero] at h1 h2 h3 ⊢
      refine ⟨?_, ?_, ?_⟩ <;> cases a <;> cases c <;> simp_all <;> omega
    | cons b y =>
      obtain ⟨h1, h2, h3⟩ := ih y ((a && b) || (c && (a ^^ b)))
      simp only [cx_add, cx_val_cons, List.length_cons, Nat.add_max_add_right] at h1 h2 h3 ⊢
      refine ⟨?_, ?_, ?_⟩ <;> cases a <;> cases b <;> cases c <;> simp_all <;> omega

/-- Ripple-borrow subtraction `x - y - c`; returns `((difference bits, final borrow), cost)`.
The final borrow is `true` iff `x < y + c`. -/
def cx_sub : List Bool → List Bool → Bool → (List Bool × Bool) × ℕ
  | [], [], c => (([], c), 1)
  | a :: x, [], c =>
    let r := cx_sub x [] (!a && c)
    (((a ^^ c) :: r.1.1, r.1.2), r.2 + 1)
  | [], b :: y, c =>
    let r := cx_sub [] y (b || c)
    (((b ^^ c) :: r.1.1, r.1.2), r.2 + 1)
  | a :: x, b :: y, c =>
    let r := cx_sub x y ((!a && (b || c)) || (b && c))
    (((a ^^ (b ^^ c)) :: r.1.1, r.1.2), r.2 + 1)
termination_by x y => x.length + y.length

theorem cx_sub_spec (x y : List Bool) (c : Bool) :
    cx_val x + 2 ^ (cx_sub x y c).1.1.length * (cx_sub x y c).1.2.toNat
      = cx_val y + c.toNat + cx_val (cx_sub x y c).1.1 ∧
    (cx_sub x y c).1.1.length = max x.length y.length ∧
    (cx_sub x y c).2 = max x.length y.length + 1 := by
  induction x generalizing y c with
  | nil =>
    induction y generalizing c with
    | nil => simp [cx_sub]
    | cons b y ih =>
      obtain ⟨h1, h2, h3⟩ := ih (b || c)
      simp only [cx_sub, cx_val_cons, cx_val_nil, List.length_cons, List.length_nil,
        Nat.zero_max, pow_succ] at h1 h2 h3 ⊢
      refine ⟨?_, ?_, ?_⟩ <;> cases b <;> cases c <;> simp_all <;> first | omega | linarith
  | cons a x ih =>
    cases y with
    | nil =>
      obtain ⟨h1, h2, h3⟩ := ih [] (!a && c)
      simp only [cx_sub, cx_val_cons, cx_val_nil, List.length_cons, List.length_nil,
        Nat.max_zero, pow_succ] at h1 h2 h3 ⊢
      refine ⟨?_, ?_, ?_⟩ <;> cases a <;> cases c <;> simp_all <;> first | omega | linarith
    | cons b y =>
      obtain ⟨h1, h2, h3⟩ := ih y ((!a && (b || c)) || (b && c))
      simp only [cx_sub, cx_val_cons, List.length_cons, Nat.add_max_add_right, pow_succ]
        at h1 h2 h3 ⊢
      refine ⟨?_, ?_, ?_⟩ <;> cases a <;> cases b <;> cases c <;> simp_all <;>
        first | omega | linarith

/-- Copy `x` to the width of the shape list `n` (truncate or zero-pad). -/
def cx_trunc : List Bool → List Bool → List Bool × ℕ
  | [], _ => ([], 1)
  | _ :: n, [] =>
    let r := cx_trunc n []
    (false :: r.1, r.2 + 1)
  | _ :: n, a :: x =>
    let r := cx_trunc n x
    (a :: r.1, r.2 + 1)

theorem cx_trunc_length (n x : List Bool) : (cx_trunc n x).1.length = n.length := by
  induction n generalizing x with
  | nil => simp [cx_trunc]
  | cons b n ih => cases x <;> simp [cx_trunc, ih]

theorem cx_trunc_cost (n x : List Bool) : (cx_trunc n x).2 = n.length + 1 := by
  induction n generalizing x with
  | nil => simp [cx_trunc]
  | cons b n ih => cases x <;> simp [cx_trunc, ih]

theorem cx_trunc_val (n x : List Bool) (h : cx_val x < 2 ^ n.length) :
    cx_val (cx_trunc n x).1 = cx_val x := by
  induction n generalizing x with
  | nil =>
    simp only [List.length_nil, pow_zero] at h
    simp only [cx_trunc, cx_val_nil]; omega
  | cons b n ih =>
    cases x with
    | nil =>
      have := ih [] (by simp)
      simp only [cx_trunc, cx_val_cons, cx_val_nil] at this ⊢
      simp [this]
    | cons a x =>
      simp only [cx_val_cons, List.length_cons, pow_succ] at h
      have := ih x (by omega)
      simp only [cx_trunc, cx_val_cons, this]

/-- Equality scan of two bit lists (meaningful for equal lengths). -/
def cx_eq : List Bool → List Bool → Bool × ℕ
  | [], [] => (true, 1)
  | a :: x, b :: y =>
    let r := cx_eq x y
    ((a == b) && r.1, r.2 + 1)
  | [], _ :: _ => (false, 1)
  | _ :: _, [] => (false, 1)

theorem cx_eq_iff (x y : List Bool) (h : x.length = y.length) :
    (cx_eq x y).1 = true ↔ cx_val x = cx_val y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => simp [cx_eq]
    | cons b y => simp at h
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      have hl : x.length = y.length := by simpa using h
      simp only [cx_eq, Bool.and_eq_true, beq_iff_eq, ih y hl, cx_val_cons]
      cases a <;> cases b <;> simp <;> omega

theorem cx_eq_cost (x y : List Bool) : (cx_eq x y).2 ≤ x.length + 1 := by
  induction x generalizing y with
  | nil => cases y <;> simp [cx_eq]
  | cons a x ih =>
    cases y with
    | nil => simp [cx_eq]
    | cons b y => have := ih y; simp only [cx_eq, List.length_cons]; omega

/-- Width-preserving increment (wraps around on overflow). -/
def cx_inc : List Bool → List Bool × ℕ
  | [] => ([], 1)
  | false :: t => (true :: t, 1)
  | true :: t =>
    let r := cx_inc t
    (false :: r.1, r.2 + 1)

theorem cx_inc_length (x : List Bool) : (cx_inc x).1.length = x.length := by
  induction x with
  | nil => simp [cx_inc]
  | cons a x ih => cases a <;> simp [cx_inc, ih]

theorem cx_inc_cost (x : List Bool) : (cx_inc x).2 ≤ x.length + 1 := by
  induction x with
  | nil => simp [cx_inc]
  | cons a x ih => cases a <;> simp [cx_inc]; omega

theorem cx_inc_val (x : List Bool) (h : cx_val x + 1 < 2 ^ x.length) :
    cx_val (cx_inc x).1 = cx_val x + 1 := by
  induction x with
  | nil => simp at h
  | cons a x ih =>
    cases a with
    | false => simp [cx_inc]; omega
    | true =>
      simp only [cx_val_cons, List.length_cons, pow_succ, Bool.toNat_true] at h
      have := ih (by omega)
      simp only [cx_inc, cx_val_cons, this, Bool.toNat_true, Bool.toNat_false]
      omega

/-! ## Schoolbook multiplication -/

/-- Schoolbook (shift-and-add) multiplication: `x * y = x₀ * y + 2 * (x' * y)`. -/
def cx_mul : List Bool → List Bool → List Bool × ℕ
  | [], _ => ([], 1)
  | a :: x, y =>
    let p := cx_mul x y
    if a then
      let s := cx_add (false :: p.1) y false
      (s.1, p.2 + s.2 + 1)
    else (false :: p.1, p.2 + 1)

theorem cx_mul_val (x y : List Bool) : cx_val (cx_mul x y).1 = cx_val x * cx_val y := by
  induction x with
  | nil => simp [cx_mul]
  | cons a x ih =>
    cases a with
    | false => simp [cx_mul, ih]; ring
    | true => simp [cx_mul, ih, (cx_add_spec _ _ _).1]; ring

theorem cx_mul_length (x y : List Bool) : (cx_mul x y).1.length ≤ 2 * x.length + y.length := by
  induction x with
  | nil => simp [cx_mul]
  | cons a x ih =>
    cases a with
    | false => simp [cx_mul]; omega
    | true => simp [cx_mul, (cx_add_spec _ _ _).2.1]; omega

theorem cx_mul_cost (x y : List Bool) :
    (cx_mul x y).2 ≤ 1 + x.length * (2 * x.length + y.length + 3) := by
  induction x with
  | nil => simp [cx_mul]
  | cons a x ih =>
    have hl := cx_mul_length x y
    cases a with
    | false =>
      simp only [cx_mul, List.length_cons, Bool.false_eq_true, if_false]
      nlinarith
    | true =>
      simp only [cx_mul, List.length_cons, if_true, (cx_add_spec _ _ _).2.2]
      have hm : max ((cx_mul x y).1.length + 1) y.length ≤ 2 * x.length + y.length + 1 := by
        omega
      nlinarith

/-! ## Schoolbook (shift-subtract) remainder -/

/-- Shift-subtract remainder, most significant bit of the dividend first (the recursion on the
little-endian list reaches the top bit first): `r ← 2 r + bit; if r ≥ n then r ← r - n`.
The result always has width `n.length`. -/
def cx_mod : List Bool → List Bool → List Bool × ℕ
  | [], n => cx_trunc n []
  | a :: m, n =>
    let r := cx_mod m n
    let d := cx_sub (a :: r.1) n false
    let t := cx_trunc n (if d.1.2 then a :: r.1 else d.1.1)
    (t.1, r.2 + d.2 + t.2 + 1)

theorem cx_mod_length (m n : List Bool) : (cx_mod m n).1.length = n.length := by
  cases m <;> simp [cx_mod, cx_trunc_length]

theorem cx_mod_cost (m n : List Bool) :
    (cx_mod m n).2 = (n.length + 1) + m.length * (2 * n.length + 4) := by
  induction m with
  | nil => simp [cx_mod, cx_trunc_cost]
  | cons a m ih =>
    simp only [cx_mod, cx_trunc_cost, (cx_sub_spec _ _ _).2.2, List.length_cons, cx_mod_length, ih]
    have : max (n.length + 1) n.length = n.length + 1 := by omega
    rw [this]; ring

theorem cx_mod_step (A M N : ℕ) :
    (A + 2 * (M % N) < N → (A + 2 * M) % N = A + 2 * (M % N)) ∧
    (N ≤ A + 2 * (M % N) → A + 2 * (M % N) < 2 * N →
      (A + 2 * M) % N = A + 2 * (M % N) - N) := by
  have key : (A + 2 * M) % N = (A + 2 * (M % N)) % N := by
    have h : A + 2 * M = A + 2 * (M % N) + N * (2 * (M / N)) := by
      have := Nat.div_add_mod M N
      nlinarith
    rw [h, Nat.add_mul_mod_self_left]
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · rw [key, Nat.mod_eq_of_lt h]
  · rw [key, Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

theorem cx_mod_val (m n : List Bool) (hn : 0 < cx_val n) :
    cx_val (cx_mod m n).1 = cx_val m % cx_val n := by
  induction m with
  | nil => simp [cx_mod, cx_trunc_val n [] (by simp)]
  | cons a m ih =>
    have hnlt := cx_val_lt n
    have hr : cx_val (cx_mod m n).1 < cx_val n := by rw [ih]; exact Nat.mod_lt _ hn
    have hb := Bool.toNat_lt a
    obtain ⟨hs1, hs2, -⟩ := cx_sub_spec (a :: (cx_mod m n).1) n false
    have hdlt := cx_val_lt (cx_sub (a :: (cx_mod m n).1) n false).1.1
    rw [hs2, List.length_cons, cx_mod_length,
      show max (n.length + 1) n.length = n.length + 1 by omega] at hdlt
    rw [hs2, List.length_cons, cx_mod_length,
      show max (n.length + 1) n.length = n.length + 1 by omega, cx_val_cons, pow_succ] at hs1
    simp only [Bool.toNat_false, add_zero] at hs1
    rw [pow_succ] at hdlt
    obtain ⟨hst1, hst2⟩ := cx_mod_step a.toNat (cx_val m) (cx_val n)
    rw [← ih] at hst1 hst2
    simp only [cx_mod, cx_val_cons]
    cases hbr : (cx_sub (a :: (cx_mod m n).1) n false).1.2 with
    | true =>
      rw [hbr] at hs1
      simp only [Bool.toNat_true, mul_one] at hs1
      simp only [if_true]
      rw [cx_trunc_val _ _ (by rw [cx_val_cons]; omega), cx_val_cons]
      exact (hst1 (by omega)).symm
    | false =>
      rw [hbr] at hs1
      simp only [Bool.toNat_false, mul_zero, add_zero] at hs1
      simp only [Bool.false_eq_true, if_false]
      rw [cx_trunc_val _ _ (by omega)]
      rw [hst2 (by omega) (by omega)]
      omega

/-! ## Modular multiplication -/

/-- Schoolbook modular multiplication: full product, then shift-subtract remainder. -/
def cx_mulmod (x y n : List Bool) : List Bool × ℕ :=
  let p := cx_mul x y
  let r := cx_mod p.1 n
  (r.1, p.2 + r.2)

theorem cx_mulmod_val (x y n : List Bool) (hn : 0 < cx_val n) :
    cx_val (cx_mulmod x y n).1 = cx_val x * cx_val y % cx_val n := by
  simp only [cx_mulmod, cx_mod_val _ _ hn, cx_mul_val]

theorem cx_mulmod_length (x y n : List Bool) : (cx_mulmod x y n).1.length = n.length := by
  simp only [cx_mulmod, cx_mod_length]

/-- **Schoolbook modular multiplication costs at most `9 b² + 16 b + 2` bit steps** on
`b`-bit operands. -/
theorem cx_mulmod_cost (x y n : List Bool) (hx : x.length = n.length) (hy : y.length = n.length) :
    (cx_mulmod x y n).2 ≤ 9 * n.length ^ 2 + 16 * n.length + 2 := by
  have h1 := cx_mul_cost x y
  have h2 := cx_mul_length x y
  rw [hx, hy] at h1 h2
  have h3 : (cx_mul x y).1.length * (2 * n.length + 4) ≤ (3 * n.length) * (2 * n.length + 4) :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [cx_mulmod, cx_mod_cost]
  nlinarith

end DetPrimality.Complexity
