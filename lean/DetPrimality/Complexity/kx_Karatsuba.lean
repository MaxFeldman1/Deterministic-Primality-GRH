import Mathlib
import DetPrimality.Complexity.cx_Bits

/-!
# Karatsuba multiplication on bit lists, with explicit bit cost

Same conventions and the same cost model as `cx_Bits.lean`: numbers are little-endian
`List Bool`, every function returns `(result, cost)`, and **one unit of cost is one constant-size
bit step** (a step of a structural recursion that inspects O(1) cons cells / flag bits, evaluates
a fixed Boolean formula and emits at most one cons cell).  No operation on `ℕ` computes a value;
`ℕ` is only the cost counter (and appears in specifications).

New primitive loops (each recursive step and the final step cost `1`):

* `kx_split t x` – tortoise/hare split: the "hare" list `t` is consumed two cells per step while
  one bit of `x` is copied, so `x` is cut at position `⌊|t|/2⌋` (zero-padding if `x` is short);
* `kx_trunc2 x y z` – copy/zero-pad `z` to width `|x| + |y|` (walks the shapes `x`, then `y`);
* `kx_shift s z` – prepend `|s|` zero bits (multiplication by `2^|s|`);
* `kx_drop s z` – drop `|s|` low bits (division by `2^|s|`);
* `kx_absdiff x y` – `|x - y|` and the sign, by one or two ripple-borrow subtractions `cx_sub`.

`kx_kar x y` is Karatsuba's algorithm (subtractive variant
`x₀y₁ + x₁y₀ = x₀y₀ + x₁y₁ - (x₀ - x₁)(y₀ - y₁)`), recursing by well-founded recursion on the
length of `x` down to lengths `≤ 1`, where the schoolbook `cx_mul` is used.  Every level charges
all its splits, subtractions, additions, shifts, the final normalisation to width `|x| + |y|`,
and `1` for its O(1) control (the XOR of the two sign bits and the dispatch).

Main results:
* `kx_kar_val : cx_val (kx_kar x y).1 = cx_val x * cx_val y` (all inputs);
* `kx_kar_length : (kx_kar x y).1.length = x.length + y.length`;
* `kx_kar_cost : x.length = y.length → x.length ≤ 2 ^ k →
    (kx_kar x y).2 + 23 * 2 ^ k + 10 ≤ 44 * 3 ^ k`.
-/

namespace DetPrimality.Complexity

/-! ## Primitive loops -/

/-- Tortoise/hare split of `x` at position `⌊|t|/2⌋`: returns `((low, high), cost)`. -/
def kx_split : List Bool → List Bool → (List Bool × List Bool) × ℕ
  | [], x => (([], x), 1)
  | [_], x => (([], x), 1)
  | _ :: _ :: t, [] =>
    let r := kx_split t []
    ((false :: r.1.1, r.1.2), r.2 + 1)
  | _ :: _ :: t, a :: x =>
    let r := kx_split t x
    ((a :: r.1.1, r.1.2), r.2 + 1)

theorem kx_split_lo_length (t x : List Bool) : (kx_split t x).1.1.length = t.length / 2 := by
  induction t, x using kx_split.induct
  · simp [kx_split]
  · simp [kx_split]
  · rename_i t ih
    simp only [kx_split, List.length_cons, ih]; omega
  · rename_i t a x ih
    simp only [kx_split, List.length_cons, ih]; omega

theorem kx_split_hi_length (t x : List Bool) :
    (kx_split t x).1.2.length = x.length - t.length / 2 := by
  induction t, x using kx_split.induct
  · simp [kx_split]
  · simp [kx_split]
  · rename_i t ih
    simp only [kx_split, List.length_cons, List.length_nil] at ih ⊢; omega
  · rename_i t a x ih
    simp only [kx_split, List.length_cons, ih]; omega

theorem kx_split_cost (t x : List Bool) : (kx_split t x).2 = t.length / 2 + 1 := by
  induction t, x using kx_split.induct
  · simp [kx_split]
  · simp [kx_split]
  · rename_i t ih
    simp only [kx_split, List.length_cons, ih]; omega
  · rename_i t a x ih
    simp only [kx_split, List.length_cons, ih]; omega

theorem kx_split_val (t x : List Bool) :
    cx_val x = cx_val (kx_split t x).1.1 + 2 ^ (t.length / 2) * cx_val (kx_split t x).1.2 := by
  induction t, x using kx_split.induct
  · simp [kx_split]
  · simp [kx_split]
  · rename_i t ih
    have e : (t.length + 1 + 1) / 2 = t.length / 2 + 1 := by omega
    simp only [kx_split, cx_val_cons, cx_val_nil, List.length_cons, e, pow_succ,
      Bool.toNat_false] at ih ⊢
    linarith
  · rename_i t a x ih
    have e : (t.length + 1 + 1) / 2 = t.length / 2 + 1 := by omega
    simp only [kx_split, cx_val_cons, List.length_cons, e, pow_succ] at ih ⊢
    linarith

/-- Copy `z` to width `|x| + |y|` (truncate or zero-pad), walking the shape `x`, then `y`. -/
def kx_trunc2 : List Bool → List Bool → List Bool → List Bool × ℕ
  | [], y, z => cx_trunc y z
  | _ :: x, y, [] =>
    let r := kx_trunc2 x y []
    (false :: r.1, r.2 + 1)
  | _ :: x, y, a :: z =>
    let r := kx_trunc2 x y z
    (a :: r.1, r.2 + 1)

theorem kx_trunc2_length (x y z : List Bool) :
    (kx_trunc2 x y z).1.length = x.length + y.length := by
  induction x generalizing z with
  | nil => simp [kx_trunc2, cx_trunc_length]
  | cons b x ih => cases z <;> simp only [kx_trunc2, List.length_cons, ih] <;> omega

theorem kx_trunc2_cost (x y z : List Bool) :
    (kx_trunc2 x y z).2 = x.length + y.length + 1 := by
  induction x generalizing z with
  | nil => simp [kx_trunc2, cx_trunc_cost]
  | cons b x ih => cases z <;> simp only [kx_trunc2, List.length_cons, ih] <;> omega

theorem kx_trunc2_val (x y z : List Bool) (h : cx_val z < 2 ^ (x.length + y.length)) :
    cx_val (kx_trunc2 x y z).1 = cx_val z := by
  induction x generalizing z with
  | nil =>
    simp only [kx_trunc2]
    exact cx_trunc_val y z (by simpa using h)
  | cons b x ih =>
    cases z with
    | nil =>
      have := ih [] (by simp)
      simp only [kx_trunc2, cx_val_cons, cx_val_nil] at this ⊢
      simp [this]
    | cons a z =>
      have h' : cx_val z < 2 ^ (x.length + y.length) := by
        simp only [cx_val_cons, List.length_cons] at h
        have e : 2 ^ (x.length + 1 + y.length) = 2 * 2 ^ (x.length + y.length) := by ring
        rw [e] at h; omega
      simp only [kx_trunc2, cx_val_cons, ih z h']

/-- Prepend `|s|` zero bits: multiplication by `2 ^ |s|`. -/
def kx_shift : List Bool → List Bool → List Bool × ℕ
  | [], z => (z, 1)
  | _ :: s, z =>
    let r := kx_shift s z
    (false :: r.1, r.2 + 1)

theorem kx_shift_spec (s z : List Bool) :
    cx_val (kx_shift s z).1 = 2 ^ s.length * cx_val z ∧
    (kx_shift s z).1.length = s.length + z.length ∧
    (kx_shift s z).2 = s.length + 1 := by
  induction s with
  | nil => simp [kx_shift]
  | cons b s ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · simp only [kx_shift, cx_val_cons, h1, List.length_cons, pow_succ, Bool.toNat_false]; ring
    · simp only [kx_shift, List.length_cons, h2]; omega
    · simp only [kx_shift, List.length_cons, h3]

/-- Drop `|s|` low bits: division by `2 ^ |s|`. -/
def kx_drop : List Bool → List Bool → List Bool × ℕ
  | [], z => (z, 1)
  | _ :: _, [] => ([], 1)
  | _ :: s, _ :: z =>
    let r := kx_drop s z
    (r.1, r.2 + 1)

theorem kx_drop_val (s z : List Bool) : cx_val (kx_drop s z).1 = cx_val z / 2 ^ s.length := by
  induction s generalizing z with
  | nil => simp [kx_drop]
  | cons b s ih =>
    cases z with
    | nil => simp [kx_drop]
    | cons a z =>
      have e : (a.toNat + 2 * cx_val z) / 2 = cx_val z := by
        have := Bool.toNat_lt a; omega
      simp only [kx_drop, ih, cx_val_cons, List.length_cons]
      rw [pow_succ', ← Nat.div_div_eq_div_mul, e]

theorem kx_drop_cost (s z : List Bool) : (kx_drop s z).2 ≤ s.length + 1 := by
  induction s generalizing z with
  | nil => simp [kx_drop]
  | cons b s ih =>
    cases z with
    | nil => simp [kx_drop]
    | cons a z => have := ih z; simp only [kx_drop, List.length_cons]; omega

/-- `|x - y|` together with the sign bit (`true` iff `x < y`): a trial subtraction, and the
reverse subtraction if it borrowed. -/
def kx_absdiff (x y : List Bool) : (List Bool × Bool) × ℕ :=
  let d := cx_sub x y false
  if d.1.2 then
    let e := cx_sub y x false
    ((e.1.1, true), d.2 + e.2 + 1)
  else ((d.1.1, false), d.2 + 1)

theorem kx_absdiff_spec (x y : List Bool) :
    ((kx_absdiff x y).1.2 = true → cx_val x + cx_val (kx_absdiff x y).1.1 = cx_val y) ∧
    ((kx_absdiff x y).1.2 = false → cx_val y + cx_val (kx_absdiff x y).1.1 = cx_val x) ∧
    (kx_absdiff x y).1.1.length = max x.length y.length ∧
    (kx_absdiff x y).2 ≤ 2 * max x.length y.length + 3 := by
  obtain ⟨h1, h2, h3⟩ := cx_sub_spec x y false
  obtain ⟨g1, g2, g3⟩ := cx_sub_spec y x false
  have hd := cx_val_lt (cx_sub x y false).1.1
  have he := cx_val_lt (cx_sub y x false).1.1
  rw [h2] at h1 hd
  rw [g2] at g1 he
  rw [max_comm] at g1 he g2 g3
  have hx : cx_val x < 2 ^ max x.length y.length :=
    lt_of_lt_of_le (cx_val_lt x) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hy : cx_val y < 2 ^ max x.length y.length :=
    lt_of_lt_of_le (cx_val_lt y) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  generalize 2 ^ max x.length y.length = P at *
  simp only [kx_absdiff]
  split_ifs with hb
  · rw [hb] at h1
    simp only [Bool.toNat_true, mul_one, Bool.toNat_false, add_zero] at h1
    have hb' : (cx_sub y x false).1.2 = false := by
      cases hb' : (cx_sub y x false).1.2 with
      | false => rfl
      | true =>
        rw [hb'] at g1
        simp only [Bool.toNat_true, mul_one, Bool.toNat_false, add_zero] at g1
        omega
    rw [hb'] at g1
    simp only [Bool.toNat_false, mul_zero, add_zero] at g1
    dsimp only
    refine ⟨fun _ => by omega, fun h => by simp at h, g2, by omega⟩
  · have hb' : (cx_sub x y false).1.2 = false := by simpa using hb
    rw [hb'] at h1
    simp only [Bool.toNat_false, mul_zero, add_zero] at h1
    dsimp only
    refine ⟨fun h => by simp at h, fun _ => by omega, h2, by omega⟩

/-! ## The Karatsuba recombination -/

/-- Middle coefficient `z₀ + z₂ ± m` (`neg = true`: add `m`; `neg = false`: subtract `m`). -/
def kx_mid (z0 z2 m : List Bool) (neg : Bool) : List Bool × ℕ :=
  let s := cx_add z0 z2 false
  if neg then
    let u := cx_add s.1 m false
    (u.1, s.2 + u.2)
  else
    let u := cx_sub s.1 m false
    (u.1.1, s.2 + u.2)

theorem kx_mid_spec (z0 z2 m : List Bool) (neg : Bool) :
    (neg = true → cx_val (kx_mid z0 z2 m neg).1 = cx_val z0 + cx_val z2 + cx_val m) ∧
    (neg = false → cx_val m ≤ cx_val z0 + cx_val z2 →
      cx_val (kx_mid z0 z2 m neg).1 + cx_val m = cx_val z0 + cx_val z2) ∧
    (kx_mid z0 z2 m neg).1.length ≤ max (max z0.length z2.length + 1) m.length + 1 ∧
    (kx_mid z0 z2 m neg).2
      ≤ (max z0.length z2.length + 1) + (max (max z0.length z2.length + 1) m.length + 1) := by
  obtain ⟨s1, s2, s3⟩ := cx_add_spec z0 z2 false
  simp only [Bool.toNat_false, add_zero] at s1
  cases neg with
  | true =>
    obtain ⟨u1, u2, u3⟩ := cx_add_spec (cx_add z0 z2 false).1 m false
    simp only [Bool.toNat_false, add_zero] at u1
    simp only [kx_mid, if_true]
    refine ⟨fun _ => by rw [u1, s1], fun h => by simp at h, by rw [u2, s2], by rw [u3, s2, s3]⟩
  | false =>
    obtain ⟨u1, u2, u3⟩ := cx_sub_spec (cx_add z0 z2 false).1 m false
    have hu := cx_val_lt (cx_sub (cx_add z0 z2 false).1 m false).1.1
    have hs : cx_val (cx_add z0 z2 false).1 < 2 ^ max (cx_add z0 z2 false).1.length m.length :=
      lt_of_lt_of_le (cx_val_lt _) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
    rw [u2] at u1 hu
    simp only [Bool.toNat_false, add_zero] at u1
    simp only [kx_mid, Bool.false_eq_true, if_false]
    refine ⟨fun h => by simp at h, fun _ hm => ?_, by rw [u2, s2]; omega, by rw [u3, s2, s3]⟩
    generalize 2 ^ max (cx_add z0 z2 false).1.length m.length = P at *
    cases hb : (cx_sub (cx_add z0 z2 false).1 m false).1.2 with
    | false =>
      rw [hb] at u1
      simp only [Bool.toNat_false, mul_zero, add_zero] at u1
      omega
    | true =>
      rw [hb] at u1
      simp only [Bool.toNat_true, mul_one] at u1
      omega

/-- Assemble `z₀ + 2^h (z₁ + 2^h z₂)` with `h = |sh|`. -/
def kx_asm (sh z0 z1 z2 : List Bool) : List Bool × ℕ :=
  let h2 := kx_shift sh z2
  let t := cx_add z1 h2.1 false
  let ht := kx_shift sh t.1
  let r := cx_add z0 ht.1 false
  (r.1, h2.2 + t.2 + ht.2 + r.2)

theorem kx_asm_spec (sh z0 z1 z2 : List Bool) :
    cx_val (kx_asm sh z0 z1 z2).1
      = cx_val z0 + 2 ^ sh.length * (cx_val z1 + 2 ^ sh.length * cx_val z2) ∧
    (kx_asm sh z0 z1 z2).2
      = (sh.length + 1) + (max z1.length (sh.length + z2.length) + 1) + (sh.length + 1)
        + (max z0.length (sh.length + (max z1.length (sh.length + z2.length) + 1)) + 1) := by
  obtain ⟨a1, a2, a3⟩ := kx_shift_spec sh z2
  obtain ⟨b1, b2, b3⟩ := cx_add_spec z1 (kx_shift sh z2).1 false
  obtain ⟨c1, c2, c3⟩ := kx_shift_spec sh (cx_add z1 (kx_shift sh z2).1 false).1
  obtain ⟨d1, d2, d3⟩ := cx_add_spec z0 (kx_shift sh (cx_add z1 (kx_shift sh z2).1 false).1).1
    false
  simp only [Bool.toNat_false, add_zero] at b1 d1
  simp only [kx_asm]
  refine ⟨by rw [d1, c1, b1, a1], ?_⟩
  rw [d3, c3, b3, a3, c2, b2, a2]

/-! ## Karatsuba multiplication -/

/-- Base case: schoolbook product, normalised to width `|x| + |y|`. -/
def kx_base (x y : List Bool) : List Bool × ℕ :=
  let p := cx_mul x y
  let t := kx_trunc2 x y p.1
  (t.1, p.2 + t.2 + 1)

/-- **Karatsuba multiplication** on bit lists: `(product of width |x| + |y|, cost)`. -/
def kx_kar : List Bool → List Bool → List Bool × ℕ
  | [], y => kx_base [] y
  | [a], y => kx_base [a] y
  | a :: b :: x', y =>
    let sx := kx_split (a :: b :: x') (a :: b :: x')
    let sy := kx_split (a :: b :: x') y
    let dx := kx_absdiff sx.1.1 sx.1.2
    let dy := kx_absdiff sy.1.1 sy.1.2
    let z0 := kx_kar sx.1.1 sy.1.1
    let z2 := kx_kar sx.1.2 sy.1.2
    let m := kx_kar dx.1.1 dy.1.1
    let z1 := kx_mid z0.1 z2.1 m.1 (dx.1.2 ^^ dy.1.2)
    let r := kx_asm sx.1.1 z0.1 z1.1 z2.1
    let f := kx_trunc2 (a :: b :: x') y r.1
    (f.1, sx.2 + sy.2 + dx.2 + dy.2 + z0.2 + z2.2 + m.2 + z1.2 + r.2 + f.2 + 1)
termination_by x _ => x.length
decreasing_by
  all_goals
    simp only [(kx_absdiff_spec _ _).2.2.1, kx_split_lo_length, kx_split_hi_length,
      List.length_cons]
    omega

theorem kx_base_val (x y : List Bool) : cx_val (kx_base x y).1 = cx_val x * cx_val y := by
  simp only [kx_base]
  rw [kx_trunc2_val _ _ _ (by
    rw [cx_mul_val, pow_add]
    exact Nat.mul_lt_mul'' (cx_val_lt x) (cx_val_lt y)), cx_mul_val]

theorem kx_kar_length (x y : List Bool) : (kx_kar x y).1.length = x.length + y.length := by
  match x with
  | [] => rw [kx_kar]; simp only [kx_base, kx_trunc2_length]
  | [a] => rw [kx_kar]; simp only [kx_base, kx_trunc2_length]
  | a :: b :: x' => rw [kx_kar]; simp only [kx_trunc2_length]

theorem kx_cross (x0 x1 y0 y1 dx dy : ℕ) (fx fy : Bool)
    (hx1 : fx = true → x0 + dx = x1) (hx2 : fx = false → x1 + dx = x0)
    (hy1 : fy = true → y0 + dy = y1) (hy2 : fy = false → y1 + dy = y0) :
    ((fx ^^ fy) = true → x0 * y0 + x1 * y1 + dx * dy = x0 * y1 + x1 * y0) ∧
    ((fx ^^ fy) = false → x0 * y1 + x1 * y0 + dx * dy = x0 * y0 + x1 * y1) := by
  cases fx <;> cases fy
  · have a := hx2 rfl; have b := hy2 rfl; subst a b
    exact ⟨fun h => absurd h (by decide), fun _ => by ring⟩
  · have a := hx2 rfl; have b := hy1 rfl; subst a b
    exact ⟨fun _ => by ring, fun h => absurd h (by decide)⟩
  · have a := hx1 rfl; have b := hy2 rfl; subst a b
    exact ⟨fun _ => by ring, fun h => absurd h (by decide)⟩
  · have a := hx1 rfl; have b := hy1 rfl; subst a b
    exact ⟨fun h => absurd h (by decide), fun _ => by ring⟩

theorem kx_kar_val_aux : ∀ (n : ℕ) (x y : List Bool), x.length ≤ n →
    cx_val (kx_kar x y).1 = cx_val x * cx_val y := by
  intro n
  induction n with
  | zero =>
    intro x y hx
    match x, hx with
    | [], _ => rw [kx_kar]; exact kx_base_val _ _
    | _ :: _, hx => simp at hx
  | succ n ih =>
    intro x y hx
    match x, hx with
    | [], _ => rw [kx_kar]; exact kx_base_val _ _
    | [a], _ => rw [kx_kar]; exact kx_base_val _ _
    | a :: b :: x', hx =>
      rw [kx_kar]
      dsimp only
      have hX : 2 ≤ (a :: b :: x').length := by simp
      generalize a :: b :: x' = X at *
      have l1 := kx_split_lo_length X X
      have l2 := kx_split_hi_length X X
      have vX := kx_split_val X X
      have vy := kx_split_val X y
      generalize kx_split X X = sx at *
      generalize kx_split X y = sy at *
      obtain ⟨dx1, dx2, dl, -⟩ := kx_absdiff_spec sx.1.1 sx.1.2
      obtain ⟨dy1, dy2, -, -⟩ := kx_absdiff_spec sy.1.1 sy.1.2
      generalize kx_absdiff sx.1.1 sx.1.2 = dx at *
      generalize kx_absdiff sy.1.1 sy.1.2 = dy at *
      have i0 := ih sx.1.1 sy.1.1 (by omega)
      have i2 := ih sx.1.2 sy.1.2 (by omega)
      have i1 := ih dx.1.1 dy.1.1 (by omega)
      generalize kx_kar sx.1.1 sy.1.1 = z0 at *
      generalize kx_kar sx.1.2 sy.1.2 = z2 at *
      generalize kx_kar dx.1.1 dy.1.1 = m at *
      obtain ⟨cr1, cr2⟩ := kx_cross _ _ _ _ _ _ _ _ dx1 dx2 dy1 dy2
      obtain ⟨m1, m2, -, -⟩ := kx_mid_spec z0.1 z2.1 m.1 (dx.1.2 ^^ dy.1.2)
      rw [i0, i2, i1] at m1 m2
      have hz1 : cx_val (kx_mid z0.1 z2.1 m.1 (dx.1.2 ^^ dy.1.2)).1
          = cx_val sx.1.1 * cx_val sy.1.2 + cx_val sx.1.2 * cx_val sy.1.1 := by
        cases hneg : (dx.1.2 ^^ dy.1.2) with
        | true =>
          have e1 := cr1 hneg
          rw [hneg] at m1
          have e2 := m1 rfl
          omega
        | false =>
          have e1 := cr2 hneg
          rw [hneg] at m2
          have e2 := m2 rfl (by omega)
          omega
      generalize kx_mid z0.1 z2.1 m.1 (dx.1.2 ^^ dy.1.2) = z1 at *
      obtain ⟨a1, -⟩ := kx_asm_spec sx.1.1 z0.1 z1.1 z2.1
      rw [l1, hz1, i0, i2] at a1
      have hr : cx_val (kx_asm sx.1.1 z0.1 z1.1 z2.1).1 = cx_val X * cx_val y := by
        rw [a1, vX, vy]; ring
      rw [kx_trunc2_val _ _ _ (by
        rw [hr, pow_add]
        exact Nat.mul_lt_mul'' (cx_val_lt X) (cx_val_lt y)), hr]

/-- **Karatsuba multiplication is correct** (for all inputs, of any lengths). -/
theorem kx_kar_val (x y : List Bool) : cx_val (kx_kar x y).1 = cx_val x * cx_val y :=
  kx_kar_val_aux x.length x y le_rfl

theorem kx_base_cost (k : ℕ) (x y : List Bool) (hxy : x.length = y.length)
    (h1 : x.length ≤ 1) : (kx_base x y).2 + 23 * 2 ^ k + 10 ≤ 44 * 3 ^ k := by
  have h23 : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hc := cx_mul_cost x y
  have hmul : (cx_mul x y).2 ≤ 7 := by
    rw [← hxy] at hc
    rcases (by omega : x.length = 0 ∨ x.length = 1) with h | h <;> rw [h] at hc <;> omega
  simp only [kx_base, kx_trunc2_cost]
  omega

/-- **Karatsuba cost.** On two `b`-bit inputs with `b ≤ 2^k`, Karatsuba multiplication uses at
most `44 · 3^k - 23 · 2^k - 10` bit steps. -/
theorem kx_kar_cost : ∀ (k : ℕ) (x y : List Bool), x.length = y.length → x.length ≤ 2 ^ k →
    (kx_kar x y).2 + 23 * 2 ^ k + 10 ≤ 44 * 3 ^ k := by
  intro k
  induction k with
  | zero =>
    intro x y hxy hk
    match x, hxy, hk with
    | [], hxy, _ => rw [kx_kar]; exact kx_base_cost 0 _ _ hxy (by simp)
    | [a], hxy, _ => rw [kx_kar]; exact kx_base_cost 0 _ _ hxy (by simp)
    | a :: b :: x', _, hk => simp only [List.length_cons, pow_zero] at hk; omega
  | succ k ih =>
    intro x y hxy hk
    match x, hxy, hk with
    | [], hxy, _ => rw [kx_kar]; exact kx_base_cost _ _ _ hxy (by simp)
    | [a], hxy, _ => rw [kx_kar]; exact kx_base_cost _ _ _ hxy (by simp)
    | a :: b :: x', hxy, hk =>
      rw [kx_kar]
      dsimp only
      have hX : 2 ≤ (a :: b :: x').length := by simp
      generalize a :: b :: x' = X at *
      have hpow2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      have hpow3 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
      rw [hpow2] at hk
      rw [hpow2, hpow3]
      have l1 := kx_split_lo_length X X
      have l2 := kx_split_hi_length X X
      have c1 := kx_split_cost X X
      have n1 := kx_split_lo_length X y
      have n2 := kx_split_hi_length X y
      have c2 := kx_split_cost X y
      generalize kx_split X X = sx at *
      generalize kx_split X y = sy at *
      obtain ⟨-, -, dl, dc⟩ := kx_absdiff_spec sx.1.1 sx.1.2
      obtain ⟨-, -, el, ec⟩ := kx_absdiff_spec sy.1.1 sy.1.2
      generalize kx_absdiff sx.1.1 sx.1.2 = dx at *
      generalize kx_absdiff sy.1.1 sy.1.2 = dy at *
      have i0 := ih sx.1.1 sy.1.1 (by omega) (by omega)
      have i2 := ih sx.1.2 sy.1.2 (by omega) (by omega)
      have i1 := ih dx.1.1 dy.1.1 (by omega) (by omega)
      have L0 := kx_kar_length sx.1.1 sy.1.1
      have L2 := kx_kar_length sx.1.2 sy.1.2
      have L1 := kx_kar_length dx.1.1 dy.1.1
      generalize kx_kar sx.1.1 sy.1.1 = z0 at *
      generalize kx_kar sx.1.2 sy.1.2 = z2 at *
      generalize kx_kar dx.1.1 dy.1.1 = m at *
      obtain ⟨-, -, ml, mc⟩ := kx_mid_spec z0.1 z2.1 m.1 (dx.1.2 ^^ dy.1.2)
      generalize kx_mid z0.1 z2.1 m.1 (dx.1.2 ^^ dy.1.2) = z1 at *
      obtain ⟨-, ac⟩ := kx_asm_spec sx.1.1 z0.1 z1.1 z2.1
      rw [kx_trunc2_cost, ac]
      omega

end DetPrimality.Complexity

#print axioms DetPrimality.Complexity.kx_kar_val
#print axioms DetPrimality.Complexity.kx_kar_cost
