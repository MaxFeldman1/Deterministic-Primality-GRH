import Mathlib
import DetPrimality.Miller.Basic

/-!
# Running time of the deterministic Miller test, Tier 1: number of modular multiplications

`Miller.sprp` recomputes `powMod a (d * 2 ^ r) n` for every `r < s`.  This file defines the
textbook strong-probable-prime test

* `cx_sprpFast n a` : one `powMod a d n` (`n - 1 = 2 ^ s * d`), then at most `s - 1` modular
  squarings, with early exit;
* `cx_millerDetFast n` : the deterministic Miller test over the *same* base range as
  `Miller.millerDet 1 n`, i.e. `2 ≤ a < min (millerBound 1 n) n`;

and proves `cx_millerDetFast n = Miller.millerDet 1 n` for all `n` (`cx_millerDetFast_eq`), so
every correctness theorem about `millerDet 1` transfers.

## Cost model of this file (Tier 1)

One unit of cost = one modular multiplication `x * y % n` with `x, y < n` (a modular squaring is
one modular multiplication).  The instrumented functions `cx_powModC`, `cx_sqLoopC`, `cx_sprpC`,
`cx_millerDetC` return explicit pairs `(value, cost)`, where `cost` is incremented by one exactly
at each occurrence of `_ * _ % n` in the code.  Nothing else is charged in this file (comparisons,
the decomposition `n - 1 = 2 ^ s * d`, loop control: these are charged in the bit-level model of
`cx_MillerBits.lean`).

Main results:
* `cx_millerDetC_fst : (cx_millerDetC n).1 = cx_millerDetFast n`;
* `cx_millerDetC_cost : (cx_millerDetC n).2 ≤ (Nat.log2 n + 1) ^ 3` for **all** `n`
  (at most `(log₂ n + 1)² / 2` bases, at most `2 (log₂ n + 1)` modular multiplications per base).
The bound is unconditional (no GRH): the base loop is bounded by construction.
-/

namespace DetPrimality.Complexity

open DetPrimality DetPrimality.Miller

/-! ## The fast strong-probable-prime test -/

/-- Squaring loop: tests `x, x², x⁴, … , x^(2^(k-1))` (mod `n`) against `n - 1`, with early exit;
performs at most `k - 1` modular squarings. -/
def cx_sqLoop (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, x =>
    if x = n - 1 then true
    else if k = 0 then false
    else cx_sqLoop n k (x * x % n)

/-- Textbook strong probable prime test: `x = a^d mod n` once, then repeated squaring. -/
def cx_sprpFast (n a : ℕ) : Bool :=
  let p := oddDecomp (n - 1)
  let x := powMod a p.2 n
  if x = 1 then true else cx_sqLoop n p.1 x

/-- Deterministic Miller test with the fast `sprp`; same base range as `Miller.millerDet 1`. -/
def cx_millerDetFast (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else (List.range' 2 (min (millerBound 1 n) n - 2)).all (fun a => cx_sprpFast n a)

theorem cx_sqLoop_eq (n k x : ℕ) (hx : x < n) :
    cx_sqLoop n k x = (List.range k).any (fun r => x ^ 2 ^ r % n == n - 1) := by
  induction k generalizing x with
  | zero => simp [cx_sqLoop]
  | succ k ih =>
    rw [cx_sqLoop, List.range_succ_eq_map, List.any_cons, List.any_map]
    by_cases h : x = n - 1
    · simp [h, Nat.mod_eq_of_lt (show n - 1 < n by omega)]
    · have h0 : (x ^ 2 ^ 0 % n == n - 1) = false := by
        simp [Nat.mod_eq_of_lt hx, h]
      rw [if_neg h, h0, Bool.false_or]
      by_cases hk : k = 0
      · subst hk; simp
      · rw [if_neg hk, ih (x * x % n) (Nat.mod_lt _ (by omega))]
        congr 1
        funext r
        simp only [Function.comp]
        have : (x * x % n) ^ 2 ^ r % n = x ^ 2 ^ (r + 1) % n := by
          rw [← Nat.pow_mod, ← pow_two, ← pow_mul, ← pow_succ']
        rw [this]

theorem cx_sprpFast_eq {n : ℕ} (hn : 1 < n) (a : ℕ) : cx_sprpFast n a = sprp n a := by
  have hlt : powMod a (oddDecomp (n - 1)).2 n < n := by
    rw [powMod_eq]; exact Nat.mod_lt _ (by omega)
  have hfun : (fun r => powMod a (oddDecomp (n - 1)).2 n ^ 2 ^ r % n == n - 1)
      = (fun r => powMod a ((oddDecomp (n - 1)).2 * 2 ^ r) n == n - 1) := by
    funext r
    rw [powMod_eq, powMod_eq, ← Nat.pow_mod, ← pow_mul]
  simp only [cx_sprpFast, sprp, twoVal, oddPart]
  rw [cx_sqLoop_eq n _ _ hlt, hfun]
  by_cases h : powMod a (oddDecomp (n - 1)).2 n = 1 <;> simp [h]

/-- **The fast test computes the same Boolean as `Miller.millerDet 1`, for every `n`.** -/
theorem cx_millerDetFast_eq (n : ℕ) : cx_millerDetFast n = millerDet 1 n := by
  unfold cx_millerDetFast millerDet
  by_cases h1 : n < 2
  · simp [h1]
  have hfun : (fun a => cx_sprpFast n a) = (fun a => sprp n a) := by
    funext a; exact cx_sprpFast_eq (by omega) a
  rw [hfun]

/-! ## Instrumented versions: counting modular multiplications -/

/-- `powMod` with a counter of modular multiplications. -/
def cx_powModC (a e n : ℕ) : ℕ × ℕ :=
  if h : e = 0 then (1 % n, 0)
  else
    let r := cx_powModC a (e / 2) n
    if e % 2 = 0 then (r.1 * r.1 % n, r.2 + 1) else (r.1 * r.1 % n * a % n, r.2 + 2)
termination_by e
decreasing_by omega

theorem cx_powModC_fst (a e n : ℕ) : (cx_powModC a e n).1 = powMod a e n := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [cx_powModC, powMod]
    dsimp only
    split_ifs with h0 h2
    · rfl
    · simp only [ih (e / 2) (by omega)]
    · simp only [ih (e / 2) (by omega)]

theorem cx_powModC_cost (a e n : ℕ) : (cx_powModC a e n).2 ≤ 2 * (Nat.log2 e + 1) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [cx_powModC]
    dsimp only
    split_ifs with h0 h2
    · simp
    · have h := ih (e / 2) (by omega)
      by_cases he : 2 ≤ e
      · rw [Nat.log2_def e, if_pos he]; simp only; omega
      · have : e / 2 = 0 := by omega
        rw [this] at h ⊢
        rw [cx_powModC]; simp; omega
    · have h := ih (e / 2) (by omega)
      by_cases he : 2 ≤ e
      · rw [Nat.log2_def e, if_pos he]; simp only; omega
      · have : e / 2 = 0 := by omega
        rw [this] at h ⊢
        rw [cx_powModC]; simp

/-- `cx_sqLoop` with a counter of modular squarings. -/
def cx_sqLoopC (n : ℕ) : ℕ → ℕ → Bool × ℕ
  | 0, _ => (false, 0)
  | k + 1, x =>
    if x = n - 1 then (true, 0)
    else if k = 0 then (false, 0)
    else
      let r := cx_sqLoopC n k (x * x % n)
      (r.1, r.2 + 1)

theorem cx_sqLoopC_fst (n k x : ℕ) : (cx_sqLoopC n k x).1 = cx_sqLoop n k x := by
  induction k generalizing x with
  | zero => simp [cx_sqLoopC, cx_sqLoop]
  | succ k ih =>
    rw [cx_sqLoopC, cx_sqLoop]
    split_ifs <;> simp [ih]

theorem cx_sqLoopC_cost (n k x : ℕ) : (cx_sqLoopC n k x).2 ≤ k - 1 := by
  induction k generalizing x with
  | zero => simp [cx_sqLoopC]
  | succ k ih =>
    rw [cx_sqLoopC]
    split_ifs with h1 h2
    · simp
    · simp
    · have := ih (x * x % n)
      simp only
      omega

/-- `cx_sprpFast` with a counter of modular multiplications. -/
def cx_sprpC (n a : ℕ) : Bool × ℕ :=
  let p := oddDecomp (n - 1)
  let x := cx_powModC a p.2 n
  if x.1 = 1 then (true, x.2)
  else
    let r := cx_sqLoopC n p.1 x.1
    (r.1, x.2 + r.2)

theorem cx_sprpC_fst (n a : ℕ) : (cx_sprpC n a).1 = cx_sprpFast n a := by
  simp only [cx_sprpC, cx_sprpFast, cx_powModC_fst]
  split_ifs <;> simp [cx_sqLoopC_fst]

/-- `2 ^ s * d = m`, `m ≠ 0` ⟹ `s + log₂ d ≤ log₂ m`. -/
theorem cx_log2_decomp {s d m : ℕ} (h : 2 ^ s * d = m) (hm : m ≠ 0) :
    s + Nat.log2 d ≤ Nat.log2 m := by
  have hd : d ≠ 0 := by rintro rfl; simp at h; omega
  have h1 : 2 ^ Nat.log2 d ≤ d := Nat.log2_self_le hd
  have h2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  have h3 : 2 ^ (s + Nat.log2 d) < 2 ^ (Nat.log2 m + 1) := by
    calc 2 ^ (s + Nat.log2 d) = 2 ^ s * 2 ^ Nat.log2 d := pow_add 2 _ _
      _ ≤ 2 ^ s * d := Nat.mul_le_mul_left _ h1
      _ = m := h
      _ < _ := h2
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

/-- At most `2 (log₂ n + 1)` modular multiplications per base. -/
theorem cx_sprpC_cost {n : ℕ} (hn : 2 ≤ n) (a : ℕ) :
    (cx_sprpC n a).2 ≤ 2 * (Nat.log2 n + 1) := by
  have hsd := (oddDecomp_spec (n - 1)).1
  have h1 := cx_log2_decomp hsd (by omega)
  have h2 : Nat.log2 (n - 1) ≤ Nat.log2 n := by
    have ha : 2 ^ Nat.log2 (n - 1) ≤ n - 1 := Nat.log2_self_le (by omega)
    have hb : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
    have hc : 2 ^ Nat.log2 (n - 1) < 2 ^ (Nat.log2 n + 1) := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hc
    omega
  have h3 := cx_powModC_cost a (oddDecomp (n - 1)).2 n
  have h4 := cx_sqLoopC_cost n (oddDecomp (n - 1)).1 (cx_powModC a (oddDecomp (n - 1)).2 n).1
  simp only [cx_sprpC]
  split_ifs
  · simp only; omega
  · simp only; omega

/-- A costed, early-exit `List.all`. -/
def cx_allC (f : ℕ → Bool × ℕ) : List ℕ → Bool × ℕ
  | [] => (true, 0)
  | a :: l =>
    let r := f a
    if r.1 then
      let t := cx_allC f l
      (t.1, r.2 + t.2)
    else (false, r.2)

theorem cx_allC_fst (f : ℕ → Bool × ℕ) (l : List ℕ) :
    (cx_allC f l).1 = l.all (fun a => (f a).1) := by
  induction l with
  | nil => simp [cx_allC]
  | cons a l ih =>
    rw [cx_allC]
    by_cases h : (f a).1 = true <;> simp [h, ih]

theorem cx_allC_cost (f : ℕ → Bool × ℕ) (B : ℕ) (hf : ∀ a, (f a).2 ≤ B) (l : List ℕ) :
    (cx_allC f l).2 ≤ l.length * B := by
  induction l with
  | nil => simp [cx_allC]
  | cons a l ih =>
    rw [cx_allC]
    have := hf a
    rw [List.length_cons, Nat.add_mul, one_mul]
    by_cases h : (f a).1 = true
    · simp only [h, if_true]; omega
    · simp only [h]
      have : 0 ≤ l.length * B := Nat.zero_le _
      simp only [Bool.false_eq_true, if_false]
      omega

/-- The deterministic Miller test with a counter of modular multiplications. -/
def cx_millerDetC (n : ℕ) : Bool × ℕ :=
  if n < 2 then (false, 0)
  else if n = 2 then (true, 0)
  else if n % 2 = 0 then (false, 0)
  else cx_allC (cx_sprpC n) (List.range' 2 (min (millerBound 1 n) n - 2))

theorem cx_millerDetC_fst (n : ℕ) : (cx_millerDetC n).1 = cx_millerDetFast n := by
  unfold cx_millerDetC cx_millerDetFast
  split_ifs
  · rfl
  · rfl
  · rfl
  · rw [cx_allC_fst]
    simp only [cx_sprpC_fst]

/-- The base bound: `2 · millerBound 1 n ≤ (log₂ n + 1)² + 1`. -/
theorem cx_two_mul_millerBound_le (n : ℕ) :
    2 * millerBound 1 n ≤ (Nat.log2 n + 1) ^ 2 + 1 := by
  have key : millerBound 1 n ≤ ((Nat.log2 n + 1) ^ 2 + 1) / 2 := by
    unfold millerBound log2SqUpper
    apply Nat.ceil_le.mpr
    have h : (Nat.log2 n + 1) ^ 2 ≤ 2 * (((Nat.log2 n + 1) ^ 2 + 1) / 2) := by omega
    have h' : (((Nat.log2 n + 1 : ℕ) : ℚ)) ^ 2
        ≤ 2 * ((((Nat.log2 n + 1) ^ 2 + 1) / 2 : ℕ) : ℚ) := by exact_mod_cast h
    have h0 : (0 : ℚ) ≤ (((Nat.log2 n + 1 : ℕ) : ℚ)) ^ 2 := sq_nonneg _
    linarith
  omega

/-- Number of bases tried: `2 · #bases ≤ (log₂ n + 1)²`. -/
theorem cx_two_mul_numBases_le (n : ℕ) :
    2 * (min (millerBound 1 n) n - 2) ≤ (Nat.log2 n + 1) ^ 2 := by
  have := cx_two_mul_millerBound_le n
  omega

/-- **Tier 1 bound.** For every `n`, the fast deterministic Miller test performs at most
`(log₂ n + 1)³` modular multiplications. -/
theorem cx_millerDetC_cost (n : ℕ) : (cx_millerDetC n).2 ≤ (Nat.log2 n + 1) ^ 3 := by
  unfold cx_millerDetC
  split_ifs with h1 h2 h3
  · simp
  · simp
  · simp
  · have hB := cx_allC_cost (cx_sprpC n) (2 * (Nat.log2 n + 1))
      (fun a => cx_sprpC_cost (by omega) a) (List.range' 2 (min (millerBound 1 n) n - 2))
    rw [List.length_range'] at hB
    have h := cx_two_mul_numBases_le n
    calc _ ≤ (min (millerBound 1 n) n - 2) * (2 * (Nat.log2 n + 1)) := hB
      _ = 2 * (min (millerBound 1 n) n - 2) * (Nat.log2 n + 1) := by ring
      _ ≤ (Nat.log2 n + 1) ^ 2 * (Nat.log2 n + 1) := Nat.mul_le_mul_right _ h
      _ = (Nat.log2 n + 1) ^ 3 := by ring

end DetPrimality.Complexity

