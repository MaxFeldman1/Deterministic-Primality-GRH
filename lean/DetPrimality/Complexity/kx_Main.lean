import Mathlib
import DetPrimality.Complexity.cx_Main
import DetPrimality.Complexity.kx_Karatsuba
import DetPrimality.Complexity.kx_Barrett

/-!
# Deterministic Miller test with Karatsuba multiplication and Barrett reduction: bit cost

Cost model: exactly that of `cx_Bits.lean` / `cx_MillerBits.lean` (one unit = one constant-size
bit step; all values are produced by Boolean operations on bit lists; `ℕ` only counts cost; the
same three conventions as in `cx_MillerBits.lean`: binary input, unary loop counters, the base
budget supplied in unary).

The program `kx_millerDetK n`:

1. computes the Barrett constant `μ = ⌊4^b / n⌋` **once**, by schoolbook division
   (`kx_mu`, cost `4 b² + 13 b + 6`, charged);
2. runs the bit-level Miller test `cx_millerDetB` of `cx_MillerBits.lean` with the modular
   multiplier `kx_barrettMM μ` (`kx_barrett`: three Karatsuba products and `O(b)` correction
   steps per modular multiplication, everything charged).

`kx_barrettMM μ` is a genuine `cx_ModMul` for *every* `μ` (the value is always right because of
the checked fallback to `cx_mod`), but its uniform cost bound is only quadratic, since for a
modulus other than the one `μ` was computed for the fallback may be taken.  The sharp bound is
obtained through `kx_barrettDev`, a *proof device* (never executed): it agrees with
`kx_barrettMM μ` on the modulus `N` actually used, and `cx_millerDetB` only ever calls the
multiplier with that modulus (`kx_millerDetB_congr`).

Main results (`L = Nat.log2 n + 1`):
* `kx_millerDet_bit_cost_karatsuba` :
  value `= millerDet 1 n`, cost `≤ 220 · L³ · 3^⌈log₂ L⌉ + 4 L⁴ + 4 L² + 13 L + 6`;
* `kx_millerDet_bit_cost_karatsuba_pow` : the same with `3^k` for any `k` with `L ≤ 2^k`;
* `kx_millerDet_bit_cost_karatsuba_real` : cost `≤ 687 · L^4.585` (as `log₂ 3 < 1.585`).
-/

namespace DetPrimality.Complexity

open DetPrimality DetPrimality.Miller

theorem kx_le_pow_clog (b : ℕ) : b ≤ 2 ^ Nat.clog 2 b := Nat.le_pow_clog (by norm_num) b

/-! ## Modular multipliers -/

/-- Karatsuba product followed by the schoolbook shift-subtract remainder (still quadratic,
because of the remainder). -/
def kx_karatsubaModMul : cx_ModMul where
  run := fun x y n =>
    let p := kx_kar x y
    let r := cx_mod p.1 n
    (r.1, p.2 + r.2)
  M := fun b => 44 * 3 ^ Nat.clog 2 b + 4 * b ^ 2 + 9 * b + 1
  run_val := fun x y n _ _ hx _ => by
    simp only [cx_mod_val _ _ (show 0 < cx_val n by omega), kx_kar_val]
  run_length := fun x y n _ _ _ _ => by simp only [cx_mod_length]
  run_cost := fun x y n hx hy _ _ => by
    have c := kx_kar_cost (Nat.clog 2 n.length) x y (by omega)
      (by rw [hx]; exact kx_le_pow_clog _)
    have e : (n.length + n.length) * (2 * n.length + 4) = 4 * n.length ^ 2 + 8 * n.length := by
      ring
    simp only [cx_mod_cost, kx_kar_length, hx, hy, e]
    omega

/-- Karatsuba + Barrett modular multiplier with precomputed constant `mu`.  Correct for every
`mu`; the uniform cost bound is the (weak) one including the fallbacks. -/
def kx_barrettMM (mu : List Bool) : cx_ModMul where
  run := fun x y n => kx_barrett mu x y n
  M := fun b => 220 * 3 ^ Nat.clog 2 b + 4 * b ^ 2 + 8 * b
  run_val := fun x y n _ _ hx _ => kx_barrett_val mu x y n (by omega)
  run_length := fun x y n _ _ _ _ => kx_barrett_length mu x y n
  run_cost := fun x y n hx hy _ _ => kx_barrett_cost_weak _ mu x y n hx hy (kx_le_pow_clog _)

open Classical in
/-- Proof device (not a program): agrees with `kx_barrettMM mu` at the modulus `N` when `mu` is
the Barrett constant of `N`, and reports cost `0` elsewhere.  Its cost bound is the sharp one. -/
noncomputable def kx_barrettDev (N mu : List Bool) : cx_ModMul where
  run := fun x y n =>
    if n = N ∧ kx_IsMu N mu then kx_barrett mu x y n else ((kx_barrett mu x y n).1, 0)
  M := fun b => 220 * 3 ^ Nat.clog 2 b
  run_val := fun x y n _ _ hx _ => by
    split_ifs <;> exact kx_barrett_val mu x y n (by omega)
  run_length := fun x y n _ _ _ _ => by
    split_ifs <;> exact kx_barrett_length mu x y n
  run_cost := fun x y n hx hy hxv hyv => by
    split_ifs with h
    · obtain ⟨h1, hmu⟩ := h
      subst h1
      exact kx_barrett_cost _ mu x y _ hx hy hxv hyv hmu (kx_le_pow_clog _)
    · exact Nat.zero_le _

/-! ## The Miller test only uses the multiplier at its own modulus -/

section congr

variable (mm mm' : cx_ModMul) (n : List Bool) (h : ∀ x y, mm.run x y n = mm'.run x y n)
include h

theorem kx_powB_congr (one a e : List Bool) :
    cx_powB mm n one a e = cx_powB mm' n one a e := by
  induction e with
  | nil => rfl
  | cons b e ih => simp only [cx_powB, ih, h]

theorem kx_sqLoopB_congr (nm1 : List Bool) (k : ℕ) (x : List Bool) :
    cx_sqLoopB mm n nm1 k x = cx_sqLoopB mm' n nm1 k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [cx_sqLoopB, h, ih]

theorem kx_sprpB_congr (one nm1 d : List Bool) (s : ℕ) (a : List Bool) :
    cx_sprpB mm n one nm1 d s a = cx_sprpB mm' n one nm1 d s a := by
  simp only [cx_sprpB, kx_powB_congr mm mm' n h, kx_sqLoopB_congr mm mm' n h]

theorem kx_loopB_congr (one nm1 d : List Bool) (s k : ℕ) (a : List Bool) :
    cx_loopB mm n one nm1 d s k a = cx_loopB mm' n one nm1 d s k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [cx_loopB, kx_sprpB_congr mm mm' n h, ih]

theorem kx_millerMainB_congr (cnt : ℕ) (nm1 : List Bool) :
    cx_millerMainB mm cnt n nm1 = cx_millerMainB mm' cnt n nm1 := by
  simp only [cx_millerMainB, kx_loopB_congr mm mm' n h]

theorem kx_millerDetB_congr (cnt : ℕ) :
    cx_millerDetB mm cnt n = cx_millerDetB mm' cnt n := by
  match n, h with
  | [], _ => rfl
  | [false], _ => rfl
  | false :: false :: _, _ => rfl
  | [false, true], _ => rfl
  | false :: true :: _ :: _, _ => rfl
  | [true], _ => rfl
  | true :: b :: t, h =>
    simp only [cx_millerDetB]
    exact kx_millerMainB_congr mm mm' _ h _ _

end congr

/-! ## The complete test -/

/-- The deterministic Miller test at bit level with Karatsuba multiplication and Barrett
reduction: `(answer, cost)`.  The Barrett constant is computed (and charged) once. -/
def kx_millerDetK (n : ℕ) : Bool × ℕ :=
  let N := cx_bits n
  let mu := kx_mu N
  let r := cx_millerDetB (kx_barrettMM mu.1) (millerBound 1 n - 2) N
  (r.1, mu.2 + r.2)

/-- **Karatsuba + Barrett bound.** With `L = log₂ n + 1`: the bit-level test returns
`millerDet 1 n` and costs at most `220 · L³ · 3^⌈log₂ L⌉ + 4 L⁴ + 4 L² + 13 L + 6` bit steps
(`3^⌈log₂ L⌉ ≤ 3 · L^{log₂ 3}`), for every `n`. -/
theorem kx_millerDet_bit_cost_karatsuba (n : ℕ) :
    (kx_millerDetK n).1 = millerDet 1 n ∧
    (kx_millerDetK n).2
      ≤ 220 * (Nat.log2 n + 1) ^ 3 * 3 ^ Nat.clog 2 (Nat.log2 n + 1)
        + 4 * (Nat.log2 n + 1) ^ 4 + 4 * (Nat.log2 n + 1) ^ 2 + 13 * (Nat.log2 n + 1) + 6 := by
  refine ⟨(cx_millerDet_bit_cost_generic (kx_barrettMM (kx_mu (cx_bits n)).1) n).1, ?_⟩
  have hmc := kx_mu_cost (cx_bits n)
  simp only [kx_millerDetK]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hmc]
    simp [cx_bits_zero, cx_millerDetB]
  · have hlen := cx_bits_length (show n ≠ 0 by omega)
    have hval := cx_val_bits n
    have hmu := kx_mu_isMu (cx_bits n) (by rw [hval]; exact hn)
    have hcongr := kx_millerDetB_congr (kx_barrettMM (kx_mu (cx_bits n)).1)
      (kx_barrettDev (cx_bits n) (kx_mu (cx_bits n)).1) (cx_bits n)
      (fun x y => by simp [kx_barrettMM, kx_barrettDev, hmu]) (millerBound 1 n - 2)
    have hc := cx_millerDetB_cost (kx_barrettDev (cx_bits n) (kx_mu (cx_bits n)).1) n
    have hM : (kx_barrettDev (cx_bits n) (kx_mu (cx_bits n)).1).M (Nat.log2 n + 1)
        = 220 * 3 ^ Nat.clog 2 (Nat.log2 n + 1) := rfl
    rw [hM] at hc
    rw [hcongr, hmc, hlen]
    have e : (Nat.log2 n + 1) ^ 3 * (220 * 3 ^ Nat.clog 2 (Nat.log2 n + 1))
        = 220 * (Nat.log2 n + 1) ^ 3 * 3 ^ Nat.clog 2 (Nat.log2 n + 1) := by ring
    rw [e] at hc
    omega

/-- The same bound with `3^k` for any `k` such that `L = log₂ n + 1 ≤ 2^k`. -/
theorem kx_millerDet_bit_cost_karatsuba_pow (n k : ℕ) (hk : Nat.log2 n + 1 ≤ 2 ^ k) :
    (kx_millerDetK n).2
      ≤ 220 * (Nat.log2 n + 1) ^ 3 * 3 ^ k
        + 4 * (Nat.log2 n + 1) ^ 4 + 4 * (Nat.log2 n + 1) ^ 2 + 13 * (Nat.log2 n + 1) + 6 := by
  have h := (kx_millerDet_bit_cost_karatsuba n).2
  have h3 : 3 ^ Nat.clog 2 (Nat.log2 n + 1) ≤ 3 ^ k :=
    Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow hk)
  have := Nat.mul_le_mul_left (220 * (Nat.log2 n + 1) ^ 3) h3
  omega

/-- Under GRH the Karatsuba/Barrett bit-level program decides primality. -/
theorem kx_millerDetK_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    (kx_millerDetK n).1 = true ↔ n.Prime := by
  rw [(kx_millerDet_bit_cost_karatsuba n).1]
  exact millerDet_correct_of_GRH hGRH n

/-! ## Real exponents -/

set_option exponentiation.threshold 400 in
theorem kx_logb_two_three_le : Real.logb 2 3 ≤ 317 / 200 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
  have keyN : (3 : ℕ) ^ 200 ≤ 2 ^ 317 := Nat.le_of_ble_eq_true rfl
  have key : (3 : ℝ) ^ (200 : ℕ) ≤ (2 : ℝ) ^ (317 : ℕ) := by exact_mod_cast keyN
  rw [← Real.rpow_le_rpow_iff (by norm_num) (by positivity)
    (show (0 : ℝ) < ((200 : ℕ) : ℝ) by norm_num), ← Real.rpow_mul (by norm_num),
    Real.rpow_natCast]
  have e : ((317 : ℝ) / 200 * ((200 : ℕ) : ℝ)) = ((317 : ℕ) : ℝ) := by norm_num
  rw [e, Real.rpow_natCast]
  exact key

/-- `3^⌈log₂ L⌉ ≤ 3 · L^{log₂ 3}`. -/
theorem kx_three_pow_clog_le (L : ℕ) (hL : 1 ≤ L) :
    (3 : ℝ) ^ Nat.clog 2 L ≤ 3 * (L : ℝ) ^ Real.logb 2 3 := by
  rcases (by omega : L = 1 ∨ 2 ≤ L) with rfl | h2
  · simp
  · have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < L by omega)
    have hc : 0 < Nat.clog 2 L := Nat.clog_pos (by norm_num) (by omega)
    obtain ⟨m, hm⟩ : ∃ m, Nat.clog 2 L = m + 1 := ⟨Nat.clog 2 L - 1, by omega⟩
    rw [hm] at hlt ⊢
    simp only [Nat.pred_succ] at hlt
    have h3 : (3 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ Real.logb 2 3 := by
      rw [← Real.rpow_natCast 2 m, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
        Real.rpow_natCast]
    have hle : (2 : ℝ) ^ m ≤ (L : ℝ) := by exact_mod_cast hlt.le
    rw [pow_succ', h3]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hle (Real.logb_nonneg (by norm_num) (by norm_num)))
      (by norm_num)

/-- **Karatsuba cost with the real exponent**: at most `132 · b^{log₂ 3}` bit steps on two
`b`-bit inputs (`b ≥ 1`). -/
theorem kx_kar_cost_real (x y : List Bool) (hxy : x.length = y.length) (hx : 1 ≤ x.length) :
    ((kx_kar x y).2 : ℝ) ≤ 132 * (x.length : ℝ) ^ Real.logb 2 3 := by
  have h := kx_kar_cost (Nat.clog 2 x.length) x y hxy (kx_le_pow_clog _)
  have h' : (kx_kar x y).2 ≤ 44 * 3 ^ Nat.clog 2 x.length := by omega
  have h'' : ((kx_kar x y).2 : ℝ) ≤ 44 * (3 : ℝ) ^ Nat.clog 2 x.length := by exact_mod_cast h'
  have := kx_three_pow_clog_le x.length hx
  linarith

/-- **Karatsuba + Barrett bound with a real exponent.** The deterministic Miller test costs at
most `687 · (log₂ n + 1)^4.585` bit steps (`3 + log₂ 3 < 4.585`), for every `n`. -/
theorem kx_millerDet_bit_cost_karatsuba_real (n : ℕ) :
    ((kx_millerDetK n).2 : ℝ) ≤ 687 * ((Nat.log2 n + 1 : ℕ) : ℝ) ^ (4.585 : ℝ) := by
  have h := (kx_millerDet_bit_cost_karatsuba n).2
  have hL : 0 < Nat.log2 n + 1 := Nat.succ_pos _
  generalize Nat.log2 n + 1 = L at h hL ⊢
  have hx : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h' : ((kx_millerDetK n).2 : ℝ) ≤ 220 * (L : ℝ) ^ 3 * (3 : ℝ) ^ Nat.clog 2 L
      + 4 * (L : ℝ) ^ 4 + 4 * (L : ℝ) ^ 2 + 13 * (L : ℝ) + 6 := by exact_mod_cast h
  have hc := kx_three_pow_clog_le L hL
  have hc' : (3 : ℝ) ^ Nat.clog 2 L ≤ 3 * (L : ℝ) ^ ((317 : ℝ) / 200) :=
    hc.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx kx_logb_two_three_le) (by norm_num))
  have e : (4.585 : ℝ) = ((3 : ℕ) : ℝ) + 317 / 200 := by norm_num
  have hR : (L : ℝ) ^ (4.585 : ℝ) = (L : ℝ) ^ 3 * (L : ℝ) ^ ((317 : ℝ) / 200) := by
    rw [e, Real.rpow_add (by linarith), Real.rpow_natCast]
  have hp : ∀ j : ℕ, (j : ℝ) ≤ 4.585 → (L : ℝ) ^ j ≤ (L : ℝ) ^ (4.585 : ℝ) := fun j hj => by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx hj
  have p4 := hp 4 (by norm_num)
  have p2 := hp 2 (by norm_num)
  have p1 : (L : ℝ) ≤ (L : ℝ) ^ (4.585 : ℝ) := by simpa using hp 1 (by norm_num)
  have p0 : (1 : ℝ) ≤ (L : ℝ) ^ (4.585 : ℝ) := by simpa using hp 0 (by norm_num)
  have hmain : (L : ℝ) ^ 3 * (3 : ℝ) ^ Nat.clog 2 L
      ≤ (L : ℝ) ^ 3 * (3 * (L : ℝ) ^ ((317 : ℝ) / 200)) :=
    mul_le_mul_of_nonneg_left hc' (by positivity)
  rw [hR] at p4 p2 p1 p0 ⊢
  nlinarith

end DetPrimality.Complexity

#print axioms DetPrimality.Complexity.kx_kar_val
#print axioms DetPrimality.Complexity.kx_kar_cost
#print axioms DetPrimality.Complexity.kx_kar_cost_real
#print axioms DetPrimality.Complexity.kx_barrett_val
#print axioms DetPrimality.Complexity.kx_barrett_cost
#print axioms DetPrimality.Complexity.kx_karatsubaModMul
#print axioms DetPrimality.Complexity.kx_barrettMM
#print axioms DetPrimality.Complexity.kx_millerDet_bit_cost_karatsuba
#print axioms DetPrimality.Complexity.kx_millerDet_bit_cost_karatsuba_pow
#print axioms DetPrimality.Complexity.kx_millerDet_bit_cost_karatsuba_real
#print axioms DetPrimality.Complexity.kx_millerDetK_correct_of_GRH
