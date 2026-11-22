import Mathlib
import DetPrimality.EndToEnd
import DetPrimality.Complexity.cx_Fast
import DetPrimality.Complexity.cx_Bits
import DetPrimality.Complexity.cx_MillerBits

/-!
# Running time of the deterministic Miller test: summary

Collects the main statements of `cx_Fast.lean` (Tier 1: number of modular multiplications),
`cx_Bits.lean` (schoolbook bit arithmetic) and `cx_MillerBits.lean` (Tier 2: bit operations),
and transfers the GRH-conditional correctness theorem `DetPrimality.millerDet_correct_of_GRH`.

All running-time bounds are **unconditional** and hold for every `n : ℕ`; only correctness
("the answer is `true` iff `n` is prime") uses GRH.  With `L = Nat.log2 n + 1` (the bit length
of `n` for `n ≠ 0`):

* `cx_millerDetFast n = Miller.millerDet 1 n`;
* modular multiplications `≤ L³`;
* bit steps, any modular multiplier of cost `M` : `≤ L³ · M(L) + 4 L⁴`;
* bit steps, schoolbook multiplication + shift-subtract remainder: `≤ 31 · L⁵`.

See the module docstrings of `cx_Bits.lean` and `cx_MillerBits.lean` for the precise cost model
(what is one bit step, and the three things assumed and not charged: binary input, unary loop
counters, and the base budget `millerBound 1 n - 2` supplied as a unary counter).
-/

namespace DetPrimality.Complexity

open DetPrimality DetPrimality.Miller

/-- Under GRH the fast deterministic Miller test decides primality. -/
theorem cx_millerDetFast_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    cx_millerDetFast n = true ↔ n.Prime := by
  rw [cx_millerDetFast_eq]
  exact millerDet_correct_of_GRH hGRH n

/-- **Tier 1.** The instrumented test returns the same answer as `millerDet 1 n` and uses at most
`(log₂ n + 1)³` modular multiplications (unconditionally, for every `n`). -/
theorem cx_millerDet_modmul_count (n : ℕ) :
    (cx_millerDetC n).1 = millerDet 1 n ∧ (cx_millerDetC n).2 ≤ (Nat.log2 n + 1) ^ 3 :=
  ⟨by rw [cx_millerDetC_fst, cx_millerDetFast_eq], cx_millerDetC_cost n⟩

/-- **Tier 2, generic multiplier.** For any bit-level modular multiplier `mm` with cost bound
`mm.M`, the bit-level test returns `millerDet 1 n` and costs at most `L³ · M(L) + 4 L⁴`. -/
theorem cx_millerDet_bit_cost_generic (mm : cx_ModMul) (n : ℕ) :
    (cx_millerDetB mm (millerBound 1 n - 2) (cx_bits n)).1 = millerDet 1 n ∧
    (cx_millerDetB mm (millerBound 1 n - 2) (cx_bits n)).2
      ≤ (Nat.log2 n + 1) ^ 3 * mm.M (Nat.log2 n + 1) + 4 * (Nat.log2 n + 1) ^ 4 :=
  ⟨by rw [cx_millerDetB_fst, cx_millerDetFast_eq], cx_millerDetB_cost mm n⟩

/-- **Tier 2, schoolbook arithmetic.** The bit-level test returns `millerDet 1 n` and costs at
most `31 · (log₂ n + 1)⁵` bit steps. -/
theorem cx_millerDet_bit_cost (n : ℕ) :
    (cx_millerDetBits n).1 = millerDet 1 n ∧ (cx_millerDetBits n).2 ≤ 31 * (Nat.log2 n + 1) ^ 5 :=
  ⟨cx_millerDetBits_fst n, cx_millerDetBits_cost n⟩

/-- **Deterministic polynomial-time primality under GRH.** The bit-level program decides
primality (under GRH) within `31 · (log₂ n + 1)⁵` bit steps (unconditionally). -/
theorem cx_millerDetBits_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    ((cx_millerDetBits n).1 = true ↔ n.Prime) ∧
    (cx_millerDetBits n).2 ≤ 31 * (Nat.log2 n + 1) ^ 5 := by
  refine ⟨?_, cx_millerDetBits_cost n⟩
  rw [cx_millerDetBits_fst]
  exact millerDet_correct_of_GRH hGRH n

end DetPrimality.Complexity

#print axioms DetPrimality.Complexity.cx_millerDetFast_eq
#print axioms DetPrimality.Complexity.cx_millerDetFast_correct_of_GRH
#print axioms DetPrimality.Complexity.cx_millerDet_modmul_count
#print axioms DetPrimality.Complexity.cx_mulmod_val
#print axioms DetPrimality.Complexity.cx_mulmod_cost
#print axioms DetPrimality.Complexity.cx_millerDet_bit_cost_generic
#print axioms DetPrimality.Complexity.cx_millerDet_bit_cost
#print axioms DetPrimality.Complexity.cx_millerDetBits_correct_of_GRH
