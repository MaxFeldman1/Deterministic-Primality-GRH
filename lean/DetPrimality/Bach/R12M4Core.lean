import Mathlib
import DetPrimality.Bach.R12M4Char
import DetPrimality.Bach.R11AsmReal

/-!
# Round 12 (miller4.md), part 2: the basic inequality for `(h, λ) = (4, 1/4)`

`H ≤ (ZMod n)ˣ` of index `≥ 4` containing every `1 ≤ a < X = W⁴`; `x = 4X`, `lo = 1.38629 ≤ log 4`.
`r12_core` is miller4.md (M8) multiplied by `X/…`: with `B` the uniform upper bound for
`Re Φ_χ̃(4X)` (`R11ChiExplicit` + `R11ZeroSumGain`, `log q_χ ≤ log n`) and `S = ∑_{m<X}Λ(m)√m log³(4X/m)`,

  `(1 + |T|) S ≤ A₃(4X) + |T| B`, `|T| ≥ 3`, `S ≤ A₃(4X)`  ⟹  `4 S ≤ A₃(4X) + 3 B`

(monotonicity in the index), and the ζ-side is bounded as in Round 11.  The displayed inequality
is this one divided by `3`:  `7.4904 = 8 D₄` (`D₄ = 0.9363`), so `c∞ = (6/7.4904)² < 0.64165`.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

theorem r12_log4_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

theorem r12_log4_ge : (1.38629 : ℝ) ≤ Real.log 4 := by
  rw [r12_log4_eq]; have := Real.log_two_gt_d9; linarith

theorem r12_log4_le : Real.log 4 ≤ (1.3863 : ℝ) := by
  rw [r12_log4_eq]; have := Real.log_two_lt_d9; linarith

theorem r12_Tlt_ge {X lo : ℝ} (hX : 0 < X) (hlo0 : 0 ≤ lo) (hlo : lo ≤ Real.log 4) :
    lo ^ 3 * r11A 0 X + 3 * lo ^ 2 * r11A 1 X + 3 * lo * r11A 2 X + r11A 3 X
      ≤ ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (4 * X / m) ^ 3 := by
  calc lo ^ 3 * r11A 0 X + 3 * lo ^ 2 * r11A 1 X + 3 * lo * r11A 2 X + r11A 3 X
      = ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * (lo + Real.log (X / m)) ^ 3 := by
        unfold r11A
        simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun m hm => ?_
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp
        · have hlt : (m : ℝ) < X := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
          have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos
          have hlog : 0 ≤ Real.log (X / m) :=
            Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
          have e : Real.log (4 * X / m) = Real.log 4 + Real.log (X / m) := by
            rw [mul_div_assoc, Real.log_mul (by norm_num) (by positivity)]
          rw [e]
          have h3 : (lo + Real.log (X / m)) ^ 3 ≤ (Real.log 4 + Real.log (X / m)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 3
          exact mul_le_mul_of_nonneg_left h3
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))

/-- **miller4.md (M8)** for index `≥ 4`, `λ = 1/4`, multiplied by `X = W⁴` and divided by `3`. -/
theorem r12_core (hGRH : DirichletLZerosOnLine) (hZ : R11ZetaZ) (hA : R11ZetaExplicit)
    (hC : R11ChiExplicit) (hG : R11ZeroSumGain) {n : ℕ} (hn : 2 < n)
    (H : Subgroup (ZMod n)ˣ) (h4 : 4 ≤ H.index) {W : ℝ} (hW : 3 ≤ W)
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < W ^ 4 →
      IsUnit (a : ZMod n) ∧ ∀ u : (ZMod n)ˣ, (u : ZMod n) = a → u ∈ H) :
    7.4904 * W ^ 6 - 1.5403 * W ^ 5 + 74.0104 * W ^ 4
      ≤ 6 * Real.log n * W ^ 4 + 24 * r11T (W ^ 4) * W ^ 4
        + (Real.log n + 1.30) * Real.log (4 * W ^ 4) ^ 3
        + 27.93 * Real.log (4 * W ^ 4) ^ 2 + 98.73 * Real.log (4 * W ^ 4) + 198.31
        + 16.3849 * r11r 1 (W ^ 4) * W + 7.6872 * r11r 1 (W ^ 4)
        + 5.5452 * r11r 2 (W ^ 4) + 4 / 3 * r11r 3 (W ^ 4) + 1 / 3 * r11r 3 (4 * W ^ 4) := by
  have hW0 : 0 < W := by linarith
  have hNZ : NeZero n := ⟨by omega⟩
  obtain ⟨hZ2, hZ4⟩ := hZ hGRH
  have hZ3 := r11Asm_Z3 hGRH hZ
  set X := W ^ 4 with hXdef
  have hX81 : (81 : ℝ) ≤ X := by
    rw [hXdef]
    calc (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ W ^ 4 := pow_le_pow_left₀ (by norm_num) hW 4
  have hX0 : 0 < X := by linarith
  have hX1 : (1 : ℝ) < X := by linarith
  have hx1 : (1 : ℝ) < 4 * X := by linarith
  have hlam0 : 0 ≤ Real.log (4 * X) := Real.log_nonneg hx1.le
  -- every `χ ∈ T` is `1` below `X`
  have hχa : ∀ χ ∈ r12T H, ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → χ (a : ZMod n) = 1 := by
    intro χ hχ a ha hax
    obtain ⟨hu, hmem⟩ := h a ha hax
    have := (r12_mem_T.mp hχ).2 hu.unit (hmem hu.unit hu.unit_spec)
    rwa [hu.unit_spec] at this
  -- the L-side, uniformly in `χ ∈ T`
  have hB : ∀ χ ∈ r12T H, (r11Phi χ.primitiveCharacter (4 * X)).re
      ≤ 6 * X * (Real.log n - 12.4 + 4 * r11T X) + (Real.log n + 1.30) * Real.log (4 * X) ^ 3
        + 27.93 * Real.log (4 * X) ^ 2 + 98.73 * Real.log (4 * X) + 198.31 := by
    intro χ hχ
    obtain ⟨-, hprim, hne, hq0, -, hlq0, hlq, hχ1, -⟩ :=
      llsElem_no_witness_facts hn χ (r12_mem_T.mp hχ).1 (hχa χ hχ)
    have : NeZero χ.conductor := ⟨hq0⟩
    have hΦ := hC hGRH χ.conductor χ.primitiveCharacter hprim hne (4 * X) hx1
    have hZχ := hG hGRH χ.conductor χ.primitiveCharacter hprim hne X hX1.le hχ1
    have b5 : 6 * (4 * X) * r11Z χ.primitiveCharacter 4
        ≤ 6 * (4 * X) * ((Real.log χ.conductor - 12.4 + 4 * r11T X) / 4) :=
      mul_le_mul_of_nonneg_left hZχ (by positivity)
    have b6 : Real.log χ.conductor * X ≤ Real.log n * X :=
      mul_le_mul_of_nonneg_right hlq hX0.le
    have b7 : Real.log χ.conductor * Real.log (4 * X) ^ 3 ≤ Real.log n * Real.log (4 * X) ^ 3 :=
      mul_le_mul_of_nonneg_right hlq (by positivity)
    linarith
  have hS1 := r12_sum_ge H (by linarith : X ≤ 4 * X) (fun χ hχ m hm hmX => by
    obtain ⟨-, -, -, -, -, -, -, hχ1, -⟩ :=
      llsElem_no_witness_facts hn χ (r12_mem_T.mp hχ).1 (hχa χ hχ)
    exact hχ1 m hm hmX)
  have hcard : (3 : ℝ) ≤ ((r12T H).card : ℝ) := by exact_mod_cast r12_three_le_card H h4
  have hSle := r12_S_le_A3 (by linarith : X ≤ 4 * X)
  have hsumB := Finset.sum_le_card_nsmul _ _ _ hB
  rw [nsmul_eq_mul] at hsumB
  have hS2 := r12_Tlt_ge hX0 (by norm_num) r12_log4_ge
  -- the ζ-side
  have hA0 := r11Asm_A0_ge hGRH hZ hA hW
  have hA1 := (abs_le.mp (r11Asm_A1 hGRH hA hX1)).1
  have hA2 := (abs_le.mp (r11Asm_A2 hGRH hA hX1)).1
  have hA3 := (abs_le.mp (r11Asm_A3 hGRH hA hX1)).1
  have hA3x := (abs_le.mp (r11Asm_A3 hGRH hA hx1)).2
  have hXp : X ^ ((3 : ℝ) / 2) = W ^ 6 := r11Asm_rpow_W hW0
  have hxp : (4 * X) ^ ((3 : ℝ) / 2) = 8 * W ^ 6 := by
    rw [r11Asm_rpow32 (by linarith), hXdef, show 4 * W ^ 4 = (2 * W ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    ring
  rw [hXp] at hA1 hA2 hA3
  rw [hxp] at hA3x
  rw [← hXdef] at hA0
  set lam := Real.log (4 * X) with hlam
  set L := Real.log n with hL
  set T := r11T X
  set B := 6 * X * (L - 12.4 + 4 * T) + (L + 1.30) * lam ^ 3 + 27.93 * lam ^ 2 + 98.73 * lam
    + 198.31 with hBdef
  set SP := ∑ χ ∈ r12T H, (r11Phi χ.primitiveCharacter (4 * X)).re
  set t := ((r12T H).card : ℝ)
  set S := ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (4 * X / m) ^ 3
  set A0 := r11A 0 X
  set A1 := r11A 1 X
  set A2 := r11A 2 X
  set A3 := r11A 3 X
  set A3x := r11A 3 (4 * X)
  set r1 := r11r 1 X
  set r2 := r11r 2 X
  set r3 := r11r 3 X
  set r3x := r11r 3 (4 * X)
  set Z2 := r11Z χ₁ 2
  set Z3 := r11Z χ₁ 3
  set Z4 := r11Z χ₁ 4
  -- monotonicity in the index: only `t ≥ 3` is used
  have h4S : 4 * S ≤ A3x + 3 * B := by
    rcases le_total S B with hSB | hSB
    · linarith
    · have := mul_nonneg (sub_nonneg.mpr hcard) (sub_nonneg.mpr hSB)
      nlinarith
  have b1 : Z2 * X ≤ 0.047 * X := mul_le_mul_of_nonneg_right hZ2 hX0.le
  have b2 : 2 * Z3 * X ≤ 2 * 0.002375 * X := by nlinarith
  have b3 : 6 * Z4 * X ≤ 6 * 0.00012 * X := by nlinarith
  have b4 : 6 * Z4 * (4 * X) ≤ 6 * 0.00012 * (4 * X) := by nlinarith
  have hW6 : 0 < W ^ 6 := by positivity
  have hW5 : 0 < W ^ 5 := by positivity
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1.le
  have hr1 : 0 ≤ r1 := by
    show 0 ≤ r11r 1 X
    rw [r11Asm_r1]; positivity
  have hr2 : 0 ≤ r2 := by
    show 0 ≤ r11r 2 X
    rw [r11Asm_r2]; positivity
  have hr1W : 0 ≤ r1 * W := mul_nonneg hr1 hW0.le
  rw [hBdef] at h4S
  linarith

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r12_core
