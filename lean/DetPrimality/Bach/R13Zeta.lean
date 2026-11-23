import Mathlib
import DetPrimality.Bach.R13Defs
import DetPrimality.Bach.R11AsmCore
import DetPrimality.Bach.R11ZetaX
import DetPrimality.Bach.R11ZeroSum

/-!
# Round 13, (P1): `R13ZetaSmooth`

Under RH, for every `i`, `A_i(Y) = i! (2/3)^{i+1} Y^{3/2} + O(Y^{5/4})` on `Y ≥ 1`.

Route (formal076 §4.2), in the variable `W = Y^{1/4}` (so that everything is polynomial in `W`):
* `r13Z_A1` : `|A₁(y) - (4/9) y^{3/2}| ≤ 3y` from `R11ZetaExplicit` (`j = 1`) and `R11ZetaZ`;
* `r13Z_A0` : `i = 0`, two-sided, by differencing `A₁` at `X e^{±δ}`, `δ = 1/(2W)`;
* `r13Z_step` : `i → i + 1` (`i ≥ 1`) from `d/dw A_{i+1}(w⁴) = 4(i+1) A_i(w⁴)/w`
  (the termwise form of `A_i(Y) = i ∫_1^Y A_{i-1}(u) du/u`) and monotonicity;
* `r13Z_main : R13ZetaSmooth`.
Only the `j = 1` case of `R11ZetaExplicit` is used.
-/

open Complex DirichletCharacter Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-- The main-term constant `i! (2/3)^{i+1}`. -/
noncomputable def r13Z_c (i : ℕ) : ℝ := (i.factorial : ℝ) * (2 / 3) ^ (i + 1)

theorem r13Z_c_nonneg (i : ℕ) : 0 ≤ r13Z_c i := by unfold r13Z_c; positivity

theorem r13Z_c_succ (i : ℕ) : 6 * r13Z_c (i + 1) = 4 * ((i : ℝ) + 1) * r13Z_c i := by
  unfold r13Z_c
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- `A_i(y) = 0` for `y ≤ 2`. -/
theorem r13Z_A_zero (i : ℕ) {y : ℝ} (hy : y ≤ 2) : r11A i y = 0 := by
  unfold r11A
  refine Finset.sum_eq_zero fun n hn => ?_
  have h2 : ⌈y⌉₊ ≤ 2 := Nat.ceil_le.mpr (by exact_mod_cast hy)
  have hn2 : n < 2 := lt_of_lt_of_le (Finset.mem_range.mp hn) h2
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl <;> simp

/-! ## `i = 1` -/

theorem r13Z_A1 (hGRH : DirichletLZerosOnLine) {y : ℝ} (hy : 1 ≤ y) :
    |r11A 1 y - 4 / 9 * y ^ ((3 : ℝ) / 2)| ≤ 3 * y := by
  rcases hy.eq_or_lt with rfl | hy'
  · rw [r13Z_A_zero 1 (by norm_num), Real.one_rpow, abs_le]
    constructor <;> norm_num
  · have h := r11Asm_A1 hGRH (r11Zx_main_of_zetaZ r11Zs_zeta) hy'
    rw [r11Asm_r1] at h
    have hZ2 := (r11Zs_zeta hGRH).1
    have hl := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < y)
    have h1 : r11Z χ₁ 2 * y ≤ 0.047 * y := mul_le_mul_of_nonneg_right hZ2 (by linarith)
    refine h.trans ?_
    linarith

/-! ## `i = 0` by differencing -/

/-- Mirror image of `r11Asm_A1_diff`. -/
theorem r13Z_A1_diff_up {X δ : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ) :
    r11A 1 X + δ * r11A 0 X ≤ r11A 1 (X * Real.exp δ) := by
  set Z := X * Real.exp δ with hZ
  have hZ0 : 0 < Z := by positivity
  have hXZ : X ≤ Z := by
    rw [hZ]
    have : 1 ≤ Real.exp δ := Real.one_le_exp hδ
    nlinarith
  have hlogZ : Real.log Z = Real.log X + δ := by
    rw [hZ, Real.log_mul hX.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hsub : Finset.range ⌈X⌉₊ ⊆ Finset.range ⌈Z⌉₊ := Finset.range_mono (Nat.ceil_mono hXZ)
  have e1 : r11A 1 X + δ * r11A 0 X
      = ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * (Real.log (X / m) + δ) := by
    unfold r11A
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have e2 : r11A 1 Z = ∑ m ∈ Finset.range ⌈Z⌉₊, Λ m * √(m : ℝ) * Real.log (Z / m) := by
    unfold r11A
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [e1, e2, ← Finset.sum_sdiff hsub]
  have h2 : 0 ≤ ∑ m ∈ Finset.range ⌈Z⌉₊ \ Finset.range ⌈X⌉₊,
      Λ m * √(m : ℝ) * Real.log (Z / m) := by
    refine Finset.sum_nonneg fun m hm => ?_
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hm
    have hXm : X ≤ m := Nat.ceil_le.mp hm.2
    have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hX hXm
    have hmZ : (m : ℝ) < Z := Nat.lt_ceil.mp hm.1
    have hl : 0 ≤ Real.log (Z / m) := Real.log_nonneg (by rw [one_le_div hm0]; exact hmZ.le)
    exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)) hl
  have h3 : ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * (Real.log (X / m) + δ)
      = ∑ m ∈ Finset.range ⌈X⌉₊, Λ m * √(m : ℝ) * Real.log (Z / m) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos
      rw [Real.log_div hX.ne' hm0.ne', Real.log_div hZ0.ne' hm0.ne', hlogZ]
      ring
  linarith

theorem r13Z_A0 (hGRH : DirichletLZerosOnLine) {W : ℝ} (hW : 1 ≤ W) :
    |r11A 0 (W ^ 4) - 2 / 3 * W ^ 6| ≤ 20 * W ^ 5 := by
  have hW0 : 0 < W := by linarith
  have hW5 : 0 < W ^ 5 := by positivity
  have hXp : (W ^ 4) ^ ((3 : ℝ) / 2) = W ^ 6 := r11Asm_rpow_W hW0
  set X := W ^ 4 with hXdef
  have hWX : W ≤ X := le_self_pow₀ hW (by norm_num)
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  rcases le_or_gt X 2 with hX2 | hX2
  · rw [r13Z_A_zero 0 hX2]
    have hW2 : W ≤ 2 := by linarith
    have h6 : W ^ 6 = W * W ^ 5 := by ring
    have h7 : W * W ^ 5 ≤ 2 * W ^ 5 := mul_le_mul_of_nonneg_right hW2 hW5.le
    have h8 : 0 ≤ W * W ^ 5 := by positivity
    rw [abs_le, h6]
    constructor <;> linarith
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (2 * W) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδ]; positivity
    have hδ1 : δ ≤ 1 / 2 := by
      rw [hδ, div_le_iff₀ (by positivity)]; linarith
    have hδW : δ * W = 1 / 2 := by rw [hδ]; field_simp
    -- lower point
    have hexp : 1 - δ ≤ Real.exp (-δ) := by
      have := Real.add_one_le_exp (-δ); linarith
    have hexp1 : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hY1 : 1 ≤ X * Real.exp (-δ) := by nlinarith
    have hYX : X * Real.exp (-δ) ≤ X := by nlinarith
    have hYp : (X * Real.exp (-δ)) ^ ((3 : ℝ) / 2)
        ≤ W ^ 6 * (1 - 3 / 2 * δ + (3 / 2 * δ) ^ 2 / 2) := by
      rw [Real.mul_rpow hX0.le (Real.exp_pos _).le, hXp, ← Real.exp_mul]
      have h1 : -δ * (3 / 2) = -(3 / 2 * δ) := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left (r11Asm_exp_neg_le (by positivity)) (by positivity)
    -- upper point
    have hexpu : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Real.exp t ≤ 1 + t + t ^ 2 := by
      intro t ht0 ht1
      have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := t)
        (by rw [abs_of_nonneg ht0]; exact ht1))).2
      linarith
    have hexp2 : Real.exp δ ≤ 2 := by
      have := hexpu δ hδ0.le (by linarith)
      nlinarith
    have hexp3 : 1 ≤ Real.exp δ := Real.one_le_exp hδ0.le
    have hZ1 : 1 ≤ X * Real.exp δ := by nlinarith
    have hZX : X * Real.exp δ ≤ 2 * X := by nlinarith
    have hZp : (X * Real.exp δ) ^ ((3 : ℝ) / 2)
        ≤ W ^ 6 * (1 + 3 / 2 * δ + (3 / 2 * δ) ^ 2) := by
      rw [Real.mul_rpow hX0.le (Real.exp_pos _).le, hXp, ← Real.exp_mul]
      have h1 : δ * (3 / 2) = 3 / 2 * δ := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left (hexpu _ (by positivity) (by linarith)) (by positivity)
    have hdn := r11Asm_A1_diff hX0 hδ0.le
    have hup := r13Z_A1_diff_up hX0 hδ0.le
    have aX := abs_le.mp (r13Z_A1 hGRH hX1)
    have aY := abs_le.mp (r13Z_A1 hGRH hY1)
    have aZ := abs_le.mp (r13Z_A1 hGRH hZ1)
    rw [hXp] at aX
    set A0 := r11A 0 X
    set A1X := r11A 1 X
    set A1Y := r11A 1 (X * Real.exp (-δ))
    set A1Z := r11A 1 (X * Real.exp δ)
    have hYp' := mul_le_mul_of_nonneg_left hYp (by norm_num : (0 : ℝ) ≤ 4 / 9)
    have hZp' := mul_le_mul_of_nonneg_left hZp (by norm_num : (0 : ℝ) ≤ 4 / 9)
    have h5 : 4 / 9 * W ^ 6 * (3 / 2 * δ - (3 / 2 * δ) ^ 2 / 2) - 6 * X ≤ δ * A0 := by
      linarith [aX.1, aY.2]
    have h7 : δ * A0 ≤ 4 / 9 * W ^ 6 * (3 / 2 * δ + (3 / 2 * δ) ^ 2) + 9 * X := by
      linarith [aX.1, aZ.2]
    have h5' := mul_le_mul_of_nonneg_right h5 hW0.le
    have h7' := mul_le_mul_of_nonneg_right h7 hW0.le
    have e1 : (4 / 9 * W ^ 6 * (3 / 2 * δ - (3 / 2 * δ) ^ 2 / 2) - 6 * X) * W
        = 2 / 3 * (δ * W) * W ^ 6 - 1 / 2 * (δ * W) ^ 2 * W ^ 5 - 6 * W ^ 5 := by
      rw [hXdef]; ring
    have e2 : (4 / 9 * W ^ 6 * (3 / 2 * δ + (3 / 2 * δ) ^ 2) + 9 * X) * W
        = 2 / 3 * (δ * W) * W ^ 6 + (δ * W) ^ 2 * W ^ 5 + 9 * W ^ 5 := by
      rw [hXdef]; ring
    have e3 : δ * A0 * W = δ * W * A0 := by ring
    rw [e1, e3, hδW] at h5'
    rw [e2, e3, hδW] at h7'
    rw [abs_le]
    constructor <;> linarith

/-! ## The induction step -/

theorem r13Z_hasDerivAt_pos (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (max s 0) ^ (k + 2)) (((k : ℝ) + 2) * (max t 0) ^ (k + 1)) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have he : (fun s : ℝ => (max s 0) ^ (k + 2)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [max_eq_right (le_of_lt hs)]; simp
    rw [max_eq_right ht.le]
    have h0 : ((k : ℝ) + 2) * (0 : ℝ) ^ (k + 1) = 0 := by simp
    rw [h0]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he
  · have h0 : ((k : ℝ) + 2) * (max (0 : ℝ) 0) ^ (k + 1) = 0 := by simp
    rw [h0, hasDerivAt_iff_tendsto_slope]
    have hc : Tendsto (fun s : ℝ => (max s 0) ^ (k + 1)) (𝓝[≠] 0) (𝓝 0) := by
      have hcont : Continuous fun s : ℝ => (max s 0) ^ (k + 1) := by fun_prop
      have h := hcont.tendsto 0
      simp only [max_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 0 := hs
    rw [slope_def_field, max_self, zero_pow (by omega), sub_zero, sub_zero, eq_div_iff hs']
    rcases le_or_gt s 0 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h.le]; ring
  · have he : (fun s : ℝ => (max s 0) ^ (k + 2)) =ᶠ[𝓝 t] fun s => s ^ (k + 2) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [max_eq_left (le_of_lt hs)]
    rw [max_eq_left ht.le]
    have h := (hasDerivAt_pow (k + 2) t).congr_of_eventuallyEq he
    refine h.congr_deriv ?_
    rw [show k + 2 - 1 = k + 1 by omega]
    push_cast
    ring

/-- `A_j(w⁴)` as a sum over a fixed range, for `j ≥ 1`. -/
theorem r13Z_A_eq {j : ℕ} (hj : j ≠ 0) {w : ℝ} (hw : 0 < w) {N : ℕ} (hN : ⌈w ^ 4⌉₊ ≤ N) :
    r11A j (w ^ 4)
      = ∑ n ∈ Finset.range N, Λ n * √(n : ℝ) * (max (4 * Real.log w - Real.log n) 0) ^ j := by
  unfold r11A
  have hlog : Real.log (w ^ 4) = 4 * Real.log w := by rw [Real.log_pow]; norm_num
  have hw4 : 0 < w ^ 4 := by positivity
  rw [← Finset.sum_subset (Finset.range_mono hN)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
      have hlt : (n : ℝ) < w ^ 4 := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
      have h1 := Real.log_le_log hn0 hlt.le
      rw [hlog] at h1
      rw [Real.log_div hw4.ne' hn0.ne', hlog, max_eq_left (by linarith)]
  · intro n _ hn
    rw [Finset.mem_range, not_lt] at hn
    have hle : w ^ 4 ≤ n := Nat.ceil_le.mp hn
    have h1 := Real.log_le_log hw4 hle
    rw [hlog] at h1
    rw [max_eq_right (by linarith), zero_pow hj, mul_zero]

theorem r13Z_hasDerivAt_sum (k N : ℕ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun w : ℝ => ∑ n ∈ Finset.range N,
        Λ n * √(n : ℝ) * (max (4 * Real.log w - Real.log n) 0) ^ (k + 2))
      (4 * ((k : ℝ) + 2) / w * ∑ n ∈ Finset.range N,
        Λ n * √(n : ℝ) * (max (4 * Real.log w - Real.log n) 0) ^ (k + 1)) w := by
  have h1 : ∀ n : ℕ, HasDerivAt (fun w : ℝ => 4 * Real.log w - Real.log n) (4 / w) w := fun n =>
    (((Real.hasDerivAt_log hw.ne').const_mul 4).sub_const _).congr_deriv (by ring)
  have h2 : ∀ n : ℕ, HasDerivAt
      (fun w : ℝ => Λ n * √(n : ℝ) * (max (4 * Real.log w - Real.log n) 0) ^ (k + 2))
      (Λ n * √(n : ℝ) * ((((k : ℝ) + 2) * (max (4 * Real.log w - Real.log n) 0) ^ (k + 1))
        * (4 / w))) w := fun n =>
    ((r13Z_hasDerivAt_pos k (4 * Real.log w - Real.log n)).comp w (h1 n)).const_mul _
  have h3 := HasDerivAt.fun_sum (u := Finset.range N) fun n _ => h2 n
  refine h3.congr_deriv ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem r13Z_mvt {H H' : ℝ → ℝ} {D W0 : ℝ} (hW : 1 ≤ W0)
    (hH : ∀ w, 1 ≤ w → w ≤ W0 → HasDerivAt H (H' w) w)
    (hb : ∀ w, 1 ≤ w → w ≤ W0 → |H' w| ≤ D * w ^ 4) :
    |H W0 - H 1| ≤ D / 5 * (W0 ^ 5 - 1) := by
  have hP : ∀ w : ℝ, HasDerivAt (fun w : ℝ => D / 5 * w ^ 5) (D * w ^ 4) w := fun w => by
    have h := (hasDerivAt_pow 5 w).const_mul (D / 5)
    refine h.congr_deriv ?_
    push_cast
    ring
  have h1 : AntitoneOn (fun w => H w - D / 5 * w ^ 5) (Set.Icc 1 W0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 1 W0)
    · exact fun w hw => ((hH w hw.1 hw.2).sub (hP w)).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      exact ((hH w hw.1.le hw.2.le).sub (hP w)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hd : HasDerivAt (fun w => H w - D / 5 * w ^ 5) (H' w - D * w ^ 4) w :=
        (hH w hw.1.le hw.2.le).sub (hP w)
      rw [hd.deriv]
      have := (abs_le.mp (hb w hw.1.le hw.2.le)).2
      linarith
  have h2 : MonotoneOn (fun w => H w + D / 5 * w ^ 5) (Set.Icc 1 W0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 1 W0)
    · exact fun w hw => ((hH w hw.1 hw.2).add (hP w)).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      exact ((hH w hw.1.le hw.2.le).add (hP w)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hd : HasDerivAt (fun w => H w + D / 5 * w ^ 5) (H' w + D * w ^ 4) w :=
        (hH w hw.1.le hw.2.le).add (hP w)
      rw [hd.deriv]
      have := (abs_le.mp (hb w hw.1.le hw.2.le)).1
      linarith
  have a := h1 (Set.left_mem_Icc.mpr hW) (Set.right_mem_Icc.mpr hW) hW
  have b := h2 (Set.left_mem_Icc.mpr hW) (Set.right_mem_Icc.mpr hW) hW
  simp only [one_pow, mul_one] at a b
  rw [abs_le]
  constructor <;> linarith

theorem r13Z_step (k : ℕ) {C : ℝ}
    (h : ∀ W : ℝ, 1 ≤ W → |r11A (k + 1) (W ^ 4) - r13Z_c (k + 1) * W ^ 6| ≤ C * W ^ 5) :
    ∀ W : ℝ, 1 ≤ W → |r11A (k + 2) (W ^ 4) - r13Z_c (k + 2) * W ^ 6|
      ≤ (r13Z_c (k + 2) + 4 * ((k : ℝ) + 2) * C) * W ^ 5 := by
  intro W0 hW0
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (h 1 le_rfl)
    simpa using this
  have hc2 := r13Z_c_nonneg (k + 2)
  have hcs : 6 * r13Z_c (k + 2) = 4 * ((k : ℝ) + 2) * r13Z_c (k + 1) := by
    have := r13Z_c_succ (k + 1)
    push_cast at this
    rw [show k + 1 + 1 = k + 2 from rfl] at this
    linarith
  set N := ⌈W0 ^ 4⌉₊ with hN
  set E : ℝ → ℝ := fun w => ∑ n ∈ Finset.range N,
    Λ n * √(n : ℝ) * (max (4 * Real.log w - Real.log n) 0) ^ (k + 2) with hE
  have hceil : ∀ w : ℝ, 0 < w → w ≤ W0 → ⌈w ^ 4⌉₊ ≤ N := fun w hw hle =>
    Nat.ceil_mono (pow_le_pow_left₀ hw.le hle 4)
  have hmvt := r13Z_mvt (H := fun w => E w - r13Z_c (k + 2) * w ^ 6)
    (H' := fun w => 4 * ((k : ℝ) + 2) / w * r11A (k + 1) (w ^ 4) - r13Z_c (k + 2) * (6 * w ^ 5))
    (D := 4 * ((k : ℝ) + 2) * C) hW0
    (by
      intro w hw1 hwW
      have hw0 : 0 < w := by linarith
      have hd := r13Z_hasDerivAt_sum k N hw0
      rw [← r13Z_A_eq (by omega) hw0 (hceil w hw0 hwW)] at hd
      have hp : HasDerivAt (fun w : ℝ => r13Z_c (k + 2) * w ^ 6)
          (r13Z_c (k + 2) * (6 * w ^ 5)) w := by
        have h6 := (hasDerivAt_pow 6 w).const_mul (r13Z_c (k + 2))
        refine h6.congr_deriv ?_
        push_cast
        ring
      exact hd.sub hp)
    (by
      intro w hw1 hwW
      have hw0 : 0 < w := by linarith
      have hq := h w hw1
      have e1 : r13Z_c (k + 2) * (6 * w ^ 5) = 4 * ((k : ℝ) + 2) * r13Z_c (k + 1) * w ^ 5 := by
        linear_combination w ^ 5 * hcs
      have e2 : 4 * ((k : ℝ) + 2) / w * r11A (k + 1) (w ^ 4) - r13Z_c (k + 2) * (6 * w ^ 5)
          = 4 * ((k : ℝ) + 2) / w * (r11A (k + 1) (w ^ 4) - r13Z_c (k + 1) * w ^ 6) := by
        rw [e1]; field_simp
      have hpos : 0 ≤ 4 * ((k : ℝ) + 2) / w := by positivity
      rw [e2, abs_mul, abs_of_nonneg hpos]
      calc 4 * ((k : ℝ) + 2) / w * |r11A (k + 1) (w ^ 4) - r13Z_c (k + 1) * w ^ 6|
          ≤ 4 * ((k : ℝ) + 2) / w * (C * w ^ 5) := mul_le_mul_of_nonneg_left hq hpos
        _ = 4 * ((k : ℝ) + 2) * C * w ^ 4 := by field_simp)
  have hEW : E W0 = r11A (k + 2) (W0 ^ 4) :=
    (r13Z_A_eq (by omega) (by linarith) le_rfl).symm
  have hE1 : E 1 = 0 := by
    have := (r13Z_A_eq (j := k + 2) (by omega) (w := 1) one_pos (hceil 1 one_pos hW0)).symm
    rw [hE]
    simp only
    rw [this]
    exact r13Z_A_zero _ (by norm_num)
  simp only [hEW, hE1, one_pow, mul_one, zero_sub] at hmvt
  have hW5 : 1 ≤ W0 ^ 5 := one_le_pow₀ hW0
  have hD : 0 ≤ 4 * ((k : ℝ) + 2) * C := by positivity
  have hm := abs_le.mp hmvt
  have p1 : 0 ≤ r13Z_c (k + 2) * (W0 ^ 5 - 1) := mul_nonneg hc2 (by linarith)
  have p2 : 0 ≤ 4 * ((k : ℝ) + 2) * C * (W0 ^ 5 - 1) := mul_nonneg hD (by linarith)
  rw [abs_le]
  constructor <;> nlinarith

/-! ## All orders -/

theorem r13Z_all (hGRH : DirichletLZerosOnLine) (i : ℕ) :
    ∃ C : ℝ, ∀ W : ℝ, 1 ≤ W → |r11A i (W ^ 4) - r13Z_c i * W ^ 6| ≤ C * W ^ 5 := by
  have hsucc : ∀ k : ℕ, ∃ C : ℝ, ∀ W : ℝ, 1 ≤ W →
      |r11A (k + 1) (W ^ 4) - r13Z_c (k + 1) * W ^ 6| ≤ C * W ^ 5 := by
    intro k
    induction k with
    | zero =>
      refine ⟨3, fun W hW => ?_⟩
      have hW0 : 0 < W := by linarith
      have hX1 : (1 : ℝ) ≤ W ^ 4 := one_le_pow₀ hW
      have h := r13Z_A1 hGRH hX1
      rw [r11Asm_rpow_W hW0] at h
      have hc : r13Z_c (0 + 1) = 4 / 9 := by unfold r13Z_c; norm_num [Nat.factorial]
      rw [hc]
      refine h.trans ?_
      have h4 : 0 < W ^ 4 := by positivity
      nlinarith
    | succ k ih =>
      obtain ⟨C, hC⟩ := ih
      exact ⟨_, r13Z_step k hC⟩
  rcases i with _ | k
  · refine ⟨20, fun W hW => ?_⟩
    have hc : r13Z_c 0 = 2 / 3 := by unfold r13Z_c; norm_num [Nat.factorial]
    rw [hc]
    exact r13Z_A0 hGRH hW
  · exact hsucc k

/-- **(P1)**: `R13ZetaSmooth`. -/
theorem r13Z_main : R13ZetaSmooth := by
  intro hGRH i
  obtain ⟨C, hC⟩ := r13Z_all hGRH i
  refine ⟨C, fun Y hY => ?_⟩
  have hY0 : 0 ≤ Y := by linarith
  set W := Y ^ ((1 : ℝ) / 4) with hWdef
  have hW : 1 ≤ W := Real.one_le_rpow hY (by norm_num)
  have e4 : W ^ 4 = Y := by
    rw [hWdef, ← Real.rpow_natCast, ← Real.rpow_mul hY0]; norm_num
  have e6 : W ^ 6 = Y ^ ((3 : ℝ) / 2) := by
    rw [hWdef, ← Real.rpow_natCast, ← Real.rpow_mul hY0]; norm_num
  have e5 : W ^ 5 = Y ^ ((5 : ℝ) / 4) := by
    rw [hWdef, ← Real.rpow_natCast, ← Real.rpow_mul hY0]; norm_num
  have h := hC W hW
  rw [e4, e6, e5] at h
  exact h

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r13Z_main
