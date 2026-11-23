import Mathlib
import DetPrimality.Bach.R14Defs
import DetPrimality.Bach.R13Zeta

/-!
# Round 14, (P1ₐ): `R14ZetaSmooth a` for every `a`

Under RH, `A^{(a)}_i(Y) = i! (a + 3/2)^{-(i+1)} Y^{3/2} + O(Y^{5/4})` on `Y ≥ 1`, for all `a`, `i`.

Everything is done in the variable `W = Y^{1/4}` for `B_i(W) = W^{4a} A^{(a)}_i(W⁴) = ∑_{n<W⁴} Λ(n) √n n^a log^i(W⁴/n)`:
* `r14Z_zero` : `i = 0`. Partial summation in differentiated form: `G(w) = ∑ Λ(n)√n (w^{4a} − n^a)₊`
  equals `w^{4a} A_0(w⁴) − B_0(w)` and has right derivative `4a w^{4a−1} ∑_{n ≤ w⁴} Λ(n)√n`; input `r13Z_A0`.
* `r14Z_one` : `i = 1` from `i = 0`, right derivative of `∑ Λ(n)√n n^a (4 log w − log n)₊`.
* `r14Z_step` : `i + 1 → i + 2` as `r13Z_step` (two-sided derivative).
* `r14Z_mvt` : comparison for right derivatives (`image_le_of_deriv_right_le_deriv_boundary`).
* `r14Z_main (a) : R14ZetaSmooth a`.
-/

open Complex DirichletCharacter Filter Topology

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- The main-term constant `i! (a + 3/2)^{-(i+1)}`. -/
noncomputable def r14Z_c (a i : ℕ) : ℝ := (i.factorial : ℝ) * (1 / ((a : ℝ) + 3 / 2)) ^ (i + 1)

theorem r14Z_c_nonneg (a i : ℕ) : 0 ≤ r14Z_c a i := by unfold r14Z_c; positivity

theorem r14Z_c_succ (a i : ℕ) :
    (4 * (a : ℝ) + 6) * r14Z_c a (i + 1) = 4 * ((i : ℝ) + 1) * r14Z_c a i := by
  unfold r14Z_c
  rw [Nat.factorial_succ]
  have h : (a : ℝ) + 3 / 2 ≠ 0 := by positivity
  have hq : (4 * (a : ℝ) + 6) * (1 / ((a : ℝ) + 3 / 2)) = 4 := by
    rw [mul_one_div, div_eq_iff h]
    ring
  rw [pow_succ (1 / ((a : ℝ) + 3 / 2)) (i + 1)]
  push_cast
  linear_combination (((i : ℝ) + 1) * (i.factorial : ℝ) * (1 / ((a : ℝ) + 3 / 2)) ^ (i + 1)) * hq

/-- `A^{(a)}_i(y) = 0` for `y ≤ 2`. -/
theorem r14Z_A_zero (a i : ℕ) {y : ℝ} (hy : y ≤ 2) : r14A a i y = 0 := by
  unfold r14A
  refine Finset.sum_eq_zero fun n hn => ?_
  have h2 : ⌈y⌉₊ ≤ 2 := Nat.ceil_le.mpr (by exact_mod_cast hy)
  have hn2 : n < 2 := lt_of_lt_of_le (Finset.mem_range.mp hn) h2
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl <;> simp

/-! ## Sums over a fixed range -/

/-- `∑_{n<N} Λ(n) √n (w^{4a} − n^a)₊`. -/
noncomputable def r14Z_G (a N : ℕ) (w : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Λ n * √(n : ℝ) * max (w ^ (4 * a) - (n : ℝ) ^ a) 0

/-- `∑_{n<N} Λ(n) √n n^a (4 log w − log n)₊^j`. -/
noncomputable def r14Z_T (a j N : ℕ) (w : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Λ n * √(n : ℝ) * (n : ℝ) ^ a * (max (4 * Real.log w - Real.log n) 0) ^ j

theorem r14Z_B_eq0 (a : ℕ) {w : ℝ} (hw : 0 < w) :
    w ^ (4 * a) * r14A a 0 (w ^ 4)
      = ∑ n ∈ Finset.range ⌈w ^ 4⌉₊, Λ n * √(n : ℝ) * (n : ℝ) ^ a := by
  unfold r14A
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_pow, ← pow_mul, pow_zero]
  field_simp

theorem r14Z_A_eq (a : ℕ) {j : ℕ} (hj : j ≠ 0) {w : ℝ} (hw : 0 < w) {N : ℕ}
    (hN : ⌈w ^ 4⌉₊ ≤ N) :
    w ^ (4 * a) * r14A a j (w ^ 4) = r14Z_T a j N w := by
  unfold r14A r14Z_T
  have hlog : Real.log (w ^ 4) = 4 * Real.log w := by rw [Real.log_pow]; norm_num
  have hw4 : 0 < w ^ 4 := by positivity
  rw [Finset.mul_sum, ← Finset.sum_subset (Finset.range_mono hN)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
      have hlt : (n : ℝ) < w ^ 4 := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
      have h1 := Real.log_le_log hn0 hlt.le
      rw [hlog] at h1
      rw [Real.log_div hw4.ne' hn0.ne', hlog, max_eq_left (by linarith), div_pow, ← pow_mul]
      field_simp
  · intro n _ hn
    rw [Finset.mem_range, not_lt] at hn
    have hle : w ^ 4 ≤ n := Nat.ceil_le.mp hn
    have h1 := Real.log_le_log hw4 hle
    rw [hlog] at h1
    rw [max_eq_right (by linarith), zero_pow hj, mul_zero]

theorem r14Z_G_eq (a : ℕ) {w : ℝ} (hw : 0 < w) {N : ℕ} (hN : ⌈w ^ 4⌉₊ ≤ N) :
    r14Z_G a N w = w ^ (4 * a) * r11A 0 (w ^ 4)
      - ∑ n ∈ Finset.range ⌈w ^ 4⌉₊, Λ n * √(n : ℝ) * (n : ℝ) ^ a := by
  unfold r11A r14Z_G
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.range_mono hN)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hlt : (n : ℝ) < w ^ 4 := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
    have hp : (n : ℝ) ^ a ≤ w ^ (4 * a) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (Nat.cast_nonneg n) hlt.le a
    rw [max_eq_left (by linarith), pow_zero]
    ring
  · intro n _ hn
    rw [Finset.mem_range, not_lt] at hn
    have hle : w ^ 4 ≤ n := Nat.ceil_le.mp hn
    have hp : w ^ (4 * a) ≤ (n : ℝ) ^ a := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hle a
    rw [max_eq_right (by linarith), mul_zero]

/-- The closed sum `n ≤ w⁴` differs from the open one by at most one term `≤ 4 w^{4a+3}`. -/
theorem r14Z_closed (a : ℕ) {w : ℝ} (hw : 1 ≤ w) {N : ℕ} (hN : ⌈w ^ 4⌉₊ ≤ N) :
    |∑ n ∈ Finset.range N, (if (n : ℝ) ≤ w ^ 4 then Λ n * √(n : ℝ) * (n : ℝ) ^ a else 0)
      - ∑ n ∈ Finset.range ⌈w ^ 4⌉₊, Λ n * √(n : ℝ) * (n : ℝ) ^ a| ≤ 4 * w ^ (4 * a + 3) := by
  have hw0 : 0 < w := by linarith
  have hB : 0 ≤ 4 * w ^ (4 * a + 3) := by positivity
  rw [← Finset.sum_sdiff (Finset.range_mono hN)]
  have h1 : ∑ n ∈ Finset.range ⌈w ^ 4⌉₊,
      (if (n : ℝ) ≤ w ^ 4 then Λ n * √(n : ℝ) * (n : ℝ) ^ a else 0)
      = ∑ n ∈ Finset.range ⌈w ^ 4⌉₊, Λ n * √(n : ℝ) * (n : ℝ) ^ a :=
    Finset.sum_congr rfl fun n hn => if_pos (Nat.lt_ceil.mp (Finset.mem_range.mp hn)).le
  rw [h1, add_sub_cancel_right]
  have hterm : ∀ n ∈ Finset.range N \ Finset.range ⌈w ^ 4⌉₊,
      0 ≤ (if (n : ℝ) ≤ w ^ 4 then Λ n * √(n : ℝ) * (n : ℝ) ^ a else 0) ∧
      (if (n : ℝ) ≤ w ^ 4 then Λ n * √(n : ℝ) * (n : ℝ) ^ a else 0)
        ≤ if n = ⌈w ^ 4⌉₊ then 4 * w ^ (4 * a + 3) else 0 := by
    intro n hn
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hn
    have hle : w ^ 4 ≤ n := Nat.ceil_le.mp hn.2
    by_cases h : (n : ℝ) ≤ w ^ 4
    · have heq : (n : ℝ) = w ^ 4 := le_antisymm h hle
      have hn' : n = ⌈w ^ 4⌉₊ := by rw [← heq, Nat.ceil_natCast]
      rw [if_pos h, if_pos hn']
      have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      have hΛ : Λ n ≤ 4 * w := by
        refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
        rw [heq, Real.log_pow]
        have := Real.log_le_sub_one_of_pos hw0
        push_cast
        linarith
      have hs : √(n : ℝ) ≤ w ^ 2 := by
        rw [heq, show w ^ 4 = (w ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      have hp : (n : ℝ) ^ a = w ^ (4 * a) := by rw [heq, ← pow_mul]
      rw [hp]
      refine ⟨mul_nonneg (mul_nonneg hΛ0 (Real.sqrt_nonneg _)) (by positivity), ?_⟩
      calc Λ n * √(n : ℝ) * w ^ (4 * a) ≤ 4 * w * w ^ 2 * w ^ (4 * a) := by gcongr
        _ = 4 * w ^ (4 * a + 3) := by ring
    · rw [if_neg h]
      refine ⟨le_rfl, ?_⟩
      split_ifs
      · exact hB
      · exact le_rfl
  have hlo := Finset.sum_nonneg fun n hn => (hterm n hn).1
  have hhi := Finset.sum_le_sum fun n hn => (hterm n hn).2
  rw [Finset.sum_ite_eq'] at hhi
  rw [abs_of_nonneg hlo]
  refine hhi.trans ?_
  split_ifs
  · exact le_rfl
  · exact hB

/-! ## Right derivatives -/

theorem r14Z_hasDerivWithinAt_pos {g : ℝ → ℝ} {g' t c : ℝ} (hg : HasDerivAt g g' t)
    (hmono : ∀ s, t ≤ s → g t ≤ g s) :
    HasDerivWithinAt (fun s => max (g s - c) 0) (if c ≤ g t then g' else 0) (Set.Ici t) t := by
  rcases lt_trichotomy (g t) c with h | h | h
  · rw [if_neg (not_le.mpr h)]
    have he : (fun s => max (g s - c) 0) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [hg.continuousAt (Iio_mem_nhds h)] with s hs
      have hs' : g s < c := hs
      exact max_eq_right (by linarith)
    exact ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he).hasDerivWithinAt
  · rw [if_pos h.ge]
    refine (hg.sub_const c).hasDerivWithinAt.congr (fun s hs => ?_) ?_
    · have := hmono s hs
      exact max_eq_left (by linarith)
    · exact max_eq_left (by linarith)
  · rw [if_pos h.le]
    have he : (fun s => max (g s - c) 0) =ᶠ[𝓝 t] fun s => g s - c := by
      filter_upwards [hg.continuousAt (Ioi_mem_nhds h)] with s hs
      have hs' : c < g s := hs
      exact max_eq_left (by linarith)
    exact ((hg.sub_const c).congr_of_eventuallyEq he).hasDerivWithinAt

theorem r14Z_mvt {H H' : ℝ → ℝ} {D W0 : ℝ} (m : ℕ) (hW : 1 ≤ W0) (hD : 0 ≤ D)
    (hc : ContinuousOn H (Set.Icc 1 W0))
    (hH : ∀ w, 1 ≤ w → w < W0 → HasDerivWithinAt H (H' w) (Set.Ici w) w)
    (hb : ∀ w, 1 ≤ w → w < W0 → |H' w| ≤ D * w ^ m) :
    |H W0 - H 1| ≤ D * W0 ^ (m + 1) := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = D / ((m : ℝ) + 1) := ⟨_, rfl⟩
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hED : E ≤ D := by
    rw [hE]
    exact div_le_self hD (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hP : ∀ w : ℝ, HasDerivAt (fun w : ℝ => E * w ^ (m + 1)) (D * w ^ m) w := fun w => by
    have h := (hasDerivAt_pow (m + 1) w).const_mul E
    refine h.congr_deriv ?_
    rw [hE, Nat.add_sub_cancel]
    push_cast
    field_simp
  have hmem : W0 ∈ Set.Icc 1 W0 := Set.right_mem_Icc.mpr hW
  have h1 := image_le_of_deriv_right_le_deriv_boundary (f := H) (f' := H') hc
    (fun x hx => hH x hx.1 hx.2)
    (B := fun w => H 1 - E + E * w ^ (m + 1)) (B' := fun w => D * w ^ m)
    (by simp) (by fun_prop)
    (fun x _ => ((hP x).const_add (H 1 - E)).hasDerivWithinAt)
    (fun x hx => (abs_le.mp (hb x hx.1 hx.2)).2) hmem
  have h2 := image_le_of_deriv_right_le_deriv_boundary (f := fun w => -H w)
    (f' := fun w => -H' w) hc.neg
    (fun x hx => (hH x hx.1 hx.2).neg)
    (B := fun w => -H 1 - E + E * w ^ (m + 1)) (B' := fun w => D * w ^ m)
    (by simp) (by fun_prop)
    (fun x _ => ((hP x).const_add (-H 1 - E)).hasDerivWithinAt)
    (fun x hx => by have := (abs_le.mp (hb x hx.1 hx.2)).1; linarith) hmem
  have hW1 : 1 ≤ W0 ^ (m + 1) := one_le_pow₀ hW
  have hq : E * W0 ^ (m + 1) ≤ D * W0 ^ (m + 1) :=
    mul_le_mul_of_nonneg_right hED (by linarith)
  rw [abs_le]
  constructor <;> linarith

/-- The derivative bound common to `r14Z_one` and `r14Z_step`. -/
theorem r14Z_dbound {w S c0 c1 E K p : ℝ} (m : ℕ) (hw : 0 < w) (hK : 0 ≤ K)
    (hcs : p * c1 = K * c0) (hS : |S - c0 * w ^ (m + 2)| ≤ E * w ^ (m + 1)) :
    |K / w * S - c1 * (p * w ^ (m + 1))| ≤ K * E * w ^ m := by
  have e : K / w * S - c1 * (p * w ^ (m + 1)) = K / w * (S - c0 * w ^ (m + 2)) := by
    have h1 : c1 * (p * w ^ (m + 1)) = K * c0 * w ^ (m + 1) := by
      linear_combination w ^ (m + 1) * hcs
    rw [h1]
    field_simp
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  calc K / w * |S - c0 * w ^ (m + 2)| ≤ K / w * (E * w ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = K * E * w ^ m := by
        field_simp
        ring

theorem r14Z_hasDerivAt_pow (a : ℕ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun w : ℝ => w ^ (4 * a)) (4 * a * w ^ (4 * a) / w) w := by
  refine (hasDerivAt_pow (4 * a) w).congr_deriv ?_
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have h : w ^ (4 * a) = w ^ (4 * a - 1) * w := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h]
    push_cast
    field_simp

/-! ## `i = 0` -/

theorem r14Z_hasDerivWithinAt_G (a N : ℕ) {w : ℝ} (hw : 0 < w) :
    HasDerivWithinAt (r14Z_G a N)
      (∑ n ∈ Finset.range N, Λ n * √(n : ℝ) *
        (if (n : ℝ) ^ a ≤ w ^ (4 * a) then 4 * a * w ^ (4 * a) / w else 0)) (Set.Ici w) w := by
  have h2 : ∀ n : ℕ, HasDerivWithinAt
      (fun w : ℝ => Λ n * √(n : ℝ) * max (w ^ (4 * a) - (n : ℝ) ^ a) 0)
      (Λ n * √(n : ℝ) * (if (n : ℝ) ^ a ≤ w ^ (4 * a) then 4 * a * w ^ (4 * a) / w else 0))
      (Set.Ici w) w := fun n =>
    (r14Z_hasDerivWithinAt_pos (c := (n : ℝ) ^ a) (r14Z_hasDerivAt_pow a hw)
      (fun s hs => pow_le_pow_left₀ hw.le hs _)).const_mul _
  have h3 := HasDerivWithinAt.fun_sum (u := Finset.range N) fun n _ => h2 n
  exact h3

theorem r14Z_zero (hGRH : DirichletLZerosOnLine) (a : ℕ) :
    ∀ W : ℝ, 1 ≤ W → |W ^ (4 * a) * r14A a 0 (W ^ 4) - r14Z_c a 0 * W ^ (4 * a + 6)|
      ≤ (21 + 96 * (a : ℝ)) * W ^ (4 * a + 5) := by
  intro W0 hW0
  have hW00 : 0 < W0 := by linarith
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 2 / 3 - r14Z_c a 0 := ⟨_, rfl⟩
  have hc0 : r14Z_c a 0 = 1 / ((a : ℝ) + 3 / 2) := by unfold r14Z_c; simp
  have hck : r14Z_c a 0 = 2 / 3 - κ := by rw [hκ]; ring
  have hκ0 : 0 ≤ κ := by
    rw [hκ, hc0, sub_nonneg, div_le_iff₀ (by positivity)]
    linarith
  have hκ1 : κ ≤ 1 := by
    have := r14Z_c_nonneg a 0
    linarith
  have hκe : κ * (4 * (a : ℝ) + 6) = 4 * a * (2 / 3) := by
    rw [hκ, hc0]
    field_simp
    ring
  have hceil : ∀ w : ℝ, 0 < w → w ≤ W0 → ⌈w ^ 4⌉₊ ≤ ⌈W0 ^ 4⌉₊ := fun w hw hle =>
    Nat.ceil_mono (pow_le_pow_left₀ hw.le hle 4)
  have hGc : Continuous (r14Z_G a ⌈W0 ^ 4⌉₊) := by
    have : Continuous fun w : ℝ => ∑ n ∈ Finset.range ⌈W0 ^ 4⌉₊,
        Λ n * √(n : ℝ) * max (w ^ (4 * a) - (n : ℝ) ^ a) 0 :=
      continuous_finsetSum _ fun n _ => by fun_prop
    exact this
  have hmvt := r14Z_mvt (H := fun w => r14Z_G a ⌈W0 ^ 4⌉₊ w - κ * w ^ (4 * a + 6))
    (H' := fun w => (∑ n ∈ Finset.range ⌈W0 ^ 4⌉₊, Λ n * √(n : ℝ) *
        (if (n : ℝ) ^ a ≤ w ^ (4 * a) then 4 * a * w ^ (4 * a) / w else 0))
      - κ * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5)))
    (D := 96 * (a : ℝ)) (4 * a + 4) hW0 (by positivity)
    (hGc.continuousOn.sub (by fun_prop))
    (by
      intro w hw1 _
      have hw0 : 0 < w := by linarith
      have hp : HasDerivAt (fun w : ℝ => κ * w ^ (4 * a + 6))
          (κ * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5))) w := by
        have h6 := (hasDerivAt_pow (4 * a + 6) w).const_mul κ
        refine h6.congr_deriv ?_
        rw [show 4 * a + 6 - 1 = 4 * a + 5 by omega]
        push_cast
        ring
      exact (r14Z_hasDerivWithinAt_G a _ hw0).sub hp.hasDerivWithinAt)
    (by
      intro w hw1 hwW
      have hw0 : 0 < w := by linarith
      rcases Nat.eq_zero_or_pos a with ha | ha
      · have hk : κ = 0 := by rw [hκ, hc0, ha]; norm_num
        simp [ha, hk]
      · have key : ∀ S : ℝ, |S - r11A 0 (w ^ 4)| ≤ 4 * w ^ (4 * 0 + 3) →
            |4 * a * w ^ (4 * a) / w * S - κ * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5))|
              ≤ 96 * a * w ^ (4 * a + 4) := by
          intro S hS
          have hA0 := r13Z_A0 hGRH hw1
          have h3 : w ^ (4 * 0 + 3) ≤ w ^ 5 := pow_le_pow_right₀ hw1 (by norm_num)
          have h5 : 0 < w ^ 5 := by positivity
          have hSb : |S - 2 / 3 * w ^ 6| ≤ 24 * w ^ 5 := by
            have := abs_sub_le S (r11A 0 (w ^ 4)) (2 / 3 * w ^ 6)
            linarith
          have e : 4 * a * w ^ (4 * a) / w * S - κ * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5))
              = 4 * a * w ^ (4 * a) / w * (S - 2 / 3 * w ^ 6) := by
            have h1 : κ * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5))
                = 4 * a * (2 / 3) * w ^ (4 * a + 5) := by
              linear_combination w ^ (4 * a + 5) * hκe
            rw [h1]
            field_simp
            ring
          rw [e, abs_mul, abs_of_nonneg (by positivity)]
          calc 4 * a * w ^ (4 * a) / w * |S - 2 / 3 * w ^ 6|
              ≤ 4 * a * w ^ (4 * a) / w * (24 * w ^ 5) :=
                mul_le_mul_of_nonneg_left hSb (by positivity)
            _ = 96 * a * w ^ (4 * a + 4) := by
                field_simp
                ring
        have hS : ∑ n ∈ Finset.range ⌈W0 ^ 4⌉₊, Λ n * √(n : ℝ) *
              (if (n : ℝ) ^ a ≤ w ^ (4 * a) then 4 * a * w ^ (4 * a) / w else 0)
            = 4 * a * w ^ (4 * a) / w * ∑ n ∈ Finset.range ⌈W0 ^ 4⌉₊,
              (if (n : ℝ) ≤ w ^ 4 then Λ n * √(n : ℝ) * (n : ℝ) ^ 0 else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          have hiff : (n : ℝ) ^ a ≤ w ^ (4 * a) ↔ (n : ℝ) ≤ w ^ 4 := by
            rw [pow_mul]
            exact pow_le_pow_iff_left₀ (Nat.cast_nonneg n) (by positivity) ha.ne'
          by_cases h : (n : ℝ) ≤ w ^ 4
          · rw [if_pos h, if_pos (hiff.mpr h)]
            ring
          · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
            ring
        have hcl := r14Z_closed 0 hw1 (hceil w hw0 hwW.le)
        have hr : r11A 0 (w ^ 4)
            = ∑ n ∈ Finset.range ⌈w ^ 4⌉₊, Λ n * √(n : ℝ) * (n : ℝ) ^ 0 := by
          unfold r11A
          simp
        rw [← hr] at hcl
        rw [hS]
        exact key _ hcl)
  have hG1 : r14Z_G a ⌈W0 ^ 4⌉₊ 1 = 0 := by
    unfold r14Z_G
    refine Finset.sum_eq_zero fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have h1 : (1 : ℝ) ≤ (n : ℝ) ^ a := one_le_pow₀ (by exact_mod_cast hpos)
      rw [one_pow, max_eq_right (by linarith), mul_zero]
  have hGW : r14Z_G a ⌈W0 ^ 4⌉₊ W0
      = W0 ^ (4 * a) * r11A 0 (W0 ^ 4) - W0 ^ (4 * a) * r14A a 0 (W0 ^ 4) := by
    rw [r14Z_B_eq0 a hW00]
    exact r14Z_G_eq a hW00 le_rfl
  simp only [hG1, hGW, one_pow, mul_one] at hmvt
  have hm : |W0 ^ (4 * a) * r11A 0 (W0 ^ 4) - W0 ^ (4 * a) * r14A a 0 (W0 ^ 4)
      - κ * W0 ^ (4 * a + 6) - (0 - κ)| ≤ 96 * a * W0 ^ (4 * a + 5) := hmvt
  have hm' := abs_le.mp hm
  have hA := abs_le.mp (r13Z_A0 hGRH hW0)
  have hP : 0 < W0 ^ (4 * a) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hA.1 hP.le
  have h2 := mul_le_mul_of_nonneg_left hA.2 hP.le
  have e5 : W0 ^ (4 * a) * W0 ^ 5 = W0 ^ (4 * a + 5) := by ring
  have e6 : W0 ^ (4 * a) * W0 ^ 6 = W0 ^ (4 * a + 6) := by ring
  have hW5 : 1 ≤ W0 ^ (4 * a + 5) := one_le_pow₀ hW0
  have hp1 : 0 ≤ a * W0 ^ (4 * a + 5) := by positivity
  rw [hck, abs_le]
  constructor <;> nlinarith

/-! ## `i = 1` -/

theorem r14Z_T_one (a N : ℕ) : r14Z_T a 1 N = fun w : ℝ => ∑ n ∈ Finset.range N,
    Λ n * √(n : ℝ) * (n : ℝ) ^ a * max (4 * Real.log w - Real.log n) 0 := by
  funext w
  unfold r14Z_T
  simp only [pow_one]

theorem r14Z_hasDerivWithinAt_T (a N : ℕ) {w : ℝ} (hw : 0 < w) :
    HasDerivWithinAt (r14Z_T a 1 N)
      (4 / w * ∑ n ∈ Finset.range N,
        (if (n : ℝ) ≤ w ^ 4 then Λ n * √(n : ℝ) * (n : ℝ) ^ a else 0)) (Set.Ici w) w := by
  rw [r14Z_T_one]
  have hw4 : 0 < w ^ 4 := by positivity
  have hl : Real.log (w ^ 4) = 4 * Real.log w := by rw [Real.log_pow]; norm_num
  have h1 : HasDerivAt (fun s : ℝ => 4 * Real.log s) (4 / w) w :=
    ((Real.hasDerivAt_log hw.ne').const_mul 4).congr_deriv (by ring)
  have h2 : ∀ n : ℕ, HasDerivWithinAt
      (fun w : ℝ => Λ n * √(n : ℝ) * (n : ℝ) ^ a * max (4 * Real.log w - Real.log n) 0)
      (Λ n * √(n : ℝ) * (n : ℝ) ^ a * (if Real.log n ≤ 4 * Real.log w then 4 / w else 0))
      (Set.Ici w) w := fun n =>
    (r14Z_hasDerivWithinAt_pos (c := Real.log n) h1
      (fun s hs => by have := Real.log_le_log hw hs; linarith)).const_mul _
  have h3 := HasDerivWithinAt.fun_sum (u := Finset.range N) fun n _ => h2 n
  refine h3.congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have hiff : Real.log n ≤ 4 * Real.log w ↔ (n : ℝ) ≤ w ^ 4 := by
      rw [← hl]
      exact Real.log_le_log_iff hn0 hw4
    by_cases h : (n : ℝ) ≤ w ^ 4
    · rw [if_pos h, if_pos (hiff.mpr h)]
      ring
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
      ring

theorem r14Z_one (a : ℕ) {C : ℝ}
    (h : ∀ W : ℝ, 1 ≤ W → |W ^ (4 * a) * r14A a 0 (W ^ 4) - r14Z_c a 0 * W ^ (4 * a + 6)|
      ≤ C * W ^ (4 * a + 5)) :
    ∀ W : ℝ, 1 ≤ W → |W ^ (4 * a) * r14A a 1 (W ^ 4) - r14Z_c a 1 * W ^ (4 * a + 6)|
      ≤ (r14Z_c a 1 + 4 * (C + 4)) * W ^ (4 * a + 5) := by
  intro W0 hW0
  have hW00 : 0 < W0 := by linarith
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (h 1 le_rfl)
    simpa using this
  have hc1 := r14Z_c_nonneg a 1
  have hcs : (4 * (a : ℝ) + 6) * r14Z_c a 1 = 4 * r14Z_c a 0 := by
    have := r14Z_c_succ a 0
    rw [Nat.cast_zero] at this
    linarith
  have hceil : ∀ w : ℝ, 0 < w → w ≤ W0 → ⌈w ^ 4⌉₊ ≤ ⌈W0 ^ 4⌉₊ := fun w hw hle =>
    Nat.ceil_mono (pow_le_pow_left₀ hw.le hle 4)
  have hTc : ContinuousOn (r14Z_T a 1 ⌈W0 ^ 4⌉₊) (Set.Icc 1 W0) := by
    rw [r14Z_T_one]
    have hl : ContinuousOn Real.log (Set.Icc 1 W0) :=
      Real.continuousOn_log.mono fun x hx => by
        have : (0 : ℝ) < x := by linarith [hx.1]
        exact this.ne'
    refine continuousOn_finsetSum _ fun n _ => ?_
    have hcn : Continuous fun t : ℝ =>
        Λ n * √(n : ℝ) * (n : ℝ) ^ a * max (4 * t - Real.log n) 0 := by fun_prop
    have hco : ContinuousOn (fun w : ℝ =>
        Λ n * √(n : ℝ) * (n : ℝ) ^ a * max (4 * Real.log w - Real.log n) 0) (Set.Icc 1 W0) :=
      hcn.comp_continuousOn hl
    exact hco
  have hmvt := r14Z_mvt (H := fun w => r14Z_T a 1 ⌈W0 ^ 4⌉₊ w - r14Z_c a 1 * w ^ (4 * a + 6))
    (H' := fun w => 4 / w * (∑ n ∈ Finset.range ⌈W0 ^ 4⌉₊,
        (if (n : ℝ) ≤ w ^ 4 then Λ n * √(n : ℝ) * (n : ℝ) ^ a else 0))
      - r14Z_c a 1 * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5)))
    (D := 4 * (C + 4)) (4 * a + 4) hW0 (by positivity)
    (hTc.sub (by fun_prop))
    (by
      intro w hw1 _
      have hw0 : 0 < w := by linarith
      have hp : HasDerivAt (fun w : ℝ => r14Z_c a 1 * w ^ (4 * a + 6))
          (r14Z_c a 1 * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5))) w := by
        have h6 := (hasDerivAt_pow (4 * a + 6) w).const_mul (r14Z_c a 1)
        refine h6.congr_deriv ?_
        rw [show 4 * a + 6 - 1 = 4 * a + 5 by omega]
        push_cast
        ring
      exact (r14Z_hasDerivWithinAt_T a _ hw0).sub hp.hasDerivWithinAt)
    (by
      intro w hw1 hwW
      have hw0 : 0 < w := by linarith
      have hcl := r14Z_closed a hw1 (hceil w hw0 hwW.le)
      rw [← r14Z_B_eq0 a hw0] at hcl
      have hq := h w hw1
      have h3 : w ^ (4 * a + 3) ≤ w ^ (4 * a + 5) := pow_le_pow_right₀ hw1 (by omega)
      have hS : |(∑ n ∈ Finset.range ⌈W0 ^ 4⌉₊,
          (if (n : ℝ) ≤ w ^ 4 then Λ n * √(n : ℝ) * (n : ℝ) ^ a else 0))
          - r14Z_c a 0 * w ^ (4 * a + 6)| ≤ (C + 4) * w ^ (4 * a + 5) := by
        have := abs_sub_le (∑ n ∈ Finset.range ⌈W0 ^ 4⌉₊,
          (if (n : ℝ) ≤ w ^ 4 then Λ n * √(n : ℝ) * (n : ℝ) ^ a else 0))
          (w ^ (4 * a) * r14A a 0 (w ^ 4)) (r14Z_c a 0 * w ^ (4 * a + 6))
        linarith
      exact r14Z_dbound (4 * a + 4) hw0 (by norm_num) hcs hS)
  have hTW : r14Z_T a 1 ⌈W0 ^ 4⌉₊ W0 = W0 ^ (4 * a) * r14A a 1 (W0 ^ 4) :=
    (r14Z_A_eq a one_ne_zero hW00 le_rfl).symm
  have hT1 : r14Z_T a 1 ⌈W0 ^ 4⌉₊ 1 = 0 := by
    rw [← r14Z_A_eq a one_ne_zero one_pos (hceil 1 one_pos hW0),
      r14Z_A_zero a 1 (by norm_num), mul_zero]
  simp only [hT1, hTW, one_pow, mul_one] at hmvt
  have hm : |W0 ^ (4 * a) * r14A a 1 (W0 ^ 4) - r14Z_c a 1 * W0 ^ (4 * a + 6)
      - (0 - r14Z_c a 1)| ≤ 4 * (C + 4) * W0 ^ (4 * a + 5) := hmvt
  have hm' := abs_le.mp hm
  have hW5 : 1 ≤ W0 ^ (4 * a + 5) := one_le_pow₀ hW0
  have p1 : r14Z_c a 1 ≤ r14Z_c a 1 * W0 ^ (4 * a + 5) := le_mul_of_one_le_right hc1 hW5
  rw [abs_le]
  constructor <;> linarith

/-! ## The induction step -/

theorem r14Z_hasDerivAt_T (a k N : ℕ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (r14Z_T a (k + 2) N) (4 * ((k : ℝ) + 2) / w * r14Z_T a (k + 1) N w) w := by
  have h1 : ∀ n : ℕ, HasDerivAt (fun w : ℝ => 4 * Real.log w - Real.log n) (4 / w) w := fun n =>
    (((Real.hasDerivAt_log hw.ne').const_mul 4).sub_const _).congr_deriv (by ring)
  have h2 : ∀ n : ℕ, HasDerivAt
      (fun w : ℝ => Λ n * √(n : ℝ) * (n : ℝ) ^ a
        * (max (4 * Real.log w - Real.log n) 0) ^ (k + 2))
      (Λ n * √(n : ℝ) * (n : ℝ) ^ a
        * ((((k : ℝ) + 2) * (max (4 * Real.log w - Real.log n) 0) ^ (k + 1)) * (4 / w))) w :=
    fun n => ((r13Z_hasDerivAt_pos k (4 * Real.log w - Real.log n)).comp w (h1 n)).const_mul _
  have h3 := HasDerivAt.fun_sum (u := Finset.range N) fun n _ => h2 n
  refine HasDerivAt.congr_deriv (f := r14Z_T a (k + 2) N) h3 ?_
  unfold r14Z_T
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem r14Z_step (a k : ℕ) {C : ℝ}
    (h : ∀ W : ℝ, 1 ≤ W →
      |W ^ (4 * a) * r14A a (k + 1) (W ^ 4) - r14Z_c a (k + 1) * W ^ (4 * a + 6)|
        ≤ C * W ^ (4 * a + 5)) :
    ∀ W : ℝ, 1 ≤ W →
      |W ^ (4 * a) * r14A a (k + 2) (W ^ 4) - r14Z_c a (k + 2) * W ^ (4 * a + 6)|
        ≤ (r14Z_c a (k + 2) + 4 * ((k : ℝ) + 2) * C) * W ^ (4 * a + 5) := by
  intro W0 hW0
  have hW00 : 0 < W0 := by linarith
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (h 1 le_rfl)
    simpa using this
  have hc2 := r14Z_c_nonneg a (k + 2)
  have hcs : (4 * (a : ℝ) + 6) * r14Z_c a (k + 2) = 4 * ((k : ℝ) + 2) * r14Z_c a (k + 1) := by
    have := r14Z_c_succ a (k + 1)
    push_cast at this
    rw [show k + 1 + 1 = k + 2 from rfl] at this
    linarith
  have hceil : ∀ w : ℝ, 0 < w → w ≤ W0 → ⌈w ^ 4⌉₊ ≤ ⌈W0 ^ 4⌉₊ := fun w hw hle =>
    Nat.ceil_mono (pow_le_pow_left₀ hw.le hle 4)
  have hd : ∀ w : ℝ, 0 < w → HasDerivAt
      (fun w => r14Z_T a (k + 2) ⌈W0 ^ 4⌉₊ w - r14Z_c a (k + 2) * w ^ (4 * a + 6))
      (4 * ((k : ℝ) + 2) / w * r14Z_T a (k + 1) ⌈W0 ^ 4⌉₊ w
        - r14Z_c a (k + 2) * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5))) w := by
    intro w hw0
    have hp : HasDerivAt (fun w : ℝ => r14Z_c a (k + 2) * w ^ (4 * a + 6))
        (r14Z_c a (k + 2) * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5))) w := by
      have h6 := (hasDerivAt_pow (4 * a + 6) w).const_mul (r14Z_c a (k + 2))
      refine h6.congr_deriv ?_
      rw [show 4 * a + 6 - 1 = 4 * a + 5 by omega]
      push_cast
      ring
    exact (r14Z_hasDerivAt_T a k _ hw0).sub hp
  have hmvt := r14Z_mvt
    (H := fun w => r14Z_T a (k + 2) ⌈W0 ^ 4⌉₊ w - r14Z_c a (k + 2) * w ^ (4 * a + 6))
    (H' := fun w => 4 * ((k : ℝ) + 2) / w * r14Z_T a (k + 1) ⌈W0 ^ 4⌉₊ w
      - r14Z_c a (k + 2) * ((4 * (a : ℝ) + 6) * w ^ (4 * a + 5)))
    (D := 4 * ((k : ℝ) + 2) * C) (4 * a + 4) hW0 (by positivity)
    (fun w hw => (hd w (by linarith [hw.1])).continuousAt.continuousWithinAt)
    (fun w hw1 _ => (hd w (by linarith)).hasDerivWithinAt)
    (by
      intro w hw1 hwW
      have hw0 : 0 < w := by linarith
      have hq := h w hw1
      rw [r14Z_A_eq a (by omega) hw0 (hceil w hw0 hwW.le)] at hq
      exact r14Z_dbound (4 * a + 4) hw0 (by positivity) hcs hq)
  have hTW : r14Z_T a (k + 2) ⌈W0 ^ 4⌉₊ W0 = W0 ^ (4 * a) * r14A a (k + 2) (W0 ^ 4) :=
    (r14Z_A_eq a (by omega) hW00 le_rfl).symm
  have hT1 : r14Z_T a (k + 2) ⌈W0 ^ 4⌉₊ 1 = 0 := by
    rw [← r14Z_A_eq a (by omega) one_pos (hceil 1 one_pos hW0),
      r14Z_A_zero a _ (by norm_num), mul_zero]
  simp only [hT1, hTW, one_pow, mul_one] at hmvt
  have hm : |W0 ^ (4 * a) * r14A a (k + 2) (W0 ^ 4) - r14Z_c a (k + 2) * W0 ^ (4 * a + 6)
      - (0 - r14Z_c a (k + 2))| ≤ 4 * ((k : ℝ) + 2) * C * W0 ^ (4 * a + 5) := hmvt
  have hm' := abs_le.mp hm
  have hW5 : 1 ≤ W0 ^ (4 * a + 5) := one_le_pow₀ hW0
  have p1 : r14Z_c a (k + 2) ≤ r14Z_c a (k + 2) * W0 ^ (4 * a + 5) :=
    le_mul_of_one_le_right hc2 hW5
  rw [abs_le]
  constructor <;> linarith

/-! ## All orders -/

theorem r14Z_all (hGRH : DirichletLZerosOnLine) (a i : ℕ) :
    ∃ C : ℝ, ∀ W : ℝ, 1 ≤ W →
      |W ^ (4 * a) * r14A a i (W ^ 4) - r14Z_c a i * W ^ (4 * a + 6)| ≤ C * W ^ (4 * a + 5) := by
  have hsucc : ∀ k : ℕ, ∃ C : ℝ, ∀ W : ℝ, 1 ≤ W →
      |W ^ (4 * a) * r14A a (k + 1) (W ^ 4) - r14Z_c a (k + 1) * W ^ (4 * a + 6)|
        ≤ C * W ^ (4 * a + 5) := by
    intro k
    induction k with
    | zero => exact ⟨_, r14Z_one a (r14Z_zero hGRH a)⟩
    | succ k ih =>
      obtain ⟨C, hC⟩ := ih
      exact ⟨_, r14Z_step a k hC⟩
  rcases i with _ | k
  · exact ⟨_, r14Z_zero hGRH a⟩
  · exact hsucc k

/-- **(P1ₐ)**: `R14ZetaSmooth a`, every `a`. -/
theorem r14Z_main (a : ℕ) : R14ZetaSmooth a := by
  intro hGRH i
  obtain ⟨C, hC⟩ := r14Z_all hGRH a i
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
  have hP : 0 < W ^ (4 * a) := by positivity
  have e : W ^ (4 * a) * r14A a i (W ^ 4) - r14Z_c a i * W ^ (4 * a + 6)
      = W ^ (4 * a) * (r14A a i (W ^ 4) - r14Z_c a i * W ^ 6) := by ring
  rw [e, abs_mul, abs_of_pos hP, show C * W ^ (4 * a + 5) = W ^ (4 * a) * (C * W ^ 5) by ring] at h
  have h' := le_of_mul_le_mul_left h hP
  rw [e4, e6, e5] at h'
  exact h'

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r14Z_main
