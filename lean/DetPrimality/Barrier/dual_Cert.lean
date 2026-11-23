import Mathlib

/-!
# A kernel-checkable certificate for `sup_y |N(y)| / √(1/4 + y²)`, `N` an exponential sum

`N(y) = ∑_k a_k e^{i y v_k}` with rational `a_k = α_k / dSa`, `v_k = V_k / dDv` (`ns : List (ℤ × ℤ)`
is the list of `(V_k, α_k)`).  The checker `dualRun` walks through `[0, T]` in cells
`[y - r, y + r]`; on each cell it uses

  `‖N(y+τ) - N(y) - τ N'(y)‖ ≤ τ² M₂ / 2`,  `τ ↦ ‖N(y) + τ N'(y)‖` convex,
  `√(1/4 + t²) ≥ (1/4 + y t)/σ` for `σ ≥ √(1/4 + y²)` (Cauchy–Schwarz),

so that the two endpoint inequalities `‖N(y) ± r N'(y)‖ ≤ c (1/4 + y (y ± r))/σ - ε` suffice.
The numbers `e^{i y v_k}` are carried along in fixed point arithmetic (scale `dS`) with a
rigorous error counter (`err` units of `1/dS`); the rotations `e^{i r v_k}` are checked against
their Taylor polynomials in `ℚ`.
-/

open Complex

namespace DetPrimality.Barrier

/-- denominators: nodes `v = V / dDv`, coefficients `a = α / dSa`, fixed point scale `dS`. -/
def dDv : ℤ := 100000
def dSa : ℤ := 1000000000000000
def dS : ℤ := 10000000000000000000000

theorem dDv_pos : (0 : ℝ) < (dDv : ℝ) := by norm_num [dDv]
theorem dSa_pos : (0 : ℝ) < (dSa : ℝ) := by norm_num [dSa]
theorem dS_pos : (0 : ℝ) < (dS : ℝ) := by norm_num [dS]

/-! ## `e^{ix}` -/

/-- `e^{ix}` for real `x`. -/
noncomputable def eI (x : ℝ) : ℂ := cexp (I * (x : ℂ))

theorem eI_add (x y : ℝ) : eI (x + y) = eI x * eI y := by
  simp [eI, mul_add, Complex.exp_add]

@[simp] theorem eI_zero : eI 0 = 1 := by simp [eI]

@[simp] theorem norm_eI (x : ℝ) : ‖eI x‖ = 1 := Complex.norm_exp_I_mul_ofReal x

theorem eI_neg (x : ℝ) : eI (-x) = (starRingEnd ℂ) (eI x) := by
  simp [eI, ← Complex.exp_conj]

theorem eI_sub_one_le (x : ℝ) : ‖eI x - 1‖ ≤ |x| := by
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)
  rwa [Real.norm_eq_abs] at this

theorem eI_hasDerivAt (s : ℝ) : HasDerivAt (fun s : ℝ => eI s - 1 - I * (s : ℂ)) (I * (eI s - 1)) s := by
  have h1 : HasDerivAt (fun s : ℝ => I * (s : ℂ)) I s := by
    simpa using ((hasDerivAt_id s).ofReal_comp).const_mul I
  have h2 : HasDerivAt (fun s : ℝ => cexp (I * (s : ℂ)) - 1 - I * (s : ℂ))
      (cexp (I * (s : ℂ)) * I - I) s := (h1.cexp.sub_const 1).sub h1
  have e : I * (eI s - 1) = cexp (I * (s : ℂ)) * I - I := by unfold eI; ring
  rw [e]; exact h2

theorem eI_second_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖eI x - 1 - I * (x : ℂ)‖ ≤ x ^ 2 / 2 := by
  have hint : ∫ s in (0 : ℝ)..x, I * (eI s - 1) = eI x - 1 - I * (x : ℂ) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => eI_hasDerivAt s)]
    · simp
    · apply Continuous.intervalIntegrable
      unfold eI; fun_prop
  rw [← hint]
  calc ‖∫ s in (0 : ℝ)..x, I * (eI s - 1)‖ ≤ ∫ s in (0 : ℝ)..x, s := by
        refine intervalIntegral.norm_integral_le_of_norm_le hx (Filter.Eventually.of_forall ?_)
          (Continuous.intervalIntegrable continuous_id _ _)
        intro s hs
        rw [norm_mul, Complex.norm_I, one_mul]
        exact (eI_sub_one_le s).trans (abs_of_pos hs.1).le
    _ = x ^ 2 / 2 := by rw [integral_id]; ring

theorem eI_second (x : ℝ) : ‖eI x - 1 - I * (x : ℂ)‖ ≤ x ^ 2 / 2 := by
  rcases le_total 0 x with hx | hx
  · exact eI_second_nonneg hx
  · have h := eI_second_nonneg (neg_nonneg.mpr hx)
    have e : eI x - 1 - I * (x : ℂ) = (starRingEnd ℂ) (eI (-x) - 1 - I * ((-x : ℝ) : ℂ)) := by
      rw [eI_neg]; simp; ring
    rw [e, Complex.norm_conj]
    simpa using h

theorem eI_taylor {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖eI x - ∑ m ∈ Finset.range n, (I * (x : ℂ)) ^ m / (m.factorial : ℂ)‖
      ≤ |x| ^ n * ((n + 1 : ℝ) / (n.factorial * n)) := by
  have h : ‖I * (x : ℂ)‖ = |x| := by simp
  have := Complex.exp_bound (x := I * (x : ℂ)) (by rw [h]; exact hx) hn
  rw [h] at this
  refine this.trans (le_of_eq ?_)
  push_cast
  rw [div_eq_mul_inv]

/-! ## Fixed point complex numbers -/

/-- `(a + b i) / dS`. -/
noncomputable def toC (p : ℤ × ℤ) : ℂ := ((p.1 : ℂ) + (p.2 : ℂ) * I) / (dS : ℂ)

theorem norm_re_add_im_le (x y : ℝ) : ‖(x : ℂ) + (y : ℂ) * I‖ ≤ |x| + |y| := by
  simpa using Complex.norm_le_abs_re_add_abs_im ((x : ℂ) + (y : ℂ) * I)

/-- rounded product of two fixed point numbers. -/
def dualMul (a ρ : ℤ × ℤ) : ℤ × ℤ :=
  ((a.1 * ρ.1 - a.2 * ρ.2) / dS, (a.1 * ρ.2 + a.2 * ρ.1) / dS)

theorem dual_ediv (x : ℤ) :
    0 ≤ (x : ℝ) / dS - ((x / dS : ℤ) : ℝ) ∧ (x : ℝ) / dS - ((x / dS : ℤ) : ℝ) ≤ 1 := by
  have h : dS * (x / dS) ≤ x ∧ x < dS * (x / dS) + dS := by unfold dS; omega
  have h1 : (dS : ℝ) * ((x / dS : ℤ) : ℝ) ≤ x := by exact_mod_cast h.1
  have h2 : (x : ℝ) < (dS : ℝ) * ((x / dS : ℤ) : ℝ) + dS := by exact_mod_cast h.2
  have hS := dS_pos
  constructor
  · rw [sub_nonneg, le_div_iff₀ hS]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hS]; linarith

theorem dualMul_round (a ρ : ℤ × ℤ) : ‖toC a * toC ρ - toC (dualMul a ρ)‖ ≤ 2 / dS := by
  have hS := dS_pos
  have hSc : (dS : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  set x : ℤ := a.1 * ρ.1 - a.2 * ρ.2 with hx
  set y : ℤ := a.1 * ρ.2 + a.2 * ρ.1 with hy
  have e : toC a * toC ρ - toC (dualMul a ρ)
      = ((((x : ℝ) / dS - ((x / dS : ℤ) : ℝ) : ℝ) : ℂ)
          + (((y : ℝ) / dS - ((y / dS : ℤ) : ℝ) : ℝ) : ℂ) * I) / (dS : ℂ) := by
    simp only [toC, dualMul, ← hx, ← hy]
    rw [hx, hy]
    push_cast
    field_simp
    linear_combination ((a.2 : ℂ) * ρ.2) * Complex.I_sq
  rw [e, norm_div]
  have hn : ‖(dS : ℂ)‖ = dS := by
    rw [show (dS : ℂ) = ((dS : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg hS.le]
  rw [hn]
  apply div_le_div_of_nonneg_right _ hS.le
  refine (norm_re_add_im_le _ _).trans ?_
  have hx' := dual_ediv x
  have hy' := dual_ediv y
  rw [abs_of_nonneg hx'.1, abs_of_nonneg hy'.1]
  linarith [hx'.2, hy'.2]

theorem dualMul_sound {E R : ℂ} {a ρ : ℤ × ℤ} {e : ℝ} (hR : ‖R‖ = 1) (hE : ‖E‖ = 1)
    (ha : ‖E - toC a‖ ≤ e) (hρ : ‖R - toC ρ‖ ≤ 3 / dS) (he : e ≤ 1) :
    ‖E * R - toC (dualMul a ρ)‖ ≤ e + 8 / dS := by
  have hS := dS_pos
  have h1 : ‖toC a‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' (toC a) E
    rw [norm_sub_rev] at this
    linarith
  have h2 := dualMul_round a ρ
  calc ‖E * R - toC (dualMul a ρ)‖
      = ‖(E - toC a) * R + toC a * (R - toC ρ) + (toC a * toC ρ - toC (dualMul a ρ))‖ := by
        congr 1; ring
    _ ≤ ‖(E - toC a) * R‖ + ‖toC a * (R - toC ρ)‖ + ‖toC a * toC ρ - toC (dualMul a ρ)‖ :=
        norm_add₃_le
    _ ≤ e * 1 + 2 * (3 / dS) + 2 / dS := by
        rw [norm_mul, norm_mul, hR]
        have h3 : ‖toC a‖ * ‖R - toC ρ‖ ≤ 2 * (3 / dS) :=
          mul_le_mul h1 hρ (norm_nonneg _) (by norm_num)
        nlinarith [norm_nonneg (E - toC a)]
    _ = e + 8 / dS := by ring

/-! ## Lists of nodes and states -/

/-- the node `v = V / dDv`. -/
noncomputable def dualV (n : ℤ × ℤ) : ℝ := (n.1 : ℝ) / dDv

/-- `st` approximates `(e^{i y v_k})_k` within `e`. -/
def DualClose (e y : ℝ) (ns st : List (ℤ × ℤ)) : Prop :=
  List.Forall₂ (fun n s => ‖eI (y * dualV n) - toC s‖ ≤ e) ns st

theorem DualClose.mono {e e' y : ℝ} {ns st : List (ℤ × ℤ)} (h : DualClose e y ns st)
    (he : e ≤ e') : DualClose e' y ns st :=
  List.Forall₂.imp (fun _ _ hh => hh.trans he) h

/-- advance all phases by the rotations `rs`. -/
def dualAdv (st rs : List (ℤ × ℤ)) : List (ℤ × ℤ) := List.zipWith dualMul st rs

theorem dualAdv_sound {e y δ : ℝ} {ns st rs : List (ℤ × ℤ)} (h : DualClose e y ns st)
    (hr : DualClose (3 / dS) δ ns rs) (he : e ≤ 1) :
    DualClose (e + 8 / dS) (y + δ) ns (dualAdv st rs) := by
  unfold DualClose at h hr ⊢
  induction h generalizing rs with
  | nil => cases hr; exact List.Forall₂.nil
  | cons hab _ ih =>
    cases hr with
    | cons hρ hrest =>
      simp only [dualAdv, List.zipWith_cons_cons]
      refine List.Forall₂.cons ?_ (ih hrest)
      rw [add_mul, eI_add]
      exact dualMul_sound (norm_eI _) (norm_eI _) hab hρ he

/-- `∑ c(n) · s_n` over nodes and state. -/
def dualWsum (c : ℤ × ℤ → ℤ) : List (ℤ × ℤ) → List (ℤ × ℤ) → ℤ × ℤ
  | n :: ns, s :: ss => (c n * s.1 + (dualWsum c ns ss).1, c n * s.2 + (dualWsum c ns ss).2)
  | _, _ => (0, 0)

/-- `∑ c(n) e^{i y v_n}`. -/
noncomputable def dualA (c : ℤ × ℤ → ℤ) (ns : List (ℤ × ℤ)) (y : ℝ) : ℂ :=
  (ns.map fun n => ((c n : ℤ) : ℂ) * eI (y * dualV n)).sum

/-- `∑ |c(n)|`. -/
def dualAbs (c : ℤ × ℤ → ℤ) (ns : List (ℤ × ℤ)) : ℤ := (ns.map fun n => |c n|).sum

theorem dualAbs_nonneg (c : ℤ × ℤ → ℤ) (ns : List (ℤ × ℤ)) : 0 ≤ dualAbs c ns := by
  induction ns with
  | nil => simp [dualAbs]
  | cons n ns ih => simp only [dualAbs, List.map_cons, List.sum_cons] at ih ⊢; positivity

theorem toC_wsum_cons (c : ℤ) (s r : ℤ × ℤ) :
    toC (c * s.1 + r.1, c * s.2 + r.2) = (c : ℂ) * toC s + toC r := by
  simp only [toC]; push_cast; ring

theorem dualWsum_sound (c : ℤ × ℤ → ℤ) {e y : ℝ} {ns st : List (ℤ × ℤ)}
    (h : DualClose e y ns st) :
    ‖dualA c ns y - toC (dualWsum c ns st)‖ ≤ (dualAbs c ns : ℝ) * e := by
  unfold DualClose at h
  induction h with
  | nil => simp [dualA, dualWsum, dualAbs, toC]
  | @cons n s ns ss hab _ ih =>
    simp only [dualA, dualWsum, dualAbs, List.map_cons, List.sum_cons] at ih ⊢
    rw [toC_wsum_cons]
    push_cast
    calc ‖(c n : ℂ) * eI (y * dualV n) + (ns.map fun n => ((c n : ℤ) : ℂ) * eI (y * dualV n)).sum
            - ((c n : ℂ) * toC s + toC (dualWsum c ns ss))‖
        = ‖(c n : ℂ) * (eI (y * dualV n) - toC s)
            + ((ns.map fun n => ((c n : ℤ) : ℂ) * eI (y * dualV n)).sum
                - toC (dualWsum c ns ss))‖ := by congr 1; ring
      _ ≤ ‖(c n : ℂ) * (eI (y * dualV n) - toC s)‖
            + ‖(ns.map fun n => ((c n : ℤ) : ℂ) * eI (y * dualV n)).sum
                - toC (dualWsum c ns ss)‖ := norm_add_le _ _
      _ ≤ |(c n : ℝ)| * e + ((ns.map fun n => |c n|).sum : ℤ) * e := by
          refine add_le_add ?_ ih
          rw [norm_mul]
          refine mul_le_mul (le_of_eq ?_) hab (norm_nonneg _) (abs_nonneg _)
          rw [show ((c n : ℤ) : ℂ) = (((c n : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
            Real.norm_eq_abs]
      _ = _ := by push_cast; ring

theorem dualA_norm_le (c : ℤ × ℤ → ℤ) (ns : List (ℤ × ℤ)) (y : ℝ) :
    ‖dualA c ns y‖ ≤ (dualAbs c ns : ℝ) := by
  induction ns with
  | nil => simp [dualA, dualAbs]
  | cons n ns ih =>
    simp only [dualA, dualAbs, List.map_cons, List.sum_cons] at ih ⊢
    rw [Int.cast_add, Int.cast_abs]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ih)
    rw [norm_mul, norm_eI, mul_one,
      show ((c n : ℤ) : ℂ) = (((c n : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs]

theorem dualA_neg (c : ℤ × ℤ → ℤ) (ns : List (ℤ × ℤ)) (y : ℝ) :
    dualA c ns (-y) = (starRingEnd ℂ) (dualA c ns y) := by
  induction ns with
  | nil => simp [dualA]
  | cons n ns ih =>
    simp only [dualA, List.map_cons, List.sum_cons] at ih ⊢
    rw [map_add, ← ih, neg_mul, eI_neg]
    simp

/-- the three weights: `α`, `α V`, `α V²`. -/
def dualC0 (n : ℤ × ℤ) : ℤ := n.2
def dualC1 (n : ℤ × ℤ) : ℤ := n.2 * n.1
def dualC2 (n : ℤ × ℤ) : ℤ := n.2 * n.1 ^ 2

/-- second order Taylor bound for the exponential sum. -/
theorem dualA_second (ns : List (ℤ × ℤ)) (y τ : ℝ) :
    ‖dualA dualC0 ns (y + τ) - dualA dualC0 ns y - (τ : ℂ) * I * dualA dualC1 ns y / (dDv : ℂ)‖
      ≤ τ ^ 2 / 2 * ((dualAbs dualC2 ns : ℝ) / (dDv : ℝ) ^ 2) := by
  have hD := dDv_pos
  have hDc : (dDv : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  induction ns with
  | nil => simp [dualA, dualAbs]
  | cons n ns ih =>
    simp only [dualA, dualAbs, List.map_cons, List.sum_cons] at ih ⊢
    set R0 := (ns.map fun n => ((dualC0 n : ℤ) : ℂ) * eI ((y + τ) * dualV n)).sum
    set R1 := (ns.map fun n => ((dualC0 n : ℤ) : ℂ) * eI (y * dualV n)).sum
    set R2 := (ns.map fun n => ((dualC1 n : ℤ) : ℂ) * eI (y * dualV n)).sum
    have hterm : ‖((dualC0 n : ℤ) : ℂ) * eI (y * dualV n)
        * (eI (τ * dualV n) - 1 - I * ((τ * dualV n : ℝ) : ℂ))‖
        ≤ τ ^ 2 / 2 * ((|dualC2 n| : ℤ) / (dDv : ℝ) ^ 2) := by
      rw [norm_mul, norm_mul, norm_eI, mul_one,
        show ((dualC0 n : ℤ) : ℂ) = (((dualC0 n : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs]
      have h2 := eI_second (τ * dualV n)
      have h3 : |((dualC0 n : ℤ) : ℝ)| * ((τ * dualV n) ^ 2 / 2)
          = τ ^ 2 / 2 * ((|dualC2 n| : ℤ) / (dDv : ℝ) ^ 2) := by
        simp only [dualC0, dualC2, dualV]
        push_cast
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n.1 : ℝ) ^ 2)]
        field_simp
      rw [← h3]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have e : ((dualC0 n : ℤ) : ℂ) * eI ((y + τ) * dualV n) + R0
          - (((dualC0 n : ℤ) : ℂ) * eI (y * dualV n) + R1)
          - (τ : ℂ) * I * (((dualC1 n : ℤ) : ℂ) * eI (y * dualV n) + R2) / (dDv : ℂ)
        = ((dualC0 n : ℤ) : ℂ) * eI (y * dualV n)
            * (eI (τ * dualV n) - 1 - I * ((τ * dualV n : ℝ) : ℂ))
          + (R0 - R1 - (τ : ℂ) * I * R2 / (dDv : ℂ)) := by
      rw [add_mul, eI_add]
      simp only [dualC0, dualC1, dualV]
      push_cast
      field_simp
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := add_le_add hterm ih
    refine this.trans (le_of_eq ?_)
    push_cast
    ring

/-! ## Rotations: Taylor polynomials in `ℚ` -/

/-- number of Taylor terms. -/
def dNT : ℕ := 24

/-- `acc + ∑_{i<k} (iz)^{m+i}/(m+i)!` with `t = (iz)^m/m!`, as pairs (re, im). -/
def dualTayAux (z : ℚ) : ℕ → ℕ → ℚ × ℚ → ℚ × ℚ → ℚ × ℚ
  | 0, _, _, acc => acc
  | k + 1, m, t, acc =>
    dualTayAux z k (m + 1) (-(t.2 * z / (m + 1)), t.1 * z / (m + 1)) (acc.1 + t.1, acc.2 + t.2)

def dualTay (z : ℚ) (n : ℕ) : ℚ × ℚ := dualTayAux z n 0 (1, 0) (0, 0)

/-- cast of a rational pair. -/
noncomputable def toCq (p : ℚ × ℚ) : ℂ := ((p.1 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * I

theorem dualTayAux_spec (z : ℚ) (k m : ℕ) (t acc : ℚ × ℚ)
    (ht : toCq t = (I * ((z : ℝ) : ℂ)) ^ m / (m.factorial : ℂ)) :
    toCq (dualTayAux z k m t acc)
      = toCq acc + ∑ i ∈ Finset.range k, (I * ((z : ℝ) : ℂ)) ^ (m + i) / ((m + i).factorial : ℂ) := by
  induction k generalizing m t acc with
  | zero => simp [dualTayAux]
  | succ k ih =>
    rw [dualTayAux, ih]
    · rw [Finset.sum_range_succ']
      have : toCq (acc.1 + t.1, acc.2 + t.2) = toCq acc + toCq t := by
        simp only [toCq]; push_cast; ring
      rw [this, ht, add_assoc]
      congr 1
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [show m + 1 + i = m + (i + 1) by ring]
    · have hm : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      have e : toCq (-(t.2 * z / (m + 1)), t.1 * z / (m + 1))
          = toCq t * (I * ((z : ℝ) : ℂ)) / ((m : ℂ) + 1) := by
        simp only [toCq]
        push_cast
        field_simp
        linear_combination (-((t.2 : ℂ) * (z : ℂ))) * Complex.I_sq
      rw [e, ht, pow_succ, Nat.factorial_succ]
      push_cast
      field_simp

theorem dualTay_spec (z : ℚ) (n : ℕ) :
    toCq (dualTay z n) = ∑ m ∈ Finset.range n, (I * ((z : ℝ) : ℂ)) ^ m / (m.factorial : ℂ) := by
  rw [dualTay, dualTayAux_spec z n 0 (1, 0) (0, 0) (by simp [toCq])]
  simp [toCq]

/-- `ρ / dS` is within `3 / dS` of `e^{i δ V / dDv}`. -/
def dualRotOK (δ : ℚ) (V : ℤ) (ρ : ℤ × ℤ) : Bool :=
  decide (|δ * V / dDv| ≤ 1)
    && decide (|δ * V / dDv| ^ dNT * ((dNT + 1 : ℚ) / (dNT.factorial * dNT)) ≤ 1 / dS)
    && decide (|(dualTay (δ * V / dDv) dNT).1 - ρ.1 / dS| ≤ 1 / dS)
    && decide (|(dualTay (δ * V / dDv) dNT).2 - ρ.2 / dS| ≤ 1 / dS)

theorem dualRotOK_sound {δ : ℚ} {V : ℤ} {ρ : ℤ × ℤ} (h : dualRotOK δ V ρ = true) :
    ‖eI ((δ : ℝ) * ((V : ℝ) / dDv)) - toC ρ‖ ≤ 3 / dS := by
  have hS := dS_pos
  simp only [dualRotOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  set z : ℚ := δ * V / dDv with hz
  have ez : (δ : ℝ) * ((V : ℝ) / dDv) = (z : ℝ) := by rw [hz]; push_cast; ring
  have h1' : |(z : ℝ)| ≤ 1 := by exact_mod_cast h1
  have h2' : |(z : ℝ)| ^ dNT * ((dNT + 1 : ℝ) / (dNT.factorial * dNT)) ≤ 1 / dS := by
    have := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at this
    exact this
  have h3' : |(((dualTay z dNT).1 : ℚ) : ℝ) - (ρ.1 : ℝ) / dS| ≤ 1 / dS := by exact_mod_cast h3
  have h4' : |(((dualTay z dNT).2 : ℚ) : ℝ) - (ρ.2 : ℝ) / dS| ≤ 1 / dS := by exact_mod_cast h4
  have t1 := (eI_taylor h1' (n := dNT) (by norm_num [dNT])).trans h2'
  rw [← dualTay_spec] at t1
  have e : toCq (dualTay z dNT) - toC ρ
      = (((((dualTay z dNT).1 : ℚ) : ℝ) - (ρ.1 : ℝ) / dS : ℝ) : ℂ)
        + (((((dualTay z dNT).2 : ℚ) : ℝ) - (ρ.2 : ℝ) / dS : ℝ) : ℂ) * I := by
    simp only [toCq, toC]; push_cast; ring
  have t2 : ‖toCq (dualTay z dNT) - toC ρ‖ ≤ 2 / dS := by
    rw [e]; refine (norm_re_add_im_le _ _).trans ?_
    exact (add_le_add h3' h4').trans_eq (by ring)
  rw [ez]
  calc ‖eI (z : ℝ) - toC ρ‖
      = ‖(eI (z : ℝ) - toCq (dualTay z dNT)) + (toCq (dualTay z dNT) - toC ρ)‖ := by
        congr 1; ring
    _ ≤ 1 / dS + 2 / dS := (norm_add_le _ _).trans (add_le_add t1 t2)
    _ = 3 / dS := by ring

def dualRotsOK (δ : ℚ) : List (ℤ × ℤ) → List (ℤ × ℤ) → Bool
  | [], [] => true
  | n :: ns, ρ :: rs => dualRotOK δ n.1 ρ && dualRotsOK δ ns rs
  | _, _ => false

theorem dualRotsOK_sound {δ : ℚ} : ∀ {ns rs : List (ℤ × ℤ)}, dualRotsOK δ ns rs = true →
    DualClose (3 / dS) (δ : ℝ) ns rs
  | [], [], _ => List.Forall₂.nil
  | n :: ns, ρ :: rs, h => by
    simp only [dualRotsOK, Bool.and_eq_true] at h
    exact List.Forall₂.cons (dualRotOK_sound h.1) (dualRotsOK_sound h.2)
  | [], _ :: _, h => by simp [dualRotsOK] at h
  | _ :: _, [], h => by simp [dualRotsOK] at h

/-! ## The cell check -/

def dualNewton (q : ℚ) : ℕ → ℚ → ℚ
  | 0, x => x
  | k + 1, x => dualNewton q k ((x + q / x) / 2)

/-- a rational `σ ≥ √(1/4 + y²)` (this property is re-checked in `dualChk`, not proved). -/
def dualSig (y : ℚ) : ℚ :=
  (((dualNewton (1 / 4 + y * y) 5 (1 / 2 + y) * 10000000000000).floor + 1 : ℤ) : ℚ) / 10000000000000

/-- parameters: `B ≥ ∑|a|`, `B1 ≥ ∑|a|v`, `M2 ≥ ∑|a|v²`, and the constant `cp`. -/
structure DualPar where
  B : ℚ
  B1 : ℚ
  M2 : ℚ
  cp : ℚ

def DualParOK (P : DualPar) (ns : List (ℤ × ℤ)) : Prop :=
  (dualAbs dualC0 ns : ℚ) / dSa ≤ P.B ∧ (dualAbs dualC1 ns : ℚ) / (dSa * dDv) ≤ P.B1
    ∧ (dualAbs dualC2 ns : ℚ) / (dSa * dDv ^ 2) ≤ P.M2 ∧ 0 ≤ P.cp

/-- Boolean version of `DualParOK`. -/
def dualParChk (P : DualPar) (ns : List (ℤ × ℤ)) : Bool :=
  decide ((dualAbs dualC0 ns : ℚ) / dSa ≤ P.B) && decide ((dualAbs dualC1 ns : ℚ) / (dSa * dDv) ≤ P.B1)
    && decide ((dualAbs dualC2 ns : ℚ) / (dSa * dDv ^ 2) ≤ P.M2) && decide (0 ≤ P.cp)

theorem dualParChk_sound {P : DualPar} {ns : List (ℤ × ℤ)} (h : dualParChk P ns = true) :
    DualParOK P ns := by
  simp only [dualParChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- endpoint inequality `‖N₀ + sg·r·N₁‖ ≤ cp (1/4 + y (y + sg·r))/σ - ε`, squared. -/
def dualChk1 (P : DualPar) (p0 p1 : ℤ × ℤ) (y r eps sig sg : ℚ) : Bool :=
  decide (0 ≤ P.cp * (1 / 4 + y * (y + sg * r)) / sig - eps) &&
  decide ((p0.1 / (dSa * dS) - sg * r * (p1.2 / (dSa * dS * dDv))) ^ 2
        + (p0.2 / (dSa * dS) + sg * r * (p1.1 / (dSa * dS * dDv))) ^ 2
      ≤ (P.cp * (1 / 4 + y * (y + sg * r)) / sig - eps) ^ 2)

/-- the check for the cell `[y - r, y + r]`; `st` approximates the phases at `y` within `err/dS`. -/
def dualChk (P : DualPar) (ns : List (ℤ × ℤ)) (y r : ℚ) (err : ℕ) (st : List (ℤ × ℤ)) : Bool :=
  decide (0 < dualSig y) && decide (1 / 4 + y * y ≤ dualSig y ^ 2) &&
  dualChk1 P (dualWsum dualC0 ns st) (dualWsum dualC1 ns st) y r
      ((P.B + r * P.B1) * (err / dS) + r * r * P.M2 / 2) (dualSig y) 1 &&
  dualChk1 P (dualWsum dualC0 ns st) (dualWsum dualC1 ns st) y r
      ((P.B + r * P.B1) * (err / dS) + r * r * P.M2 / 2) (dualSig y) (-1)

/-- the exponential sum `N(y) = ∑ (α/dSa) e^{i y V/dDv}`. -/
noncomputable def dualNq (ns : List (ℤ × ℤ)) (y : ℝ) : ℂ := dualA dualC0 ns y / (dSa : ℂ)

theorem dual_norm_div_int (z : ℂ) {d : ℤ} (hd : (0 : ℝ) < d) : ‖z / (d : ℂ)‖ = ‖z‖ / d := by
  rw [norm_div, show (d : ℂ) = ((d : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_of_nonneg hd.le]

theorem dual_tangent {y t σ : ℝ} (hσ0 : 0 < σ) (hσ : 1 / 4 + y ^ 2 ≤ σ ^ 2) :
    (1 / 4 + y * t) / σ ≤ Real.sqrt (1 / 4 + t ^ 2) := by
  rw [div_le_iff₀ hσ0]
  have h1 : (1 / 4 + y * t) ^ 2 ≤ (1 / 4 + y ^ 2) * (1 / 4 + t ^ 2) := by
    nlinarith [sq_nonneg (y - t)]
  have h2 : |1 / 4 + y * t| ≤ Real.sqrt ((1 / 4 + y ^ 2) * (1 / 4 + t ^ 2)) := Real.abs_le_sqrt h1
  have h3 : Real.sqrt ((1 / 4 + y ^ 2) * (1 / 4 + t ^ 2)) ≤ Real.sqrt (1 / 4 + t ^ 2) * σ := by
    rw [mul_comm, Real.sqrt_mul (by positivity)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hσ0.le, hσ⟩) (Real.sqrt_nonneg _)
  exact (le_abs_self _).trans (h2.trans h3)

theorem dual_convex {N0 N1 : ℂ} {r τ α β : ℝ} (hr : 0 < r) (hτ : |τ| ≤ r)
    (hp : ‖N0 + (r : ℂ) * N1‖ ≤ α + β * r) (hm : ‖N0 - (r : ℂ) * N1‖ ≤ α - β * r) :
    ‖N0 + (τ : ℂ) * N1‖ ≤ α + β * τ := by
  obtain ⟨h1, h2⟩ := abs_le.mp hτ
  set l : ℝ := (r + τ) / (2 * r) with hl
  have hl0 : 0 ≤ l := div_nonneg (by linarith) (by linarith)
  have hl1 : 0 ≤ 1 - l := by rw [hl, sub_nonneg, div_le_one (by linarith)]; linarith
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e : N0 + (τ : ℂ) * N1
      = (l : ℂ) * (N0 + (r : ℂ) * N1) + ((1 - l : ℝ) : ℂ) * (N0 - (r : ℂ) * N1) := by
    rw [hl]; push_cast; field_simp; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hl0,
    Real.norm_of_nonneg hl1]
  have e2 : α + β * τ = l * (α + β * r) + (1 - l) * (α - β * r) := by
    rw [hl]; field_simp; ring
  rw [e2]
  exact add_le_add (mul_le_mul_of_nonneg_left hp hl0) (mul_le_mul_of_nonneg_left hm hl1)

theorem dualChk1_sound {P : DualPar} {p0 p1 : ℤ × ℤ} {y r eps sig sg : ℚ}
    (h : dualChk1 P p0 p1 y r eps sig sg = true) :
    ‖toC p0 / (dSa : ℂ) + ((sg : ℝ) : ℂ) * ((r : ℝ) : ℂ) * (I * toC p1 / ((dSa : ℂ) * (dDv : ℂ)))‖
      ≤ (P.cp : ℝ) * (1 / 4 + (y : ℝ) * ((y : ℝ) + (sg : ℝ) * (r : ℝ))) / (sig : ℝ) - (eps : ℝ) := by
  simp only [dualChk1, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  have h0' := (Rat.cast_le (K := ℝ)).mpr h0
  have h1' := (Rat.cast_le (K := ℝ)).mpr h1
  push_cast at h0' h1'
  have e : toC p0 / (dSa : ℂ) + ((sg : ℝ) : ℂ) * ((r : ℝ) : ℂ) * (I * toC p1 / ((dSa : ℂ) * (dDv : ℂ)))
      = (((p0.1 : ℝ) / (dSa * dS) - sg * r * (p1.2 / (dSa * dS * dDv)) : ℝ) : ℂ)
        + (((p0.2 : ℝ) / (dSa * dS) + sg * r * (p1.1 / (dSa * dS * dDv)) : ℝ) : ℂ) * I := by
    simp only [toC]
    push_cast
    linear_combination ((sg : ℂ) * r * p1.2 / ((dS : ℂ) * dSa * dDv)) * Complex.I_sq
  rw [e, Complex.norm_add_mul_I]
  exact Real.sqrt_le_iff.mpr ⟨h0', h1'⟩

theorem dualChk_sound {P : DualPar} {ns : List (ℤ × ℤ)} (hP : DualParOK P ns) {y r : ℚ} {err : ℕ}
    {st : List (ℤ × ℤ)} (hr : 0 < r) (hcl : DualClose ((err : ℝ) / dS) (y : ℝ) ns st)
    (h : dualChk P ns y r err st = true) {τ : ℝ} (hτ : |τ| ≤ (r : ℝ)) :
    ‖dualNq ns ((y : ℝ) + τ)‖ ≤ (P.cp : ℝ) * Real.sqrt (1 / 4 + ((y : ℝ) + τ) ^ 2) := by
  obtain ⟨hB, hB1, hM2, hcp⟩ := hP
  simp only [dualChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hσ0, hσ⟩, hp⟩, hm⟩ := h
  have hp' := dualChk1_sound hp
  have hm' := dualChk1_sound hm
  have hSa := dSa_pos
  have hDv := dDv_pos
  have hS := dS_pos
  have hSaD : (0 : ℝ) < ((dSa * dDv : ℤ) : ℝ) := by push_cast; positivity
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hσ0' : (0 : ℝ) < (dualSig y : ℝ) := by exact_mod_cast hσ0
  have hσ' : 1 / 4 + (y : ℝ) ^ 2 ≤ (dualSig y : ℝ) ^ 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hσ
    push_cast at this
    nlinarith [this]
  have hcp' : (0 : ℝ) ≤ P.cp := by exact_mod_cast hcp
  have he0 : (0 : ℝ) ≤ (err : ℝ) / dS := by positivity
  have hB' : (dualAbs dualC0 ns : ℝ) / dSa ≤ P.B := by
    have := (Rat.cast_le (K := ℝ)).mpr hB
    push_cast at this; exact this
  have hB1' : (dualAbs dualC1 ns : ℝ) / (dSa * dDv) ≤ P.B1 := by
    have := (Rat.cast_le (K := ℝ)).mpr hB1
    push_cast at this; exact this
  have hM2' : (dualAbs dualC2 ns : ℝ) / (dSa * dDv ^ 2) ≤ P.M2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hM2
    push_cast at this; exact this
  -- approximations of `N(y)`, `N'(y)`
  have a0 : ‖dualA dualC0 ns y / (dSa : ℂ) - toC (dualWsum dualC0 ns st) / (dSa : ℂ)‖
      ≤ P.B * ((err : ℝ) / dS) := by
    rw [← sub_div, dual_norm_div_int _ hSa]
    calc _ ≤ (dualAbs dualC0 ns : ℝ) * ((err : ℝ) / dS) / dSa :=
          div_le_div_of_nonneg_right (dualWsum_sound dualC0 hcl) hSa.le
      _ = (dualAbs dualC0 ns : ℝ) / dSa * ((err : ℝ) / dS) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hB' he0
  have a1 : ‖I * dualA dualC1 ns y / ((dSa : ℂ) * (dDv : ℂ))
        - I * toC (dualWsum dualC1 ns st) / ((dSa : ℂ) * (dDv : ℂ))‖ ≤ P.B1 * ((err : ℝ) / dS) := by
    rw [← sub_div, ← mul_sub, show ((dSa : ℂ) * (dDv : ℂ)) = ((dSa * dDv : ℤ) : ℂ) by push_cast; rfl,
      dual_norm_div_int _ hSaD, norm_mul, Complex.norm_I, one_mul]
    calc _ ≤ (dualAbs dualC1 ns : ℝ) * ((err : ℝ) / dS) / ((dSa * dDv : ℤ) : ℝ) :=
          div_le_div_of_nonneg_right (dualWsum_sound dualC1 hcl) hSaD.le
      _ = (dualAbs dualC1 ns : ℝ) / (dSa * dDv) * ((err : ℝ) / dS) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hB1' he0
  -- second order
  have s2 : ‖dualNq ns ((y : ℝ) + τ) - dualA dualC0 ns y / (dSa : ℂ)
        - (τ : ℂ) * (I * dualA dualC1 ns y / ((dSa : ℂ) * (dDv : ℂ)))‖ ≤ (r : ℝ) * r * P.M2 / 2 := by
    have hDc : (dDv : ℂ) ≠ 0 := by exact_mod_cast hDv.ne'
    have hSc : (dSa : ℂ) ≠ 0 := by exact_mod_cast hSa.ne'
    have e : dualNq ns ((y : ℝ) + τ) - dualA dualC0 ns y / (dSa : ℂ)
        - (τ : ℂ) * (I * dualA dualC1 ns y / ((dSa : ℂ) * (dDv : ℂ)))
        = (dualA dualC0 ns ((y : ℝ) + τ) - dualA dualC0 ns y
            - (τ : ℂ) * I * dualA dualC1 ns y / (dDv : ℂ)) / (dSa : ℂ) := by
      simp only [dualNq]; field_simp
    rw [e, dual_norm_div_int _ hSa]
    have hτ2 : τ ^ 2 ≤ (r : ℝ) * r := by
      have := abs_le.mp hτ; nlinarith
    have hM0 : (0 : ℝ) ≤ (dualAbs dualC2 ns : ℝ) / (dSa * dDv ^ 2) := by
      have : (0 : ℝ) ≤ (dualAbs dualC2 ns : ℝ) := by exact_mod_cast dualAbs_nonneg _ _
      positivity
    calc _ ≤ τ ^ 2 / 2 * ((dualAbs dualC2 ns : ℝ) / (dDv : ℝ) ^ 2) / dSa :=
          div_le_div_of_nonneg_right (dualA_second ns y τ) hSa.le
      _ = τ ^ 2 * ((dualAbs dualC2 ns : ℝ) / (dSa * dDv ^ 2)) / 2 := by field_simp
      _ ≤ (r : ℝ) * r * P.M2 / 2 := by
          have := mul_le_mul hτ2 hM2' hM0 (by positivity)
          linarith
  -- endpoints
  set N0 : ℂ := toC (dualWsum dualC0 ns st) / (dSa : ℂ) with hN0
  set N1 : ℂ := I * toC (dualWsum dualC1 ns st) / ((dSa : ℂ) * (dDv : ℂ)) with hN1
  set σ : ℝ := (dualSig y : ℝ) with hσdef
  set eps : ℝ := ((P.B : ℝ) + r * P.B1) * ((err : ℝ) / dS) + r * r * P.M2 / 2 with heps
  have hp2 : ‖N0 + ((r : ℝ) : ℂ) * N1‖
      ≤ ((P.cp : ℝ) * (1 / 4 + (y : ℝ) ^ 2) / σ - eps) + (P.cp * y / σ) * r := by
    have := hp'
    simp only [Rat.cast_one, Complex.ofReal_one, one_mul] at this
    refine this.trans (le_of_eq ?_)
    push_cast
    rw [heps]; field_simp; ring
  have hm2 : ‖N0 - ((r : ℝ) : ℂ) * N1‖
      ≤ ((P.cp : ℝ) * (1 / 4 + (y : ℝ) ^ 2) / σ - eps) - (P.cp * y / σ) * r := by
    have := hm'
    simp only [Rat.cast_neg, Rat.cast_one, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
      ← sub_eq_add_neg] at this
    refine this.trans (le_of_eq ?_)
    push_cast
    rw [heps]; field_simp; ring
  have hc := dual_convex hrR hτ hp2 hm2
  have hτr : |τ| * (P.B1 * ((err : ℝ) / dS)) ≤ r * (P.B1 * ((err : ℝ) / dS)) := by
    have hB10 : (0 : ℝ) ≤ P.B1 := by
      have : (0 : ℝ) ≤ (dualAbs dualC1 ns : ℝ) := by exact_mod_cast dualAbs_nonneg _ _
      exact le_trans (by positivity) hB1'
    exact mul_le_mul_of_nonneg_right hτ (by positivity)
  have key : ‖dualNq ns ((y : ℝ) + τ)‖ ≤ ‖N0 + (τ : ℂ) * N1‖ + eps := by
    have e : dualNq ns ((y : ℝ) + τ)
        = (dualNq ns ((y : ℝ) + τ) - dualA dualC0 ns y / (dSa : ℂ)
            - (τ : ℂ) * (I * dualA dualC1 ns y / ((dSa : ℂ) * (dDv : ℂ))))
          + (dualA dualC0 ns y / (dSa : ℂ) - N0)
          + (τ : ℂ) * (I * dualA dualC1 ns y / ((dSa : ℂ) * (dDv : ℂ)) - N1)
          + (N0 + (τ : ℂ) * N1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have t3 : ‖(τ : ℂ) * (I * dualA dualC1 ns y / ((dSa : ℂ) * (dDv : ℂ)) - N1)‖
        ≤ |τ| * (P.B1 * ((err : ℝ) / dS)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left a1 (abs_nonneg _)
    have := (norm_add₃_le (a := dualNq ns ((y : ℝ) + τ) - dualA dualC0 ns y / (dSa : ℂ)
            - (τ : ℂ) * (I * dualA dualC1 ns y / ((dSa : ℂ) * (dDv : ℂ))))
          (b := dualA dualC0 ns y / (dSa : ℂ) - N0)
          (c := (τ : ℂ) * (I * dualA dualC1 ns y / ((dSa : ℂ) * (dDv : ℂ)) - N1)))
    rw [heps]
    linarith
  calc ‖dualNq ns ((y : ℝ) + τ)‖ ≤ ‖N0 + (τ : ℂ) * N1‖ + eps := key
    _ ≤ (P.cp : ℝ) * ((1 / 4 + (y : ℝ) * ((y : ℝ) + τ)) / σ) := by
        refine (add_le_add hc (le_refl eps)).trans (le_of_eq ?_)
        field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dual_tangent hσ0' hσ') hcp'

/-! ## Cells, segments, the run -/

structure DualSt where
  st : List (ℤ × ℤ)
  err : ℕ
  y : ℚ

/-- one cell `[y, y + 2r]`: advance to the centre, check, advance to the right end. -/
def dualCell (P : DualPar) (ns : List (ℤ × ℤ)) (r : ℚ) (rs : List (ℤ × ℤ)) (s : DualSt) :
    Option DualSt :=
  if decide (0 < r) && decide ((s.err : ℤ) + 16 ≤ dS)
      && dualChk P ns (s.y + r) r (s.err + 8) (dualAdv s.st rs) then
    some ⟨dualAdv (dualAdv s.st rs) rs, s.err + 16, s.y + r + r⟩
  else none

def dualSeg (P : DualPar) (ns : List (ℤ × ℤ)) (r : ℚ) (rs : List (ℤ × ℤ)) : ℕ → DualSt → Option DualSt
  | 0, s => some s
  | n + 1, s =>
    match dualCell P ns r rs s with
    | none => none
    | some s' => dualSeg P ns r rs n s'

/-- `lv`: table of levels `(r, rotations)`; `prog`: list of `(level index, number of cells)`. -/
def dualRun (P : DualPar) (ns : List (ℤ × ℤ)) (lv : List (ℚ × List (ℤ × ℤ))) :
    List (ℕ × ℕ) → DualSt → Option DualSt
  | [], s => some s
  | p :: ps, s =>
    match lv[p.1]? with
    | none => none
    | some l =>
      match dualSeg P ns l.1 l.2 p.2 s with
      | none => none
      | some s' => dualRun P ns lv ps s'

def DualInv (ns : List (ℤ × ℤ)) (s : DualSt) : Prop :=
  DualClose ((s.err : ℝ) / dS) (s.y : ℝ) ns s.st

def DualBd (P : DualPar) (ns : List (ℤ × ℤ)) (t : ℝ) : Prop :=
  ‖dualNq ns t‖ ≤ (P.cp : ℝ) * Real.sqrt (1 / 4 + t ^ 2)

theorem dualCell_sound {P : DualPar} {ns : List (ℤ × ℤ)} (hP : DualParOK P ns) {r : ℚ}
    {rs : List (ℤ × ℤ)} (hrs : DualClose (3 / dS) (r : ℝ) ns rs) {s s' : DualSt}
    (hi : DualInv ns s) (h : dualCell P ns r rs s = some s') :
    DualInv ns s' ∧ (s.y : ℝ) ≤ s'.y ∧ ∀ t : ℝ, (s.y : ℝ) ≤ t → t ≤ s'.y → DualBd P ns t := by
  have hS := dS_pos
  unfold dualCell at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hr, herr⟩, hchk⟩ := hc
    have hs' : s' = ⟨dualAdv (dualAdv s.st rs) rs, s.err + 16, s.y + r + r⟩ :=
      (Option.some.inj h).symm
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have herr' : (s.err : ℝ) + 16 ≤ dS := by exact_mod_cast herr
    have he1 : (s.err : ℝ) / dS ≤ 1 := by rw [div_le_one hS]; linarith
    have he2 : ((s.err + 8 : ℕ) : ℝ) / dS ≤ 1 := by rw [div_le_one hS]; push_cast; linarith
    have c1 : DualClose (((s.err + 8 : ℕ) : ℝ) / dS) ((s.y + r : ℚ) : ℝ) ns (dualAdv s.st rs) := by
      have := dualAdv_sound hi hrs he1
      rw [show ((s.err + 8 : ℕ) : ℝ) / dS = (s.err : ℝ) / dS + 8 / dS by push_cast; ring,
        show ((s.y + r : ℚ) : ℝ) = (s.y : ℝ) + r by push_cast; rfl]
      exact this
    have c2 : DualInv ns s' := by
      have := dualAdv_sound c1 hrs he2
      rw [hs']
      unfold DualInv
      simp only
      rw [show ((s.err + 16 : ℕ) : ℝ) / dS = ((s.err + 8 : ℕ) : ℝ) / dS + 8 / dS by push_cast; ring,
        show ((s.y + r + r : ℚ) : ℝ) = ((s.y + r : ℚ) : ℝ) + r by push_cast; rfl]
      exact this
    have hy' : (s'.y : ℝ) = (s.y : ℝ) + r + r := by rw [hs']; push_cast; rfl
    refine ⟨c2, by rw [hy']; linarith, fun t ht1 ht2 => ?_⟩
    rw [hy'] at ht2
    have := dualChk_sound hP hr c1 hchk (τ := t - ((s.y : ℝ) + r))
      (by rw [abs_le]; constructor <;> linarith)
    unfold DualBd
    have e : ((s.y + r : ℚ) : ℝ) + (t - ((s.y : ℝ) + r)) = t := by push_cast; ring
    rwa [e] at this
  · exact absurd h (by simp)

theorem dualSeg_sound {P : DualPar} {ns : List (ℤ × ℤ)} (hP : DualParOK P ns) {r : ℚ}
    {rs : List (ℤ × ℤ)} (hrs : DualClose (3 / dS) (r : ℝ) ns rs) :
    ∀ (n : ℕ) {s s' : DualSt}, DualInv ns s → dualSeg P ns r rs n s = some s' →
      DualInv ns s' ∧ (s.y : ℝ) ≤ s'.y ∧ ∀ t : ℝ, (s.y : ℝ) ≤ t → t < s'.y → DualBd P ns t
  | 0, s, s', hi, h => by
    have : s = s' := Option.some.inj h
    subst this
    exact ⟨hi, le_refl _, fun t h1 h2 => absurd h2 (not_lt.mpr h1)⟩
  | n + 1, s, s', hi, h => by
    unfold dualSeg at h
    split at h
    · exact absurd h (by simp)
    · rename_i s1 hc
      obtain ⟨i1, y1, b1⟩ := dualCell_sound hP hrs hi hc
      obtain ⟨i2, y2, b2⟩ := dualSeg_sound hP hrs n i1 h
      refine ⟨i2, y1.trans y2, fun t h1 h2 => ?_⟩
      rcases lt_or_ge t (s1.y : ℝ) with ht | ht
      · exact b1 t h1 ht.le
      · exact b2 t ht h2

theorem dualRun_sound {P : DualPar} {ns : List (ℤ × ℤ)} (hP : DualParOK P ns)
    {lv : List (ℚ × List (ℤ × ℤ))} (hlv : ∀ l ∈ lv, DualClose (3 / dS) ((l.1 : ℚ) : ℝ) ns l.2) :
    ∀ (prog : List (ℕ × ℕ)) {s s' : DualSt}, DualInv ns s → dualRun P ns lv prog s = some s' →
      (s.y : ℝ) ≤ s'.y ∧ ∀ t : ℝ, (s.y : ℝ) ≤ t → t < s'.y → DualBd P ns t
  | [], s, s', _, h => by
    have : s = s' := Option.some.inj h
    subst this
    exact ⟨le_refl _, fun t h1 h2 => absurd h2 (not_lt.mpr h1)⟩
  | p :: ps, s, s', hi, h => by
    unfold dualRun at h
    split at h
    · exact absurd h (by simp)
    · rename_i l hl
      split at h
      · exact absurd h (by simp)
      · rename_i s1 hc
        obtain ⟨i1, y1, b1⟩ := dualSeg_sound hP (hlv l (List.mem_of_getElem? hl)) p.2 hi hc
        obtain ⟨y2, b2⟩ := dualRun_sound hP hlv ps i1 h
        refine ⟨y1.trans y2, fun t h1 h2 => ?_⟩
        rcases lt_or_ge t (s1.y : ℝ) with ht | ht
        · exact b1 t h1 ht
        · exact b2 t ht h2

/-- initial state: `y = 0`, all phases `1`. -/
def dualInit (ns : List (ℤ × ℤ)) : DualSt := ⟨ns.map fun _ => (dS, 0), 0, 0⟩

theorem dualInit_inv (ns : List (ℤ × ℤ)) : DualInv ns (dualInit ns) := by
  have hS : (dS : ℂ) ≠ 0 := by exact_mod_cast dS_pos.ne'
  unfold DualInv DualClose dualInit
  simp only
  induction ns with
  | nil => exact List.Forall₂.nil
  | cons n ns ih =>
    refine List.Forall₂.cons ?_ ih
    simp [toC, hS]

/-- the complete check: run the programme from `0` and compare the end point with the trivial
bound `‖N‖ ≤ B ≤ cp · y`. -/
def dualRunOK (P : DualPar) (ns : List (ℤ × ℤ)) (lv : List (ℚ × List (ℤ × ℤ)))
    (prog : List (ℕ × ℕ)) : Bool :=
  match dualRun P ns lv prog (dualInit ns) with
  | some f => decide (P.B ≤ P.cp * f.y)
  | none => false

/-- **Soundness of the certificate.** -/
theorem dual_cert {P : DualPar} {ns : List (ℤ × ℤ)} {lv : List (ℚ × List (ℤ × ℤ))}
    {prog : List (ℕ × ℕ)} (hP : dualParChk P ns = true)
    (hlv : lv.all (fun l => dualRotsOK l.1 ns l.2) = true)
    (hrun : dualRunOK P ns lv prog = true) (t : ℝ) :
    ‖dualNq ns t‖ ≤ (P.cp : ℝ) * Real.sqrt (1 / 4 + t ^ 2) := by
  have hP' := dualParChk_sound hP
  have hlv' : ∀ l ∈ lv, DualClose (3 / dS) ((l.1 : ℚ) : ℝ) ns l.2 := fun l hl =>
    dualRotsOK_sound (List.all_eq_true.mp hlv l hl)
  have hB := hP'.1
  have hcp := hP'.2.2.2
  have hcp' : (0 : ℝ) ≤ P.cp := by exact_mod_cast hcp
  have hSa := dSa_pos
  unfold dualRunOK at hrun
  split at hrun
  · rename_i f hf
    have hfin : (P.B : ℝ) ≤ P.cp * f.y := by
      have := (Rat.cast_le (K := ℝ)).mpr (of_decide_eq_true hrun)
      push_cast at this; exact this
    obtain ⟨y0, b⟩ := dualRun_sound hP' hlv' prog (dualInit_inv ns) hf
    have hy0 : ((dualInit ns).y : ℝ) = 0 := by simp [dualInit]
    rw [hy0] at y0 b
    have main : ∀ t : ℝ, 0 ≤ t → DualBd P ns t := by
      intro t ht
      rcases lt_or_ge t (f.y : ℝ) with h | h
      · exact b t ht h
      · unfold DualBd dualNq
        rw [dual_norm_div_int _ hSa]
        have h1 : ‖dualA dualC0 ns t‖ / dSa ≤ (dualAbs dualC0 ns : ℝ) / dSa :=
          div_le_div_of_nonneg_right (dualA_norm_le _ _ _) hSa.le
        have h2 : (dualAbs dualC0 ns : ℝ) / dSa ≤ P.B := by
          have := (Rat.cast_le (K := ℝ)).mpr hB
          push_cast at this; exact this
        have h3 : t ≤ Real.sqrt (1 / 4 + t ^ 2) :=
          (le_abs_self t).trans (Real.abs_le_sqrt (by linarith))
        calc _ ≤ (P.cp : ℝ) * f.y := h1.trans (h2.trans hfin)
          _ ≤ (P.cp : ℝ) * Real.sqrt (1 / 4 + t ^ 2) :=
            mul_le_mul_of_nonneg_left (h.trans h3) hcp'
    rcases le_total 0 t with ht | ht
    · exact main t ht
    · have h := main (-t) (by linarith)
      unfold DualBd dualNq at h
      rw [dualA_neg, norm_div, Complex.norm_conj, ← norm_div, neg_sq] at h
      exact h
  · exact absurd hrun (by simp)

end DetPrimality.Barrier
