import Mathlib

/-!
# A kernel-checkable certificate for `sup_y |N(y)| / √(1/4 + y²)`, `N` an exponential sum

`N(y) = ∑_k a_k e^{i y v_k}` with rational `a_k = α_k / dSa`, `v_k = V_k / dDv` (`ns : List (ℤ × ℤ)`
is the list of `(V_k, α_k)`).  The checker `dualRun` walks through `[0, T]` in cells
`[y - r, y + r]` (beyond `T` the trivial bound `|N| ≤ ∑|a_k| ≤ c·y` suffices, `dualTailOK`); on
each cell it uses

  `‖N(y+τ) - N(y) - τ N'(y)‖ ≤ τ² M₂ / 2`,  `τ ↦ ‖N(y) + τ N'(y)‖` convex,
  `√(1/4 + t²) ≥ (1/4 + y t)/σ` for `σ ≥ √(1/4 + y²)` (Cauchy–Schwarz),

so that the two endpoint inequalities `‖N(y) ± r N'(y)‖ ≤ c (1/4 + y (y ± r))/σ - ε` suffice.
The numbers `e^{i y v_k}` are carried along in fixed point arithmetic (scale `dS`) with a
rigorous error counter (`err` units of `1/dS`); the rotations `e^{i r v_k}` are checked against
their Taylor polynomials in `ℚ` (`dualRotsOK`).  The endpoint inequalities are specified in `ℚ`
(`dualChk1`, `dualChk_sound`) and executed with denominators cleared, in `ℤ` (`dualChkZ`).
Main results: `dual_cert_chain` (soundness of a run given in consecutive pieces) and `dual_cert`.
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

/-- parameters: `B ≥ ∑|a|`, `B1 ≥ ∑|a|v`, `M2 ≥ ∑|a|v²`, and the constant `cp`. -/
structure DualPar where
  B : ℚ
  B1 : ℚ
  M2 : ℚ
  cp : ℚ

def DualParOK (P : DualPar) (ns : List (ℤ × ℤ)) : Prop :=
  (dualAbs dualC0 ns : ℚ) / dSa ≤ P.B ∧ (dualAbs dualC1 ns : ℚ) / (dSa * dDv) ≤ P.B1
    ∧ (dualAbs dualC2 ns : ℚ) / (dSa * dDv ^ 2) ≤ P.M2 ∧ 0 ≤ P.cp

/-- endpoint inequality `‖N₀ + sg·r·N₁‖ ≤ cp (1/4 + y (y + sg·r))/σ - ε`, squared. -/
def dualChk1 (P : DualPar) (p0 p1 : ℤ × ℤ) (y r eps sig sg : ℚ) : Bool :=
  decide (0 ≤ P.cp * (1 / 4 + y * (y + sg * r)) / sig - eps) &&
  decide ((p0.1 / (dSa * dS) - sg * r * (p1.2 / (dSa * dS * dDv))) ^ 2
        + (p0.2 / (dSa * dS) + sg * r * (p1.1 / (dSa * dS * dDv))) ^ 2
      ≤ (P.cp * (1 / 4 + y * (y + sg * r)) / sig - eps) ^ 2)

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

theorem dualChk_sound {P : DualPar} {ns : List (ℤ × ℤ)} (hP : DualParOK P ns) {y r sig : ℚ}
    {err : ℕ} {st : List (ℤ × ℤ)} (hr : 0 < r) (hcl : DualClose ((err : ℝ) / dS) (y : ℝ) ns st)
    (hσ0 : 0 < sig) (hσ : 1 / 4 + y * y ≤ sig ^ 2)
    (hp : dualChk1 P (dualWsum dualC0 ns st) (dualWsum dualC1 ns st) y r
      ((P.B + r * P.B1) * (err / dS) + r * r * P.M2 / 2) sig 1 = true)
    (hm : dualChk1 P (dualWsum dualC0 ns st) (dualWsum dualC1 ns st) y r
      ((P.B + r * P.B1) * (err / dS) + r * r * P.M2 / 2) sig (-1) = true)
    {τ : ℝ} (hτ : |τ| ≤ (r : ℝ)) :
    ‖dualNq ns ((y : ℝ) + τ)‖ ≤ (P.cp : ℝ) * Real.sqrt (1 / 4 + ((y : ℝ) + τ) ^ 2) := by
  obtain ⟨hB, hB1, hM2, hcp⟩ := hP
  have hp' := dualChk1_sound hp
  have hm' := dualChk1_sound hm
  have hSa := dSa_pos
  have hDv := dDv_pos
  have hS := dS_pos
  have hSaD : (0 : ℝ) < ((dSa * dDv : ℤ) : ℝ) := by push_cast; positivity
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hσ0' : (0 : ℝ) < (sig : ℝ) := by exact_mod_cast hσ0
  have hσ' : 1 / 4 + (y : ℝ) ^ 2 ≤ (sig : ℝ) ^ 2 := by
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
  set σ : ℝ := (sig : ℝ) with hσdef
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

/-! ## The integer version of the cell check (the one that is executed) -/

/-- `y = Y / dQ`, `r = Rn / dQ`; `σ = Sg / dSd`; `cp = Cn / dCd`. -/
def dQ : ℤ := 65536
def dSd : ℤ := 10000000000000
def dCd : ℤ := 10000000

/-- integer parameters: `B = Bn/dSa`, `B1 = B1n/(dSa dDv)`, `M2 = M2n/(dSa dDv²)`, `cp = Cn/dCd`. -/
structure DualParZ where
  Bn : ℤ
  B1n : ℤ
  M2n : ℤ
  Cn : ℤ

def DualParZ.toQ (P : DualParZ) : DualPar :=
  ⟨P.Bn / dSa, P.B1n / (dSa * dDv), P.M2n / (dSa * dDv ^ 2), P.Cn / dCd⟩

def dualParChk (P : DualParZ) (ns : List (ℤ × ℤ)) : Bool :=
  decide (dualAbs dualC0 ns ≤ P.Bn) && decide (dualAbs dualC1 ns ≤ P.B1n)
    && decide (dualAbs dualC2 ns ≤ P.M2n) && decide (0 ≤ P.Cn)

theorem dualParChk_sound {P : DualParZ} {ns : List (ℤ × ℤ)} (h : dualParChk P ns = true) :
    DualParOK P.toQ ns := by
  simp only [dualParChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have hSa : (0 : ℚ) < dSa := by norm_num [dSa]
  have hDv : (0 : ℚ) < dDv := by norm_num [dDv]
  have hCd : (0 : ℚ) < dCd := by norm_num [dCd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast h0) hSa.le
  · exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (by positivity)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast h2) (by positivity)
  · exact div_nonneg (by exact_mod_cast h3) hCd.le

/-- all four sums `∑ α s`, `∑ α V s` in one pass. -/
def dualSumsAux : List (ℤ × ℤ) → List (ℤ × ℤ) → ℤ → ℤ → ℤ → ℤ → (ℤ × ℤ) × (ℤ × ℤ)
  | n :: ns, s :: ss, a, b, c, d =>
    dualSumsAux ns ss (a + n.2 * s.1) (b + n.2 * s.2) (c + n.2 * n.1 * s.1) (d + n.2 * n.1 * s.2)
  | [], _, a, b, c, d => ((a, b), (c, d))
  | _ :: _, [], a, b, c, d => ((a, b), (c, d))

def dualSums (ns st : List (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) := dualSumsAux ns st 0 0 0 0

theorem dualSumsAux_eq : ∀ (ns ss : List (ℤ × ℤ)) (a b c d : ℤ),
    dualSumsAux ns ss a b c d
      = ((a + (dualWsum dualC0 ns ss).1, b + (dualWsum dualC0 ns ss).2),
         (c + (dualWsum dualC1 ns ss).1, d + (dualWsum dualC1 ns ss).2))
  | n :: ns, s :: ss, a, b, c, d => by
    rw [dualSumsAux, dualSumsAux_eq ns ss]
    simp only [dualWsum, dualC0, dualC1, Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring
  | [], _, a, b, c, d => by simp [dualSumsAux, dualWsum]
  | _ :: _, [], a, b, c, d => by simp [dualSumsAux, dualWsum]

theorem dualSums_eq (ns st : List (ℤ × ℤ)) :
    dualSums ns st = (dualWsum dualC0 ns st, dualWsum dualC1 ns st) := by
  rw [dualSums, dualSumsAux_eq]; simp

def dualNewtZ (n : ℤ) : ℕ → ℤ → ℤ
  | 0, x => x
  | k + 1, x => dualNewtZ n k ((x + n / x) / 2)

/-- `Sg` with `Sg / dSd ≥ √(1/4 + (Y/dQ)²)`, slightly (re-checked in `dualChkZ`, not proved). -/
def dualSigZ (Y : ℤ) : ℤ :=
  dualNewtZ ((dQ * dQ + 4 * Y * Y) * (dSd * dSd) / (4 * dQ * dQ) + 1) 5 (dSd / 2 + Y * dSd / dQ + 1) + 1

/-- the endpoint inequality of `dualChk1` with denominators cleared. -/
def dualChk1Z (P : DualParZ) (p0 p1 : ℤ × ℤ) (Y Rn epsN Sg sg : ℤ) : Bool :=
  decide (0 ≤ P.Cn * (dQ * dQ + 4 * Y * (Y + sg * Rn)) * dSd * dSa * (dDv * dDv) * dS
      - 2 * dCd * Sg * epsN) &&
  decide (((dQ * dDv * p0.1 - sg * Rn * p1.2) ^ 2 + (dQ * dDv * p0.2 + sg * Rn * p1.1) ^ 2)
        * (4 * dQ * dCd * Sg * dDv) ^ 2
      ≤ (P.Cn * (dQ * dQ + 4 * Y * (Y + sg * Rn)) * dSd * dSa * (dDv * dDv) * dS
          - 2 * dCd * Sg * epsN) ^ 2)

/-- the check for the cell `[y - r, y + r]`, `y = Y/dQ`, `r = Rn/dQ`; `st` approximates the phases
at `y` within `err/dS`. -/
def dualChkZ (P : DualParZ) (ns : List (ℤ × ℤ)) (Y Rn : ℤ) (err : ℕ) (st : List (ℤ × ℤ)) : Bool :=
  decide (0 < dualSigZ Y)
    && decide ((dQ * dQ + 4 * Y * Y) * (dSd * dSd) ≤ 4 * dQ * dQ * (dualSigZ Y * dualSigZ Y))
    && dualChk1Z P (dualSums ns st).1 (dualSums ns st).2 Y Rn
        (2 * dQ * dDv * err * (dQ * dDv * P.Bn + Rn * P.B1n) + Rn * Rn * P.M2n * dS) (dualSigZ Y) 1
    && dualChk1Z P (dualSums ns st).1 (dualSums ns st).2 Y Rn
        (2 * dQ * dDv * err * (dQ * dDv * P.Bn + Rn * P.B1n) + Rn * Rn * P.M2n * dS) (dualSigZ Y) (-1)

theorem dualChk1Z_imp {P : DualParZ} {p0 p1 : ℤ × ℤ} {Y Rn epsN Sg sg : ℤ} (hSg : 0 < Sg)
    (h : dualChk1Z P p0 p1 Y Rn epsN Sg sg = true) :
    dualChk1 P.toQ p0 p1 ((Y : ℚ) / dQ) ((Rn : ℚ) / dQ)
      ((epsN : ℚ) / (2 * dQ ^ 2 * dSa * dDv ^ 2 * dS)) ((Sg : ℚ) / dSd) (sg : ℚ) = true := by
  simp only [dualChk1Z, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  simp only [dualChk1, Bool.and_eq_true, decide_eq_true_eq]
  simp only [DualParZ.toQ]
  have hQ : (0 : ℚ) < dQ := by norm_num [dQ]
  have hSd : (0 : ℚ) < dSd := by norm_num [dSd]
  have hCd : (0 : ℚ) < dCd := by norm_num [dCd]
  have hSa : (0 : ℚ) < dSa := by norm_num [dSa]
  have hDv : (0 : ℚ) < dDv := by norm_num [dDv]
  have hS : (0 : ℚ) < dS := by norm_num [dS]
  have hSg' : (0 : ℚ) < Sg := by exact_mod_cast hSg
  have hQ' := hQ.ne'
  have hSd' := hSd.ne'
  have hCd' := hCd.ne'
  have hSa' := hSa.ne'
  have hDv' := hDv.ne'
  have hS' := hS.ne'
  have hSg'' := hSg'.ne'
  set RN : ℤ := P.Cn * (dQ * dQ + 4 * Y * (Y + sg * Rn)) * dSd * dSa * (dDv * dDv) * dS
      - 2 * dCd * Sg * epsN with hRN
  set ReN : ℤ := dQ * dDv * p0.1 - sg * Rn * p1.2 with hReN
  set ImN : ℤ := dQ * dDv * p0.2 + sg * Rn * p1.1 with hImN
  have eR : (P.Cn : ℚ) / dCd * (1 / 4 + (Y : ℚ) / dQ * ((Y : ℚ) / dQ + (sg : ℚ) * ((Rn : ℚ) / dQ)))
        / ((Sg : ℚ) / dSd) - (epsN : ℚ) / (2 * dQ ^ 2 * dSa * dDv ^ 2 * dS)
      = (RN : ℚ) / (4 * dQ ^ 2 * dCd * Sg * dSa * dDv ^ 2 * dS) := by
    rw [hRN]; push_cast; field_simp; ring
  have eRe : (p0.1 : ℚ) / (dSa * dS) - (sg : ℚ) * ((Rn : ℚ) / dQ) * ((p1.2 : ℚ) / (dSa * dS * dDv))
      = (ReN : ℚ) / (dQ * dDv * dSa * dS) := by
    rw [hReN]; push_cast; field_simp
  have eIm : (p0.2 : ℚ) / (dSa * dS) + (sg : ℚ) * ((Rn : ℚ) / dQ) * ((p1.1 : ℚ) / (dSa * dS * dDv))
      = (ImN : ℚ) / (dQ * dDv * dSa * dS) := by
    rw [hImN]; push_cast; field_simp
  rw [eR, eRe, eIm]
  constructor
  · exact div_nonneg (by exact_mod_cast h0) (by positivity)
  · rw [div_pow, div_pow, div_pow, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1' : (((ReN : ℚ)) ^ 2 + (ImN : ℚ) ^ 2) * (4 * dQ * dCd * Sg * dDv) ^ 2 ≤ (RN : ℚ) ^ 2 := by
      exact_mod_cast h1
    have e : ((4 : ℚ) * dQ ^ 2 * dCd * Sg * dSa * dDv ^ 2 * dS)
        = (4 * dQ * dCd * Sg * dDv) * (dQ * dDv * dSa * dS) := by ring
    rw [e, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1' (by positivity)

theorem dualChkZ_sound {P : DualParZ} {ns : List (ℤ × ℤ)} (hP : DualParOK P.toQ ns) {Y Rn : ℤ}
    {err : ℕ} {st : List (ℤ × ℤ)} (hr : 0 < Rn)
    (hcl : DualClose ((err : ℝ) / dS) ((Y : ℝ) / dQ) ns st)
    (h : dualChkZ P ns Y Rn err st = true) {τ : ℝ} (hτ : |τ| ≤ (Rn : ℝ) / dQ) :
    ‖dualNq ns ((Y : ℝ) / dQ + τ)‖
      ≤ (P.Cn : ℝ) / dCd * Real.sqrt (1 / 4 + ((Y : ℝ) / dQ + τ) ^ 2) := by
  simp only [dualChkZ, Bool.and_eq_true, decide_eq_true_eq, dualSums_eq] at h
  obtain ⟨⟨⟨hσ0, hσ⟩, hp⟩, hm⟩ := h
  have hQ : (0 : ℚ) < dQ := by norm_num [dQ]
  have hSd : (0 : ℚ) < dSd := by norm_num [dSd]
  have hSa : (0 : ℚ) < dSa := by norm_num [dSa]
  have hDv : (0 : ℚ) < dDv := by norm_num [dDv]
  have hS : (0 : ℚ) < dS := by norm_num [dS]
  have hQ' := hQ.ne'
  have hSd' := hSd.ne'
  have hSa' := hSa.ne'
  have hDv' := hDv.ne'
  have hS' := hS.ne'
  have hp' := dualChk1Z_imp hσ0 hp
  have hm' := dualChk1Z_imp hσ0 hm
  have eeps : ((2 * dQ * dDv * (err : ℤ) * (dQ * dDv * P.Bn + Rn * P.B1n) + Rn * Rn * P.M2n * dS : ℤ) : ℚ)
        / (2 * dQ ^ 2 * dSa * dDv ^ 2 * dS)
      = (P.toQ.B + (Rn : ℚ) / dQ * P.toQ.B1) * ((err : ℚ) / dS)
          + (Rn : ℚ) / dQ * ((Rn : ℚ) / dQ) * P.toQ.M2 / 2 := by
    simp only [DualParZ.toQ]; push_cast; field_simp
  rw [eeps] at hp' hm'
  simp only [Int.cast_one, Int.cast_neg] at hp' hm'
  have hσ0' : (0 : ℚ) < (dualSigZ Y : ℚ) / dSd := div_pos (by exact_mod_cast hσ0) hSd
  have hσ' : (1 : ℚ) / 4 + (Y : ℚ) / dQ * ((Y : ℚ) / dQ) ≤ ((dualSigZ Y : ℚ) / dSd) ^ 2 := by
    have hz : (((dQ : ℚ) * dQ + 4 * Y * Y) * (dSd * dSd)) ≤ 4 * dQ * dQ * ((dualSigZ Y : ℚ) * dualSigZ Y) := by
      exact_mod_cast hσ
    rw [div_pow, le_div_iff₀ (by positivity)]
    have e : ((1 : ℚ) / 4 + (Y : ℚ) / dQ * ((Y : ℚ) / dQ)) * (dSd : ℚ) ^ 2
        = (((dQ : ℚ) * dQ + 4 * Y * Y) * (dSd * dSd)) / (4 * dQ * dQ) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have hrQ : (0 : ℚ) < (Rn : ℚ) / dQ := div_pos (by exact_mod_cast hr) hQ
  have hcl' : DualClose ((err : ℝ) / dS) (((Y : ℚ) / dQ : ℚ) : ℝ) ns st := by
    rw [show (((Y : ℚ) / dQ : ℚ) : ℝ) = (Y : ℝ) / dQ by push_cast; rfl]; exact hcl
  have hτ' : |τ| ≤ (((Rn : ℚ) / dQ : ℚ) : ℝ) := by
    rw [show (((Rn : ℚ) / dQ : ℚ) : ℝ) = (Rn : ℝ) / dQ by push_cast; rfl]; exact hτ
  have := dualChk_sound hP hrQ hcl' hσ0' hσ' hp' hm' hτ'
  rw [show (((Y : ℚ) / dQ : ℚ) : ℝ) = (Y : ℝ) / dQ by push_cast; rfl] at this
  rw [show ((P.toQ.cp : ℚ) : ℝ) = (P.Cn : ℝ) / dCd by simp only [DualParZ.toQ]; push_cast; rfl] at this
  exact this

/-! ## Cells, segments, the run -/

structure DualSt where
  st : List (ℤ × ℤ)
  err : ℕ
  Y : ℤ
deriving DecidableEq

/-- one cell `[y, y + 2r]`: advance to the centre, check, advance to the right end. -/
def dualCell (P : DualParZ) (ns : List (ℤ × ℤ)) (Rn : ℤ) (rs : List (ℤ × ℤ)) (s : DualSt) :
    Option DualSt :=
  if decide (0 < Rn) && decide ((s.err : ℤ) + 16 ≤ dS)
      && dualChkZ P ns (s.Y + Rn) Rn (s.err + 8) (dualAdv s.st rs) then
    some ⟨dualAdv (dualAdv s.st rs) rs, s.err + 16, s.Y + Rn + Rn⟩
  else none

def dualSeg (P : DualParZ) (ns : List (ℤ × ℤ)) (Rn : ℤ) (rs : List (ℤ × ℤ)) :
    ℕ → DualSt → Option DualSt
  | 0, s => some s
  | n + 1, s =>
    match dualCell P ns Rn rs s with
    | none => none
    | some s' => dualSeg P ns Rn rs n s'

/-- `lv`: table of levels `(Rn, rotations)`, `r = Rn/dQ`; `prog`: list of
`(level index, number of cells)`. -/
def dualRun (P : DualParZ) (ns : List (ℤ × ℤ)) (lv : List (ℤ × List (ℤ × ℤ))) :
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
  DualClose ((s.err : ℝ) / dS) ((s.Y : ℝ) / dQ) ns s.st

def DualBd (P : DualParZ) (ns : List (ℤ × ℤ)) (t : ℝ) : Prop :=
  ‖dualNq ns t‖ ≤ (P.Cn : ℝ) / dCd * Real.sqrt (1 / 4 + t ^ 2)

theorem dQ_pos : (0 : ℝ) < (dQ : ℝ) := by norm_num [dQ]

theorem dualCell_sound {P : DualParZ} {ns : List (ℤ × ℤ)} (hP : DualParOK P.toQ ns) {Rn : ℤ}
    {rs : List (ℤ × ℤ)} (hrs : DualClose (3 / dS) ((Rn : ℝ) / dQ) ns rs) {s s' : DualSt}
    (hi : DualInv ns s) (h : dualCell P ns Rn rs s = some s') :
    DualInv ns s' ∧ (s.Y : ℝ) / dQ ≤ (s'.Y : ℝ) / dQ
      ∧ ∀ t : ℝ, (s.Y : ℝ) / dQ ≤ t → t ≤ (s'.Y : ℝ) / dQ → DualBd P ns t := by
  have hS := dS_pos
  have hQ := dQ_pos
  unfold dualCell at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hr, herr⟩, hchk⟩ := hc
    have hs' : s' = ⟨dualAdv (dualAdv s.st rs) rs, s.err + 16, s.Y + Rn + Rn⟩ :=
      (Option.some.inj h).symm
    have hrR : (0 : ℝ) < (Rn : ℝ) / dQ := div_pos (by exact_mod_cast hr) hQ
    have herr' : (s.err : ℝ) + 16 ≤ dS := by exact_mod_cast herr
    have he1 : (s.err : ℝ) / dS ≤ 1 := by rw [div_le_one hS]; linarith
    have he2 : ((s.err + 8 : ℕ) : ℝ) / dS ≤ 1 := by rw [div_le_one hS]; push_cast; linarith
    have c1 : DualClose (((s.err + 8 : ℕ) : ℝ) / dS) (((s.Y + Rn : ℤ) : ℝ) / dQ) ns
        (dualAdv s.st rs) := by
      have := dualAdv_sound hi hrs he1
      rw [show ((s.err + 8 : ℕ) : ℝ) / dS = (s.err : ℝ) / dS + 8 / dS by push_cast; ring,
        show (((s.Y + Rn : ℤ) : ℝ)) / dQ = (s.Y : ℝ) / dQ + (Rn : ℝ) / dQ by push_cast; ring]
      exact this
    have c2 : DualInv ns s' := by
      have := dualAdv_sound c1 hrs he2
      rw [hs']
      unfold DualInv
      simp only
      rw [show ((s.err + 16 : ℕ) : ℝ) / dS = ((s.err + 8 : ℕ) : ℝ) / dS + 8 / dS by push_cast; ring,
        show (((s.Y + Rn + Rn : ℤ) : ℝ)) / dQ = ((s.Y + Rn : ℤ) : ℝ) / dQ + (Rn : ℝ) / dQ by
          push_cast; ring]
      exact this
    have hy' : (s'.Y : ℝ) / dQ = (s.Y : ℝ) / dQ + (Rn : ℝ) / dQ + (Rn : ℝ) / dQ := by
      rw [hs']; push_cast; ring
    refine ⟨c2, by rw [hy']; linarith, fun t ht1 ht2 => ?_⟩
    rw [hy'] at ht2
    have := dualChkZ_sound hP hr c1 hchk (τ := t - ((s.Y : ℝ) / dQ + (Rn : ℝ) / dQ))
      (by rw [abs_le]; constructor <;> linarith)
    unfold DualBd
    have e : ((s.Y + Rn : ℤ) : ℝ) / dQ + (t - ((s.Y : ℝ) / dQ + (Rn : ℝ) / dQ)) = t := by
      push_cast; ring
    rwa [e] at this
  · exact absurd h (by simp)

theorem dualSeg_sound {P : DualParZ} {ns : List (ℤ × ℤ)} (hP : DualParOK P.toQ ns) {Rn : ℤ}
    {rs : List (ℤ × ℤ)} (hrs : DualClose (3 / dS) ((Rn : ℝ) / dQ) ns rs) :
    ∀ (n : ℕ) {s s' : DualSt}, DualInv ns s → dualSeg P ns Rn rs n s = some s' →
      DualInv ns s' ∧ (s.Y : ℝ) / dQ ≤ (s'.Y : ℝ) / dQ
        ∧ ∀ t : ℝ, (s.Y : ℝ) / dQ ≤ t → t < (s'.Y : ℝ) / dQ → DualBd P ns t
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
      rcases lt_or_ge t ((s1.Y : ℝ) / dQ) with ht | ht
      · exact b1 t h1 ht.le
      · exact b2 t ht h2

theorem dualRun_sound {P : DualParZ} {ns : List (ℤ × ℤ)} (hP : DualParOK P.toQ ns)
    {lv : List (ℤ × List (ℤ × ℤ))} (hlv : ∀ l ∈ lv, DualClose (3 / dS) ((l.1 : ℝ) / dQ) ns l.2) :
    ∀ (prog : List (ℕ × ℕ)) {s s' : DualSt}, DualInv ns s → dualRun P ns lv prog s = some s' →
      DualInv ns s' ∧ (s.Y : ℝ) / dQ ≤ (s'.Y : ℝ) / dQ
        ∧ ∀ t : ℝ, (s.Y : ℝ) / dQ ≤ t → t < (s'.Y : ℝ) / dQ → DualBd P ns t
  | [], s, s', hi, h => by
    have : s = s' := Option.some.inj h
    subst this
    exact ⟨hi, le_refl _, fun t h1 h2 => absurd h2 (not_lt.mpr h1)⟩
  | p :: ps, s, s', hi, h => by
    unfold dualRun at h
    split at h
    · exact absurd h (by simp)
    · rename_i l hl
      split at h
      · exact absurd h (by simp)
      · rename_i s1 hc
        obtain ⟨i1, y1, b1⟩ := dualSeg_sound hP (hlv l (List.mem_of_getElem? hl)) p.2 hi hc
        obtain ⟨i2, y2, b2⟩ := dualRun_sound hP hlv ps i1 h
        refine ⟨i2, y1.trans y2, fun t h1 h2 => ?_⟩
        rcases lt_or_ge t ((s1.Y : ℝ) / dQ) with ht | ht
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

/-- the rotations of all levels are correct. -/
def dualLvOK (ns : List (ℤ × ℤ)) (lv : List (ℤ × List (ℤ × ℤ))) : Bool :=
  lv.all fun l => dualRotsOK ((l.1 : ℚ) / dQ) ns l.2

/-- beyond the end point `Yf/dQ` the trivial bound `‖N‖ ≤ B ≤ cp · y` suffices. -/
def dualTailOK (P : DualParZ) (Yf : ℤ) : Bool := decide (P.Bn * dCd * dQ ≤ P.Cn * Yf * dSa)

/-- a run split into consecutive pieces: `chain` is a list of `(programme, state after it)`. -/
def DualChainOK (P : DualParZ) (ns : List (ℤ × ℤ)) (lv : List (ℤ × List (ℤ × ℤ))) :
    DualSt → List (List (ℕ × ℕ) × DualSt) → Prop
  | _, [] => True
  | s, c :: chain => dualRun P ns lv c.1 s = some c.2 ∧ DualChainOK P ns lv c.2 chain

def dualChainEnd : DualSt → List (List (ℕ × ℕ) × DualSt) → DualSt
  | s, [] => s
  | _, c :: chain => dualChainEnd c.2 chain

theorem dual_cert_chain {P : DualParZ} {ns : List (ℤ × ℤ)} {lv : List (ℤ × List (ℤ × ℤ))}
    (hP : dualParChk P ns = true) (hlv : dualLvOK ns lv = true) :
    ∀ (chain : List (List (ℕ × ℕ) × DualSt)) (s : DualSt), DualInv ns s →
      DualChainOK P ns lv s chain →
      ∀ t : ℝ, (s.Y : ℝ) / dQ ≤ t → t < ((dualChainEnd s chain).Y : ℝ) / dQ → DualBd P ns t
  | [], s, _, _, t, h1, h2 => absurd h2 (not_lt.mpr h1)
  | c :: chain, s, hi, hch, t, h1, h2 => by
    have hP' := dualParChk_sound hP
    have hlv' : ∀ l ∈ lv, DualClose (3 / dS) ((l.1 : ℝ) / dQ) ns l.2 := fun l hl => by
      have := dualRotsOK_sound (List.all_eq_true.mp hlv l hl)
      rwa [show (((l.1 : ℚ) / dQ : ℚ) : ℝ) = (l.1 : ℝ) / dQ by push_cast; rfl] at this
    obtain ⟨hrun, hrest⟩ := hch
    obtain ⟨i1, y1, b1⟩ := dualRun_sound hP' hlv' c.1 hi hrun
    rcases lt_or_ge t ((c.2.Y : ℝ) / dQ) with ht | ht
    · exact b1 t h1 ht
    · exact dual_cert_chain hP hlv chain c.2 i1 hrest t ht h2

/-- **Soundness of the certificate.**  `Yf/dQ` is the end point of the run. -/
theorem dual_cert {P : DualParZ} {ns : List (ℤ × ℤ)}
    (hP : dualParChk P ns = true) {Yf : ℤ}
    (hrun : ∀ t : ℝ, 0 ≤ t → t < (Yf : ℝ) / dQ → DualBd P ns t)
    (htail : dualTailOK P Yf = true) (t : ℝ) :
    ‖dualNq ns t‖ ≤ (P.Cn : ℝ) / dCd * Real.sqrt (1 / 4 + t ^ 2) := by
  have hP' := dualParChk_sound hP
  have hSa := dSa_pos
  have hQ := dQ_pos
  have hCd : (0 : ℝ) < (dCd : ℝ) := by norm_num [dCd]
  simp only [dualParChk, Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨⟨hB, -⟩, -⟩, hC⟩ := hP
  have hB' : (dualAbs dualC0 ns : ℝ) ≤ P.Bn := by exact_mod_cast hB
  have hC' : (0 : ℝ) ≤ P.Cn := by exact_mod_cast hC
  have hfin : (P.Bn : ℝ) / dSa ≤ (P.Cn : ℝ) / dCd * ((Yf : ℝ) / dQ) := by
    have : (P.Bn : ℝ) * dCd * dQ ≤ P.Cn * Yf * dSa := by
      exact_mod_cast of_decide_eq_true htail
    rw [div_mul_div_comm, div_le_div_iff₀ hSa (by positivity)]
    linarith
  have main : ∀ t : ℝ, 0 ≤ t → DualBd P ns t := by
    intro t ht
    rcases lt_or_ge t ((Yf : ℝ) / dQ) with h | h
    · exact hrun t ht h
    · unfold DualBd dualNq
      rw [dual_norm_div_int _ hSa]
      have h1 : ‖dualA dualC0 ns t‖ / dSa ≤ (P.Bn : ℝ) / dSa :=
        div_le_div_of_nonneg_right ((dualA_norm_le _ _ _).trans hB') hSa.le
      have h3 : t ≤ Real.sqrt (1 / 4 + t ^ 2) :=
        (le_abs_self t).trans (Real.abs_le_sqrt (by linarith))
      calc _ ≤ (P.Cn : ℝ) / dCd * ((Yf : ℝ) / dQ) := h1.trans hfin
        _ ≤ (P.Cn : ℝ) / dCd * Real.sqrt (1 / 4 + t ^ 2) :=
          mul_le_mul_of_nonneg_left (h.trans h3) (by positivity)
  rcases le_total 0 t with ht | ht
  · exact main t ht
  · have h := main (-t) (by linarith)
    unfold DualBd dualNq at h
    rw [dualA_neg, norm_div, Complex.norm_conj, ← norm_div, neg_sq] at h
    exact h

end DetPrimality.Barrier
