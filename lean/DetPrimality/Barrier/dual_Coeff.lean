import DetPrimality.Barrier.dual_Duality
import DetPrimality.Barrier.dual_Cert

/-!
# From integer data to the dual function

`vd : List (ℤ × ℤ)` is the list of `(V, D)`: node `v = V / dDv`, coefficient `d = D / dDd`.
The dual function is `g = dualG (dualL vd)`, i.e. `g(t) = e^{π t} ∑ d · 1_{2πt < v}`.

* `dualStep_abs_le`, `dualStep_neg`: the admissibility conditions (`g = e^{π t}` for `t < 0`,
  `|g| ≤ e^{π t}` for `t > 0`) from a finite check of suffix sums (`dualSufOK`).
* `dualExpErr_sound`: the exponential sum `dualN` with the true coefficients `d e^{v/2}` is within
  `η` of the rational exponential sum `dualNq` with coefficients `α / dSa`.
-/

open Complex

namespace DetPrimality.Barrier

/-- denominator of the coefficients `d = D / dDd`. -/
def dDd : ℤ := 10000000

theorem dDd_pos : (0 : ℝ) < (dDd : ℝ) := by norm_num [dDd]

/-- the real list `(v, d)`. -/
noncomputable def dualL (vd : List (ℤ × ℤ)) : List (ℝ × ℝ) :=
  vd.map fun p => ((p.1 : ℝ) / dDv, (p.2 : ℝ) / dDd)

/-! ## The step function -/

theorem dualStep_cons (p : ℤ × ℤ) (l : List (ℤ × ℤ)) (u : ℝ) :
    dualStep (dualL (p :: l)) u
      = (if u < (p.1 : ℝ) / dDv then (p.2 : ℝ) / dDd else 0) + dualStep (dualL l) u := by
  simp [dualStep, dualL]

theorem dualStep_all (l : List (ℤ × ℤ)) (u : ℝ) (h : ∀ q ∈ l, u < (q.1 : ℝ) / dDv) :
    dualStep (dualL l) u = (((l.map (·.2)).sum : ℤ) : ℝ) / dDd := by
  induction l with
  | nil => simp [dualStep, dualL]
  | cons p l ih =>
    rw [dualStep_cons, if_pos (h p (List.mem_cons_self ..)),
      ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    simp only [List.map_cons, List.sum_cons]
    push_cast
    ring

/-- nodes non-decreasing and all suffix sums of the `D` in `[-dDd, dDd]`. -/
def dualSufOK : List (ℤ × ℤ) → Bool
  | [] => true
  | p :: l => l.all (fun q => decide (p.1 ≤ q.1)) && decide (|((p :: l).map (·.2)).sum| ≤ dDd)
      && dualSufOK l

theorem dualStep_abs_le : ∀ (vd : List (ℤ × ℤ)), dualSufOK vd = true → ∀ u : ℝ,
    |dualStep (dualL vd) u| ≤ 1
  | [], _, u => by simp [dualStep, dualL]
  | p :: l, h, u => by
    have hD := dDd_pos
    have hV := dDv_pos
    simp only [dualSufOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    by_cases hu : u < (p.1 : ℝ) / dDv
    · have hall : ∀ q ∈ p :: l, u < (q.1 : ℝ) / dDv := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hu
        · have : (p.1 : ℝ) ≤ q.1 := by exact_mod_cast h1 q hq
          exact hu.trans_le (div_le_div_of_nonneg_right this hV.le)
      rw [dualStep_all _ _ hall, abs_div, abs_of_pos hD, div_le_one hD]
      exact_mod_cast h2
    · rw [dualStep_cons, if_neg hu, zero_add]
      exact dualStep_abs_le l h3 u

theorem dualStep_neg (vd : List (ℤ × ℤ)) (h0 : vd.all (fun q => decide (0 ≤ q.1)) = true)
    (hs : (vd.map (·.2)).sum = dDd) {u : ℝ} (hu : u < 0) : dualStep (dualL vd) u = 1 := by
  have hD := dDd_pos
  have hV := dDv_pos
  rw [dualStep_all vd u, hs, div_self hD.ne']
  intro q hq
  have : (0 : ℝ) ≤ q.1 := by exact_mod_cast of_decide_eq_true (List.all_eq_true.mp h0 q hq)
  exact hu.trans_le (by positivity)

/-! ## The coefficients `d e^{v/2}` -/

/-- number of Taylor terms for `e^{v/8}`. -/
def dNE : ℕ := 18

def dualTayR (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => dualTayR q n + q ^ n / n.factorial

theorem dualTayR_cast (q : ℚ) (n : ℕ) :
    ((dualTayR q n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (q : ℝ) ^ m / (m.factorial : ℝ) := by
  induction n with
  | zero => simp [dualTayR]
  | succ n ih => rw [dualTayR, Finset.sum_range_succ, ← ih]; push_cast; rfl

/-- a bound for `|d e^{v/2} - α/dSa|`, `p = (V, D)`, `n = (V, α)`. -/
def dualExpTerm (p n : ℤ × ℤ) : ℚ :=
  |(p.2 : ℚ) / dDd| * ((dualTayR (p.1 / (8 * dDv)) dNE
        + (p.1 / (8 * dDv) : ℚ) ^ dNE * (dNE + 1) / (dNE.factorial * dNE)) ^ 4
      - dualTayR (p.1 / (8 * dDv)) dNE ^ 4)
    + |(p.2 : ℚ) / dDd * dualTayR (p.1 / (8 * dDv)) dNE ^ 4 - n.2 / dSa|

theorem dualExpTerm_sound {p n : ℤ × ℤ} (h0 : 0 ≤ p.1) (h8 : p.1 ≤ 8 * dDv) :
    |(p.2 : ℝ) / dDd * Real.exp ((p.1 : ℝ) / dDv / 2) - (n.2 : ℝ) / dSa| ≤ (dualExpTerm p n : ℝ) := by
  have hV := dDv_pos
  set q : ℚ := p.1 / (8 * dDv) with hq
  have hqR : (q : ℝ) = (p.1 : ℝ) / (8 * dDv) := by rw [hq]; push_cast; rfl
  have hq0 : (0 : ℝ) ≤ q := by
    rw [hqR]; have : (0 : ℝ) ≤ p.1 := by exact_mod_cast h0
    positivity
  have hq1 : (q : ℝ) ≤ 1 := by
    rw [hqR, div_le_one (by positivity)]
    exact_mod_cast h8
  set lo : ℝ := ((dualTayR q dNE : ℚ) : ℝ) with hlo
  set hi : ℝ := lo + (q : ℝ) ^ dNE * (dNE + 1) / (dNE.factorial * dNE) with hhi
  have e1 : Real.exp ((p.1 : ℝ) / dDv / 2) = Real.exp (q : ℝ) ^ 4 := by
    rw [← Real.exp_nat_mul, hqR]; congr 1; push_cast; field_simp; ring
  have l1 : lo ≤ Real.exp (q : ℝ) := by
    rw [hlo, dualTayR_cast]; exact Real.sum_le_exp_of_nonneg hq0 _
  have l2 : Real.exp (q : ℝ) ≤ hi := by
    rw [hhi, hlo, dualTayR_cast]
    exact Real.exp_bound' hq0 hq1 (by norm_num [dNE])
  have l0 : 0 ≤ lo := by
    rw [hlo, dualTayR_cast]; exact Finset.sum_nonneg fun m _ => by positivity
  have p1 : lo ^ 4 ≤ Real.exp (q : ℝ) ^ 4 := pow_le_pow_left₀ l0 l1 4
  have p2 : Real.exp (q : ℝ) ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le l2 4
  have et : (dualExpTerm p n : ℝ)
      = |(p.2 : ℝ) / dDd| * (hi ^ 4 - lo ^ 4) + |(p.2 : ℝ) / dDd * lo ^ 4 - (n.2 : ℝ) / dSa| := by
    simp only [dualExpTerm, ← hq]
    push_cast
    rfl
  rw [et, e1]
  calc |(p.2 : ℝ) / dDd * Real.exp (q : ℝ) ^ 4 - (n.2 : ℝ) / dSa|
      = |(p.2 : ℝ) / dDd * (Real.exp (q : ℝ) ^ 4 - lo ^ 4)
          + ((p.2 : ℝ) / dDd * lo ^ 4 - (n.2 : ℝ) / dSa)| := by congr 1; ring
    _ ≤ |(p.2 : ℝ) / dDd * (Real.exp (q : ℝ) ^ 4 - lo ^ 4)|
          + |(p.2 : ℝ) / dDd * lo ^ 4 - (n.2 : ℝ) / dSa| := abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr p1)]
        gcongr

/-- total coefficient error; `none` if the two lists do not have the same nodes in `[0, 8]`. -/
def dualExpErr : List (ℤ × ℤ) → List (ℤ × ℤ) → Option ℚ
  | [], [] => some 0
  | p :: ps, n :: ns =>
    if p.1 = n.1 ∧ 0 ≤ p.1 ∧ p.1 ≤ 8 * dDv then
      match dualExpErr ps ns with
      | some η => some (dualExpTerm p n + η)
      | none => none
    else none
  | _, _ => none

theorem dualN_cons (p : ℝ × ℝ) (l : List (ℝ × ℝ)) (y : ℝ) :
    dualN (p :: l) y = ((p.2 * Real.exp (p.1 / 2) : ℝ) : ℂ) * eI (y * p.1) + dualN l y := by
  simp [dualN, eI]

theorem dualNq_cons (n : ℤ × ℤ) (ns : List (ℤ × ℤ)) (y : ℝ) :
    dualNq (n :: ns) y = ((n.2 : ℝ) / dSa : ℝ) * eI (y * ((n.1 : ℝ) / dDv)) + dualNq ns y := by
  simp only [dualNq, dualA, List.map_cons, List.sum_cons, dualC0, dualV]
  push_cast
  ring

theorem dualExpErr_sound : ∀ (vd va : List (ℤ × ℤ)) (η : ℚ), dualExpErr vd va = some η →
    ∀ y : ℝ, ‖dualN (dualL vd) y - dualNq va y‖ ≤ (η : ℝ)
  | [], [], η, h, y => by
    have : η = 0 := (Option.some.inj h).symm
    subst this
    simp [dualN, dualL, dualNq, dualA]
  | p :: ps, n :: ns, η, h, y => by
    unfold dualExpErr at h
    split at h
    · rename_i hc
      obtain ⟨hV, h0, h8⟩ := hc
      split at h
      · rename_i η' hη'
        have hη : η = dualExpTerm p n + η' := (Option.some.inj h).symm
        have ih := dualExpErr_sound ps ns η' hη' y
        have ht := dualExpTerm_sound (n := n) h0 h8
        have e : dualN (dualL (p :: ps)) y - dualNq (n :: ns) y
            = (((p.2 : ℝ) / dDd * Real.exp ((p.1 : ℝ) / dDv / 2) - (n.2 : ℝ) / dSa : ℝ) : ℂ)
                * eI (y * ((p.1 : ℝ) / dDv))
              + (dualN (dualL ps) y - dualNq ns y) := by
          have : dualL (p :: ps) = ((p.1 : ℝ) / dDv, (p.2 : ℝ) / dDd) :: dualL ps := by
            simp [dualL]
          rw [this, dualN_cons, dualNq_cons, ← hV]
          push_cast
          ring
        rw [e, hη]
        push_cast
        refine (norm_add_le _ _).trans (add_le_add ?_ ih)
        rw [norm_mul, norm_eI, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact ht
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | [], _ :: _, η, h, y => by simp [dualExpErr] at h
  | _ :: _, [], η, h, y => by simp [dualExpErr] at h

/-- all the checks on the pair of lists `(V, D)`, `(V, α)`. -/
def dualCoeffOK (vd va : List (ℤ × ℤ)) (η0 : ℚ) : Bool :=
  dualSufOK vd && vd.all (fun q => decide (0 ≤ q.1)) && decide ((vd.map (·.2)).sum = dDd)
    && (match dualExpErr vd va with
        | some η => decide (η ≤ η0)
        | none => false)

theorem dualCoeffOK_sound {vd va : List (ℤ × ℤ)} {η0 : ℚ} (h : dualCoeffOK vd va η0 = true) :
    (∀ u : ℝ, |dualStep (dualL vd) u| ≤ 1) ∧ (∀ u : ℝ, u < 0 → dualStep (dualL vd) u = 1)
      ∧ ∀ y : ℝ, ‖dualN (dualL vd) y - dualNq va y‖ ≤ (η0 : ℝ) := by
  simp only [dualCoeffOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hsuf, hall⟩, hsum⟩, hexp⟩ := h
  refine ⟨dualStep_abs_le vd hsuf, fun u hu => dualStep_neg vd hall hsum hu, fun y => ?_⟩
  split at hexp
  · rename_i η hη
    have h1 : (η : ℝ) ≤ η0 := by exact_mod_cast of_decide_eq_true hexp
    exact (dualExpErr_sound vd va η hη y).trans h1
  · exact absurd hexp (by simp)

end DetPrimality.Barrier
