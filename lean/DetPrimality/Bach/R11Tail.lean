import Mathlib
import DetPrimality.Bach.R11Defs
import DetPrimality.Bach.ConstPsiTheta

/-!
# Round 11, designB Lemma 5: the tail `T(X) = ∑_{n ≥ X} Λ(n)(1 + log n) n^{-3/2}`

Partial summation against a Chebyshev bound `ψ(n) ≤ a n + b √n` gives
`T(X) ≤ a (3 log X + 7)/√X + b (1.5 log X + 2)/X` for `X ≥ 1` (`r11Tail_general`).
With `ψ ≤ θ + 1.84 √x ≤ log 4 · x + 1.84 √x` (Mathlib + `psi_sub_theta_le_small`):

* `r11Tail_twoTerm` : `a = 1.3863`, `b = 1.84`;
* `r11Tail_192 : R11Tail 1.92` and `r11Tail_two : R11Tail 2`.

Everything is done in the variable `s = √y`, where the three functions are
`F(s) = (1 + 2 log s)/s³`, `G₁(s) = (6 log s + 7)/s`, `G₂(s) = (3 log s + 2)/s²` with
`G₁' = s² F'`, `G₂' = s F'`.
-/

open Real

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `F(s) = (1 + 2 log s)/s³`, i.e. `(1 + log y) y^{-3/2}` at `y = s²`. -/
noncomputable def r11TailF (s : ℝ) : ℝ := (1 + 2 * Real.log s) / s ^ 3

/-- `a G₁(s) + b G₂(s) + c F(s)`. -/
noncomputable def r11TailPhi (a b c : ℝ) (s : ℝ) : ℝ :=
  a * ((6 * Real.log s + 7) / s) + b * ((3 * Real.log s + 2) / s ^ 2)
    + c * ((1 + 2 * Real.log s) / s ^ 3)

theorem r11Tail_hasDerivAt_phi (a b c : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (r11TailPhi a b c)
      (-(1 + 6 * Real.log s) * (a * s ^ 2 + b * s + c) / s ^ 4) s := by
  have hl := Real.hasDerivAt_log hs.ne'
  have hp1 : HasDerivAt (fun s : ℝ => s) 1 s := hasDerivAt_id s
  have hp2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hp3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * s ^ 2) s := by
    simpa using hasDerivAt_pow 3 s
  have h1 := (((hl.const_mul 6).add_const 7).div hp1 hs.ne').const_mul a
  have h2 := (((hl.const_mul 3).add_const 2).div hp2 (by positivity)).const_mul b
  have h3 := (((hl.const_mul 2).const_add 1).div hp3 (by positivity)).const_mul c
  have h := (h1.add h2).add h3
  have hs0 : s ≠ 0 := hs.ne'
  have h' : HasDerivAt (r11TailPhi a b c) _ s := h
  refine h'.congr_deriv ?_
  field_simp
  ring

theorem r11Tail_anti {a b c s₀ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs₀ : 1 ≤ s₀)
    (hc : 0 ≤ a * s₀ ^ 2 + b * s₀ + c) : AntitoneOn (r11TailPhi a b c) (Set.Ici s₀) := by
  have hpos : ∀ s ∈ Set.Ici s₀, 0 < s := fun s hs => by
    have : s₀ ≤ s := hs
    linarith
  refine antitoneOn_of_deriv_nonpos (convex_Ici s₀)
    (fun s hs => (r11Tail_hasDerivAt_phi a b c (hpos s hs)).continuousAt.continuousWithinAt)
    (fun s hs => (r11Tail_hasDerivAt_phi a b c
      (hpos s (interior_subset hs))).differentiableAt.differentiableWithinAt)
    (fun s hs => ?_)
  have hs' : s₀ ≤ s := interior_subset hs
  have hs0 : 0 < s := hpos s (interior_subset hs)
  rw [(r11Tail_hasDerivAt_phi a b c hs0).deriv]
  have hlog : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have h1 : 0 ≤ a * s ^ 2 + b * s + c := by
    have h2 : s₀ ^ 2 ≤ s ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left hs' hb]
  have h3 : 0 ≤ (1 + 6 * Real.log s) * (a * s ^ 2 + b * s + c) / s ^ 4 := by positivity
  have e : -(1 + 6 * Real.log s) * (a * s ^ 2 + b * s + c) / s ^ 4
      = -((1 + 6 * Real.log s) * (a * s ^ 2 + b * s + c) / s ^ 4) := by ring
  rw [e]
  linarith

theorem r11Tail_F_eq (c : ℝ) (s : ℝ) : r11TailPhi 0 0 c s = c * r11TailF s := by
  unfold r11TailPhi r11TailF; ring

theorem r11Tail_F_nonneg {s : ℝ} (hs : 1 ≤ s) : 0 ≤ r11TailF s := by
  unfold r11TailF
  have := Real.log_nonneg hs
  positivity

/-- `(a s² + b s) F(s) ≤ a G₁(s) + b G₂(s)`. -/
theorem r11Tail_UF_le {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 1 ≤ s) :
    (a * s ^ 2 + b * s) * r11TailF s ≤ r11TailPhi a b 0 s := by
  have hs0 : 0 < s := by linarith
  have hl := Real.log_nonneg hs
  have e : (a * s ^ 2 + b * s) * r11TailF s
      = a * ((1 + 2 * Real.log s) / s) + b * ((1 + 2 * Real.log s) / s ^ 2) := by
    unfold r11TailF; field_simp
  rw [e]
  unfold r11TailPhi
  have h1 : (1 + 2 * Real.log s) / s ≤ (6 * Real.log s + 7) / s :=
    div_le_div_of_nonneg_right (by linarith) hs0.le
  have h2 : (1 + 2 * Real.log s) / s ^ 2 ≤ (3 * Real.log s + 2) / s ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- The step inequality: `U (F(s) - F(s')) ≤ G(s) - G(s')` for `U = a s² + b s`, `s ≤ s'`. -/
theorem r11Tail_step {a b s s' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 1 ≤ s) (hss : s ≤ s') :
    (a * s ^ 2 + b * s) * (r11TailF s - r11TailF s')
      ≤ r11TailPhi a b 0 s - r11TailPhi a b 0 s' := by
  have h := r11Tail_anti (c := -(a * s ^ 2 + b * s)) ha hb hs (by linarith)
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hss) hss
  have e : ∀ t, r11TailPhi a b (-(a * s ^ 2 + b * s)) t
      = r11TailPhi a b 0 t - (a * s ^ 2 + b * s) * r11TailF t := by
    intro t; unfold r11TailPhi r11TailF; ring
  rw [e, e] at h
  linarith

/-- Abel summation with the bound `∑_{k ≤ n} Λ(k) ≤ a n + b √n`. -/
theorem r11Tail_abel {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hψ : ∀ n : ℕ, Chebyshev.psi n ≤ a * n + b * √n) {N : ℕ} (hN : 1 ≤ N) (M : ℕ)
    (hM : N ≤ M) :
    ∑ n ∈ Finset.Ico N (M + 1), Λ n * r11TailF (√n)
      ≤ (∑ n ∈ Finset.Ico N (M + 1), Λ n) * r11TailF (√M)
        + r11TailPhi a b 0 (√N) - r11TailPhi a b 0 (√M) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have : Finset.Ico N (N + 1) = {N} := by
      ext i; simp
    rw [this]; simp
  | succ M hM ih =>
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hN.trans hM
    have hs : (1 : ℝ) ≤ √M := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hM1
    have hss : √(M : ℝ) ≤ √((M + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
    rw [Finset.sum_Ico_succ_top (by omega : N ≤ M + 1),
      Finset.sum_Ico_succ_top (by omega : N ≤ M + 1)]
    set D := ∑ n ∈ Finset.Ico N (M + 1), Λ n with hD
    have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    have hDU : D ≤ a * (√M) ^ 2 + b * √M := by
      have h1 : D ≤ Chebyshev.psi M := by
        rw [Chebyshev.psi, Nat.floor_natCast]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_)
          (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
        rw [Finset.mem_Ico] at hi
        rw [Finset.mem_Ioc]; omega
      rw [Real.sq_sqrt (by linarith)]
      exact h1.trans (hψ M)
    have hstep := r11Tail_step ha hb hs hss
    have hFF : 0 ≤ r11TailF (√M) - r11TailF (√((M + 1 : ℕ) : ℝ)) := by
      have h := r11Tail_anti (a := 0) (b := 0) (c := 1) le_rfl le_rfl hs (by norm_num)
        (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hss) hss
      rw [r11Tail_F_eq, r11Tail_F_eq] at h
      linarith
    have h2 : D * (r11TailF (√M) - r11TailF (√((M + 1 : ℕ) : ℝ)))
        ≤ (a * (√M) ^ 2 + b * √M) * (r11TailF (√M) - r11TailF (√((M + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hDU hFF
    nlinarith [ih, hstep, h2]

theorem r11Tail_term_eq {y : ℝ} (hy : 0 < y) :
    (1 + Real.log y) / y ^ ((3 : ℝ) / 2) = r11TailF (√y) := by
  unfold r11TailF
  have h1 : (√y) ^ 3 = y ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num
  rw [h1, Real.log_sqrt hy.le]
  ring_nf

/-- **designB Lemma 5**, two-term form. -/
theorem r11Tail_general {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hψ : ∀ n : ℕ, Chebyshev.psi n ≤ a * n + b * √n) (X : ℝ) (hX : 1 ≤ X) :
    r11T X ≤ a * (3 * Real.log X + 7) / √X + b * (1.5 * Real.log X + 2) / X := by
  have hX0 : 0 < X := by linarith
  have hsX : (1 : ℝ) ≤ √X := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hX
  have hsX0 : 0 < √X := by linarith
  have hGX : a * (3 * Real.log X + 7) / √X + b * (1.5 * Real.log X + 2) / X
      = r11TailPhi a b 0 (√X) := by
    unfold r11TailPhi
    rw [Real.log_sqrt hX0.le, Real.sq_sqrt hX0.le]
    ring
  rw [hGX]
  have hGnn : ∀ s : ℝ, 1 ≤ s → 0 ≤ r11TailPhi a b 0 s := by
    intro s hs
    have := Real.log_nonneg hs
    unfold r11TailPhi
    positivity
  set N := ⌈X⌉₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef, Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero]; linarith
  have hXN : X ≤ N := Nat.le_ceil X
  have hsN : √X ≤ √(N : ℝ) := Real.sqrt_le_sqrt hXN
  have hGN : r11TailPhi a b 0 (√(N : ℝ)) ≤ r11TailPhi a b 0 (√X) :=
    r11Tail_anti ha hb le_rfl (by positivity) (Set.mem_Ici.mpr hsX)
      (Set.mem_Ici.mpr (hsX.trans hsN)) hsN
  unfold r11T
  refine Real.tsum_le_of_sum_range_le (fun n => ?_) (fun m => ?_)
  · split_ifs with h
    · have hn1 : (1 : ℝ) ≤ n := hX.trans h
      have := Real.log_nonneg hn1
      have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    · exact le_rfl
  · set M := max N m with hMdef
    have hNM : N ≤ M := le_max_left _ _
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hN1.trans hNM
    have hsM : (1 : ℝ) ≤ √(M : ℝ) := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hM1
    have h1 : ∑ i ∈ Finset.range m,
          (if X ≤ (i : ℝ) then Λ i * (1 + Real.log i) / (i : ℝ) ^ ((3 : ℝ) / 2) else 0)
        ≤ ∑ n ∈ Finset.Ico N (M + 1), Λ n * r11TailF (√n) := by
      rw [← Finset.sum_filter]
      have hsub : (Finset.range m).filter (fun i : ℕ => X ≤ (i : ℝ)) ⊆ Finset.Ico N (M + 1) := by
        intro i hi
        rw [Finset.mem_filter, Finset.mem_range] at hi
        rw [Finset.mem_Ico]
        have h2 : N ≤ i := Nat.ceil_le.mpr hi.2
        have h3 : m ≤ M := le_max_right _ _
        omega
      have hterm : ∀ i ∈ Finset.Ico N (M + 1),
          Λ i * (1 + Real.log i) / (i : ℝ) ^ ((3 : ℝ) / 2) = Λ i * r11TailF (√i) := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
        rw [mul_div_assoc, r11Tail_term_eq hi0]
      calc _ ≤ ∑ i ∈ Finset.Ico N (M + 1),
            Λ i * (1 + Real.log i) / (i : ℝ) ^ ((3 : ℝ) / 2) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => ?_)
            rw [hterm i hi]
            rw [Finset.mem_Ico] at hi
            have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (by omega : 1 ≤ i)
            have hsi : (1 : ℝ) ≤ √(i : ℝ) := by
              rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hi1
            exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (r11Tail_F_nonneg hsi)
        _ = _ := Finset.sum_congr rfl hterm
    have h2 := r11Tail_abel ha hb hψ hN1 M hNM
    have hD0 : 0 ≤ ∑ n ∈ Finset.Ico N (M + 1), Λ n :=
      Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    have hDU : ∑ n ∈ Finset.Ico N (M + 1), Λ n ≤ a * (√(M : ℝ)) ^ 2 + b * √(M : ℝ) := by
      have h3 : ∑ n ∈ Finset.Ico N (M + 1), Λ n ≤ Chebyshev.psi M := by
        rw [Chebyshev.psi, Nat.floor_natCast]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_)
          (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
        rw [Finset.mem_Ico] at hi
        rw [Finset.mem_Ioc]; omega
      rw [Real.sq_sqrt (by linarith)]
      exact h3.trans (hψ M)
    have h4 : (∑ n ∈ Finset.Ico N (M + 1), Λ n) * r11TailF (√(M : ℝ))
        ≤ r11TailPhi a b 0 (√(M : ℝ)) :=
      (mul_le_mul_of_nonneg_right hDU (r11Tail_F_nonneg hsM)).trans (r11Tail_UF_le ha hb hsM)
    linarith

/-- `ψ(x) ≤ 1.3863 x + 1.84 √x`. -/
theorem r11Tail_psi_le (x : ℝ) (hx : 0 ≤ x) : Chebyshev.psi x ≤ 1.3863 * x + 1.84 * √x := by
  have h1 := psi_sub_theta_le_small x
  have h2 := Chebyshev.theta_le_log4_mul_x hx
  have h3 : Real.log 4 ≤ 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast; linarith
  have h4 : Real.log 4 * x ≤ 1.3863 * x := mul_le_mul_of_nonneg_right h3 hx
  linarith

/-- **designB Lemma 5** with `ψ(x) ≤ 1.3863 x + 1.84 √x`. -/
theorem r11Tail_twoTerm (X : ℝ) (hX : 1 ≤ X) :
    r11T X ≤ 1.3863 * (3 * Real.log X + 7) / √X + 1.84 * (1.5 * Real.log X + 2) / X :=
  r11Tail_general (by norm_num) (by norm_num)
    (fun n => r11Tail_psi_le n (Nat.cast_nonneg n)) X hX

/-- **designB Lemma 5** in the hand-off shape, `c₀ = 1.92`. -/
theorem r11Tail_192 : R11Tail 1.92 := by
  intro X hX
  have h := r11Tail_twoTerm X hX
  have hX0 : 0 < X := by linarith
  have hs1 : (1 : ℝ) ≤ √X := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hX
  have hs0 : 0 < √X := by linarith
  set s := √X with hs
  have hXs : X = s ^ 2 := (Real.sq_sqrt hX0.le).symm
  have hl : 0 ≤ Real.log X := Real.log_nonneg hX
  -- `log X = 2 log s ≤ 2 (s - 1)`
  have hls : Real.log X ≤ 2 * (s - 1) := by
    have := Real.log_le_sub_one_of_pos hs0
    have e : Real.log X = 2 * Real.log s := by rw [hs, Real.log_sqrt hX0.le]; ring
    linarith
  set l := Real.log X with hldef
  have key : 1.84 * (1.5 * l + 2) / X ≤ (1.92 - 1.3863) * (3 * l + 7) / s := by
    rw [hXs, div_le_div_iff₀ (by positivity) hs0]
    have h1 : 1.84 * (1.5 * l + 2) ≤ (1.92 - 1.3863) * (3 * l + 7) * (1 + l / 2) := by
      nlinarith [mul_nonneg hl hl]
    have h2 : 1 + l / 2 ≤ s := by linarith
    have h3 : (1.92 - 1.3863) * (3 * l + 7) * (1 + l / 2) ≤ (1.92 - 1.3863) * (3 * l + 7) * s :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right (h1.trans h3) (sq_nonneg s)]
  have e : 1.92 * (3 * l + 7) / s
      = 1.3863 * (3 * l + 7) / s + (1.92 - 1.3863) * (3 * l + 7) / s := by ring
  rw [e]
  linarith

theorem r11Tail_mono {c c' : ℝ} (h : R11Tail c) (hc : c ≤ c') : R11Tail c' := by
  intro X hX
  have hl : 0 ≤ Real.log X := Real.log_nonneg hX
  have hs0 : 0 < √X := Real.sqrt_pos.mpr (by linarith)
  refine (h X hX).trans ?_
  gcongr

theorem r11Tail_two : R11Tail 2 := r11Tail_mono r11Tail_192 (by norm_num)

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r11Tail_twoTerm
#print axioms DetPrimality.Bach.r11Tail_192
#print axioms DetPrimality.Bach.r11Tail_two
