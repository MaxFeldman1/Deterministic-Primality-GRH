import Mathlib
import DetPrimality.Bach.R11Tail
import DetPrimality.Bach.ChebyshevThirty

/-!
# Round 11, designB Lemma 5, sharpened

Partial summation keeps the boundary term: with `N = ⌈X⌉`,
`T(X) ≤ a G₁(√N) + b G₂(√N) - ψ(N-1) F(√N)`.  Inserting the Chebyshev lower bound
`ψ(N-1) ≥ 0.88 N` (`N ≥ 250`, from `cheb30_psi_ge`) gives, for `X ≥ 250`,

`T(X) ≤ 1.093 (3 log X + 7)/√X + 1.84 (1.5 log X + 2)/X + 1.1734/√X`   (`r11TailS_sharp`),

i.e. the effective Chebyshev constant drops from `1.39` to about `1.14`.
-/

open Real

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

theorem r11TailS_psi_split {N M : ℕ} (hN : 1 ≤ N) (hM : N ≤ M) :
    Chebyshev.psi ((N - 1 : ℕ) : ℝ) + ∑ n ∈ Finset.Ico N (M + 1), Λ n ≤ Chebyshev.psi (M : ℝ) := by
  rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast, Nat.floor_natCast]
  have hdisj : Disjoint (Finset.Ioc 0 (N - 1)) (Finset.Ico N (M + 1)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_Ioc] at hi
    rw [Finset.mem_Ico] at hi'
    omega
  rw [← Finset.sum_union hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ico] at hi
  rw [Finset.mem_Ioc]
  omega

theorem r11TailS_abel {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hψ : ∀ n : ℕ, Chebyshev.psi n ≤ a * n + b * √n) {N : ℕ} (hN : 1 ≤ N)
    (hp : p ≤ Chebyshev.psi ((N - 1 : ℕ) : ℝ)) (M : ℕ) (hM : N ≤ M) :
    ∑ n ∈ Finset.Ico N (M + 1), Λ n * r11TailF (√n)
      ≤ (∑ n ∈ Finset.Ico N (M + 1), Λ n) * r11TailF (√M)
        + r11TailPhi a b 0 (√N) - r11TailPhi a b 0 (√M)
        - p * (r11TailF (√N) - r11TailF (√M)) := by
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
    have hDU : D ≤ a * (√M) ^ 2 + b * √M - p := by
      have h1 := r11TailS_psi_split hN hM
      rw [Real.sq_sqrt (by linarith)]
      linarith [hψ M]
    have hstep := r11Tail_step ha hb hs hss
    have hFF : 0 ≤ r11TailF (√M) - r11TailF (√((M + 1 : ℕ) : ℝ)) := by
      have h := r11Tail_anti (a := 0) (b := 0) (c := 1) le_rfl le_rfl hs (by norm_num)
        (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hss) hss
      rw [r11Tail_F_eq, r11Tail_F_eq] at h
      linarith
    have h2 : D * (r11TailF (√M) - r11TailF (√((M + 1 : ℕ) : ℝ)))
        ≤ (a * (√M) ^ 2 + b * √M - p) * (r11TailF (√M) - r11TailF (√((M + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hDU hFF
    nlinarith [ih, hstep, h2]

/-- Partial summation with the boundary term kept. -/
theorem r11TailS_general {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hp0 : 0 ≤ p)
    (hψ : ∀ n : ℕ, Chebyshev.psi n ≤ a * n + b * √n) (X : ℝ) (hX : 1 ≤ X)
    (hp : p ≤ Chebyshev.psi ((⌈X⌉₊ - 1 : ℕ) : ℝ)) :
    r11T X ≤ r11TailPhi a b 0 (√(⌈X⌉₊ : ℝ)) - p * r11TailF (√(⌈X⌉₊ : ℝ)) := by
  have hX0 : 0 < X := by linarith
  set N := ⌈X⌉₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef, Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero]; linarith
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hsN : (1 : ℝ) ≤ √(N : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hN1'
  have hpU : p ≤ a * (√(N : ℝ)) ^ 2 + b * √(N : ℝ) := by
    have h1 := r11TailS_psi_split hN1 le_rfl
    have h2 : 0 ≤ ∑ n ∈ Finset.Ico N (N + 1), Λ n :=
      Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    rw [Real.sq_sqrt (by linarith)]
    linarith [hψ N]
  have hbase : 0 ≤ r11TailPhi a b 0 (√(N : ℝ)) - p * r11TailF (√(N : ℝ)) := by
    have h1 := r11Tail_UF_le ha hb hsN
    have h2 := mul_le_mul_of_nonneg_right hpU (r11Tail_F_nonneg hsN)
    linarith
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
    have h2 := r11TailS_abel ha hb hψ hN1 hp M hNM
    have hDU : ∑ n ∈ Finset.Ico N (M + 1), Λ n
        ≤ a * (√(M : ℝ)) ^ 2 + b * √(M : ℝ) - p := by
      have h3 := r11TailS_psi_split hN1 hNM
      rw [Real.sq_sqrt (by linarith)]
      linarith [hψ M]
    have h4 := mul_le_mul_of_nonneg_right hDU (r11Tail_F_nonneg hsM)
    have h5 := r11Tail_UF_le ha hb hsM
    nlinarith [h1, h2, h4, h5]

/-- `ψ(N - 1) ≥ 0.88 N` for `N ≥ 250`. -/
theorem r11TailS_psi_ge {N : ℕ} (hN : 250 ≤ N) :
    0.88 * (N : ℝ) ≤ Chebyshev.psi ((N - 1 : ℕ) : ℝ) := by
  have h := cheb30_psi_ge (N := N - 1) (by omega)
  have hy : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hy] at h ⊢
  have hN' : (250 : ℝ) ≤ N := by exact_mod_cast hN
  set y := (N : ℝ) - 1 with hydef
  have hy249 : (249 : ℝ) ≤ y := by rw [hydef]; linarith
  have hy0 : 0 < y := by linarith
  have hlog : Real.log y ≤ y / 256 + 4.5452 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < y / 256 by positivity)
    rw [Real.log_div hy0.ne' (by norm_num)] at h1
    have h2 : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; push_cast; ring
    have := Real.log_two_lt_d9
    linarith
  have h30 : 30 / y ≤ 0.1205 := by
    rw [div_le_iff₀ hy0]; linarith
  linarith

/-- **designB Lemma 5, sharpened.** -/
theorem r11TailS_sharp (X : ℝ) (hX : 250 ≤ X) :
    r11T X ≤ 1.093 * (3 * Real.log X + 7) / √X + 1.84 * (1.5 * Real.log X + 2) / X
      + 1.1734 / √X := by
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  set N := ⌈X⌉₊ with hNdef
  have hXN : X ≤ N := Nat.le_ceil X
  have hN250 : 250 ≤ N := by
    have : (250 : ℝ) ≤ N := hX.trans hXN
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by linarith
  have hsX : (1 : ℝ) ≤ √X := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hX1
  have hsN : √X ≤ √(N : ℝ) := Real.sqrt_le_sqrt hXN
  have hsN0 : 0 < √(N : ℝ) := by linarith
  have h := r11TailS_general (a := 1.3863) (b := 1.84) (p := 0.88 * (N : ℝ)) (by norm_num)
    (by norm_num) (by positivity) (fun n => r11Tail_psi_le n (Nat.cast_nonneg n)) X hX1
    (r11TailS_psi_ge hN250)
  rw [← hNdef] at h
  -- rewrite `a G₁ - q s² F = (a - q/3) G₁ + (4q/3)/s`
  have e : r11TailPhi 1.3863 1.84 0 (√(N : ℝ)) - 0.88 * (N : ℝ) * r11TailF (√(N : ℝ))
      = r11TailPhi (1.3863 - 0.88 / 3) 1.84 0 (√(N : ℝ)) + 0.88 * 4 / 3 / √(N : ℝ) := by
    have hsq : (N : ℝ) = (√(N : ℝ)) ^ 2 := (Real.sq_sqrt hN0.le).symm
    rw [hsq]
    set s := √(N : ℝ)
    rw [Real.sqrt_sq hsN0.le]
    unfold r11TailPhi r11TailF
    field_simp
    ring
  rw [e] at h
  have h1 : r11TailPhi (1.3863 - 0.88 / 3) 1.84 0 (√(N : ℝ))
      ≤ r11TailPhi (1.3863 - 0.88 / 3) 1.84 0 (√X) :=
    r11Tail_anti (by norm_num) (by norm_num) le_rfl (by norm_num) (Set.mem_Ici.mpr hsX)
      (Set.mem_Ici.mpr (hsX.trans hsN)) hsN
  have h2 : 0.88 * 4 / 3 / √(N : ℝ) ≤ 0.88 * 4 / 3 / √X :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) hsN
  have hs0 : 0 < √X := by linarith
  have hl : 0 ≤ Real.log X := Real.log_nonneg hX1
  have e2 : r11TailPhi (1.3863 - 0.88 / 3) 1.84 0 (√X)
      = (1.3863 - 0.88 / 3) * (3 * Real.log X + 7) / √X
        + 1.84 * (1.5 * Real.log X + 2) / X := by
    unfold r11TailPhi
    rw [Real.log_sqrt hX0.le, Real.sq_sqrt hX0.le]
    ring
  rw [e2] at h1
  have h3 : (1.3863 - 0.88 / 3) * (3 * Real.log X + 7) / √X
      ≤ 1.093 * (3 * Real.log X + 7) / √X :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by linarith)) hs0.le
  have h4 : 0.88 * 4 / 3 / √X ≤ 1.1734 / √X :=
    div_le_div_of_nonneg_right (by norm_num) hs0.le
  linarith

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r11TailS_sharp
