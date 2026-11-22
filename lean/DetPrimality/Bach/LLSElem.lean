import Mathlib
import DetPrimality.Bach.LLSDefs
import DetPrimality.Bach.ChebyshevThirty
import DetPrimality.Bach.CompositeReduction

/-!
# Elementary inputs for LLS Theorem 1.1(2)

* `llsElem_weightedLower : LLSWeightedLower` (unconditional): `log x - 2 ≤ ∑_{n ≤ x} Λ(n)/n (1 - n/x)`.
  From `log k! = ∑ Λ(d) ⌊k/d⌋` we get `A(k) = ∑_{n ≤ k} Λ(n)/n ≥ log k - 1 + 1/k`; with
  `T(N) = ∑_{n ≤ N} Λ(n)/n (N - n)`, `T(N+1) = T(N) + A(N)` gives `T(N) ≥ N log N - 2N + 2`, and
  `x W(x) = T(N) + (x - N) A(N)` for `N = ⌊x⌋`.
* Reduction lemmas (`llsElem_logPsi_eq`, `llsElem_weightedLogSum_eq`, `llsElem_no_witness_facts`,
  `llsElem_sq_le`).
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Task 1: the weighted lower bound -/

theorem llsElem_log_factorial_ge (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * Real.log k - k + 1 ≤ Real.log (k.factorial : ℝ) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 : Real.log (((k : ℝ) + 1) / k) ≤ ((k : ℝ) + 1) / k - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hk0.ne'] at h1
    have h2 : (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 hk0.le
      have e : (k : ℝ) * (((k : ℝ) + 1) / k - 1) = 1 := by field_simp; ring
      linarith
    push_cast
    linarith

theorem llsElem_sum_range_eq_Ioc (f : ℕ → ℝ) (h0 : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), f n = ∑ n ∈ Finset.Ioc 0 N, f n := by
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_succ_top (Nat.zero_le _)]

/-- `∑_{n ≤ k} Λ(n)/n ≥ log k - 1 + 1/k`. -/
theorem llsElem_harmonic_ge {k : ℕ} (hk : 1 ≤ k) :
    Real.log k - 1 + 1 / k ≤ ∑ n ∈ Finset.range (k + 1), Λ n / n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := llsElem_log_factorial_ge k hk
  rw [cheb30_log_factorial_eq (le_refl k)] at h1
  have h2 : ∑ d ∈ Finset.Ioc 0 k, Λ d * ((k / d : ℕ) : ℝ)
      ≤ k * ∑ n ∈ Finset.range (k + 1), Λ n / n := by
    rw [llsElem_sum_range_eq_Ioc _ (by simp), Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have h3 : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) / d := Nat.cast_div_le
    calc Λ d * ((k / d : ℕ) : ℝ) ≤ Λ d * ((k : ℝ) / d) :=
          mul_le_mul_of_nonneg_left h3 ArithmeticFunction.vonMangoldt_nonneg
      _ = k * (Λ d / d) := by ring
  have h3 : (k : ℝ) * (Real.log k - 1 + 1 / k) ≤ k * ∑ n ∈ Finset.range (k + 1), Λ n / n := by
    have e : (k : ℝ) * (Real.log k - 1 + 1 / k) = k * Real.log k - k + 1 := by field_simp
    linarith
  exact le_of_mul_le_mul_left h3 hk0

/-- `∑_{n ≤ N} Λ(n)/n (N - n) ≥ N log N - 2N + 2`. -/
theorem llsElem_T_ge {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - 2 * N + 2 ≤ ∑ n ∈ Finset.range (N + 1), Λ n / n * ((N : ℝ) - n) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ]
  | succ N hN ih =>
    rw [Finset.sum_range_succ]
    have e : ∑ n ∈ Finset.range (N + 1), Λ n / n * (((N + 1 : ℕ) : ℝ) - n)
        = ∑ n ∈ Finset.range (N + 1), Λ n / n * ((N : ℝ) - n)
          + ∑ n ∈ Finset.range (N + 1), Λ n / n := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast; ring
    rw [e, sub_self, mul_zero, add_zero]
    have hA := llsElem_harmonic_ge hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : Real.log (((N : ℝ) + 1) / N) ≤ ((N : ℝ) + 1) / N - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hN0.ne'] at h1
    have h2 : ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - Real.log N) ≤ 1 + 1 / N := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
      have e2 : ((N : ℝ) + 1) * (((N : ℝ) + 1) / N - 1) = 1 + 1 / N := by field_simp; ring
      linarith
    push_cast
    linarith

/-- **Unconditional replacement for LLS Lemma 4.** -/
theorem llsElem_weightedLower : LLSWeightedLower := by
  intro x hx
  unfold weightedLogSumZeta
  have hx0 : 0 < x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  generalize ⌊x⌋₊ = N at hN1 hNx hxN ⊢
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hT := llsElem_T_ge hN1
  have hA := llsElem_harmonic_ge hN1
  have e : x * ∑ n ∈ Finset.range (N + 1), Λ n / n * (1 - (n : ℝ) / x)
      = ∑ n ∈ Finset.range (N + 1), Λ n / n * ((N : ℝ) - n)
        + (x - N) * ∑ n ∈ Finset.range (N + 1), Λ n / n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp; ring
  have h1 : Real.log (x / N) ≤ x / N - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx0.ne' hN0.ne'] at h1
  obtain ⟨d, rfl⟩ : ∃ d : ℝ, x = N + d := ⟨x - N, by ring⟩
  have hd0 : 0 ≤ d := by linarith
  have hd1 : d < 1 := by linarith
  have h3 : ((N : ℝ) + d) * (Real.log (N + d) - Real.log N) ≤ d + d * d / N := by
    have := mul_le_mul_of_nonneg_left h1 hx0.le
    have e2 : ((N : ℝ) + d) * (((N : ℝ) + d) / N - 1) = d + d * d / N := by field_simp; ring
    linarith
  have h5 : d * d / N ≤ d / N := div_le_div_of_nonneg_right (by nlinarith) hN0.le
  have h6 : 0 ≤ d / N := div_nonneg hd0 hN0.le
  have h7 : d * Real.log N - d + d / N ≤ d * ∑ n ∈ Finset.range (N + 1), Λ n / n := by
    have := mul_le_mul_of_nonneg_left hA hd0
    have e3 : d * (Real.log N - 1 + 1 / N) = d * Real.log N - d + d / N := by ring
    linarith
  have key : ((N : ℝ) + d) * (Real.log (N + d) - 2)
      ≤ (N + d) * ∑ n ∈ Finset.range (N + 1), Λ n / n * (1 - (n : ℝ) / (N + d)) := by
    rw [e, add_sub_cancel_left]
    linarith
  exact le_of_mul_le_mul_left key hx0

/-! ## Task 2: reduction lemmas -/

theorem llsElem_le_of_mem_range {n : ℕ} {X : ℝ} (hpos : 0 < n)
    (hn : n ∈ Finset.range (⌊X⌋₊ + 1)) : (n : ℝ) ≤ X :=
  (Nat.le_floor_iff' hpos.ne').mp (by have := Finset.mem_range.mp hn; omega)

/-- If `ψ a = 1` for all `1 ≤ a < X` then `S(X, ψ) = S(X, 1)` (the `n = X` term vanishes). -/
theorem llsElem_logPsi_eq {q : ℕ} (ψ : DirichletCharacter ℂ q) {X : ℝ}
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → ψ (a : ZMod q) = 1) :
    logPsi ψ X = (logPsiZeta X : ℂ) := by
  unfold logPsi logPsiZeta
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Complex.ofReal_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  rcases (llsElem_le_of_mem_range hpos hn).lt_or_eq with hlt | heq
  · rw [h n hpos hlt, mul_one]
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    have : Real.log (X / n) = 0 := by rw [← heq, div_self hn0, Real.log_one]
    rw [this]; simp

theorem llsElem_logPsi_re {q : ℕ} (ψ : DirichletCharacter ℂ q) {X : ℝ}
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → ψ (a : ZMod q) = 1) :
    (logPsi ψ X).re = logPsiZeta X := by
  rw [llsElem_logPsi_eq ψ h, Complex.ofReal_re]

/-- If `ψ a = 1` for all `1 ≤ a < X` then `W(X, ψ) = W(X, 1)` (the `n = X` term vanishes). -/
theorem llsElem_weightedLogSum_eq {q : ℕ} (ψ : DirichletCharacter ℂ q) {X : ℝ}
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → ψ (a : ZMod q) = 1) :
    weightedLogSum ψ X = (weightedLogSumZeta X : ℂ) := by
  unfold weightedLogSum weightedLogSumZeta
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  rcases (llsElem_le_of_mem_range hpos hn).lt_or_eq with hlt | heq
  · rw [h n hpos hlt, mul_one]; push_cast; ring
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    rw [← heq]
    simp [div_self hn0, div_self hnc]

theorem llsElem_weightedLogSum_re {q : ℕ} (ψ : DirichletCharacter ℂ q) {X : ℝ}
    (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → ψ (a : ZMod q) = 1) :
    (weightedLogSum ψ X).re = weightedLogSumZeta X := by
  rw [llsElem_weightedLogSum_eq ψ h, Complex.ofReal_re]

/-- **Reduction to the primitive character.**  If `χ ≠ 1` mod `n > 2` has `χ a = 1` for all
`1 ≤ a < X`, then all such `a` are coprime to `n`, and the primitive character `χ̃` inducing `χ`
(conductor dividing `n`) is nontrivial, is `1` below `X`, and has `S(X, χ̃)`, `W(X, χ̃)` equal to
the `ζ` sums. -/
theorem llsElem_no_witness_facts {n : ℕ} (hn : 2 < n) (χ : DirichletCharacter ℂ n) (hχ : χ ≠ 1)
    {X : ℝ} (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → χ (a : ZMod n) = 1) :
    (∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → Nat.Coprime a n) ∧
      χ.primitiveCharacter.IsPrimitive ∧ χ.primitiveCharacter ≠ 1 ∧
      χ.conductor ≠ 0 ∧ χ.conductor ∣ n ∧
      0 ≤ Real.log χ.conductor ∧ Real.log χ.conductor ≤ Real.log n ∧
      (∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → χ.primitiveCharacter (a : ZMod χ.conductor) = 1) ∧
      logPsi χ.primitiveCharacter X = (logPsiZeta X : ℂ) ∧
      (logPsi χ.primitiveCharacter X).re = logPsiZeta X ∧
      weightedLogSum χ.primitiveCharacter X = (weightedLogSumZeta X : ℂ) ∧
      (weightedLogSum χ.primitiveCharacter X).re = weightedLogSumZeta X := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hp, hne, hl0, hl⟩ := compred_primitive_facts (by omega) χ hχ
  have hprim : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X →
      χ.primitiveCharacter (a : ZMod χ.conductor) = 1 :=
    fun _ ha hax => compred_primitive_eq_one χ h ha hax
  exact ⟨fun _ ha hax => compred_coprime χ h ha hax, hp, hne, χ.conductor_ne_zero,
    χ.conductor_dvd_level, hl0, hl, hprim, llsElem_logPsi_eq _ hprim, llsElem_logPsi_re _ hprim,
    llsElem_weightedLogSum_eq _ hprim, llsElem_weightedLogSum_re _ hprim⟩

/-- For composite `n`, the hypothesis forces `X ≤ minFac n` and `X² ≤ n`. -/
theorem llsElem_sq_le {n : ℕ} (hn : 2 < n) (hnp : ¬ n.Prime) (χ : DirichletCharacter ℂ n)
    {X : ℝ} (hX : 0 ≤ X) (h : ∀ a : ℕ, 1 ≤ a → (a : ℝ) < X → χ (a : ZMod n) = 1) :
    X ≤ n.minFac ∧ X ^ 2 ≤ n :=
  compred_sq_le hn hnp χ hX h

end DetPrimality.Bach

#print axioms DetPrimality.Bach.llsElem_weightedLower
#print axioms DetPrimality.Bach.llsElem_no_witness_facts
#print axioms DetPrimality.Bach.llsElem_sq_le
