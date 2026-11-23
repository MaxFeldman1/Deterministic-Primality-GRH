import Mathlib
import DetPrimality.Bach.R14Defs

/-!
# Round 14 assembly, part 1: certificate structure, signed positivity over `p + 1` cells, ζ side
(research/barrier/formal0760.md §1, §1.2, §4 Stage 1)

Scaled variables: `L″ = β·log(x/n)`, `s″ = (s + β − 1)/β`, `a = β − 1`.  The weight of `n < x` is
`√n · (n/x)^a · W(β log(x/n))` with `W = r13W θ J`.

* `r14A_R`, `r14A_F` : `R_κ(L)` and `F(L) = e^{-κL} R_κ(L)` (`κ = 1 + 1/(2β)`), so that
  `∑_{n<Y} Λ(n) √n (n/x)^a W(β log(x/n)) = (1/β)·F(L″)·x^{3/2} + O(x^{5/4})` for `x = e^{L″/β} Y`;
* `R14Cert β p J m θ e b N₀` : the certificate (`b 0 = 0 < b 1 < … < b (p+1) = ℓ″ = βℓ`,
  `W` has sign `(-1)^(p-i)` on `[b i, b (i+1)]`); the resulting constant is
  `c* = e^{-b(p+1)/β} · (β e₁ / (2 N₀))²` (`r14A_eventually` in `R14Asm.lean`);
* `r14A_S` : `S(Y) = ∑_{n<Y} Λ(n) √n (n/x)^a W(β log(x/n))`;
* `r14A_sum_ge` : signed positivity, `S(X) − ∑_i (-1)^{p-i} (S(Y_i) − S(Y_{i+1})) ≤ ∑_j θ_j β^j/j! · Re Φ^{(a)}_{χ,j}(x)`,
  `Y_i = e^{-b_i/β} x`, when `χ = 1` below `X = Y_{p+1}`;
* `r14A_zeta` : from `R14ZetaSmooth a`, `(N₀/β) x^{3/2} − C x^{5/4} ≤` the left side.
-/

open Complex DirichletCharacter

namespace DetPrimality.Bach

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `R_κ(L) = ∑_j θ_j ∑_{i ≤ j} L^i/i! · κ^{-(j+1-i)}` (`r13R` is `κ = 3/2`). -/
noncomputable def r14A_R (κ : ℝ) (θ : ℕ → ℝ) (J : ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    θ j * ∑ i ∈ Finset.range (j + 1), L ^ i / (i.factorial : ℝ) * (1 / κ) ^ (j + 1 - i)

/-- `F(L) = e^{-κL} R_κ(L) = ∫_L^∞ W(τ) e^{-κτ} dτ`. -/
noncomputable def r14A_F (κ : ℝ) (θ : ℕ → ℝ) (J : ℕ) (L : ℝ) : ℝ :=
  Real.exp (-(κ * L)) * r14A_R κ θ J L

/-- The Round 14 certificate in the scaled variables (`L″ = β log(x/n)`, `s″ = (s+β−1)/β`).
`b 0 = 0 < b 1 < … < b (p+1) = ℓ″`; `W = r13W θ J` has sign `(-1)^(p-i)` on `[b i, b (i+1)]`;
`modulus` is Lemma E on `Re s″ = 1`; `num` is the lower bound for
`N = F(b_{p+1}) − ∑_{i ≤ p} (-1)^{p-i} (F(b_i) − F(b_{i+1}))`, `F = r14A_F (1 + 1/(2β))`.
The constant is `c* = e^{-b(p+1)/β} (β e₁/(2N₀))²`. `β = 1`, `p = 1` is `R13Cert`. -/
structure R14Cert (β p J m : ℕ) (θ e b : ℕ → ℝ) (N₀ : ℝ) : Prop where
  beta : 1 ≤ β
  low : ∀ j, j < 3 → θ j = 0
  b0 : b 0 = 0
  mono : ∀ i, i ≤ p → b i < b (i + 1)
  cell : ∀ i, i ≤ p → ∀ L, b i ≤ L → L ≤ b (i + 1) → 0 ≤ (-1) ^ (p - i) * r13W θ J L
  modulus : ∀ t : ℝ, ‖r13K θ J (1 + (t : ℂ) * I)‖ ≤ r13G e m t
  e1pos : 0 < e 1
  num : 0 < N₀ ∧ N₀ ≤ r14A_F (1 + 1 / (2 * (β : ℝ))) θ J (b (p + 1))
      - ∑ i ∈ Finset.range (p + 1), (-1) ^ (p - i) *
          (r14A_F (1 + 1 / (2 * (β : ℝ))) θ J (b i) - r14A_F (1 + 1 / (2 * (β : ℝ))) θ J (b (i + 1)))

/-- `S(Y) = ∑_{n<Y} Λ(n) √n (n/x)^a W(β log(x/n))`. -/
noncomputable def r14A_S (a : ℕ) (β : ℝ) (θ : ℕ → ℝ) (J : ℕ) (x Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌈Y⌉₊,
    Λ n * Real.sqrt n * ((n : ℝ) / x) ^ a * r13W θ J (β * Real.log (x / n))

variable {β p J m a : ℕ} {θ e b : ℕ → ℝ} {N₀ : ℝ}

theorem r14A_b_mono (cert : R14Cert β p J m θ e b N₀) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p + 1) :
    b i ≤ b j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (ih (by omega)).trans (cert.mono k (by omega)).le

theorem r14A_b_nonneg (cert : R14Cert β p J m θ e b N₀) {i : ℕ} (hi : i ≤ p + 1) : 0 ≤ b i := by
  have := r14A_b_mono cert (Nat.zero_le i) hi
  rwa [cert.b0] at this

/-! ## Signed positivity -/

theorem r14A_re_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℕ) (β : ℝ) (θ : ℕ → ℝ) (J : ℕ)
    (x : ℝ) :
    ∑ j ∈ Finset.range (J + 1), θ j * β ^ j / (j.factorial : ℝ) * (r14Phi χ a j x).re
      = ∑ n ∈ Finset.range ⌈x⌉₊, Λ n * (χ (n : ZMod q)).re *
          (Real.sqrt n * ((n : ℝ) / x) ^ a * r13W θ J (β * Real.log (x / n))) := by
  have hre : ∀ j, (r14Phi χ a j x).re = ∑ n ∈ Finset.range ⌈x⌉₊,
      Λ n * (χ (n : ZMod q)).re * (Real.sqrt n * ((n : ℝ) / x) ^ a * Real.log (x / n) ^ j) := by
    intro j
    unfold r14Phi
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero]
  simp only [hre, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold r13W
  simp only [Finset.mul_sum, mul_pow]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Signed positivity over `p + 1` cells** (generalises `r13A_sum_ge`). -/
theorem r14A_sum_ge {q : ℕ} (χ : DirichletCharacter ℂ q) {X x : ℝ}
    (cert : R14Cert β p J m θ e b N₀) (hX0 : 0 < X) (hx : x = Real.exp (b (p + 1) / β) * X)
    (h1 : ∀ n : ℕ, 1 ≤ n → (n : ℝ) < X → χ (n : ZMod q) = 1) :
    r14A_S a β θ J x X - ∑ i ∈ Finset.range (p + 1), (-1) ^ (p - i) *
        (r14A_S a β θ J x (Real.exp (-(b i / β)) * x)
          - r14A_S a β θ J x (Real.exp (-(b (i + 1) / β)) * x))
      ≤ ∑ j ∈ Finset.range (J + 1), θ j * (β : ℝ) ^ j / (j.factorial : ℝ) * (r14Phi χ a j x).re := by
  rw [r14A_re_sum]
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast cert.beta
  have hx0 : 0 < x := by rw [hx]; positivity
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun n : ℕ =>
      Λ n * Real.sqrt n * ((n : ℝ) / x) ^ a * r13W θ J (β * Real.log (x / n)) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun n : ℕ => Λ n * (χ (n : ZMod q)).re *
      (Real.sqrt n * ((n : ℝ) / x) ^ a * r13W θ J (β * Real.log (x / n))) := ⟨_, rfl⟩
  have hfn : ∀ n, f n
      = Λ n * Real.sqrt n * ((n : ℝ) / x) ^ a * r13W θ J (β * Real.log (x / n)) :=
    fun n => by rw [hf]
  have hgn : ∀ n, g n = Λ n * (χ (n : ZMod q)).re *
      (Real.sqrt n * ((n : ℝ) / x) ^ a * r13W θ J (β * Real.log (x / n))) := fun n => by rw [hg]
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ, Y = fun i : ℕ => Real.exp (-(b i / β)) * x := ⟨_, rfl⟩
  have hYi : ∀ i, Y i = Real.exp (-(b i / β)) * x := fun i => by rw [hY]
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ, G = fun i : ℕ => ∑ n ∈ Finset.range ⌈Y i⌉₊, g n := ⟨_, rfl⟩
  have hGi : ∀ i, G i = ∑ n ∈ Finset.range ⌈Y i⌉₊, g n := fun i => by rw [hG]
  have hS : ∀ Y' : ℝ, r14A_S a β θ J x Y' = ∑ n ∈ Finset.range ⌈Y'⌉₊, f n := fun Y' => by
    unfold r14A_S; rw [hf]
  have hY0 : Y 0 = x := by rw [hYi, cert.b0]; simp
  have hYp : Y (p + 1) = X := by
    rw [hYi, hx, ← mul_assoc, ← Real.exp_add]; simp
  have hYanti : ∀ i, i ≤ p → Y (i + 1) ≤ Y i := by
    intro i hi
    rw [hYi, hYi]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hx0.le
    have := div_le_div_of_nonneg_right (cert.mono i hi).le hβ0.le
    linarith
  have hre : ∀ n : ℕ, |(χ (n : ZMod q)).re| ≤ 1 := fun n =>
    (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
  have htel : ∑ i ∈ Finset.range (p + 1), (G i - G (i + 1)) = G 0 - G (p + 1) :=
    Finset.sum_range_sub' G (p + 1)
  have hGp : G (p + 1) = r14A_S a β θ J x X := by
    rw [hGi, hS, hYp]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hfn, hgn]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have hlt : (n : ℝ) < X := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
      rw [h1 n hpos hlt, Complex.one_re]; ring
  have hG0 : G 0 = ∑ n ∈ Finset.range ⌈x⌉₊, g n := by rw [hGi, hY0]
  have hcell : ∀ i ∈ Finset.range (p + 1),
      -((-1) ^ (p - i) * (r14A_S a β θ J x (Real.exp (-(b i / β)) * x)
          - r14A_S a β θ J x (Real.exp (-(b (i + 1) / β)) * x))) ≤ G i - G (i + 1) := by
    intro i hi
    have hip : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [← hYi, ← hYi, hS, hS, hGi, hGi]
    have sub : Finset.range ⌈Y (i + 1)⌉₊ ⊆ Finset.range ⌈Y i⌉₊ :=
      Finset.range_mono (Nat.ceil_mono (hYanti i hip))
    rw [← Finset.sum_sdiff sub, ← Finset.sum_sdiff (f := g) sub, add_sub_cancel_right,
      add_sub_cancel_right, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hn
    rw [hfn, hgn]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have hlo : Y (i + 1) ≤ n := Nat.ceil_le.mp hn.2
    have hhi : (n : ℝ) < Y i := Nat.lt_ceil.mp hn.1
    rw [hYi] at hlo hhi
    have hee : ∀ u : ℝ, Real.exp u * Real.exp (-u) = 1 := fun u => by
      rw [← Real.exp_add]; simp
    have hLlo : b i ≤ β * Real.log (x / n) := by
      have h : b i / β ≤ Real.log (x / n) := by
        rw [Real.le_log_iff_exp_le (div_pos hx0 hn0), le_div_iff₀ hn0]
        have := mul_le_mul_of_nonneg_left hhi.le (Real.exp_pos (b i / β)).le
        rw [← mul_assoc, hee, one_mul] at this
        exact this
      have := (div_le_iff₀ hβ0).mp h
      linarith
    have hLhi : β * Real.log (x / n) ≤ b (i + 1) := by
      have h : Real.log (x / n) ≤ b (i + 1) / β := by
        rw [Real.log_le_iff_le_exp (div_pos hx0 hn0), div_le_iff₀ hn0]
        have := mul_le_mul_of_nonneg_left hlo (Real.exp_pos (b (i + 1) / β)).le
        rw [← mul_assoc, hee, one_mul] at this
        exact this
      have := (le_div_iff₀ hβ0).mp h
      linarith
    have hW := cert.cell i hip _ hLlo hLhi
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hq : 0 ≤ ((n : ℝ) / x) ^ a := by positivity
    have hpre : 0 ≤ Λ n * Real.sqrt n * ((n : ℝ) / x) ^ a :=
      mul_nonneg (mul_nonneg hΛ (Real.sqrt_nonneg _)) hq
    obtain ⟨w, hw⟩ : ∃ w : ℝ, w = r13W θ J (β * Real.log (x / n)) := ⟨_, rfl⟩
    rw [← hw] at hW ⊢
    rcases neg_one_pow_eq_or ℝ (p - i) with hs | hs
    · rw [hs] at hW ⊢
      rw [one_mul] at hW
      have h1re : 0 ≤ 1 + (χ (n : ZMod q)).re := by linarith [(abs_le.mp (hre n)).1]
      have h0 : 0 ≤ Λ n * Real.sqrt n * ((n : ℝ) / x) ^ a * w * (1 + (χ (n : ZMod q)).re) :=
        mul_nonneg (mul_nonneg hpre hW) h1re
      linarith
    · rw [hs] at hW ⊢
      have hW' : 0 ≤ -w := by linarith
      have h1re : 0 ≤ 1 - (χ (n : ZMod q)).re := by linarith [(abs_le.mp (hre n)).2]
      have h0 : 0 ≤ Λ n * Real.sqrt n * ((n : ℝ) / x) ^ a * (-w) * (1 - (χ (n : ZMod q)).re) :=
        mul_nonneg (mul_nonneg hpre hW') h1re
      linarith
  have hsum := Finset.sum_le_sum hcell
  rw [Finset.sum_neg_distrib, htel, hGp, hG0] at hsum
  have hGoal : ∑ n ∈ Finset.range ⌈x⌉₊, Λ n * (χ (n : ZMod q)).re *
      (Real.sqrt n * ((n : ℝ) / x) ^ a * r13W θ J (β * Real.log (x / n)))
      = ∑ n ∈ Finset.range ⌈x⌉₊, g n := by rw [hg]
  rw [hGoal]
  linarith

/-! ## The ζ side -/

/-- Binomial re-expansion `log(x/n) = log(x/Y) + log(Y/n)`, `(n/x)^a = (Y/x)^a (n/Y)^a`. -/
theorem r14A_binom (a : ℕ) (β : ℝ) (θ : ℕ → ℝ) (J : ℕ) {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y) :
    r14A_S a β θ J x Y = ∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1),
      (Y / x) ^ a * (θ j * β ^ j / (j.factorial : ℝ) *
        ((j.choose i : ℝ) * Real.log (x / Y) ^ (j - i))) * r14A a i Y := by
  unfold r14A_S r14A r13W
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
  have e : Real.log (x / n) = Real.log (Y / n) + Real.log (x / Y) := by
    rw [Real.log_div hx.ne' hn0.ne', Real.log_div hY.ne' hn0.ne', Real.log_div hx.ne' hY.ne']
    ring
  have hq : ((n : ℝ) / x) ^ a = (Y / x) ^ a * ((n : ℝ) / Y) ^ a := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [e, hq, mul_pow, add_pow]
  simp only [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem r14A_R_eq (θ : ℕ → ℝ) (J : ℕ) {β r : ℝ} (hβ : 0 < β) (hr : 0 < r) (L : ℝ) :
    ∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1),
      θ j * β ^ j / (j.factorial : ℝ) * ((j.choose i : ℝ) * (L / β) ^ (j - i))
        * ((i.factorial : ℝ) * (1 / r) ^ (i + 1))
      = 1 / β * r14A_R (r / β) θ J L := by
  unfold r14A_R
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_range_reflect
    (fun i => L ^ i / (i.factorial : ℝ) * (1 / (r / β)) ^ (j + 1 - i)) (j + 1)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + i := ⟨j - i, by omega⟩
  have e1 : k + i + 1 - 1 - i = k := by omega
  have e2 : k + i + 1 - k = i + 1 := by omega
  have e3 : k + i - i = k := by omega
  rw [e1, e2, e3]
  have hc : ((k + i).choose i : ℝ) * (i.factorial : ℝ) * (k.factorial : ℝ)
      = ((k + i).factorial : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial hi'
    rw [e3] at this
    exact_mod_cast this
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((k + i).choose i : ℝ) ≠ 0 := by
    have := Nat.choose_pos hi'
    positivity
  rw [← hc]
  simp only [div_pow, one_div_div, one_pow]
  field_simp
  ring

theorem r14A_zeta_one (hGRH : DirichletLZerosOnLine) {a : ℕ} (hZ : R14ZetaSmooth a) (θ : ℕ → ℝ)
    (J : ℕ) {β : ℝ} (hβ : β = a + 1) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x Y : ℝ, 1 ≤ Y → Y ≤ x → x = Real.exp (L / β) * Y →
      |r14A_S a β θ J x Y - 1 / β * r14A_F (1 + 1 / (2 * β)) θ J L * x ^ ((3 : ℝ) / 2)|
        ≤ C * x ^ ((5 : ℝ) / 4) := by
  choose Ci hCi using hZ hGRH
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hCi0 : ∀ i, 0 ≤ Ci i := by
    intro i
    have := hCi i 1 le_rfl
    simp only [Real.one_rpow, mul_one] at this
    exact (abs_nonneg _).trans this
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = L / β := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (a : ℝ) + 3 / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hκ : 1 + 1 / (2 * β) = r / β := by
    rw [hr, hβ]; field_simp; ring
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℝ, c = fun j i =>
      θ j * β ^ j / (j.factorial : ℝ) * ((j.choose i : ℝ) * lam ^ (j - i)) := ⟨_, rfl⟩
  have hcji : ∀ j i, c j i
      = θ j * β ^ j / (j.factorial : ℝ) * ((j.choose i : ℝ) * lam ^ (j - i)) :=
    fun j i => by rw [hc]
  refine ⟨∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1), |c j i| * Ci i, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
      mul_nonneg (abs_nonneg _) (hCi0 i)
  intro x Y hY hYx hx
  have hY0 : 0 < Y := by linarith
  have hx0 : 0 < x := by linarith
  rw [← hlam] at hx
  have hlog : Real.log (x / Y) = lam := by
    rw [hx, mul_div_assoc, div_self hY0.ne', mul_one, Real.log_exp]
  have hYxe : Y / x = Real.exp (-lam) := by
    rw [hx, Real.exp_neg]; field_simp
  have hq0 : 0 ≤ (Y / x) ^ a := by positivity
  have hq1 : (Y / x) ^ a ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one hx0).mpr hYx)
  have hmain : Real.exp (-((1 + 1 / (2 * β)) * L)) * x ^ ((3 : ℝ) / 2)
      = (Y / x) ^ a * Y ^ ((3 : ℝ) / 2) := by
    have hYe : Y = Real.exp (-lam) * x := by
      rw [hx, ← mul_assoc, ← Real.exp_add]; simp
    have h32 : Y ^ ((3 : ℝ) / 2) = Real.exp (-lam * (3 / 2)) * x ^ ((3 : ℝ) / 2) := by
      conv_lhs => rw [hYe]
      rw [Real.mul_rpow (Real.exp_pos _).le hx0.le, ← Real.exp_mul]
    rw [hYxe, ← Real.exp_nat_mul, h32, ← mul_assoc, ← Real.exp_add]
    congr 2
    rw [hκ, hr, hlam]
    field_simp
    ring
  have hpow : Y ^ ((5 : ℝ) / 4) ≤ x ^ ((5 : ℝ) / 4) :=
    Real.rpow_le_rpow hY0.le hYx (by norm_num)
  have e1 : r14A_S a β θ J x Y = ∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1),
      (Y / x) ^ a * c j i * r14A a i Y := by
    rw [r14A_binom a β θ J hx0 hY0, hlog]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hcji]
  have e2 : 1 / β * r14A_R (r / β) θ J L * Y ^ ((3 : ℝ) / 2)
      = ∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1),
        c j i * ((i.factorial : ℝ) * (1 / r) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)) := by
    rw [← r14A_R_eq θ J hβ0 hr0 L, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hcji, hlam]; ring
  have e3 : r14A_S a β θ J x Y - 1 / β * r14A_F (1 + 1 / (2 * β)) θ J L * x ^ ((3 : ℝ) / 2)
      = ∑ j ∈ Finset.range (J + 1), ∑ i ∈ Finset.range (j + 1),
        (Y / x) ^ a * c j i
          * (r14A a i Y - (i.factorial : ℝ) * (1 / r) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)) := by
    have : 1 / β * r14A_F (1 + 1 / (2 * β)) θ J L * x ^ ((3 : ℝ) / 2)
        = (Y / x) ^ a * (1 / β * r14A_R (r / β) θ J L * Y ^ ((3 : ℝ) / 2)) := by
      unfold r14A_F
      rw [← hκ]
      linear_combination (1 / β * r14A_R (1 + 1 / (2 * β)) θ J L) * hmain
    rw [this, e1, e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e3, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg hq0]
  have h := hCi i Y hY
  rw [← hr] at h
  calc (Y / x) ^ a * |c j i|
        * |r14A a i Y - (i.factorial : ℝ) * (1 / r) ^ (i + 1) * Y ^ ((3 : ℝ) / 2)|
      ≤ 1 * |c j i| * (Ci i * Y ^ ((5 : ℝ) / 4)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hq1 (abs_nonneg _)) h (abs_nonneg _)
          (mul_nonneg zero_le_one (abs_nonneg _))
    _ ≤ 1 * |c j i| * (Ci i * x ^ ((5 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (hCi0 i))
          (mul_nonneg zero_le_one (abs_nonneg _))
    _ = |c j i| * Ci i * x ^ ((5 : ℝ) / 4) := by ring

/-- **ζ side**: main term of the left side of `r14A_sum_ge`. -/
theorem r14A_zeta (hGRH : DirichletLZerosOnLine) (hZ : R14ZetaSmooth a) (hβ : β = a + 1)
    (cert : R14Cert β p J m θ e b N₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ x : ℝ, x = Real.exp (b (p + 1) / β) * X →
      N₀ / β * x ^ ((3 : ℝ) / 2) - C * x ^ ((5 : ℝ) / 4)
        ≤ r14A_S a β θ J x X - ∑ i ∈ Finset.range (p + 1), (-1) ^ (p - i) *
          (r14A_S a β θ J x (Real.exp (-(b i / β)) * x)
            - r14A_S a β θ J x (Real.exp (-(b (i + 1) / β)) * x)) := by
  have hβR : (β : ℝ) = (a : ℝ) + 1 := by rw [hβ]; push_cast; ring
  have hβ0 : (0 : ℝ) < β := by rw [hβR]; positivity
  choose C hC0 hC using fun i : ℕ => r14A_zeta_one hGRH hZ θ J hβR (b i)
  refine ⟨C (p + 1) + ∑ i ∈ Finset.range (p + 1), (C i + C (i + 1)),
    add_nonneg (hC0 _) (Finset.sum_nonneg fun i _ => add_nonneg (hC0 _) (hC0 _)), ?_⟩
  intro X hX x hx
  have hx0 : 0 < x := by rw [hx]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = x ^ ((3 : ℝ) / 2) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = x ^ ((5 : ℝ) / 4) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  rw [← hP, ← hQ]
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ,
      S = fun i : ℕ => r14A_S a β θ J x (Real.exp (-(b i / β)) * x) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ,
      F = fun i : ℕ => r14A_F (1 + 1 / (2 * (β : ℝ))) θ J (b i) := ⟨_, rfl⟩
  have hSi : ∀ i, S i = r14A_S a β θ J x (Real.exp (-(b i / β)) * x) := fun i => by rw [hS]
  have hFi : ∀ i, F i = r14A_F (1 + 1 / (2 * (β : ℝ))) θ J (b i) := fun i => by rw [hF]
  have hXe : X = Real.exp (-(b (p + 1) / β)) * x := by
    rw [hx, ← mul_assoc, ← Real.exp_add]; simp
  have hD : ∀ i, i ≤ p + 1 → |S i - 1 / β * F i * P| ≤ C i * Q := by
    intro i hi
    rw [hSi, hFi, hP, hQ]
    have hbi := r14A_b_mono cert hi le_rfl
    have hbi0 := r14A_b_nonneg cert hi
    have hY1 : 1 ≤ Real.exp (-(b i / β)) * x := by
      rw [hx, ← mul_assoc, ← Real.exp_add]
      have h0 : 0 ≤ -(b i / β) + b (p + 1) / β := by
        have := div_le_div_of_nonneg_right hbi hβ0.le
        linarith
      have := Real.one_le_exp h0
      nlinarith
    have hYx : Real.exp (-(b i / β)) * x ≤ x := by
      have : Real.exp (-(b i / β)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := div_nonneg hbi0 hβ0.le; linarith)
      nlinarith
    exact hC i x _ hY1 hYx (by rw [← mul_assoc, ← Real.exp_add]; simp)
  have hnum := cert.num.2
  simp only [← hFi] at hnum
  rw [hXe, ← hSi]
  simp only [← hSi]
  have hcell : ∀ i ∈ Finset.range (p + 1), (-1) ^ (p - i) * (S i - S (i + 1))
      ≤ (-1) ^ (p - i) * (F i - F (i + 1)) * (P / β) + (C i + C (i + 1)) * Q := by
    intro i hi
    have hip : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have d1 := abs_le.mp (hD i (by omega))
    have d2 := abs_le.mp (hD (i + 1) (by omega))
    have eF : ∀ k, 1 / (β : ℝ) * F k * P = F k * (P / β) := fun k => by ring
    rw [eF] at d1 d2
    rcases neg_one_pow_eq_or ℝ (p - i) with hs | hs
    · rw [hs]; linarith [d1.1, d1.2, d2.1, d2.2]
    · rw [hs]; linarith [d1.1, d1.2, d2.1, d2.2]
  have hsum := Finset.sum_le_sum hcell
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  have dp := abs_le.mp (hD (p + 1) le_rfl)
  have hPβ : 0 ≤ P / β := div_nonneg hP0 hβ0.le
  have hmul := mul_le_mul_of_nonneg_right hnum hPβ
  have e1 : N₀ / (β : ℝ) * P = N₀ * (P / β) := by ring
  have e2 : 1 / (β : ℝ) * F (p + 1) * P = F (p + 1) * (P / β) := by ring
  rw [e2] at dp
  rw [sub_mul] at hmul
  rw [e1, add_mul]
  linarith [dp.1]

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r14A_sum_ge
#print axioms DetPrimality.Bach.r14A_zeta
