import DetPrimality.Bach.ExplicitZeros

/-!
# Smoothed explicit formula: assembly (blueprint §3)

`explicit_formula_bound_of_hadamard` has exactly the conclusion of `explicit_formula_bound`
(`Blueprint.lean`), under `HadamardLogDeriv χ` and `∑ m_ρ/|ρ|² < ∞`.
-/

open Complex DirichletCharacter MeasureTheory Set Filter Topology

namespace DetPrimality.Bach

/-! ## Assembly -/

/-- **§3, smoothed explicit formula** (conclusion identical to `explicit_formula_bound`). -/
theorem explicit_formula_bound_of_hadamard {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hH : HadamardLogDeriv χ)
    (hS : Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2) {x : ℝ} (hx : 1 ≤ x) :
    ‖smoothPsi χ x + deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ))
        + ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) *
            ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x))‖
      ≤ Real.log x + 4 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hZi, hZ⟩ := zero_part χ hχ1 hH hS hx
  obtain ⟨hGi, hG⟩ := gamma_part χ hx
  set c0 : ℂ := -(deriv (LFunction χ) 2 / LFunction χ 2) with hc0
  set Z : ℂ → ℂ := fun s => ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) * (1 / (s - ρ) - 1 / (2 - ρ)) with hZdef
  have hAi : VerticalIntegrable (fun s => (c0 + (Gfun χ s - Gfun χ 2)) / (s * (s + 1))) 2 := by
    have h := Integrable.add (verticalIntegrable_const_kernel c0) hGi
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, add_div]
  have h1 : smoothPsi χ x = perronI (fun s => (c0 + (Gfun χ s - Gfun χ 2)) - Z s) x := by
    rw [smoothPsi_eq_perronI χ hx]
    apply perronI_congr_line
    intro y
    exact neg_logDeriv_decomp χ hχ1 hH hS (by simp)
  rw [perronI_sub hAi hZi hx0, perronI_add (verticalIntegrable_const_kernel c0) hGi hx0,
    perronI_const, perronI_one hx, hZ] at h1
  have key : smoothPsi χ x + deriv (LFunction χ) 2 / LFunction χ 2 * (1 - 1 / (x : ℂ))
        + ∑' ρ : ℂ, (zeroOrd χ ρ : ℂ) *
            ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) + 3 / ((ρ + 1) * (2 - ρ) * x))
      = perronI (fun s => Gfun χ s - Gfun χ 2) x := by
    rw [h1, hc0]
    simp only [zeroTerm]
    ring
  rw [key]
  exact hG

end DetPrimality.Bach
