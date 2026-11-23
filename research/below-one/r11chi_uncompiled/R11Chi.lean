import DetPrimality.Bach.R11ChiBound
import DetPrimality.Bach.R11ChiNum

/-!
# designB Lemma 3, (3.2): `r11Chi_main : R11ChiExplicit`

Under GRH, for primitive `χ ≠ 1` mod `q` and `y > 1`,
`Re Φ_χ(y) ≤ 6 y Z₄(χ) + (log q + 1.30) log³ y + 3·9.31 log² y + 3·32.91 log y + 198.31`.

Files: `R11ChiPerron` (Perron integrals with kernel `y^s/s^{j+1}`, residue formula, termwise
integration), `R11ChiFormula` (the explicit formula), `R11ChiDeriv` (derivatives of the Hadamard
expansion at `3/2`), `R11ChiNum` (certified `F₁, F₂, F₃`), `R11ChiBound` (real parts).
-/

namespace DetPrimality.Bach

/-- **designB Lemma 3, (3.2).** -/
theorem r11Chi_main : R11ChiExplicit :=
  r11Chi_main_of_F r11Chi_F1_le r11Chi_F2_le r11Chi_F3_le

#print axioms r11Chi_main
#print axioms r11Chi_perron_one
#print axioms r11Chi_perron_inv_sub
#print axioms r11Chi_perron_LSeries
#print axioms r11Chi_perron_hasSum_of_dom
#print axioms r11Chi_perron_hasSum_poles
#print axioms r11Chi_vi_poles
#print axioms r11Chi_Phi_formula

end DetPrimality.Bach
