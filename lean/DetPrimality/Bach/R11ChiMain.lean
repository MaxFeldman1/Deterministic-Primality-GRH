import DetPrimality.Bach.R11ChiBound
import DetPrimality.Bach.R11ChiF

/-!
# Round 11, Lemma 3 (designB (3.2)): `R11ChiExplicit`, unconditional on the numeric inputs
-/

namespace DetPrimality.Bach

/-- designB (3.2). -/
theorem r11Chi_main' : R11ChiExplicit := r11Chi_main_of_F r11F_F1 r11F_F2 r11F_F3

end DetPrimality.Bach

#print axioms DetPrimality.Bach.r11Chi_main'
