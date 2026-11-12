/- Copyright (c) 2026 Sil. Apache-2.0.
The return at theta = 2183367/2500000: the retuned PR103 source, physical return and principal
continuation (Joseph Bebel, Hailey Collet, ArviFoxy, Sil; Apache-2.0) with the improved count window. -/
import Submissions.marked_anchor_induction.Qrh.PositiveGap.BestEndpoint

/-!
# Return.Final

The only hypothesis is `Qrh.MarkedAnchor.Interface.ImprovedFiberMoments` (under `51/100 ≤ β`): the two
improved fiber moments (inverse marked at free width `r ∈ [1467/2000, 311/400]`, ordinary two-factor at
doubled width in the same interval, slot capacity `(1-w)/2 + g0 - g1 w`). The PR103 source
`G(1-10^-256, 2+10^-255, 3/20)` (`QRH.PositiveGap.source`) and every native moment are proved here.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Return
open OAI.SevenEighths Qrh.MarkedAnchor.Interface

/-- `β ≤ 2183367/2500000` from the improved fiber moments. -/
theorem beta_le_of_improved
    (hImp : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → ImprovedFiberMoments) :
    HeckeZeroSupremum.beta ≤ (2183367/2500000 : ℝ) :=
  Qrh.PositiveGap.beta_le_theta_of_improved hImp

/-- Dirichlet nonvanishing for `Re s > 2183367/2500000` from the improved fiber moments. -/
theorem dirichlet_of_improved
    (hImp : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → ImprovedFiberMoments)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2183367/2500000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 :=
  Qrh.PositiveGap.bound_of_improved hImp χ hs hpole

end Qrh.MarkedAnchor.Return
