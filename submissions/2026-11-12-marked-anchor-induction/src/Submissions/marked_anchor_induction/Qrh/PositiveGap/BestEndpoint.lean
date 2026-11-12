/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Dirichlet nonvanishing above the fraction closest to the contact. -/
/- Modified by Sil (2026-11-11): the return runs at theta = 2183367/2500000 and needs, besides the
PR103 source below, the improved fiber moments; the endpoint theorems are the conditional
`beta_le_theta_of_improved` and `bound_of_improved` instead of the unconditional endpoint at the
PR103 fraction. -/
import Submissions.marked_anchor_induction.Qrh.PositiveGap.SourceComposition
import Submissions.marked_anchor_induction.Qrh.PositiveGap.Return.Tuning.Endpoint

set_option autoImplicit false
namespace Qrh.PositiveGap
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source

/-- The proved positive-gap source is the return's source face. -/
theorem return_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (3/20) :=
  QRH.PositiveGap.source hβ

theorem beta_le_theta_of_improved
    (hImp : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → Qrh.MarkedAnchor.Interface.ImprovedFiberMoments) :
    HeckeZeroSupremum.beta ≤ (2183367/2500000 : ℝ) :=
  QRH.PositiveGap.Return.Tuning.beta_le_theta_of_source return_source hImp

/-- Dirichlet nonvanishing for every positive modulus and every character, given the improved fiber
moments. -/
theorem bound_of_improved
    (hImp : (51/100:ℝ) ≤ HeckeZeroSupremum.beta → Qrh.MarkedAnchor.Interface.ImprovedFiberMoments)
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2183367/2500000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.PositiveGap.Return.Tuning.dirichlet_of_source return_source hImp χ hs hpole
end
end Qrh.PositiveGap
