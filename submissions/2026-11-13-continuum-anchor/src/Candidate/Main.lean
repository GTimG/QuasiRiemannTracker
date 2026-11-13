/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Extends Sil's marked-anchor method; supporting notices remain in the closure. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ClosestEndpoint
set_option autoImplicit false
namespace Candidate
theorem bound {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (9908119238306612133369374975000622988619121777878229799765263366946606045502455625911569003364955967645745531862430068266267717/11345012023616779600791582323373494582287250283647959965785871011074347975117040113347744503437234376916434871293982689424818700 : ℝ) < s.re) (hpole : ¬(χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Qrh.TwoSlot.AnchorContinuum.ClosestRational.bound χ hs hpole
end Candidate
#print axioms Candidate.bound
