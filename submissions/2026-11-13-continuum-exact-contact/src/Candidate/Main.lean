/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Exact-contact theorem via finite positive-cost constructions, extending Sil's
marked-anchor induction. Inherited authors' notices remain in the closure. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactEndpoint
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PolynomialContact
set_option autoImplicit false
namespace Candidate

/-- Full all-moduli theorem at the exact degree-nine contact. -/
theorem exact_contact_bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : Qrh.TwoSlot.AnchorContinuum.Contact.theta < s.re)
    (hpole : ¬(χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Qrh.TwoSlot.AnchorContinuum.ExactEndpoint.bound χ hs hpole

/-- Exact endpoint in the tracker's canonical polynomial-root presentation. -/
theorem bound {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (sInf {x | (13 / 15) < x ∧ x < (7 / 8) ∧ ((-274959111914881) + x * (2643837682856883 + x * ((-11291220876239226) + x * (28111661257098222 + x * ((-44964545308854309) + x * (47916748658170215 + x * ((-34020380857037616) + x * (15517896164111592 + x * ((-4126408710053184) + x * 487371101862528))))))))) = 0} : ℝ) < s.re) (hpole : ¬(χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  change Qrh.TwoSlot.AnchorContinuum.PolynomialContact.contact < s.re at hs
  rw [Qrh.TwoSlot.AnchorContinuum.PolynomialContact.contact_eq] at hs
  exact exact_contact_bound χ hs hpole

theorem bound_le : (sInf {x | (13 / 15) < x ∧ x < (7 / 8) ∧ ((-274959111914881) + x * (2643837682856883 + x * ((-11291220876239226) + x * (28111661257098222 + x * ((-44964545308854309) + x * (47916748658170215 + x * ((-34020380857037616) + x * (15517896164111592 + x * ((-4126408710053184) + x * 487371101862528))))))))) = 0} : ℝ) ≤ (9908119238306612133369374975000622988619121777878229799765263366946606045502455625911569003364955967645745531862430068266267717/11345012023616779600791582323373494582287250283647959965785871011074347975117040113347744503437234376916434871293982689424818700 : ℝ) := by
  change Qrh.TwoSlot.AnchorContinuum.PolynomialContact.contact ≤ _
  rw [Qrh.TwoSlot.AnchorContinuum.PolynomialContact.contact_eq]
  exact Qrh.TwoSlot.AnchorContinuum.ClosestRational.target_bounds.1.le

theorem bound_isolated : ∃! x : ℝ, (13 / 15) < x ∧ x < (7 / 8) ∧ ((-274959111914881) + x * (2643837682856883 + x * ((-11291220876239226) + x * (28111661257098222 + x * ((-44964545308854309) + x * (47916748658170215 + x * ((-34020380857037616) + x * (15517896164111592 + x * ((-4126408710053184) + x * 487371101862528))))))))) = 0 :=
  Qrh.TwoSlot.AnchorContinuum.PolynomialContact.isolated

end Candidate
#print axioms Candidate.exact_contact_bound
#print axioms Candidate.bound
#print axioms Candidate.bound_le
#print axioms Candidate.bound_isolated
