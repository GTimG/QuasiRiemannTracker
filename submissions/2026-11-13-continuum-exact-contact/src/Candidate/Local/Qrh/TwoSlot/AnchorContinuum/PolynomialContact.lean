/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Canonical polynomial-root presentation of the exact continuum contact. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ContactUniqueness

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.PolynomialContact
noncomputable section
open Contact Set

def expanded (x : ℝ) : ℝ :=
  ((-274959111914881) + x * (2643837682856883 + x *
  ((-11291220876239226) + x * (28111661257098222 + x *
  ((-44964545308854309) + x * (47916748658170215 + x *
  ((-34020380857037616) + x * (15517896164111592 + x *
  ((-4126408710053184) + x * 487371101862528)))))))))

theorem expanded_eq (x : ℝ) : expanded x = -polynomial x := by
  unfold expanded polynomial
  ring

theorem isolated : ∃! x : ℝ, (13 / 15 : ℝ) < x ∧ x < (7 / 8 : ℝ) ∧ expanded x = 0 := by
  refine ⟨theta, ⟨theta_range.1, theta_range.2, ?_⟩, ?_⟩
  · rw [expanded_eq, theta_root, neg_zero]
  · intro x hx
    apply root_unique ⟨hx.1, hx.2.1⟩
    have hh := hx.2.2
    rw [expanded_eq] at hh
    exact neg_eq_zero.mp hh

def contact : ℝ := sInf {x | (13 / 15 : ℝ) < x ∧ x < (7 / 8 : ℝ) ∧ expanded x = 0}

theorem contact_eq : contact = theta := by
  have hset : {x | (13 / 15 : ℝ) < x ∧ x < (7 / 8 : ℝ) ∧ expanded x = 0} = {theta} := by
    ext x
    constructor
    · intro hx
      apply Set.mem_singleton_iff.mpr
      apply root_unique ⟨hx.1, hx.2.1⟩
      have hh := hx.2.2
      rw [expanded_eq] at hh
      exact neg_eq_zero.mp hh
    · intro hx
      have he : x = theta := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨theta_range.1, theta_range.2, by rw [expanded_eq, theta_root, neg_zero]⟩
  unfold contact
  rw [hset, csInf_singleton]

end
end Qrh.TwoSlot.AnchorContinuum.PolynomialContact
#print axioms Qrh.TwoSlot.AnchorContinuum.PolynomialContact.isolated
#print axioms Qrh.TwoSlot.AnchorContinuum.PolynomialContact.contact_eq
