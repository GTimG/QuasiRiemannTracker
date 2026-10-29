/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Strict source-curve adapter at fixed selected gap 1/10^9.
Inherited notices follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.FrontierSourceCurveFamilyMargins

import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveTheorem
import Candidate.Local.Qrh.JointDetector.FrontierSourceFromCores
import Candidate.Local.Qrh.JointDetector.FrontierActualNorm

namespace Qrh.JointDetector.FrontierRepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
open Set RepeatedMarks RepeatedMarks.SourceCurve RepeatedMarks.CurvedSourceStep

/-- Closed finite composition on a source curve. The remaining inlet is
explicitly a scalar small-step geometry assertion, not an analytic estimate
or a source theorem at unproved intermediate points. -/
theorem piece_reachable {a b floor : ℝ} (hab : a ≤ b)
    (B L s n r : ℝ → ℝ)
    (hB : ContinuousOn B (Icc a b)) (hL : ContinuousOn L (Icc a b))
    (hs : ContinuousOn s (Icc a b)) (hn : ContinuousOn n (Icc a b))
    (hr : ContinuousOn r (Icc a b))
    (hcert : ∀ x∈Icc a b, RayCrossing (B x) (L x) (s x) (n x) (r x))
    (hBmin : ∀ x∈Icc a b, (9/10:ℝ) ≤ B x)
    (hfloor : (50001/100000:ℝ) ≤ floor)
    (hscalar : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧
      ∀ x∈Icc a b, ∀ y∈Icc a b, x < y → y-x ≤ δ →
      ∃ g : ScalarStepGeometry (B x) (L x) (B y) (L y) (n x) floor,
        |g.secant-s x| ≤ ρ)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (seed : QRH.Record1252270103Source.GlobalSource (B a) (L a) (1/10)) :
    QRH.Record1252270103Source.GlobalSource (B b) (L b) (1/10) := by
  letI : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  obtain ⟨ε,ρ,hε,hρ,hcross⟩ := compact_family_secant_tolerance
    (fun x : Icc a b => B x) (fun x : Icc a b => L x)
    (fun x : Icc a b => s x) (fun x : Icc a b => n x) (fun x : Icc a b => r x)
    hB.domRestrict hL.domRestrict hs.domRestrict hn.domRestrict hr.domRestrict
    (fun x => hcert x x.property)
  obtain ⟨δ,hδ,hstep⟩ := hscalar ρ hρ
  apply finite_forward_reachability
    (fun x => QRH.Record1252270103Source.GlobalSource (B x) (L x) (1/10)) hab hδ seed
  intro x hx y hy hxy hsmall hp
  obtain ⟨g,hclose⟩ := hstep x hx y hy hxy hsmall
  have hp' : QRH.Record1252270103Source.GlobalSource g.p.B0 g.p.L0 g.p.c0 := by
    simpa only [g.parent_B,g.parent_L,g.parent_cap] using hp
  have hout := source_step_of_crossing g.geometry hfloor
    (by simpa only [g.parent_B] using hBmin x hx)
    (by simpa only [g.parent_L] using (hcert x hx).L_lower)
    (by rw [g.parent_cap]) (by rw [g.parent_cap]) g.linear g.cut g.small hε
    (by simpa only [g.parent_B,g.parent_L,ScalarStepGeometry.secant] using hcross ⟨x,hx⟩ g.secant hclose)
    hβ hp'
  simpa only [g.child_B,g.child_L,g.child_cap] using hout


theorem piece_reachable_backward {a b floor : ℝ} (hab : a ≤ b)
    (B L s n r : ℝ → ℝ)
    (hB : ContinuousOn B (Icc a b)) (hL : ContinuousOn L (Icc a b))
    (hs : ContinuousOn s (Icc a b)) (hn : ContinuousOn n (Icc a b))
    (hr : ContinuousOn r (Icc a b))
    (hcert : ∀ x∈Icc a b, RayCrossing (B x) (L x) (s x) (n x) (r x))
    (hBmin : ∀ x∈Icc a b, (9/10:ℝ) ≤ B x)
    (hfloor : (50001/100000:ℝ) ≤ floor)
    (hscalar : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧
      ∀ x∈Icc a b, ∀ y∈Icc a b, x < y → y-x ≤ δ →
      ∃ g : ScalarStepGeometry (B y) (L y) (B x) (L x) (n y) floor,
        |g.secant-s y| ≤ ρ)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (seed : QRH.Record1252270103Source.GlobalSource (B b) (L b) (1/10)) :
    QRH.Record1252270103Source.GlobalSource (B a) (L a) (1/10) := by
  letI : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  obtain ⟨ε,ρ,hε,hρ,hcross⟩ := compact_family_secant_tolerance
    (fun x : Icc a b => B x) (fun x : Icc a b => L x)
    (fun x : Icc a b => s x) (fun x : Icc a b => n x) (fun x : Icc a b => r x)
    hB.domRestrict hL.domRestrict hs.domRestrict hn.domRestrict hr.domRestrict
    (fun x => hcert x x.property)
  obtain ⟨δ,hδ,hstep⟩ := hscalar ρ hρ
  apply finite_backward_reachability
    (fun x => QRH.Record1252270103Source.GlobalSource (B x) (L x) (1/10)) hab hδ seed
  intro x hx y hy hxy hsmall hp
  obtain ⟨g,hclose⟩ := hstep x hx y hy hxy hsmall
  have hp' : QRH.Record1252270103Source.GlobalSource g.p.B0 g.p.L0 g.p.c0 := by
    simpa only [g.parent_B,g.parent_L,g.parent_cap] using hp
  have hout := source_step_of_crossing g.geometry hfloor
    (by simpa only [g.parent_B] using hBmin y hy)
    (by simpa only [g.parent_L] using (hcert y hy).L_lower)
    (by rw [g.parent_cap]) (by rw [g.parent_cap]) g.linear g.cut g.small hε
    (by simpa only [g.parent_B,g.parent_L,ScalarStepGeometry.secant] using hcross ⟨y,hy⟩ g.secant hclose)
    hβ hp'
  simpa only [g.child_B,g.child_L,g.child_cap] using hout

end
end Qrh.JointDetector.FrontierRepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.FrontierRepeatedMarks.SourceCurve.piece_reachable

#print axioms Qrh.JointDetector.FrontierRepeatedMarks.SourceCurve.piece_reachable_backward
