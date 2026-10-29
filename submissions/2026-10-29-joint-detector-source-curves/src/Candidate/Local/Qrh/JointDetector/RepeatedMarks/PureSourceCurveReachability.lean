/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveReachability
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.PureSourceCurveMargins
namespace Qrh.JointDetector.RepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
open Set CurvedSourceStep

theorem pure_piece_reachable_backward {a b floor : ℝ} (hab : a ≤ b)
    (B L s n : ℝ → ℝ)
    (hB : ContinuousOn B (Icc a b)) (hL : ContinuousOn L (Icc a b))
    (hs : ContinuousOn s (Icc a b)) (hn : ContinuousOn n (Icc a b))
    (hcert : ∀ x∈Icc a b, PureCrossing (B x) (L x) (s x) (n x))
    (hBmin : ∀ x∈Icc a b, (9/10:ℝ) ≤ B x)
    (hfloor : (2/5:ℝ) ≤ floor)
    (hscalar : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧
      ∀ x∈Icc a b, ∀ y∈Icc a b, x < y → y-x ≤ δ →
      ∃ g : ScalarStepGeometry (B y) (L y) (B x) (L x) (n y) floor,
        |g.secant-s y| ≤ ρ)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (seed : QRH.Record1252270103Source.GlobalSource (B b) (L b) (1/10)) :
    QRH.Record1252270103Source.GlobalSource (B a) (L a) (1/10) := by
  letI : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  obtain ⟨ε,ρ,hε,hρ,hcross⟩ := compact_pure_family_secant_tolerance
    (fun x : Icc a b => B x) (fun x : Icc a b => L x)
    (fun x : Icc a b => s x) (fun x : Icc a b => n x)
    hB.domRestrict hL.domRestrict hs.domRestrict hn.domRestrict
    (fun x => hcert x x.property)
  obtain ⟨δ,hδ,hstep⟩ := hscalar ρ hρ
  apply finite_backward_reachability
    (fun x => QRH.Record1252270103Source.GlobalSource (B x) (L x) (1/10)) hab hδ seed
  intro x hx y hy hxy hsmall hp
  obtain ⟨g,hclose⟩ := hstep x hx y hy hxy hsmall
  have hp' : QRH.Record1252270103Source.GlobalSource g.p.B0 g.p.L0 g.p.c0 := by
    simpa only [g.parent_B,g.parent_L,g.parent_cap] using hp
  have hout := source_step_of_pure_crossing g.geometry hfloor
    (by simpa only [g.parent_B] using hBmin y hy)
    (by simpa only [g.parent_L] using (hcert y hy).L_lower)
    (by rw [g.parent_cap]) (by rw [g.parent_cap]) g.linear g.cut g.small hε
    (by simpa only [g.parent_B,g.parent_L,ScalarStepGeometry.secant] using hcross ⟨y,hy⟩ g.secant hclose)
    hβ hp'
  simpa only [g.child_B,g.child_L,g.child_cap] using hout

end
end Qrh.JointDetector.RepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.pure_piece_reachable_backward
