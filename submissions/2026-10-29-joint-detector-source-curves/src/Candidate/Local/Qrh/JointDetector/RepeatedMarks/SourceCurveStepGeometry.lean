/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveReachability
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveSelector
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveOpenGeometry

namespace Qrh.JointDetector.RepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
open CurvedSourceStep SourceCurveSelector

/-- Build the literal source-step geometry from strict open endpoint gates.
The LOW cut and positive per-width residual are the exact finite identities. -/
def scalarStepGeometry_of_gates {B0 L0 B1 L1 n floor : ℝ}
    (hB0 : 0 < B0) (hBmax : B0 < 1) (hL0 : 0 < L0)
    (hΔ : 0 < L0-L1) (hC : 0 ≤ 6*B0-L0) (hn : 0 < n)
    (hgap : 0 < L0-n*(6*B0-L0)) (hfloor : 0 < floor)
    (hfn : floor ≤ n) (hnhi : n ≤ 3/4)
    (hg : ∀ i, 0 < SourceCurveOpenGeometry.gate B1 L1 ((B0-B1)/(L0-L1))
      (amplitude L0 (6*B0-L0) n (L0-L1)) (1/10) i)
    (hsmall : 5*amplitude L0 (6*B0-L0) n (L0-L1) ≤ n*(L1-1)) :
    ScalarStepGeometry B0 L0 B1 L1 n floor := by
  let A := amplitude L0 (6*B0-L0) n (L0-L1)
  let phi := lowFactor L0 (6*B0-L0) n
  let p : Params := ⟨B0,L0,1/10,B1,L1,1/10,A,0⟩
  have hA : 0 < A := amplitude_pos hn hΔ hgap
  have hphi := lowFactor_mem hL0 hC hn hgap
  have he : 0 < L0-L1+(6*B0-L0)*A := by positivity
  have hcut : matchedCut p phi 0=n := by
    simpa [matchedCut,cutNumerator,cutIntercept,p,A,phi] using
      matched_cut hL0 hC hn hΔ hgap
  have hs : crossing p=(B0-B1)/(L0-L1) := by rfl
  have hg' : ∀ i, 0 < SourceCurveOpenGeometry.gate p.B p.L (crossing p) p.A p.c i := by
    change ∀ i, 0 < SourceCurveOpenGeometry.gate B1 L1 (crossing p) A (1/10) i
    rw [hs]
    exact hg
  have hB : B1 ≤ B0 := by
    have hspos : 0 < (B0-B1)/(L0-L1) := by simpa [SourceCurveOpenGeometry.gate] using hg 10
    have hnum : 0 < B0-B1 := (div_pos_iff.mp hspos).elim (fun h => h.1) (fun h => by linarith [h.2])
    linarith
  have hL : 1 < L1 := by
    have hh := hg 12
    norm_num [SourceCurveOpenGeometry.gate] at hh
    linarith
  have hwidth : 0 < p.c-crossing p := by
    simpa [SourceCurveOpenGeometry.gate] using hg' 11
  have hAlt : A < 1 := by
    have hh := hg' 9
    norm_num [SourceCurveOpenGeometry.gate,p] at hh
    linarith
  have g : GeometryCertificate p phi floor := by
    refine ⟨⟨hB,hBmax,by simpa [p] using hΔ,by simpa [p] using hL,
      by norm_num [p],by norm_num [p]⟩,hB0,hA,hAlt,by norm_num [p],
      hphi.1,hphi.2.le,hfloor,hwidth,?_,?_,?_,?_,?_⟩
    · simpa [cutIntercept,p] using he
    · have hcutV : matchedCut p phi (p.c-crossing p)=n := by simpa [matchedCut,p] using hcut
      rw [hcutV]
      exact hfn
    · simpa only [hcut] using hnhi
    · rw [hcut]
      dsimp [p]
      linarith
    · exact SourceCurveOpenGeometry.geometrySigns rfl rfl (by norm_num [p]) hA hg'
  exact ⟨p,phi,g,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hcut,hsmall⟩

end
end Qrh.JointDetector.RepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.scalarStepGeometry_of_gates
