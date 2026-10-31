/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.CanonicalCount (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Original retained full-class and error-mask count transport, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.PhysicalSourceCount
import Submissions.hailey_collet_1252270103.Cycle61.Assembly.Count.SourceCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
open QRH.Record1252270103Return

namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open OAI OAI.SevenEighths QRH.Record12518109Count
open QRH.Record1252270103Return.GenericPhysical (SourceData)
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection ProbeHighRowFamily

def canonicalFamily (D : BaselineData) (F : SourceData) (Z : ℝ) (z : ℂ) : FreeRow→Fin D.N→ℂ :=
  fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val
    (fun y=>(F.w y:ℂ)) 2 (Z^(D.length j)) z

theorem physical_eq_canonical (D : BaselineData) (F : SourceData) (Z d : ℝ)
    (hZ : 0<Z) (hd : d≠0) (z : ℂ) :
    physical F.modulus ⊤ (fun u : FreeRow=>u.val) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun j=>D.length j/d) (fun _=>z) (Z^d) = canonicalFamily D F Z z := by
  funext u j
  exact source_physical_amplitude F.modulus ⊤ D.length (fun _ y=>(F.w y:ℂ)) Z d 2 z hZ hd u j
end
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
