/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
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
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.MomentMono (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Monotonicity of the genuine moment sums. Apache-2.0, adapted Gao/OpenAI/Hailey Collet. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
/- Modified by Sil (2026-11-11): monotonicity also of the improved fiber moments; over the count scheme `Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line` (native and improved windows) and its envelope `ImprovedCount.envelope`. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.MomentGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
open QRH.Record1252270103Return

namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds] [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ProbePhysical ProbeHighRowFamily HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorBatch
lemma SourceMomentBound.mono_constant {D : BaselineData}
    {F : QRH.Record1252270103Return.GenericPhysical.SourceData}
    {counts : CountParameters F.modulus ⊤ D.t} {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤Z) (h : SourceMomentBound D F counts η Z τ C height)
    (hC : C≤C') : SourceMomentBound D F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots hwidth
    hprof hupp hext hmesh hbin hfam bin j J K hne
  obtain ⟨hm,hm0,haf,himp⟩ := h rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots
    hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  have mono {κ c k : ℝ} (hm : Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κ c k C height D.t) :
      Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κ c k C' height D.t := by
    refine ⟨ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _) hm.original hC,?_⟩
    intro selected hsel hcap j k hj s hs t ht
    exact (hm.plain_marked selected hsel hcap j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))
  refine ⟨mono hm,mono hm0,?_,himp.mono_constant (Real.rpow_nonneg hZ _) hC⟩
  intro w hw hmlo hmhi selected hsel h1 h2 h3 j k hj s hs t ht
  exact (haf w hw hmlo hmhi selected hsel h1 h2 h3 j k hj s hs t ht).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))
end
