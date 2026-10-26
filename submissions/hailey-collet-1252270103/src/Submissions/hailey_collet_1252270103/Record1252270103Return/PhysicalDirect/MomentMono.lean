/- Monotonicity of the genuine moment sums. Apache-2.0, adapted Gao/OpenAI/Hailey Collet. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Schedule
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.MomentGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
open QRH.Record1252270103Return

namespace QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
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
  obtain ⟨hm,hm0,haf⟩ := h rows d a hd hd' ha ha' hrows i z hz hzh q B hsub hdata hrev hslots
    hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  have mono {κ c k : ℝ} (hm : Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κ c k C height D.t) :
      Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κ c k C' height D.t := by
    refine ⟨ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _) hm.original hC,?_⟩
    intro selected hsel hcap j k hj s hs t ht
    exact (hm.plain_marked selected hsel hcap j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))
  refine ⟨mono hm,mono hm0,?_⟩
  intro w hw hmlo hmhi selected hsel h1 h2 h3 j k hj s hs t ht
  exact (haf w hw hmlo hmhi selected hsel h1 h2 h3 j k hj s hs t ht).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.rpow_nonneg hZ _) _))
end
#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.SourceMomentBound.mono_constant
