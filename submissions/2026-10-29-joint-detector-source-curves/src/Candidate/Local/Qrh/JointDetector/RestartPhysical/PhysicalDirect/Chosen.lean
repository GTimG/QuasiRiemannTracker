/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-9.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Chosen (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Chosen physical/count data at the new geometry. Apache-2.0.
The established incumbent beta cap remains an explicit input until Bootstrap integration. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.RestartPhysical.PhysicalDirect.MomentGates
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Transport.FinalHeight
set_option autoImplicit false
open QRH.Record1252270103Return

namespace Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount
open QRH.Record1252270103Return.GenericPhysical (baselineSource)
open Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.Assembly

structure ChosenData where
  D : BaselineData
  kappa_exact : D.momentKappa=2*HeckeZeroSupremum.beta-1
  kappa_incumbent : D.momentKappa≤scheme.naturalκ
  count_budget : 159*D.ε+609*D.t≤(HeckeZeroSupremum.beta-theta)/10000
  fine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200
  sourceMesh : ℝ
  sourceMesh_pos : 0<sourceMesh
  source_fine : ∀j,D.length j≤sourceMesh/200
  P : TransportParameters D
  F : BaselineSourceData D
  counts : CountParameters (baselineSource D F).modulus ⊤ D.t

theorem fresh_count_parameters (D : BaselineData)
    (F : QRH.Record1252270103Return.GenericPhysical.SourceData) :
    Nonempty (CountParameters F.modulus ⊤ D.t) :=
  exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun y=>(F.bounded y).1) F.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2) D.t D.t_pos

theorem exists_chosen_data_with_mesh (hgap : theta<HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤scheme.naturalκ)
    (mesh : ℝ→ℝ) (hmesh : ∀t : ℝ,0<t→0<mesh t) :
    ∃A : ChosenData,A.sourceMesh=mesh A.D.t := by
  have hk : (7/10:ℝ)≤2*HeckeZeroSupremum.beta-1 := by
    have ht : (85/100:ℝ)<theta := by linarith [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN.theta_bounds.1]
    linarith
  have hkhi : 2*HeckeZeroSupremum.beta-1≤3/4 :=
    hκbeta.trans scheme.natural_hi
  obtain ⟨D,hκ,hbudget,hfine,_hcommon,hextra,⟨P⟩⟩ :=
    exists_compatible_data_with_mesh hk hkhi
      (show 0<(HeckeZeroSupremum.beta-theta)/10000 by positivity) mesh hmesh
  obtain ⟨F⟩ := QRH.Record1252270103Return.GenericPhysical.exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D (baselineSource D F)
  exact ⟨⟨D,hκ,hκ.symm ▸ hκbeta,hbudget,hfine,mesh D.t,hmesh D.t D.t_pos,hextra,P,F,counts⟩,rfl⟩
end
end Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
