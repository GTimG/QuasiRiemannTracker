/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact mixed upper contract from the genuine earlier P1 source alone. -/
import Candidate.C092.transport.MixedUpperFinalGuarded
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank
open QRH.Cycle090
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
local notation "contact" => Qrh.TwoSlot.AnchorContinuum.Contact.theta

theorem earlier_P1_mixed_upper_estimate
    (h : ℝ) (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hP1 : RawTicket.EarlierP1) : Final.MixedUpperEstimate contact := by
  classical
  cases hgeometry
  letI := ActualGeometry.parameters h hh hh'
  unfold Final.MixedUpperEstimate
  intro hθβ affineError loss haff hloss
  have hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta:=by
    change QRH.Cycle090.theta<HeckeZeroSupremum.beta at hθβ
    have hθ : (51/100:ℝ) ≤ QRH.Cycle090.theta:=by norm_num [QRH.Cycle090.theta]
    exact hθ.trans hθβ.le
  by_cases hκ : 2*HeckeZeroSupremum.beta-1 ≤ (3/4:ℝ)
  · obtain ⟨mc,hmc,mp,hmp,hsource⟩:=earlier_P1_guarded_mixed_upper h hh hh' rfl hP1 hβ hκ affineError loss haff hloss
    refine ⟨mc,hmc,mp,hmp,?_⟩
    intro D F hf hs hp hc hkβ η
    by_cases hg : D.ε ≤ 1/10000000 ∧ D.t ≤ 1/10000000 ∧ D.ε ≤ 3*witnessCollar
    · exact hsource D F hf hs hp hc hkβ hg.1 hg.2.1 hg.2.2 η
    · refine ⟨0,1,by norm_num,?_⟩
      intro P padding τ hτ hheight hpad n
      filter_upwards [eventually_gt_atTop (1:ℝ)] with Z hZ
      refine ⟨hZ,?_⟩
      intro idx grid hsel k hk i hi j hn
      dsimp only
      intro hd hdh x z hx hz him bins hbins hreserve
      exact (hg (native_early_guards D P affineError loss haff hloss hreserve)).elim
  · refine ⟨fun _=>1,(fun _ _=>by norm_num),1,by norm_num,?_⟩
    intro D F hf hs hp hc hkβ
    exact (hκ (hkβ.trans D.momentKappa_hi)).elim

#print axioms earlier_P1_mixed_upper_estimate
end
end QRH.Cycle092.MixedUpperFinal
