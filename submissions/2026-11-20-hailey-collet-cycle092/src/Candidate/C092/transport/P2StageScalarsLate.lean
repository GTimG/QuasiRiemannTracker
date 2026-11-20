/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early scalars and conductor caps feed the genuine late common metadata.
The actual packet degree precedes every selected positive tau. -/
import Candidate.C092.transport.P2StageScalarsEarly
import Candidate.C092.transport.P2CommonSourceMetadataFinal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.P2StageScalars
noncomputable section
open scoped Classical ContDiff
open OAI OAI.SevenEighths HeckeFamily
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.StrongPair
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.RegularColoredForward
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open Qrh.MarkedAnchor.Interface
local notation "O" => HeckeFamily.O

namespace Scalars
variable (s : Scalars)
 theorem total_early_loss : s.loss+s.heightLoss+s.dyadLoss+s.reserve<(rho:ℝ)/8 := by
  have hr : (0:ℝ)<(rho:ℝ):=by norm_num [rho]
  linarith only [s.loss_small,s.heightLoss_small,s.dyadLoss_small,s.reserve_small,hr]

/-- The selected bank cap simultaneously pays the actual state's conductor
collar and the native source margin. The true radius V is never enlarged
inside the physical original-row sum. -/
theorem selected_cap_geometry {V : ℝ} (hV : 98/100≤ V) (hV' : V≤2) :
    ∃db : s.dBank,s.dmin≤ db.val ∧ db.val≤ s.dmax ∧
      V+s.conductor≤ s.Mcap db ∧ s.Mcap db+0+s.conductor≤ db.val ∧
      db.val≤ V+3*s.conductor := by
  obtain ⟨db,hdV,hVd,hw⟩:=s.selected_state_width hV hV'
  have hb:=s.bank_source_bounds db.val db.property
  exact ⟨db,hb.2.1,hb.2.2,hw,by simpa only [add_zero] using s.Mcap_supply db,hVd⟩
end Scalars

/-- Direct call of the sealed genuine late constructor, with margin and
Mcap fixed by the early conductor bank. All analytic packet functions are
returned, retaining original families/rows/marks and early source degrees. -/
theorem genuine_stage_late {s : Scalars} {n y : ℝ} (r : ReadyStage s n y)
    {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    {M : Ideal O} [NeZero M] {A : Arithmetic M} {buffer : ℝ}
    (P : EarlyPackets Slot M A (r.cell.threshold:ℝ) 2 r.smallMesh r.lowMesh r.ordinaryMesh
      s.εsource buffer r.ordinaryBank r.dec r.B)
    (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta) (hbuffer : 0< buffer) :
    ∃G : LateGeometry s.dmin s.dmax s.dBank,
      G.Mcap=s.Mcap ∧ G.Bmask=0 ∧ G.margin=s.conductor ∧ G.R=22 ∧
      G.τ≤1/4 ∧ G.τ*(P.degreeBound:ℝ)≤ s.heightLoss ∧ G.τ*(P.degreeBound:ℝ)≤ s.reserve ∧
      G.ε≤1/7500 ∧ (s.dmax+1)*G.ε≤ r.B.feeFloor/1000 ∧
      G.heightCost≤1 ∧ 12*G.ez*(22+2)+8*G.κ+2*G.heightCost≤ G.ε/2 ∧
      (s.dmax+1)*G.ε≤ s.reserve/1000 ∧
      ∃D : DetectorBank Slot M A buffer s.price s.dmin s.dmax y (s.loss/10) r.cell r.table s.dBank G,
        Nonempty (LateBundle P G (s.m0 y) s.gap V) := by
  exact genuine_common_late_metadata P (s.m0 y) s.gap V hV hbeta hbuffer s.price_pos
    r.actual_threshold_gap s.dmin_pos s.dmin_dmax
    (fun d hd=>⟨(s.bank_source_bounds d hd).2.1,(s.bank_source_bounds d hd).2.2⟩)
    s.conductor s.reserve s.Mcap s.conductor_pos s.reserve_pos s.heightLoss_pos
    s.Mcap_supply s.εsource_pos.le r.bank_meta r.bank_net

end
end QRH.Cycle092.P2StageScalars
#print axioms QRH.Cycle092.P2StageScalars.Scalars.selected_cap_geometry
#print axioms QRH.Cycle092.P2StageScalars.genuine_stage_late
