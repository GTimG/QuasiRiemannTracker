/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The pure scalar choices feed the genuine common early P2 factory directly.
All finite bank metadata precedes slot counts, degrees and late tau. -/
import Candidate.C092.transport.P2StageScalarsCore
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.P2StageScalars
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths HeckeFamily
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.StrongPair
open QRH.Cycle092.SourceFurtherWitness QRH.Cycle092.LowActual
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.RegularColoredForward
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open Qrh.MarkedAnchor.Interface
local notation "O" => HeckeFamily.O

/-- Exact early scalar/source output. The packet field is the actual
factory's function, not an assumed original-row energy inequality. -/
structure ReadyStage (s : Scalars) (n y : ℝ) where
  cell : Cell
  cell_member : cell∈sourceCells
  cell_lower : (cell.lower:ℝ)≤ y
  cell_upper : y≤(cell.upper:ℝ)
  threshold_pos : 0<(cell.threshold:ℝ)
  threshold_upper : (cell.threshold:ℝ)≤(responseUpper:ℝ)
  low_paid : (cell.threshold:ℝ)*max 0 (lowBracketAt y)<(u-rho:ℚ)
  table : TerminalResponseTable y (s.loss/10) cell
  εm : ℝ
  nativeError : ℝ
  B : TableBank (n:=n) (heightLoss:=s.heightLoss) (dmin:=s.dmin) (dmax:=s.dmax)
    (price:=s.price) table s.dBank εm nativeError
  smallMesh : ℝ
  lowMesh : ℝ
  ordinaryMesh : ℝ
  smallMesh_pos : 0< smallMesh
  lowMesh_pos : 0< lowMesh
  ordinaryMesh_pos : 0< ordinaryMesh
  ordinaryBank : Finset (ℝ×ℝ)
  dec : (ℝ×ℝ)→ℝ
  bank_meta : ∀b∈ordinaryBank,(98/100:ℝ)≤ b.1 ∧ b.1≤(H:ℝ) ∧ s.m0 y≤ b.2 ∧ b.2≤51/100 ∧
    0< dec b ∧ dec b≤ s.gap ∧ 0< nearOrdinaryQuota n b.2 b.1-dec b
  bank_net : ∀d m : ℝ,(98/100:ℝ)≤ d → s.m0 y≤ m → m≤51/100 →
    ∃b∈ordinaryBank,b.1≤ min d (H:ℝ) ∧ min d (H:ℝ)-b.1< s.gap ∧ m≤ b.2 ∧ b.2-m< s.gap
  commonMesh : ℝ
  commonMesh_pos : 0< commonMesh
  common_small : commonMesh≤ smallMesh
  common_low : commonMesh≤ lowMesh
  common_ordinary : commonMesh≤ ordinaryMesh
  common_inverse : commonMesh≤ s.dmin*B.mesh
  packets : ∀(Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃buffer : ℝ,0< buffer ∧ buffer*(Fintype.card Slot:ℝ)≤ B.feeFloor/1000 ∧
      buffer*(Fintype.card Slot:ℝ)≤(rho:ℝ)/1000 ∧
    ∀(M : Ideal O) [NeZero M] (A : Arithmetic M),
      Nonempty (EarlyPackets Slot M A (cell.threshold:ℝ) 2 smallMesh lowMesh ordinaryMesh
        s.εsource buffer ordinaryBank dec B)

/-- The actual checked cell, table and common packet/source metadata are
constructed, with every scalar obligation discharged by the early chooser. -/
theorem genuine_stage_early (s : Scalars)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    {n y : ℝ} (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0≤ y) (hy1 : y≤ sourceY) (hyn : y≤ n) (hn : n≤ sourceRatio*y) :
    Nonempty (ReadyStage s n y) := by
  obtain ⟨cell,hcell,hlo,hhi,hth,hth',hlow,htables⟩:=terminal_actual_checked_cell hy0 hy1
  obtain ⟨table⟩:=htables (s.loss/10) (by have:=s.loss_pos;positivity)
  have hm:=s.m0_source_bounds hy0 hy1
  obtain ⟨εm,nativeError,B,ms,ml,mo,hms,hml,hmo,bank,dec,hbank,hnet,mesh,hmesh,
    hmeshS,hmeshL,hmeshO,hmeshI,hpackets⟩:=
    genuine_common_early_packets (Vmax:=2) hbeta table cover hy0 hy1 hyn hn hth.le hth' hlow
      s.loss_pos s.heightLoss_pos.le (by norm_num) hm.2.1 hm.2.2 s.gap_pos s.εsource_pos
      s.dmin_pos s.dmin_dmax s.dBank s.bank_source_bounds s.price_pos.le s.price_fee
  exact ⟨⟨cell,hcell,hlo,hhi,hth,hth',hlow,table,εm,nativeError,B,ms,ml,mo,hms,hml,hmo,
    bank,dec,hbank,hnet,mesh,hmesh,hmeshS,hmeshL,hmeshO,hmeshI,hpackets⟩⟩

namespace ReadyStage
variable {s : Scalars} {n y : ℝ} (r : ReadyStage s n y)

def mesh : ℝ:=s.finalMesh r.commonMesh r.ordinaryMesh
 theorem mesh_bounds :
    0< r.mesh ∧ r.mesh≤ r.commonMesh ∧ r.mesh/s.dmin≤ r.ordinaryMesh ∧ r.mesh≤ s.gap ∧
    r.mesh/s.dmin≤ r.B.mesh := by
  have hh:=s.finalMesh_bounds r.commonMesh_pos r.ordinaryMesh_pos
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,s.finalMesh_inverse r.common_inverse⟩
 theorem mesh_all_sources : r.mesh≤ r.smallMesh ∧ r.mesh≤ r.lowMesh ∧ r.mesh≤ r.ordinaryMesh := by
  have hm:=r.mesh_bounds.2.1
  exact ⟨hm.trans r.common_small,hm.trans r.common_low,hm.trans r.common_ordinary⟩
 theorem actual_threshold_gap : (1/50:ℝ)+s.price<(r.cell.threshold:ℝ):=
  s.threshold_gap r.cell r.cell_member
end ReadyStage

end
end QRH.Cycle092.P2StageScalars
#print axioms QRH.Cycle092.P2StageScalars.genuine_stage_early
#print axioms QRH.Cycle092.P2StageScalars.ReadyStage.mesh_bounds
