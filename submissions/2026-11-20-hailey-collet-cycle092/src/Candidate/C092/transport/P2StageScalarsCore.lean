/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early scalar errors and the true finite outer conductor bank for regular P2.
These choices precede source degrees, tau, rows and profiles. -/
import Candidate.C092.transport.P2CommonSourceMetadataEarly
import Candidate.C092.transport.WitnessConductorBank
set_option autoImplicit false
namespace QRH.Cycle092.P2StageScalars
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open QRH.Cycle092.MediumReplace.Source

structure Scalars where
  loss : ℝ
  heightLoss : ℝ
  dyadLoss : ℝ
  reserve : ℝ
  conductor : ℝ
  εsource : ℝ
  gap : ℝ
  price : ℝ
  dmin : ℝ
  dmax : ℝ
  loss_pos : 0< loss
  heightLoss_pos : 0< heightLoss
  dyadLoss_pos : 0< dyadLoss
  reserve_pos : 0< reserve
  loss_small : loss≤(rho:ℝ)/64
  heightLoss_small : heightLoss≤(rho:ℝ)/64
  dyadLoss_small : dyadLoss≤(rho:ℝ)/64
  reserve_small : reserve≤(rho:ℝ)/64
  loss_height : loss+heightLoss≤(rho:ℝ)/8
  dyad_budget : dyadLoss<(rho:ℝ)/8
  conductor_pos : 0< conductor
  conductor_loss : conductor≤ loss/10
  conductor_fee : 3*conductor≤(rho:ℝ)/128
  dmin_eq : dmin=98/100
  dmax_eq : dmax=2+3*conductor
  εsource_pos : 0< εsource
  source_fee : dmax*εsource≤(rho:ℝ)/128
  gap_pos : 0< gap
  gap_small : gap≤1
  cap_fee : (responseUpper:ℝ)*(dmax*(2*gap)+dmax*gap+gap)≤(rho:ℝ)/128
  price_pos : 0< price
  price_fee : price*dmax≤ loss/4
  threshold_gap : ∀cell∈sourceCells,(1/50:ℝ)+price<(cell.threshold:ℝ)
  dBank : Finset ℝ
  bank_bounds : ∀d∈dBank,dmin+2*conductor≤ d ∧ d≤ dmax
  bank_cover : ∀V : ℝ,98/100≤ V → V≤2 →
    ∃d∈dBank,V+2*conductor≤ d ∧ d≤ V+3*conductor

/-- The scalar choices are uniform over every literal source cell. The
finite bank is constructed by the native conductor_bank theorem. -/
theorem choose_stage_scalars : Nonempty Scalars := by
  let loss : ℝ:=(rho:ℝ)/1024
  let conductor : ℝ:=loss/100
  let dmax : ℝ:=2+3*conductor
  let εsource : ℝ:=(rho:ℝ)/(256*dmax)
  let gap : ℝ:=(rho:ℝ)/(1024*((responseUpper:ℝ)+1)*(dmax+1))
  let price : ℝ:=loss/(8*dmax)
  have hc : 0< conductor:=by norm_num [conductor,loss,rho]
  obtain ⟨bank,hbank,hcover⟩:=conductor_bank (98/100) 2 conductor (by norm_num) hc
  refine ⟨{
    loss:=loss,heightLoss:=loss,dyadLoss:=loss,reserve:=loss,conductor:=conductor,
    εsource:=εsource,gap:=gap,price:=price,dmin:=98/100,dmax:=dmax,
    loss_pos:=?_,heightLoss_pos:=?_,dyadLoss_pos:=?_,reserve_pos:=?_,
    loss_small:=?_,heightLoss_small:=?_,dyadLoss_small:=?_,reserve_small:=?_,
    loss_height:=?_,dyad_budget:=?_,conductor_pos:=hc,conductor_loss:=?_,conductor_fee:=?_,
    dmin_eq:=rfl,dmax_eq:=rfl,εsource_pos:=?_,source_fee:=?_,gap_pos:=?_,gap_small:=?_,cap_fee:=?_,
    price_pos:=?_,price_fee:=?_,threshold_gap:=?_,dBank:=bank,bank_bounds:=hbank,bank_cover:=hcover }⟩
  all_goals try norm_num [loss,conductor,dmax,εsource,gap,price,rho,responseUpper]
  intro cell hcell
  have ht:=(Rat.cast_le (K:=ℝ)).mpr (sourceCells_threshold_lower cell hcell)
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at ht
  apply lt_of_lt_of_le ?_ ht
  norm_num [price,loss,dmax,conductor,rho]

namespace Scalars
variable (s : Scalars)

theorem dmin_pos : 0< s.dmin := by rw [s.dmin_eq];norm_num
 theorem dmin_dmax : s.dmin≤ s.dmax := by rw [s.dmin_eq,s.dmax_eq];linarith only [s.conductor_pos]
 theorem dmax_pos : 0< s.dmax := s.dmin_pos.trans_le s.dmin_dmax
 theorem reserve_rho : s.reserve≤(rho:ℝ) := s.reserve_small.trans (by norm_num [rho])
 theorem bank_source_bounds : ∀d∈s.dBank,(98/100:ℝ)≤ d ∧ s.dmin≤ d ∧ d≤ s.dmax := by
  intro d hd
  have hh:=s.bank_bounds d hd
  rw [s.dmin_eq] at hh
  exact ⟨by linarith only [hh.1,s.conductor_pos],by rw [s.dmin_eq];linarith only [hh.1,s.conductor_pos],hh.2⟩

def Mcap (db : s.dBank) : ℝ:=db.val-s.conductor
 theorem Mcap_supply (db : s.dBank) : s.Mcap db+s.conductor≤ db.val := by unfold Mcap;linarith
 theorem selected_state_width {V : ℝ} (hV : 98/100≤ V) (hV' : V≤2) :
    ∃db : s.dBank,V+2*s.conductor≤ db.val ∧ db.val≤ V+3*s.conductor ∧
      V+s.conductor≤ s.Mcap db := by
  obtain ⟨d,hd,hdV,hVd⟩:=s.bank_cover V hV hV'
  exact ⟨⟨d,hd⟩,hdV,hVd,by dsimp [Mcap];linarith only [hdV]⟩

def m0 (_s : Scalars) (y : ℝ) : ℝ:=y/(H:ℝ)
 theorem m0_source_bounds {y : ℝ} (hy0 : sourceY0≤ y) (hy1 : y≤ sourceY) :
    0< s.m0 y ∧ y/(H:ℝ)≤ s.m0 y ∧ s.m0 y≤51/100 := by
  have hH : (0:ℝ)<(H:ℝ):=by norm_num [H,u]
  have hy : 0< y:=(by norm_num [sourceY0] : (0:ℝ)< sourceY0).trans_le hy0
  refine ⟨div_pos hy hH,le_refl _,?_⟩
  apply (div_le_iff₀ hH).mpr
  have hmax : sourceY≤(51/100:ℝ)*(H:ℝ):=by norm_num [sourceY,H,u]
  exact hy1.trans hmax

/-- Shared late mesh only shrinks the authentic packet/source meshes. -/
def finalMesh (common ordinary : ℝ) : ℝ:=min common (min (s.dmin*ordinary) s.gap)
 theorem finalMesh_bounds {common ordinary : ℝ} (hc : 0< common) (ho : 0< ordinary) :
    0< s.finalMesh common ordinary ∧ s.finalMesh common ordinary≤ common ∧
    s.finalMesh common ordinary/s.dmin≤ ordinary ∧ s.finalMesh common ordinary≤ s.gap := by
  have hm : s.finalMesh common ordinary≤ s.dmin*ordinary:=(min_le_right _ _).trans (min_le_left _ _)
  exact ⟨lt_min hc (lt_min (mul_pos s.dmin_pos ho) s.gap_pos),min_le_left _ _,
    (div_le_iff₀ s.dmin_pos).mpr (by linarith only [hm]),(min_le_right _ _).trans (min_le_right _ _)⟩
 theorem finalMesh_inverse {common ordinary inverse : ℝ} (hc : common≤ s.dmin*inverse) :
    s.finalMesh common ordinary/s.dmin≤ inverse :=
  (div_le_iff₀ s.dmin_pos).mpr (by have h : s.finalMesh common ordinary≤ common:=min_le_left _ _;linarith only [h,hc])

end Scalars
end
end QRH.Cycle092.P2StageScalars
#print axioms QRH.Cycle092.P2StageScalars.choose_stage_scalars
#print axioms QRH.Cycle092.P2StageScalars.Scalars.selected_state_width
#print axioms QRH.Cycle092.P2StageScalars.Scalars.finalMesh_bounds
