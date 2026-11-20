/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
import Candidate.C092.transport.P2CommonSourceMetadataPackets
import Candidate.C092.transport.P2CommonSourceMetadataTable
import Candidate.C092.transport.RegularColoredTerminalLeafTable
import Candidate.C092.transport.RegularColoredTerminalLeafLowHigh
import Candidate.C092.transport.RegularColoredTerminalLeafSmallActual
import Candidate.C092.transport.RegularColoredTerminalLeafOrdinaryBank
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.P2CommonSourceMetadata
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros HeckeDetectorRowwisePolynomial
open ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentHeckeSlots HeckePrimeAnnular
open QRH.Cycle092.WholeSlot
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.PairMarkAnchor QRH.Cycle092.TinyCore QRH.Cycle092.MediumReplace.Source
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.StrongPair QRH.Cycle092.LowActual QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.RegularColoredForward QRH.Cycle092.SourceInverseP6 QRH.Cycle092.MediumInversePrice
open QRH.Cycle092.OrdinaryColumn Qrh.MarkedAnchor.Interface
local notation "O" =>  HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataTableBank_55f58144bc8c852e_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

abbrev WindowKey {y step : ℝ} {cell : Cell} (table : TerminalResponseTable y step cell) :=
  Fin table.Je × Fin table.Jν

/-- Genuine analytic source functions and the scalar witnesses that chose
them. In particular, the fee floor precedes both error tolerances. -/
structure TableBank {n y loss heightLoss dmin dmax price : ℝ} {cell : Cell}
    (table : TerminalResponseTable y (loss/10) cell) (dBank : Finset ℝ) (εm nativeError : ℝ) where
  hεm : 0 < εm
  hNativeError : 0 < nativeError
  feeM : WindowKey table → ℝ
  feeU : WindowKey table → ℝ
  commonFee : WindowKey table → ℝ
  fees : ∀k,0 < feeM k ∧ 0 < feeU k ∧ 0 < commonFee k ∧ commonFee k ≤ feeM k ∧ commonFee k ≤ feeU k
  feeFloor : ℝ
  feeFloor_pos : 0 < feeFloor
  feeFloor_le : ∀k,feeFloor ≤ commonFee k
  error_paid : ∀k,(dmax+1)*(εm+nativeError) ≤ commonFee k/100
  ζ : ℝ
  ζ_pos : 0 < ζ
  ζ_fee : ∀k,ζ ≤ commonFee k/2
  rhoδ : ℝ
  rhoδ_pos : 0 < rhoδ
  rhoδ_small : rhoδ ≤ 1/1000
  rhoδ_ζ : 3*rhoδ ≤ ζ
  J : ℕ
  rhoBank : Fin J → Contract.AnchorRect
  genuine : ∀j,Contract.UniformInverseRectSource Contract.canonicalFamily (rhoBank j)
  cover : ∀r : ℝ,367/500 ≤ r  →  r ≤ 1  → 
    inverseQuota r ≤ ζ ∨ (0 ≤ inverseQuota r-ζ  →  ∃j,(rhoBank j).Admissible r (inverseQuota r-ζ) 1)
  quota : WindowKey table → dBank → ℝ
  native : ∀k d,0 ≤ terminalNativeCap n d.val ∧ terminalNativeCap n d.val < 1/2 ∧
    0 < quota k d ∧ quota k d < 3/20 ∧ quota k d < (1-2*terminalNativeCap n d.val)/2 ∧
    2*NativeFourthEffective.credit n d.val-d.val*quota k d ≤ commonFee k/4 ∧
    ∀{U X : ℝ},0 < U  →  length U X ≤ n  →  length (U^d.val) X ≤ terminalNativeCap n d.val
  im : WindowKey table → dBank → Fin J → ℝ
  nm : WindowKey table → dBank → Fin J → ℝ
  nu : WindowKey table → dBank → ℝ
  marked_mesh_pos : ∀k d j,0 < im k d j ∧ 0 < nm k d j
  unmarked_mesh_pos : ∀k d,0 < nu k d
  mesh : ℝ
  mesh_pos : 0 < mesh
  marked_mesh : ∀k d j,mesh ≤ im k d j ∧ mesh ≤ nm k d j
  unmarked_mesh : ∀k d,mesh ≤ nu k d
  marked : ∀k d j,TerminalActualClassMarkedPhysical n y (table.egrid k.1)
    (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss (table.cutoff k) (loss/10) (loss/10) (feeM k)
    (rhoBank j) εm nativeError (terminalNativeCap n d.val) (quota k d) dmin dmax price (im k d j) (nm k d j)
  unmarked : ∀k d,TerminalActualClassUnmarkedPhysical n y (table.egrid k.1)
    (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss (table.cutoff k) (loss/10) (loss/10) (feeU k)
    εm nativeError (terminalNativeCap n d.val) (quota k d) dmin dmax price (nu k d)

/-- The checked table first chooses actual scalar fees and genuine rho.
Only then are both analytic error tolerances chosen from their common floor.
All native quotas and all source meshes still precede Slot and arithmetic. -/
theorem genuine_table_bank (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y loss heightLoss dmin dmax price : ℝ} {cell : Cell}
    (table : TerminalResponseTable y (loss/10) cell)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (ht : 0 ≤ (cell.threshold:ℝ)) (hloss : 0 < loss) (hheightLoss : 0 ≤ heightLoss)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (dBank : Finset ℝ) (hdb : ∀d∈dBank,(98/100:ℝ) ≤ d ∧ dmin ≤ d ∧ d ≤ dmax)
    (hprice0 : 0 ≤ price) (hpriceBudget : price*dmax ≤ loss/4) :
    ∃εm nativeError : ℝ,Nonempty (TableBank (n:=n) (heightLoss:=heightLoss)
      (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError) := by
  obtain ⟨feeM,feeU,fc,hfee,ζ,hζ,hζf,δ,hδ,hδsmall,hδζ,J,bank,hsource,hcover,hlate⟩ :=
    common_early_actual_table_bank hβ table hy0 hy1 hyn hn ht hloss heightLoss hheightLoss
  obtain ⟨floor,hfloor,hfloorle⟩ := terminal_positive_mesh_floor fc (fun k=>(hfee k).2.2.1)
  have hdm : 0 < dmax := hdmin.trans_le hdmax
  let ε := min (1/1000:ℝ) (floor/(1000*(dmax+1)))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hfloor (by positivity))
  obtain ⟨quota,hquota,im,nm,nu,hpos,hnu,mesh,hmesh,hfloorM,hfloorU,hM,hU⟩ :=
    hlate ε ε hε hε dmin dmax hdmin hdmax dBank hdb price hprice0 hpriceBudget
  have herr : ∀k,(dmax+1)*(ε+ε) ≤ fc k/100 := by
    intro k
    have hεcap : ε ≤ floor/(1000*(dmax+1)) := min_le_right _ _
    have hscaled := (le_div_iff₀ (show 0 < 1000*(dmax+1) by positivity)).mp hεcap
    nlinarith only [hscaled,hfloorle k,hfloor]
  refine ⟨ε,ε,⟨?_⟩⟩
  exact {
    hεm:=hε,hNativeError:=hε,feeM:=feeM,feeU:=feeU,commonFee:=fc,fees:=hfee,
    feeFloor:=floor,feeFloor_pos:=hfloor,feeFloor_le:=hfloorle,error_paid:=herr,
    ζ:=ζ,ζ_pos:=hζ,ζ_fee:=hζf,rhoδ:=δ,rhoδ_pos:=hδ,rhoδ_small:=hδsmall,rhoδ_ζ:=hδζ,
    J:=J,rhoBank:=bank,genuine:=hsource,cover:=hcover,quota:=quota,native:=hquota,
    im:=im,nm:=nm,nu:=nu,marked_mesh_pos:=hpos,unmarked_mesh_pos:=hnu,
    mesh:=mesh,mesh_pos:=hmesh,marked_mesh:=hfloorM,unmarked_mesh:=hfloorU,marked:=hM,unmarked:=hU }

#print axioms genuine_table_bank
end
end QRH.Cycle092.P2CommonSourceMetadata
