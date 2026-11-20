/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
import Candidate.C092.transport.P2CommonSourceMetadataReady
import Candidate.C092.transport.P2CommonSourceMetadataInverse
import Candidate.C092.transport.P2CommonSourceMetadataTableBank
import Candidate.C092.transport.P2CommonSourceMetadataTypes
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
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataSchedule_1727d9f9b42e524f_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- One positive height exponent is chosen after the common finite degree,
with room for the true native height budget and both height-loss reserves. -/
theorem choose_common_tau (D : ℕ) (dmin heightCost heightLoss reserve : ℝ)
    (hd : 0 < dmin) (hh : 0 < heightCost) (hl : 0 < heightLoss) (hr : 0 < reserve) :
    ∃τ : ℝ,0 < τ ∧ τ ≤ 1/4 ∧ 4*τ < dmin*heightCost ∧
      τ*(D:ℝ) ≤ heightLoss ∧ τ*(D:ℝ) ≤ reserve := by
  let τ := min (1/4:ℝ) (min (dmin*heightCost/8) (min (heightLoss/(2*((D:ℝ)+1))) (reserve/(2*((D:ℝ)+1)))))
  have hden : 0 < 2*((D:ℝ)+1) := by positivity
  have hτ : 0 < τ := lt_min (by norm_num) (lt_min (by positivity) (lt_min (div_pos hl hden) (div_pos hr hden)))
  have hc : τ ≤ dmin*heightCost/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hl' : τ ≤ heightLoss/(2*((D:ℝ)+1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr' : τ ≤ reserve/(2*((D:ℝ)+1)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hls := (le_div_iff₀ hden).mp hl'
  have hrs := (le_div_iff₀ hden).mp hr'
  refine ⟨τ,hτ,min_le_left _ _,?_,?_,?_⟩
  · nlinarith only [hc,mul_pos hd hh]
  · nlinarith only [hls,hτ,(show 0 ≤ (D:ℝ) from Nat.cast_nonneg D)]
  · nlinarith only [hrs,hτ,(show 0 ≤ (D:ℝ) from Nat.cast_nonneg D)]

/-- The short-source contour, detector epsilon and height cost are fixed
from the actual common fee before any live Cslot. The same epsilon may be
used for the supported witnesses and the genuine short upper. -/
theorem choose_late_geometry {dBank : Finset ℝ}
    (D : ℕ) (dmin dmax R feeFloor heightLoss reserve margin : ℝ)
    (Mcap : dBank → ℝ) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hR : 0 ≤ R)
    (hf : 0 < feeFloor) (hl : 0 < heightLoss) (hr : 0 < reserve) (hm : 0 < margin) :
    ∃G : LateGeometry dmin dmax dBank,
      G.Mcap=Mcap ∧ G.Bmask=0 ∧ G.margin=margin ∧ G.R=R ∧
      G.τ ≤ 1/4 ∧ G.τ*(D:ℝ) ≤ heightLoss ∧ G.τ*(D:ℝ) ≤ reserve ∧
      G.ε ≤ 1/7500 ∧ (dmax+1)*G.ε ≤ feeFloor/1000 ∧
      G.heightCost ≤ 1 ∧ 12*G.ez*(22+2)+8*G.κ+2*G.heightCost ≤ G.ε/2 ∧
      (dmax+1)*G.ε ≤ reserve/1000 := by
  have hdm : 0 < dmax := hdmin.trans_le hdmax
  let ε := min (1/10000:ℝ) (min (feeFloor/(1000*(dmax+1))) (reserve/(1000*(dmax+1))))
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (div_pos hf (by positivity)) (div_pos hr (by positivity)))
  have hεtiny : ε ≤ 1/7500 := (min_le_left _ _).trans (by norm_num)
  have hεsmall : ε ≤ 1/1000 := hεtiny.trans (by norm_num)
  let κ := ε/1000
  let hc := ε/1000
  let ez := min (1/2000:ℝ) (ε/(1000*(R+2)))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκ' : κ ≤ 1 := by dsimp [κ]; linarith only [hεsmall]
  have hhc : 0 < hc := by dsimp [hc]; positivity
  have he : 0 < ez := lt_min (by norm_num) (div_pos hε (by positivity))
  have he' : ez < 1/1000 := (min_le_left _ _).trans_lt (by norm_num)
  have heshort : ez*(1000*(R+2)) ≤ ε :=
    (le_div_iff₀ (show 0 < 1000*(R+2) by positivity)).mp (min_le_right _ _)
  have hbudget : 12*ez*(R+2)+8*κ+2*hc ≤ ε := by
    dsimp only [κ,hc]
    nlinarith only [heshort,hε]
  obtain ⟨τ,hτ,hτsmall,hheight,hτloss,hτreserve⟩ := choose_common_tau D dmin hc heightLoss reserve hdmin hhc hl hr
  let G : LateGeometry dmin dmax dBank := {
    Mcap:=Mcap,Bmask:=0,margin:=margin,hmargin:=hm,R:=R,hR:=hR,
    τ:=τ,hτ:=hτ,ε:=ε,hε:=hε,ez:=ez,hez:=he,hez_small:=he',κ:=κ,hκ:=hκ,hκ_small:=hκ',
    heightCost:=hc,heightCost_nonneg:=hhc.le,height:=hheight,budget:=hbudget,hdmax:=hdmax }
  refine ⟨G,rfl,rfl,rfl,rfl,hτsmall,hτloss,hτreserve,hεtiny,?_,?_,?_,?_⟩
  ·
    have h := (le_div_iff₀ (show 0 < 1000*(dmax+1) by positivity)).mp
      ((min_le_right _ _).trans (min_le_left _ _) : ε ≤ feeFloor/(1000*(dmax+1)))
    change (dmax+1)*ε ≤ feeFloor/1000
    nlinarith only [h]
  · change ε/1000 ≤ 1
    linarith only [hεsmall]
  · change 12*ez*(22+2)+8*(ε/1000)+2*(ε/1000) ≤ ε/2
    have hez0 := le_of_lt he
    nlinarith only [heshort,hR,he,hε,mul_nonneg hez0 hR]
  · have h := (le_div_iff₀ (show 0 < 1000*(dmax+1) by positivity)).mp
      ((min_le_right _ _).trans (min_le_right _ _) : ε ≤ reserve/(1000*(dmax+1)))
    change (dmax+1)*ε ≤ reserve/1000
    nlinarith only [h]

/-- The same early buffer pays the cardinality of every true surviving
whole-slot subset, including the empty subset. -/
theorem subset_buffer_paid {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T : Finset Slot) {buffer fee : ℝ} (hb : 0 ≤ buffer)
    (h : buffer*(Fintype.card Slot:ℝ) ≤ fee) : buffer*(Fintype.card T:ℝ) ≤ fee := by
  apply (mul_le_mul_of_nonneg_left (show (Fintype.card T:ℝ) ≤ Fintype.card Slot by
    exact_mod_cast (show Fintype.card T ≤ Fintype.card Slot by simpa only [Fintype.card_coe] using Finset.card_le_univ T)) hb).trans h

/-- The actual common-fee record pays every error term requested by the
marked and unmarked native leaves, using exactly their original tolerances. -/
theorem inverse_error_paid {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
    {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
    (B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError)
    (G : LateGeometry dmin dmax dBank) (k : WindowKey table)
    {Slot : Type} [Fintype Slot] [DecidableEq Slot] (T : Finset Slot)
    {buffer d : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ dmax) (hb : 0 ≤ buffer)
    (hbuffer : buffer*(Fintype.card Slot:ℝ) ≤ B.feeFloor/1000)
    (hε : (dmax+1)*G.ε ≤ B.feeFloor/1000) :
    0 ≤ G.ε ∧ G.ε ≤ B.feeM k ∧ G.ε ≤ B.feeU k ∧
    d*G.ε+(d*(2*G.ε+εm)+d*nativeError)/2+buffer*(Fintype.card T:ℝ) ≤ B.commonFee k := by
  have hdm : 0 ≤ dmax := hd.trans hdmax
  have hεd : d*G.ε ≤ B.feeFloor/1000 :=
    (mul_le_mul_of_nonneg_right (show d ≤ dmax+1 by linarith only [hdmax]) G.hε.le).trans hε
  have hε0 : G.ε ≤ B.feeFloor/1000 := by
    have h := mul_le_mul_of_nonneg_right (show 1 ≤ dmax+1 by linarith only [hdm]) G.hε.le
    simpa only [one_mul] using h.trans hε
  have hNative : d*(εm+nativeError) ≤ B.commonFee k/100 :=
    (mul_le_mul_of_nonneg_right (show d ≤ dmax+1 by linarith only [hdmax]) (add_nonneg B.hεm.le B.hNativeError.le)).trans (B.error_paid k)
  have hbufferT := subset_buffer_paid T hb hbuffer
  have hf : 0 < B.commonFee k := (B.fees k).2.2.1
  have hfloor := B.feeFloor_le k
  refine ⟨G.hε.le,?_,?_,?_⟩
  · exact hε0.trans ((by nlinarith only [hfloor,B.feeFloor_pos,hf] : B.feeFloor/1000 ≤ B.commonFee k).trans (B.fees k).2.2.2.1)
  · exact hε0.trans ((by nlinarith only [hfloor,B.feeFloor_pos,hf] : B.feeFloor/1000 ≤ B.commonFee k).trans (B.fees k).2.2.2.2)
  · nlinarith only [hεd,hNative,hbufferT,hfloor,hf]

#print axioms choose_common_tau
#print axioms choose_late_geometry
#print axioms subset_buffer_paid
#print axioms inverse_error_paid
end
end QRH.Cycle092.P2CommonSourceMetadata
