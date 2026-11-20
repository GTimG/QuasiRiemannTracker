/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Apply the genuine fixed native packet to its literal restored first hit.
The empty carrier is exact zero; the nonempty cutoff uses the true prefix volume. -/
import Candidate.C092.transport.ActualStageFrameBudgetNativeHit
import Candidate.C092.transport.ActualStageFrameBudgetPointwise
import Candidate.C092.transport.ActualStageFrameBudgetWindow
import Candidate.C092.transport.ActualStageFrameBudgetFirstBound
import Candidate.C092.transport.ActualFrameFeeGates
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily CenteredMomentSecondLocalization
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock MixedOriginalNormCap MixedCompletedRows
open CenteredMomentFirstPhysicalSource CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentNaturalFixedRaySource CenteredMomentSecondWindowBudget MixedCompletedRows
open CenteredMomentFirstPhysicalSource CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentNaturalFixedRaySource CenteredMomentSecondWindowBudget
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup QRH.Cycle092.FixedCubeGauss
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.ColoredGaussFrameProvider
open QRH.Cycle092.TwistedRawBallRootProducer QRH.Cycle092.PairedRetainedBudget
open QRH.Cycle092.ActualRootFrameHit
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) dispatchSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSourceLiveColumn
open CenteredMomentFirstPhysicalDyadicAssembly
open MixedFirstRetainedFixed MixedFirstExceptionalWindow
open QRH.Cycle092.RegularPhysicalClassBudget
open Filter QRH.Cycle092.FixedFramePacking QRH.Cycle092.NativeStrip QRH.Cycle090 QRH.SourceCertificate
open CenteredMomentFirstSectorTransform CenteredMomentFirstDiscardedEnergy CenteredMomentFirstExceptionalPrefactor
open QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry
/-- The actual native physical bank supplies every retained first-label
price. All primitive numeric/source gates are derived on its actual
restored children; no physical energy or retained budget is an input. -/
theorem retained_frame_prices_of_bank (N:ℕ)(n y l δ mesh ξsecond:ℝ)
    (hδ:0 < δ)(hρ:δ ≤ (QRH.SourceCertificate.rho:ℝ)/10000)(hm0:0 < mesh)(hm:mesh ≤ δ)
    (hξ:ξsecond ≤ 1)(hsep:ξsecond/2 < mesh)
    (hy0:sourceY0 ≤ y)(hy1:y ≤ sourceY)(hn:n ≤ sourceRatio*y)(hl:l ≤ sourceWidth n y) :
    RetainedBankHorizon N n y l δ mesh ξsecond hδ := by
  unfold RetainedBankHorizon
  filter_upwards [eventual_actual_scales N δ ξsecond mesh hδ hsep] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι inst M instM Hr hHr r hZr hW hL hN X₁ X₂ t₁ t₂ d hd₁ hd₂ g hx₁ hx₂ hws hshort
    s cover caps height hh hwm hfreq hholes hTime Q hQ hQ0 hQt hQ72 hQbase ω₁ ω₂ Kslot hMarks
    bank hBankFee hAt Kroot hKroot
  subst Z
  have hP:∀i,s.P i=r.Z^(r.w i):=fun i=>rfl
  have hd:s.d=(1,1):=rfl
  have hc4:=divided_bank_caps M Hr hHr r X₁ X₂ (r.Z^(115/1000:ℝ)) (X₁*X₂/r.Z^(115/1000:ℝ)) t₁ t₂ d g
  have hc0:=divided_canonical M Hr hHr r X₁ X₂ (r.Z^(115/1000:ℝ)) (X₁*X₂/r.Z^(115/1000:ℝ)) t₁ t₂ d g
  rw [hL] at hc0
  have hδsmall:δ ≤ 1/1000:=by norm_num [QRH.SourceCertificate.rho] at hρ;linarith only [hρ]
  have hn34:n ≤ 3/4:=by norm_num [sourceRatio,sourceY] at hn hy1;linarith only [hn,hy1]
  have hy34:y ≤ 3/4:=by norm_num [sourceY] at hy1;linarith only [hy1]
  have hsc:=hz.2.2.2.2 ι s hN cover r.w r.hw hP n y hy0 hy1 hn caps.originalBox
  have hactive:∀I∈RootColoredSeed.active s (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂),
      (I.absNorm:ℝ) ≤ r.Z^(8:ℝ):=by
    intro I hI
    have hI':TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂) 1 I≠0:=by
      change I∈activeSource _ _ at hI
      rw [mem_activeSource] at hI
      exact hI.2
    exact (TwistedRawSource.sourceColumn_cap s (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂) 1 I hI').2.trans caps.norm
  intro p E hE b hdy
  have hj:(b 1).val∈retainedIndices (firstRadius s p.val.1 p.val.2 E Kroot r.Z δ):=(b 1).property
  have hc:=(commonLabels_supported _ p)
  have hlabels:=QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry.lab_cols_le
    (RootColoredSeed.active s (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂)) (r.Z^(8:ℝ)) hactive ⟨p,E⟩
  have hK40:=actual_first_scale_bound s ω₁ ω₂ p E Kroot r.Z δ (b 1).val hz.2.1 hKroot hj
    (by linarith only [hδsmall]) hsc.1.le
  refine ⟨hK40,?_⟩
  intro χ ζ v
  let F:=fixedPair ColoredRootRestore.bareBase p.val.1 p.val.2 hc.1 E χ (ζ⁻¹)
  have side (G:Id)(P:SidePack ColoredRootRestore.bareBase)
      (hside:P.base=F.left ∨ P.base=F.right)(hCs:P.Cs=G)
      (hGcap:(G.absNorm:ℝ) ≤ r.Z^(8:ℝ))
      (horient:(G=p.val.1 ∧ P.V=QRH.SilDensitySplit.CubeFree.Packet.firstPacked p.val.1 p.val.2 hc.1 E) ∨
        (G=p.val.2 ∧ P.V=QRH.SilDensitySplit.CubeFree.Packet.firstPackedRight p.val.1 p.val.2 hc.1 E))
      (Js:∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
      (hJs:FirstSelection s G r.w mesh (sourceWidth n y) Js) :
      SelectedFramePrices s cover r.w G P.base ω₁ ω₂ 1 Q fixedBadMask Js v
        (childScale r.Z δ (b 1)) r.Z ξsecond
        ((r.p.control bank.controls)^2*(1+|t₁|+|t₂|+height)^bank.degree)
        bank.totalFee (10*δ) ((Ideal.span {P.V}).absNorm:ℝ) bank.J := by
    intro part B hwt ζ'
    let J:=Js B
    let W:=RawSides.selectionScaleQ s (by norm_num) cover G B J
    let K:=childScale r.Z δ (b 1)
    let K₂:=16*K*W^4
    let rest:=restOf s (by norm_num) cover G B J
    let X:=RawSides.residualCapQ rest
    let θ:=frameData N (Fintype.card (Rest J)) M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase
    let rs:GSrc θ mesh r.Z:=bankFrame N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes hc4.1 hc4.2.1 hc4.2.2.1 hc4.2.2.2 G B J P.V P.hV (Real.logb r.Z K₂)
    have hs:=hJs B
    obtain ⟨hWone,hWcap,hX,hXcap,hcut⟩:=hsc.2.2 G B J hs.2.1
    have hfields:=bank_fields N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes hc4.1 hc4.2.1 hc4.2.2.1 hc4.2.2.2 G B J P.V P.hV (Real.logb r.Z K₂)
    have hvol:=bank_volume_rest N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes hc4.1 hc4.2.1 hc4.2.2.1 hc4.2.2.2 G B J P.V P.hV (Real.logb r.Z K₂) hc0
    have hcolLog:=bank_colLog N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes hc4.1 hc4.2.1 hc4.2.2.1 hc4.2.2.2 G B J P.V P.hV (Real.logb r.Z K₂) hc0
    have hWS:=bank_wsum N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes hc4.1 hc4.2.1 hc4.2.2.1 hc4.2.2.2 G B J P.V P.hV (Real.logb r.Z K₂)
    have hRsV:(rs).V₀=P.V:=rfl
    have hlog:(rs).kLog=Real.logb r.Z K₂:=rfl
    have hOrient:(G=p.val.1 ∧ (rs).V₀=QRH.SilDensitySplit.CubeFree.Packet.firstPacked p.val.1 p.val.2 hc.1 E) ∨
        (G=p.val.2 ∧ (rs).V₀=QRH.SilDensitySplit.CubeFree.Packet.firstPackedRight p.val.1 p.val.2 hc.1 E):=by
      simpa only [hRsV] using horient
    obtain ⟨hK,hK40,hlo,hhi,hK8,hK2,hT0,hT2,hX8⟩:=actual_label_window s cover r.w r.hw hP hd ω₁ ω₂
      p E Kroot δ (b 1).val hz.2.1 hKroot hj hdy hδ.le hδsmall hsc.2.1 G B J hwt rs hvol hlog
      hOrient hWone hWcap hX hXcap
    have hG:G≠0:=RawSides.allocation_common_ne_zero s G B
    have hledger:=selected_restored_ledger M Hr hHr r X₁ X₂ (r.Z^(115/1000:ℝ)) (X₁*X₂/r.Z^(115/1000:ℝ))
      t₁ t₂ n y l d hd₁ hd₂ g hx₁ hx₂ hy0 hy1 hn hws hl hshort cover G hG B J
    have hcol:(rs).colLog ≤ 9179599/10000000-
        Real.logb r.Z (((d.1.absNorm:ℝ)*d.2.absNorm)*(G.absNorm:ℝ))-(∑j∈J,r.w j.val)+Real.logb r.Z ((2:ℝ)^Fintype.card ι):=by
      rw [hcolLog]
      exact hledger.1
    have hcardJ:J.card ≤ N:=(Finset.card_le_univ J).trans
      ((Fintype.card_le_of_injective (fun j:liveIndices B.val=>j.val) Subtype.val_injective).trans hN)
    have hα:0 ≤ Real.logb r.Z (64*((2:ℝ)^J.card)^4):=by
      apply Real.logb_nonneg r.hZ
      have h2:1 ≤ (2:ℝ)^J.card:=one_le_pow₀ (by norm_num)
      have h4:=one_le_pow₀ h2 (n:=4)
      exact one_le_mul_of_one_le_of_one_le (by norm_num) h4
    have hαcap:Real.logb r.Z (64*((2:ℝ)^J.card)^4) ≤ δ:=(hz.2.2.2.1 _ hcardJ).1
    have hcf:Real.logb r.Z ((2:ℝ)^Fintype.card ι) ≤ δ:=(hz.2.2.2.1 _ hN).2
    have hu0:0 ≤ ∑j∈J,r.w j.val:=Finset.sum_nonneg (fun j _=>r.hw j.val)
    obtain ⟨hc,he,hmin,hH0,hH1,hfee,hfull,hex⟩:=hit_fees hδ hρ r.hZ hm0.le hm hδ.le le_rfl hα hαcap hcf
      hz.2.2.1 (le_refl (9179599/10000000:ℝ)) hs.1 hu0 hcol hledger.2 hlo hhi
    have hrect:=selected_rectangles M Hr hHr r X₁ X₂ t₁ t₂ n y d hd₁ hd₂ g hx₁ hx₂ hy1 hn cover G B J
    have hfCaps:filledCaps θ mesh n y r.Z rs:=by
      refine ⟨hfields.2.2.2.2.1.le.trans hrect.1,hfields.2.2.2.2.2.1.le.trans hrect.2.1,
        (by convert hfields.2.2.2.2.2.2.1.le.trans hrect.2.2.1 using 1 <;> norm_num),
        (by convert hfields.2.2.2.2.2.2.2.1.le.trans hrect.2.2.2 using 1 <;> norm_num),?_⟩
      rw [hWS]
      exact hs.2.2.1
    have heCaps:exhaustedCaps θ mesh r.Z rs:=by
      refine ⟨hfCaps.1.trans (Real.rpow_le_rpow_of_exponent_le r.hZ.le hn34),
        hfCaps.2.1.trans (Real.rpow_le_rpow_of_exponent_le r.hZ.le hy34),
        hfCaps.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le r.hZ.le (by norm_num)),
        hfCaps.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le r.hZ.le (by norm_num))⟩
    have hchoice:Fintype.card (Rest J)=0 ∨ (u:ℝ)-mesh ≤ ∑j∈J,r.w j.val:=
      hs.2.2.2.imp (fun h=>h.2) id
    have hPaid:(u:ℝ)-mesh ≤ ∑j∈J,r.w j.val → ∀w₀:ℝ,
        filledPrice θ mesh r.Z rs w₀+δ+δ ≤ (∑j∈J,r.w j.val)+10*δ:=by
      intro hfilled w₀
      exact hfull w₀ (gP rs) (∑i,rs.w i) hfilled
    have hExPaid:exhaustedPrice θ mesh δ hδ.le r.Z rs (∑j∈J,r.w j.val)+δ+δ ≤ (∑j∈J,r.w j.val)+10*δ:=
      hex (gP rs) (∑i,rs.w i)
    exact actual_selected_parts_of_bank N M Hr hHr r hW hL X₁ X₂ (r.Z^(115/1000:ℝ)) (X₁*X₂/r.Z^(115/1000:ℝ)) t₁ t₂ d g mesh height hwm hh hfreq hholes Q hQ hQ0 hQt hQ72 hQbase ColoredRootRestore.bareBase ω₁ ω₂ p.val.1 p.val.2 (commonLabels_supported _ p).1 E χ (ζ⁻¹) F P G B J K δ ξsecond v n y Kslot hδ bank hN hBankFee hAt hMarks hTime hside hCs hlabels.1 hGcap (by linarith only [hK]) (by linarith only [hWone]) hX8 (3*δ) hs.1 hc he hH0 hH1 hmin hfee hK8 hK2 hT0 hT2 hξ hcut hfCaps heCaps hchoice hPaid hExPaid part ζ'
  constructor
  · intro JL hJL
    exact side p.val.1 (SidePack.left F) (Or.inl rfl) rfl hlabels.1 (Or.inl ⟨rfl,rfl⟩) JL hJL
  · intro JR hJR
    exact side p.val.2 (SidePack.right F) (Or.inr rfl) rfl hlabels.2 (Or.inr ⟨rfl,rfl⟩) JR hJR

#print axioms retained_frame_prices_of_bank
end
end QRH.Cycle092.ActualStageFrameBudget
