/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Apply the genuine fixed native packet to its literal restored first hit.
The empty carrier is exact zero; the nonempty cutoff uses the true prefix volume. -/
import Candidate.C092.transport.ActualStageFrameBudgetFixedHit
import Candidate.C092.transport.ActualStageFrameBudgetRegularHit
import Candidate.C092.transport.ActualStageFrameBudgetPhysicalBank
import Candidate.C092.transport.ActualRootFrameHitWidth
import Candidate.C092.transport.ActualStageFrameBudgetEmpty
import Candidate.C092.transport.ActualRootFrameHitAll
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
local instance (priority := 2000) nativeHitSubtypeDecEq {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable {ι:Type}[Fintype ι]
variable (N:ℕ)(M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)(hHr:RayOrthogonality.globalUnits M ≤ Hr)
variable (r:RestoredRootSource.Data M Hr ι)(hW:ContDiff ℝ ∞ r.W)(hL:r.Lcap=8)
variable (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)(d:IdealPair)(g:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d)
local notation "src"=>dividedCanonicalSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g
local notation "cov"=>canonicalPairSource_original_enclosure M Hr hHr r _ _ _ _ t₁ t₂
  g.x₁ g.x₂ g.y₁ g.y₂ g.product g.capx₁ g.capx₂ g.capy₁ g.capy₂
local notation "caps₄"=>divided_bank_caps M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g
variable (mesh height:ℝ)(hwm:∀i,r.w i ≤ mesh)(hh:0 ≤ height)(hfreq:∀i,|r.freq i| ≤ height)
variable (hholes:∀i,(r.R₀ i).card ≤ 2*N)
variable (Q:Id)(hQ:Q ≤ M)(hQ0:Q≠0)(hQt:Q≠⊤)(hQ72:Q ≤ Ideal.span {(72:O)})(hQbase:Q ≤ r.η₀.modulus)
variable (η ω₁ ω₂:Character)(C₀ D₀:Id)(hC₀:Supported C₀)(E₀:Finset (CommonIndex C₀ D₀))
variable (χ₁ χ₂:RayCharacter)(F:FixedPair η C₀ D₀ hC₀ E₀ χ₁ χ₂)(P:SidePack η)
open QRH.Cycle092.RegularPhysicalClassBudget
include hL in
/-- Both actual physical parts consume the genuine early finite bank. -/
theorem actual_selected_parts_of_bank :
  let s:=src
  let cover:=cov
  ∀(G:Id)(B:actualAllocations (tuplePools s) G)(Js:Finset (liveIndices B.val))(K:ℝ),
  let ws:=RawSides.selectionScaleQ s (by norm_num) cover G B Js
  let kr:=16*K*ws^4
  let rem:=restOf s (by norm_num) cover G B Js
  let xcap:=RawSides.residualCapQ rem
  let ts:=RootColoredSeed.secondCutoffQ xcap K ws
  let child:=originalSelectedSource s (by norm_num) cover G B Js
  let th:=frameData N (Fintype.card (Rest Js)) M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase
  let rs:GSrc th mesh r.Z:=bankFrame N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes (caps₄).1 (caps₄).2.1 (caps₄).2.2.1 (caps₄).2.2.2 G B Js P.V P.hV (Real.logb r.Z kr)
  let usel:=∑j∈Js,r.w j.val
  let cinv:=Real.logb r.Z (((d.1.absNorm:ℝ)*d.2.absNorm)*(G.absNorm:ℝ))
  ∀(δ ξ v n y Kslot:ℝ)(hδ:0 < δ)(bank:NativePhysicalBank N),
  Fintype.card ι ≤ N → bank.Fee →
  bank.At (fun k=>frameData N k.val M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase)
    η ω₁ ω₂ Q mesh δ n y Kslot r.Z hδ →
  RestoredRootSource.slotBound r.W r.hW r.hWs ≤ Kslot → r.t=t₁ →
  (P.base=F.left ∨ P.base=F.right) → P.Cs=G →
  (C₀.absNorm:ℝ) ≤ r.Z^(8:ℝ) → (G.absNorm:ℝ) ≤ r.Z^(8:ℝ) →
  0<K → 0<ws → xcap ≤ r.Z^(8:ℝ) →
  ∀err:ℝ,usel ≤ (QRH.SourceCertificate.u:ℝ) →
  rs.colLog ≤ 9179599/10000000-cinv-usel+err → 1-6*usel ≤ commonH rs+err →
  0 ≤ commonH rs → commonH rs ≤ 19/10 →
  max 0 (115/1000-cinv) ≤ Real.logb r.Z (max 1 child.L)+err →
  δ+3*mesh+Real.logb r.Z 2+(17/6)*err+δ/8 ≤ 3036/100000 →
  8 ≤ kr → kr ≤ r.Z^(2:ℝ) → 0 ≤ ts → ts ≤ r.Z^(2:ℝ) → ξ ≤ 1 →
  32*((9/4:ℝ)^2*(2:ℝ)^Fintype.card (Rest Js))^2*r.Z^(ξ/2) ≤ r.Z^mesh →
  filledCaps th mesh n y r.Z rs → exhaustedCaps th mesh r.Z rs →
  (Fintype.card (Rest Js)=0 ∨ (QRH.SourceCertificate.u:ℝ)-mesh ≤ usel) →
  ((QRH.SourceCertificate.u:ℝ)-mesh ≤ usel → ∀w₀:ℝ,filledPrice th mesh r.Z rs w₀+δ+δ ≤ usel+10*δ) →
  exhaustedPrice th mesh δ hδ.le r.Z rs usel+δ+δ ≤ usel+10*δ →
  ∀part:Bool,∀ζ:RayCharacter,
    selectedPartTerm part s cover G B Js ω₁ ω₂ P.base 1 Q fixedBadMask v K r.Z ξ ζ ≤
      (bank.totalFee*((r.p.control bank.controls)^2*(1+|t₁|+|t₂|+height)^bank.degree)*r.Z^(10*δ)*
        sourceVolume (renorm rem)^2*r.Z^usel*((Ideal.span {P.V}).absNorm:ℝ))*(1+‖v‖)^(2*bank.J) := by
  intro s cover G B Js K ws kr rem xcap ts child th rs usel cinv δ ξ v n y Kslot hδ bank hN hBankFee hAt
    hMarks hTime hside hCs hCcap hGcap hK hWs hXcap err hu hcol hfill hH0 hH1 hmin hfee
    hk8 hk2 ht0 ht2 hξ hcut hFilledCaps hExCaps hchoice hFilledPaid hExPaid part ζ
  have hRest:Fintype.card (Rest Js) ≤ N:=by
    apply (Fintype.card_le_of_injective (fun j:Rest Js=>j.val.val) ?_).trans hN
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  let k:Fin (N+1):=⟨Fintype.card (Rest Js),Nat.lt_succ_of_le hRest⟩
  have hz0:0 < r.Z:=zero_lt_one.trans r.hZ
  have hpkt:=hAt k
  have hfields:=bank_fields N M Hr hHr r.W hW r.hWs r.η₀ Q hQ hQ0 hQt hQ72 hQbase s cover r.hZ r.θ r.w (fun _=>33/50) r.freq r.t height r.R₀ r.hw hwm (fun _=>rfl) hh hfreq hholes (caps₄).1 (caps₄).2.1 (caps₄).2.2.1 (caps₄).2.2.2 G B Js P.V P.hV (Real.logb r.Z kr)
  have hprofiles:=selected_profiles M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g cover G B Js
  have hLam:classLambda 1 (bank.Cgr k) 1 (bank.Cr k*gAmp 3 th mesh η r.Z rs (bank.jr k) (bank.Sr k)) th.a (bank.jr k) ≤
      bank.Cregular*((r.p.control bank.controls)^2*(1+|t₁|+|t₂|+height)^bank.degree):=by
    apply hBankFee k rfl η rs r.p t₁ t₂ height hh
    · change height ≤ height;exact le_rfl
    · change r.t=t₁;exact hTime
    · exact hfields.2.2.1.trans (congrArg (fun x:ℝ=>x/(2*Real.pi)) hprofiles.2.2.1)
    · exact hfields.2.2.2.1.trans (congrArg (fun x:ℝ=>x/(2*Real.pi)) hprofiles.2.2.2)
    · exact hfields.1.trans hprofiles.1
    · exact hfields.2.1.trans hprofiles.2.1
  have hcf:bank.Cfixed ≤ bank.totalFee:=by unfold NativePhysicalBank.totalFee;linarith [bank.regular_pos]
  have hcr:bank.Cregular ≤ bank.totalFee:=by unfold NativePhysicalBank.totalFee;linarith [bank.fixed_pos]
  cases part
  · have hreturn:∃fee debit:ℝ,∃price:∀U:ℝ,GSrc th mesh U→ℝ→ℝ,
        ∃caps:∀U:ℝ,GSrc th mesh U→Prop,
        PartWithFeeAt th mesh η ω₁ ω₂ 0 (19/10) δ δ fee (bank.jr k) (bank.Sr k) (bank.Cr k) (bank.Cgr k) price caps r.Z ∧
          caps r.Z rs ∧ δ+fee+debit ≤ 10*δ ∧ price r.Z rs usel+δ ≤ usel+debit+fee:=by
      by_cases hk:k.val=0
      · refine ⟨δ+δ,7*δ,exhaustedPrice th mesh δ hδ.le,exhaustedCaps th mesh,(hpkt.2.1 hk),hExCaps,by linarith,?_⟩
        linarith [hExPaid]
      · have hf:=hpkt.2.2 hk
        have hf':=part_fee_of_part th mesh η ω₁ ω₂ 0 (19/10) δ δ 0 (bank.jr k) (bank.Sr k)
          (bank.Cr k) (bank.Cgr k) (filledPrice th mesh) (filledCaps th mesh n y) r.Z hf
        refine ⟨0,9*δ,filledPrice th mesh,filledCaps th mesh n y,hf',hFilledCaps,by linarith,?_⟩
        have hfil:(QRH.SourceCertificate.u:ℝ)-mesh ≤ usel:=hchoice.resolve_left (fun h0=>hk h0)
        linarith [hFilledPaid hfil usel]
    obtain ⟨fee,debit,price,caps,hpacket,hcaps,hprice,hpaid⟩:=hreturn
    have hreal:=regular_selected_from_native_packet N M Hr hHr r hW hL X₁ X₂ Y₁ Y₂ t₁ t₂ d g mesh height hwm hh hfreq hholes Q hQ hQ0 hQt hQ72 hQbase η ω₁ ω₂ P G B Js K δ δ fee debit (10*δ) ξ v (bank.jr k) bank.J bank.degree (bank.Sr k) bank.controls (bank.Cr k) (bank.Cgr k) bank.Cregular price caps hpacket bank.regular_pos.le (bank.regular_J_le k) hLam hCs hGcap hK hWs hXcap hH0 hH1 hcaps hk8 hk2 ht0 ht2 hξ hcut hprice usel hpaid ζ
    apply hreal.trans
    have hrest:0 ≤ ((r.p.control bank.controls)^2*(1+|t₁|+|t₂|+height)^bank.degree)*r.Z^(10*δ)*
        sourceVolume (renorm rem)^2*r.Z^usel*((Ideal.span {P.V}).absNorm:ℝ)*(1+‖v‖)^(2*bank.J):=by positivity
    have hmono:=mul_le_mul_of_nonneg_right hcr hrest
    convert hmono using 1 <;> ring
  · have hreal:=fixed_selected_from_native_packet N M Hr hHr r hW hL X₁ X₂ Y₁ Y₂ t₁ t₂ d g mesh height hwm hh hfreq hholes Q hQ hQ0 hQt hQ72 hQbase η ω₁ ω₂ C₀ D₀ hC₀ E₀ χ₁ χ₂ F P G B Js K δ δ δ ξ v (bank.jf k) bank.J bank.degree (bank.Sf k) bank.controls (bank.Cgf k) (bank.Cf k) bank.Cfixed Kslot hpkt.1 bank.fixed_pos.le hMarks hside hCs hCcap hGcap hK hWs hXcap err hu hcol hfill hH0 hH1 hmin hfee hk8 hk2 ht0 ht2 hξ hcut ζ
    apply hreal.trans
    have hp:r.Z^δ ≤ r.Z^(10*δ):=Real.rpow_le_rpow_of_exponent_le r.hZ.le (by linarith)
    have hfirst:bank.Cfixed*r.Z^δ ≤ bank.totalFee*r.Z^(10*δ):=
      mul_le_mul hcf hp (Real.rpow_nonneg (zero_lt_one.trans r.hZ).le _) (by unfold NativePhysicalBank.totalFee;linarith [bank.fixed_pos,bank.regular_pos])
    have hrest:0 ≤ ((r.p.control bank.controls)^2*(1+|t₁|+|t₂|+height)^bank.degree)*
        sourceVolume (renorm rem)^2*r.Z^usel*((Ideal.span {P.V}).absNorm:ℝ)*(1+‖v‖)^(2*bank.J):=by positivity
    have hmono:=mul_le_mul_of_nonneg_right hfirst hrest
    convert hmono using 1 <;> ring

#print axioms actual_selected_parts_of_bank
end
end QRH.Cycle092.ActualStageFrameBudget
