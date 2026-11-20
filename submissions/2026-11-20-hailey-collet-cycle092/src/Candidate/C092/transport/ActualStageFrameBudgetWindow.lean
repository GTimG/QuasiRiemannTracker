/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Both actual native first orientations control their common second window.
Only literal first labels, retained dyads and positive actual allocations occur. -/
import Candidate.C092.transport.ActualStageFrameBudgetScale
import Candidate.C092.transport.FirstLabelParameters
import Candidate.C092.transport.FirstGroupWindow
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstSectorTransform
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock MixedFirstExceptionalWindow MixedFirstRetainedFixed MixedOriginalTail RepairedRawContext
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry
open CenteredMomentSourceRow CenteredMomentSourceLiveColumn
open QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.Second.Provider QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.FixedFramePacking QRH.Cycle092.TwistedRawBall
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local instance (priority := 2000) windowSubtypeDecEq {κ:Type*}{p:κ→Prop} : DecidableEq (Subtype p):=Classical.decEq _
variable {ι:Type}[Fintype ι] {L mesh Z:ℝ}{θ:GData L}

theorem actual_label_window (s:Source ι (1/4) (9/4))(cover:OriginalEnclosure s)
    (w:ι→ℝ)(hw:∀i,0 ≤ w i)(hP:∀i,s.P i=Z^(w i))(hd:s.d=(1,1))
    (ω₁ ω₂:Character)(p:Labels s (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂) 1)
    (E:Finset (CommonIndex p.val.1 p.val.2))(Kr κ:ℝ)(j:ℤ)
    (hZ:4096 ≤ Z)(hKr:Z ≤ Kr)(hj:j∈retainedIndices (firstRadius s p.val.1 p.val.2 E Kr Z κ))
    (hdy:(1/2:ℝ) ≤ dyadicScale j)(hκ:0 ≤ κ)(hk:κ ≤ 1/1000)
    (hvolRoot:sourceVolume s ≤ Z^(9179599/10000000:ℝ))
    (G:Id)(B:actualAllocations (tuplePools s) G)(Js:Finset (liveIndices B.val))
    (hweight:allocationWeight s (idealCoeff ω₁) (idealCoeff ω₂) G B≠0)
    (rs:GSrc θ mesh Z)
    (hvol:rs.vol=sourceVolume (renorm (restOf s (by norm_num) cover G B Js)))
    (hlog:rs.kLog=Real.logb Z (16*childScale Z κ j*(QRH.Cycle092.RawSides.selectionScaleQ s (by norm_num) cover G B Js)^4))
    (horient:
      (G=p.val.1 ∧ rs.V₀=QRH.SilDensitySplit.CubeFree.Packet.firstPacked p.val.1 p.val.2 (commonLabels_supported _ p).1 E) ∨
      (G=p.val.2 ∧ rs.V₀=QRH.SilDensitySplit.CubeFree.Packet.firstPackedRight p.val.1 p.val.2 (commonLabels_supported _ p).1 E))
    (hW:1 ≤ QRH.Cycle092.RawSides.selectionScaleQ s (by norm_num) cover G B Js)
    (hwcap:QRH.Cycle092.RawSides.selectionScaleQ s (by norm_num) cover G B Js ≤ Z^(1/1000:ℝ))
    (hX:1 ≤ QRH.Cycle092.RawSides.residualCapQ (restOf s (by norm_num) cover G B Js))
    (hXcap:QRH.Cycle092.RawSides.residualCapQ (restOf s (by norm_num) cover G B Js) ≤ Z^(919/1000:ℝ)) :
    let K:=childScale Z κ j
    let W:=QRH.Cycle092.RawSides.selectionScaleQ s (by norm_num) cover G B Js
    let X:=QRH.Cycle092.RawSides.residualCapQ (restOf s (by norm_num) cover G B Js)
    let u':=∑q∈Js,w q.val
    (1/2:ℝ) ≤ K ∧ K ≤ Z^(40:ℝ) ∧
      (1-6*u'+mesh-(Real.logb Z (64*((2:ℝ)^Js.card)^4)+(3/2)*κ) ≤ commonH rs) ∧
      commonH rs ≤ 2*(9179599/10000000:ℝ)+2*Real.logb Z ((2:ℝ)^Fintype.card ι)+mesh ∧
      8 ≤ 16*K*W^4 ∧ 16*K*W^4 ≤ Z^(2:ℝ) ∧
      0 ≤ RootColoredSeed.secondCutoffQ X K W ∧ RootColoredSeed.secondCutoffQ X K W ≤ Z^(2:ℝ) ∧ X ≤ Z^(8:ℝ) := by
  intro K W X u'
  have hz:1<Z:=by linarith
  have ht:=true_twist_caps s (by norm_num) ω₁ ω₂ p E
  have hr:=true_first_radius s (by norm_num) ω₁ ω₂ p E Kr Z κ j hz hKr hj
  have htw:((Ideal.span {rs.V₀}).absNorm:ℝ) ≤ (G.absNorm:ℝ)^2:=by
    rcases horient with ⟨hG,hV⟩|⟨hG,hV⟩
    · rw [hG,hV];exact ht.1
    · rw [hG,hV];exact ht.2
  have hfirst:K*(G.absNorm:ℝ)^2*Z ≤ 4*((Ideal.span {rs.V₀}).absNorm:ℝ)*(sourceVolume s)^2*Z^((3/2)*κ):=by
    rcases horient with ⟨hG,hV⟩|⟨hG,hV⟩
    · rw [hG,hV];exact hr.1
    · rw [hG,hV];exact hr.2
  have hK:(1/2:ℝ) ≤ K:=by
    rw [show K=dyadicScale j*Z^κ by exact QRH.SilDensitySplit.CubeFree.Second.Provider.childScale_eq Z κ hz j]
    exact hdy.trans (le_mul_of_one_le_right (dyadicScale_pos _).le (Real.one_le_rpow hz.le hκ))
  have hw:=actual_window rs s (by norm_num) cover G (QRH.Cycle092.RawSides.allocation_common_ne_zero s G B)
    B Js hd (idealCoeff ω₁) (idealCoeff ω₂) hweight w hw hP K κ (9179599/10000000)
    hK hvolRoot hvol hlog htw hfirst
  have hroot:sourceVolume s ≤ Z:=hvolRoot.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num : (9179599/10000000:ℝ) ≤ 1))
  have hb:=hit_box_parameters s (by norm_num) ω₁ ω₂ p E Kr Z κ j hZ hKr hj hroot hdy hκ hk W X hW hwcap hX hXcap
  have hK₂:K ≤ 16*K*W^4:=by
    have h4:=one_le_pow₀ hW (n:=4)
    nlinarith [show 0 ≤ K by linarith]
  have h40:Z^(2:ℝ) ≤ Z^(40:ℝ):=Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num)
  refine ⟨hK,(hK₂.trans hb.2.1).trans h40,hw.1,hw.2,hb.1,hb.2.1,?_,?_,hb.2.2.2.2⟩
  · exact hb.2.2.1
  · exact hb.2.2.2.1

#print axioms actual_label_window
end
end QRH.Cycle092.ActualStageFrameBudget
