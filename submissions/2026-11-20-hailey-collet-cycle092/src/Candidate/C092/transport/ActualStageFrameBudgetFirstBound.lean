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
local instance (priority := 2000) firstBoundSubtypeDecEq {κ:Type*}{p:κ→Prop} : DecidableEq (Subtype p):=Classical.decEq _
variable {ι:Type}[Fintype ι] {L mesh Z:ℝ}{θ:GData L}

/-- The actual retained first dyad is bounded even when a particular
allocation set is empty. The true packed twist cancels against its own
common ideal; no second-allocation witness is introduced. -/
theorem actual_first_scale_bound (s:Source ι (1/4) (9/4))(ω₁ ω₂:Character)
    (p:Labels s (by norm_num) (idealCoeff ω₁) (idealCoeff ω₂) 1)
    (E:Finset (CommonIndex p.val.1 p.val.2))(Kr Z κ:ℝ)(j:ℤ)
    (hZ:4096 ≤ Z)(hKr:Z ≤ Kr)(hj:j∈retainedIndices (firstRadius s p.val.1 p.val.2 E Kr Z κ))
    (hκ:(3/2:ℝ)*κ ≤ 1)(hroot:sourceVolume s ≤ Z) :
    childScale Z κ j ≤ Z^(40:ℝ) := by
  have hz:1<Z:=by linarith
  have hz0:=zero_lt_one.trans hz
  have hC:= (commonLabels_supported _ p).1
  have hc:0<(p.val.1.absNorm:ℝ):=nrm_pos hC.1
  have hfactor:0<(p.val.1.absNorm:ℝ)^2*Z:=mul_pos (sq_pos_of_pos hc) hz0
  have hr:=(true_first_radius s (by norm_num) ω₁ ω₂ p E Kr Z κ j hz hKr hj).1
  have ht:=(true_twist_caps s (by norm_num) ω₁ ω₂ p E).1
  have hp:Z^((3/2)*κ) ≤ Z:=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hz.le hκ
  have hvol0:0 ≤ sourceVolume s:=(sourceVolume_pos s).le
  have hh:childScale Z κ j*(p.val.1.absNorm:ℝ)^2*Z ≤ (4*Z^2)*(p.val.1.absNorm:ℝ)^2*Z:=by
    calc
      _ ≤ 4*((Ideal.span {QRH.SilDensitySplit.CubeFree.Packet.firstPacked p.val.1 p.val.2 hC E}).absNorm:ℝ)*
          (sourceVolume s)^2*Z^((3/2)*κ) := hr
      _ ≤ 4*(p.val.1.absNorm:ℝ)^2*Z^2*Z := by gcongr
      _ = _ := by ring
  have hK:childScale Z κ j ≤ 4*Z^2:=by
    apply le_of_mul_le_mul_right (a:=((p.val.1.absNorm:ℝ)^2*Z)) _ hfactor
    convert hh using 1 <;> ring
  calc
    _ ≤ 4*Z^2:=hK
    _ ≤ Z^3:=by nlinarith [sq_nonneg Z]
    _ ≤ Z^(40:ℝ):=by
      rw [show (Z^3:ℝ)=Z^(3:ℝ) by norm_cast]
      exact Real.rpow_le_rpow_of_exponent_le hz.le (by norm_num)

#print axioms actual_first_scale_bound
end
end QRH.Cycle092.ActualStageFrameBudget
