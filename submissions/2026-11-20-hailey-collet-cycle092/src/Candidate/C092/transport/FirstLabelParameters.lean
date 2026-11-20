/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The two genuine first active colored labels control the actual left and
right physical radii; their twist generators are distinct. -/
import Candidate.C092.transport.FirstLabelRadius
import Candidate.C092.transport.FirstWindowRange
import Candidate.C092.transport.ColoredGaussFrameProviderPacking
import Candidate.C092.transport.TwistedRawBallMass
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeometry6
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentFirstSectorTransform CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstExceptionalPrefactor CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedInnerExceptionalBlock
open MixedFirstRetainedFixed MixedFirstExceptionalWindow MixedOriginalTail RepairedRawContext
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry
open QRH.Cycle092
namespace QRH.Cycle092.FixedFramePacking
local notation "Id" => Ideal HeckeFamily.O
variable {ι:Type} [Fintype ι] {a b:ℝ}

theorem true_twist_caps (s:Source ι a b) (ha:0<a) (ω₁ ω₂:Character)
    (p:TwistedRawBall.Labels s ha (idealCoeff ω₁) (idealCoeff ω₂) 1)
    (E:Finset (CommonIndex p.val.1 p.val.2)) :
    let hC:= (commonLabels_supported _ p).1
    ((Ideal.span {Packet.firstPacked p.val.1 p.val.2 hC E}).absNorm:ℝ)  ≤  (p.val.1.absNorm:ℝ)^2 ∧
    ((Ideal.span {Packet.firstPackedRight p.val.1 p.val.2 hC E}).absNorm:ℝ)  ≤  (p.val.2.absNorm:ℝ)^2 := by
  dsimp only
  have h:=commonLabels_supported _ p
  have hd:=commonLabels_data _ _ p.val.1 p.val.2 p.property
  have c:=commonPart_of_equal_support p.val.1 p.val.2 h.1.1 hd.2.2
  have d:=commonPart_of_equal_support p.val.2 p.val.1 h.2.1 hd.2.2.symm
  have hf:=ColoredGaussFrameProvider.lab_cubeFree ω₁ ω₂ s ha ⟨p,E⟩
  exact ⟨packed_le_sq p.val.1 p.val.2 h.1 E h.2 hf c d,packedRight_le_sq p.val.1 p.val.2 h.1 E h.2 hf c d⟩

theorem hit_box_parameters (s:Source ι a b) (ha:0<a) (ω₁ ω₂:Character)
    (p:TwistedRawBall.Labels s ha (idealCoeff ω₁) (idealCoeff ω₂) 1)
    (E:Finset (CommonIndex p.val.1 p.val.2)) (Kr Z κ:ℝ) (j:ℤ)
    (hZ:4096 ≤ Z) (hKr:Z ≤ Kr) (hj:j∈retainedIndices (firstRadius s p.val.1 p.val.2 E Kr Z κ))
    (hroot:sourceVolume s ≤ Z) (hdy:(1/2:ℝ) ≤ dyadicScale j) (hκ:0 ≤ κ) (hk:κ ≤ 1/1000)
    (W X:ℝ) (hW:1 ≤ W) (hw:W ≤ Z^(1/1000:ℝ)) (hX:1 ≤ X) (hx:X ≤ Z^(919/1000:ℝ)) :
    let K₂:=16*childScale Z κ j*W^4
    let Tsec:=X^2/K₂
    8 ≤ K₂ ∧ K₂ ≤ Z^(2:ℝ) ∧ 0 ≤ Tsec ∧ Tsec ≤ Z^(2:ℝ) ∧ X ≤ Z^(8:ℝ) := by
  have hZ':1<Z:=by linarith
  have hc:0 < (p.val.1.absNorm:ℝ) := QRH.SilDensitySplit.CubeFree.Second.Provider.nrm_pos (commonLabels_supported _ p).1.1
  have hr := true_first_radius s ha ω₁ ω₂ p E Kr Z κ j hZ' hKr hj
  have hwc:=true_twist_caps s ha ω₁ ω₂ p E
  have hl:(1/2:ℝ)  ≤  childScale Z κ j := by
    rw [childScale_eq Z κ hZ' j]
    exact hdy.trans (le_mul_of_one_le_right (dyadicScale_pos _).le (Real.one_le_rpow hZ'.le hκ))
  exact box_parameters hZ hc (Nat.cast_nonneg _) hwc.1 (sourceVolume_pos s).le hroot hl hW hw hk hr.1 hX hx

#print axioms true_twist_caps
#print axioms hit_box_parameters
end QRH.Cycle092.FixedFramePacking
