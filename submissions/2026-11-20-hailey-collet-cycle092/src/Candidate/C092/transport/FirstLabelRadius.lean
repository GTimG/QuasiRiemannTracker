/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The two genuine first active colored labels control the actual left and
right physical radii; their twist generators are distinct. -/
import Candidate.C092.transport.FixedFirstCollar
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

theorem true_first_radius (s:Source ι a b) (ha:0<a) (ω₁ ω₂:Character)
    (p:TwistedRawBall.Labels s ha (idealCoeff ω₁) (idealCoeff ω₂) 1)
    (E:Finset (CommonIndex p.val.1 p.val.2)) (Kr Z κ:ℝ) (j:ℤ)
    (hZ:1<Z) (hKr:Z≤Kr) (hj:j∈retainedIndices (firstRadius s p.val.1 p.val.2 E Kr Z κ)) :
    let hC:= (commonLabels_supported _ p).1
    let K:=childScale Z κ j
    K*(p.val.1.absNorm:ℝ)^2*Z ≤ 4*((Ideal.span {Packet.firstPacked p.val.1 p.val.2 hC E}).absNorm:ℝ)*
      (sourceVolume s)^2*Z^((3/2)*κ) ∧
    K*(p.val.2.absNorm:ℝ)^2*Z ≤ 4*((Ideal.span {Packet.firstPackedRight p.val.1 p.val.2 hC E}).absNorm:ℝ)*
      (sourceVolume s)^2*Z^((3/2)*κ) := by
  dsimp only
  have h:=commonLabels_supported _ p
  have hd:=commonLabels_data _ _ p.val.1 p.val.2 p.property
  have c:=commonPart_of_equal_support p.val.1 p.val.2 h.1.1 hd.2.2
  have d:=commonPart_of_equal_support p.val.2 p.val.1 h.2.1 hd.2.2.symm
  have hf:=ColoredGaussFrameProvider.lab_cubeFree ω₁ ω₂ s ha ⟨p,E⟩
  exact ⟨block_K_left _ _ h.1 h.2 E hf c d s Kr Z κ hZ hKr j hj,
    block_K_right _ _ h.1 h.2 E hf c d s Kr Z κ hZ hKr j hj⟩

#print axioms true_first_radius
end QRH.Cycle092.FixedFramePacking
