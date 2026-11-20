/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Literal projectors on the genuine collision/inverse divided source. -/
import Candidate.C092.transport.ActualRootFrameHitSource
import Candidate.C092.transport.OrderedPairActualRestoredGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualRootFrameHit
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.ColoredGaussFrameProvider
open QRH.Cycle092.TwistedRawBallRootProducer
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {ι:Type} [Fintype ι]
variable (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)(hHr:RayOrthogonality.globalUnits M ≤ Hr)
variable (r:RestoredRootSource.Data M Hr ι)
variable (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)(d:IdealPair)(h:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d)
local notation "src"=>dividedCanonicalSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d h

theorem divided_canonical :
    MixedFirstActualNonexceptional.Canonical M Hr hHr r.W 16 r.Lcap r.Z r.η₀ r.θ r.w
      (fun _=>33/50) r.freq r.t r.R₀ (src) :=
  canonicalPairSource_canonical M Hr hHr r _ _ _ _ t₁ t₂ h.x₁ h.x₂ h.y₁ h.y₂ h.product
    h.capx₁ h.capx₂ h.capy₁ h.capy₂

theorem divided_bank_caps : (src).X₁ ≤ r.Z^(3:ℝ) ∧ (src).X₂ ≤ r.Z^(3:ℝ) ∧
    (src).Y₁ ≤ r.Z^(3:ℝ) ∧ (src).Y₂ ≤ r.Z^(3:ℝ) := by
  have hz : r.Z ≤ r.Z^(3:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le r.hZ.le (by norm_num : (1:ℝ) ≤ 3)
  exact ⟨h.capx₁.trans hz,h.capx₂.trans hz,h.capy₁.trans hz,h.capy₂.trans hz⟩

#print axioms divided_canonical
#print axioms divided_bank_caps
end
end QRH.Cycle092.ActualRootFrameHit
