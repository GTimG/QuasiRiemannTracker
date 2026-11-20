/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   True selected second physical ledgers supply both colored first raw sides. -/
import Candidate.C092.transport.PairedRetainedBudgetCorrected
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentEnergyBands
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentLogDyadic
open CenteredMomentFirstSectorTransform CenteredMomentActiveSource
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedPrincipalAllocations MixedFirstPhysicalApplication MixedFirstRetainedFixed
open MixedInnerExceptionalBlock MixedOriginalTail MixedOriginalNormCap
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.TwistedRawBall
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

def AveragedBalancedSidesQ (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (w : ι→ℝ) (η₁ η₂ η : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (KL KR A Z loss ξ Cz Ct : ℝ) (J : ℕ) : Prop :=
  ∀χ ζ : RayCharacter,∀v : ℝ,
    AveragedSecondSidePrice s cover w C η₁ η₂ (fixedPair η C D hC E χ (ζ⁻¹)).left
      χ₀ Q m v KL Z ξ Cz Ct
      (balancedBudget s (fixedPair η C D hC E χ (ζ⁻¹)).left C D A Z loss*(1+‖v‖)^(2*J)) ∧
    AveragedSecondSidePrice s cover w D η₁ η₂ (fixedPair η C D hC E χ (ζ⁻¹)).right
      χ₀ Q m v KR Z ξ Cz Ct
      (balancedBudget s (fixedPair η C D hC E χ (ζ⁻¹)).right D C A Z loss*(1+‖v‖)^(2*J))

def AveragedRetainedSidesQ (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (w : ι→ℝ) (η₁ η₂ η : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (K Z ξfirst κ H A loss ξsecond Cz Ct : ℝ) (J : ℕ) : Prop :=
  ∀p : Labels s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1,
  ∀E∈inactiveSubsets p.val.1 p.val.2,
  ∀n : Blocks (effectiveScale p.val.1 p.val.2 E K) (firstRadius s p.val.1 p.val.2 E K Z ξfirst)
    (H/p.val.1.absNorm) (H/p.val.2.absNorm),
    1/2 ≤ dyadicScale (n 1) →
    AveragedBalancedSidesQ s cover w η₁ η₂ η χ₀ Q m p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s)
        (TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns s)
        (TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1)) p).2 E
      (MixedFirstExceptionalWindow.childScale Z κ (n 1))
      (MixedFirstExceptionalWindow.childScale Z κ (n 1)) A Z loss ξsecond Cz Ct J


end
end QRH.Cycle092.PairedRetainedBudget
