/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   True selected second physical ledgers supply both colored first raw sides. -/
import Candidate.C092.transport.TwistedRawBallFull
import Candidate.C092.transport.TwistedRawBallRadius
import Candidate.C092.transport.TwistedRawBallPhysicalSides
import Candidate.C092.transport.ColoredGaussSelectionSecondCaps
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
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
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

/-- Both actual first sides, with independent opposite label and seed-pool
    labels. Every analytical input is a price for literal physical second terms. -/
theorem balanced_sides_of_physical_Q_caps (N : ℕ) (ξ : ℝ) (hξ : 0<ξ) :
    ∃Cz Ct : ℝ,0<Cz ∧ 0<Ct ∧ ∀ᶠZ : ℝ in atTop,3 ≤ Z ∧
    ∀s : Source ι (1/4) (9/4),Fintype.card ι ≤ N →
    ∀(cover : OriginalEnclosure s)(w : ι→ℝ),(∀i,0 ≤ w i) → (∀i,s.P i=Z^(w i)) →
    ∀n y : ℝ,sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑i,w i) →
      poolCap s ≤ Z^(8:ℝ) →
    ∀(η₁ η₂ η : Character)(χ₀ : RayCharacter)(Q : Id)(m : O),
    ∀(C D : Id)(hC : Supported C)(hD : Supported D),
      QRH.Record1252270103KernelMass.primeSupport C=QRH.Record1252270103KernelMass.primeSupport D →
    ∀(E : Finset (CommonIndex C D))(KL KR A loss : ℝ)(J : ℕ),
      1/2 ≤ KL → KL ≤ Z^(40:ℝ) → 1/2 ≤ KR → KR ≤ Z^(40:ℝ) →
      PhysicalBalancedSidesQ s cover w η₁ η₂ η χ₀ Q m C D hC hD E KL KR A Z loss ξ Cz Ct J →
      BalancedSummedRawSideBounds s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) η
        C D hC hD E KL KR A Z loss J := by
  obtain ⟨Cz,Ct,hCz,hCt,hr⟩ := ColoredGaussSelection.original_raw_selected_second_Q_caps N ξ hξ
  refine ⟨Cz,Ct,hCz,hCt,hr.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hN cover w hw hP n y hy hy' hn hX hpool η₁ η₂ η χ₀ Q m C D hC hD hCD
    E KL KR A loss J hKL hKLcap hKR hKRcap hphys χ ζ
  constructor
  · intro v
    obtain ⟨Js,hJs,hprice⟩ := (hphys χ ζ v).1
    have h := hZ.2 ι s hN cover w hw hP n y hy hy' hn hX hpool C D C D hD.1 hD hC hCD.symm
      Js hJs η₁ η₂ (fixedPair η C D hC E χ (ζ⁻¹)).left χ₀ Q m v KL hKL hKLcap
    exact (div_le_div_iff_of_pos_right (sourceVolume_pos s)).mp (h.trans hprice)
  · intro v
    obtain ⟨Js,hJs,hprice⟩ := (hphys χ ζ v).2
    have h := hZ.2 ι s hN cover w hw hP n y hy hy' hn hX hpool C D D C hD.1 hC hD hCD
      Js hJs η₁ η₂ (fixedPair η C D hC E χ (ζ⁻¹)).right χ₀ Q m v KR hKR hKRcap
    exact (div_le_div_iff_of_pos_right (sourceVolume_pos s)).mp (h.trans hprice)

#print axioms balanced_sides_of_physical_Q_caps
end
end QRH.Cycle092.TwistedRawBall
