/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The checked original arbitrary-saving unmarked source at EVERY core radius,
including unequal ordinary lengths exceeding the radial core scale. -/
import Candidate.C092.transport.ExhaustedPairPriceAllRadii
set_option autoImplicit false
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge HeckeFamily HeckeInverseAmplification
open ProbeHighRowFamily CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyBands
open QRH.Cycle092.TinyCore QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.ExhaustedPairPrice
local notation "O" => HeckeFamily.O

theorem unmarked_fourth_all_radii
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM≤ Hr)
    (bPhi epsilon : ℝ) (hepsilon : 0< epsilon) (hbPhi : 0< bPhi)
    (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
    (eta base : Character) (Q : Ideal O) (hQray : Q≤ rayM)
    (hQ0 : internalQ Q base≠0) (hQt : internalQ Q base≠⊤)
    (hQ72 : internalQ Q base≤ Ideal.span {(72:O)}) :
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,1< U ∧ ∀V : ℝ,0≤ V → V≤2 →
    ∀ (p : Profiles (1/4) (9/4)) (j : Fin 2) (t height X : ℝ),0≤ height → 0< X → X≤ U →
    ∀rows : Finset FreeRow,(∀u∈rows,initialKeep eta (internalQ Q base) u.val) →
      (∀u∈rows,rowNorm u≤ U^V) →
      (∑u∈rows,‖original eta (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^4) ≤
        C*QuadraticInitialBound.diagonalControl radialMajorant*(sourceControl controls (p.profile j))^4*
          (1+|t|+|t|+height)^degree*U^(V+epsilon) := by
  obtain ⟨degree,controls,C,hC,hsource⟩ := exhausted_pair_all_radii hbeta rayM Hr hHr bPhi 2
    epsilon (by norm_num) hepsilon hbPhi hPhi eta eta base base Q Q
    hQray hQ0 hQt hQ72 hQray hQ0 hQt hQ72
  refine ⟨degree,controls,C,hC,hsource.mono ?_⟩
  intro U hU
  refine ⟨hU.1,?_⟩
  intro V hV hV2 p j t height X hh hX hXU rows hk hy
  have he := hU.2 V hV hV2 (repeatedProfile p j) t t height X X hh hX hX hXU hXU rows hk hk hy
  rw [repeated_control,←pow_mul] at he
  simpa only [repeatedProfile,←pow_add,show (2:ℕ)+2=4 from rfl,show (2:ℕ)*2=4 from rfl] using he

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.unmarked_fourth_all_radii
