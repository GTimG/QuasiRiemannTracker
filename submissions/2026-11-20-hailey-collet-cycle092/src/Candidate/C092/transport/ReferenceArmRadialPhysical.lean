/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.3 on the literal original ray-prime pools and original annular marked
coefficients, with independent ordinary characters, profiles and pitches. -/
import Candidate.C092.transport.ReferenceShortP3Physical
import Candidate.C092.transport.ReferenceArmRadialFourthJoin
import Candidate.C092.transport.ReferenceArmRadialGates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.ReferenceShortP3 QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
open QRH.SilDensitySplit.CubeFree.FP.MixedCanonicalSource (slotProfile)
local notation "O" => HeckeFamily.O

theorem actual_two_radius_reference (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (ε bΦ : ℝ) (hε : 0 < ε) (hbΦ : 0 < bΦ)
    (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ ηshort₀ ηlong₀ : Character) (Q : Ideal O) (hQr : Q ≤ rayM)
    (hQ0 : internalQ Q ηlong₀ ≠ 0) (hQt : internalQ Q ηlong₀ ≠ ⊤)
    (hQ72 : internalQ Q ηlong₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ V : ℝ, 0≤ V → V≤2 →
    ∀ (θ : ι → RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ),
    (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ (33/50:ℝ)) → (∑i,w i)≤ widthCap →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U^shortCap → X₂ ≤ U →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₂ (internalQ Q ηlong₀) u.val) →
    (∀ u∈s,rowNorm u ≤ U^V) →
    (∀ u∈s, ∀ i, ‖mark i u‖ =
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i) t₁ (U^(w i))‖) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*(1+|t₂|+|t₂|+height)^d*U^((max V markedRadius+V)/2+ε) := by
  obtain ⟨M,hM,hmeta⟩ := actual_slot_profile_metadata W hW hWs (33/50) (33/50)
  obtain ⟨d,S,C,hC,hsource⟩ := two_radius_reference_source ι hβ rayM Hr hHr ε cutoffBuffer M bΦ
    hε genuine_short_capacity.2.2.2.1 hM hbΦ hΦs η₁ η₂ ηlong₀ Q hQr hQ0 hQt hQ72
  refine ⟨d,S,C,hC,?_⟩
  filter_upwards [hsource,uniform_arm_gates] with U hU hg
  refine ⟨hU.1,?_⟩
  intro V hV hV2 θ w σ v hσlo hσhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hshort hlong s mark hk hy hm
  have gates := hg.2 w X₁ V hX₁.le hshort hsum
  apply hU.2 V hV hV2 (originalPools rayM Hr 2 U w)
    (fun i I => idealCoeff (relativeCharacter rayM Hr hHr ηshort₀ (θ i)) I)
    (fun i => slotProfile W (σ i) (v i)) (fun i => U^(w i))
    (fun i I hI => original_pool_prime rayM Hr U w i I hI)
    (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _)
    (fun i I => actual_ray_coefficient_bound rayM Hr hHr ηshort₀ θ i I)
    (fun i => (hmeta (σ i) (v i) (hσlo i) (hσhi i)).1)
    (fun i => (hmeta (σ i) (v i) (hσlo i) (hσhi i)).2)
    p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hlong gates.1 gates.2 s mark hk hy
  intro u hu i
  exact hm u hu i

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.actual_two_radius_reference
