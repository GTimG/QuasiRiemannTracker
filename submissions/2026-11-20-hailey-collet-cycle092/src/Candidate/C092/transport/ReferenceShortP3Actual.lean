/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.3 on the literal original ray-prime pools and original annular marked
coefficients, with independent ordinary characters, profiles and pitches. -/
import Candidate.C092.transport.ReferenceShortP3Physical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
open QRH.SilDensitySplit.CubeFree.FP.MixedCanonicalSource (slotProfile)
local notation "O" => HeckeFamily.O

theorem actual_annular_reference_source (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (H ε ξ bΦ : ℝ) (hH : 0 < H) (hε : 0 < ε) (hεH : ε ≤ H)
    (hξ : 0 < ξ) (hbΦ : 0 < bΦ)
    (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ ηshort₀ ηlong₀ : Character) (Q : Ideal O) (hQr : Q ≤ rayM)
    (hQ0 : internalQ Q ηlong₀ ≠ 0) (hQt : internalQ Q ηlong₀ ≠ ⊤)
    (hQ72 : internalQ Q ηlong₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (θ : ι → RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ),
    (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ (33/50:ℝ)) →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → X₂ ≤ U^H →
    X₁^2*(∏ i,U^(w i))^2 ≤ U^(2:ℝ) →
    4*((X₁^2*(∏ i,U^(w i))^2)^2/(U^H))*U^(ξ/2) < 1 →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₂ (internalQ Q ηlong₀) u.val) →
    (∀ u∈s,rowNorm u ≤ U^H) →
    (∀ u∈s, ∀ i, ‖mark i u‖ =
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i) t₁ (U^(w i))‖) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*(1+|t₂|+height)^d*U^(H+ε) := by
  obtain ⟨M,hM,hmeta⟩ := actual_slot_profile_metadata W hW hWs (33/50) (33/50)
  obtain ⟨d,S,C,hC,hsource⟩ := actual_reference_source ι hβ rayM Hr hHr H ε ξ M bΦ
    hH hε hεH hξ hM hbΦ hΦs η₁ η₂ ηlong₀ Q hQr hQ0 hQt hQ72
  refine ⟨d,S,C,hC,hsource.mono ?_⟩
  intro U hU
  refine ⟨hU.1,?_⟩
  intro θ w σ v hσlo hσhi p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hX₂K hvol hcut s mark hk hy hm
  apply hU.2 (originalPools rayM Hr 2 U w)
    (fun i I => idealCoeff (relativeCharacter rayM Hr hHr ηshort₀ (θ i)) I)
    (fun i => slotProfile W (σ i) (v i)) (fun i => U^(w i))
    (fun i I hI => original_pool_prime rayM Hr U w i I hI)
    (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _)
    (fun i I => actual_ray_coefficient_bound rayM Hr hHr ηshort₀ θ i I)
    (fun i => (hmeta (σ i) (v i) (hσlo i) (hσhi i)).1)
    (fun i => (hmeta (σ i) (v i) (hσlo i) (hσhi i)).2)
    p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hX₂K hvol hcut s mark hk hy
  intro u hu i
  exact hm u hu i

#print axioms actual_annular_reference_source
end
end QRH.Cycle092.ReferenceShortP3
