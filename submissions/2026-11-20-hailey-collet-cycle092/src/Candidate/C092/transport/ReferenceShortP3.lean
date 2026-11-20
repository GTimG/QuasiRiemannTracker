/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Unconditional analytic P.3 short reference, on original kept finite rows,
under its actual scalar width reserve. No marked-source hypothesis. -/
import Candidate.C092.transport.ReferenceShortP3Actual
import Candidate.C092.transport.ReferenceShortP3Gates

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
local notation "O" => HeckeFamily.O

/-- The actual .115 short-reference source. Its constant, degree, controls
and threshold precede all live slot/ray/response data and both Schwartz
profiles. Every positive short scale is allowed, including below one. -/
theorem actual_short_reference (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (H Wmax ε bΦ : ℝ) (hH : 0 < H) (hH1 : H ≤ 1)
    (hreserve : 4*(shortWidth+Wmax) < H) (hε : 0 < ε) (hεH : ε ≤ H)
    (hbΦ : 0 < bΦ) (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ ηshort₀ ηlong₀ : Character) (Q : Ideal O) (hQr : Q ≤ rayM)
    (hQ0 : internalQ Q ηlong₀ ≠ 0) (hQt : internalQ Q ηlong₀ ≠ ⊤)
    (hQ72 : internalQ Q ηlong₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (θ : ι → RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ),
    (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ (33/50:ℝ)) → (∑ i,w i) ≤ Wmax →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U^shortWidth → X₂ ≤ U^H →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₂ (internalQ Q ηlong₀) u.val) →
    (∀ u∈s,rowNorm u ≤ U^H) →
    (∀ u∈s, ∀ i, ‖mark i u‖ =
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i) t₁ (U^(w i))‖) →
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*(1+|t₂|+height)^d*U^(H+ε) := by
  let ξ := H-4*(shortWidth+Wmax)
  have hξ : 0 < ξ := by dsimp [ξ]; linarith only [hreserve]
  have hres : 4*(shortWidth+Wmax)+ξ/2 < H := by dsimp [ξ]; linarith only [hreserve]
  obtain ⟨d,S,C,hC,hsource⟩ := actual_annular_reference_source ι hβ rayM Hr hHr W hW hWs
    H ε ξ bΦ hH hε hεH hξ hbΦ hΦs η₁ η₂ ηshort₀ ηlong₀ Q hQr hQ0 hQt hQ72
  refine ⟨d,S,C,hC,?_⟩
  filter_upwards [hsource,uniform_original_short_gates hH1 hξ.le hres] with U hU hgate
  refine ⟨hU.1,?_⟩
  intro θ w σ v hσlo hσhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hshort hlong s mark hk hy hm
  have hg := hgate.2 w X₁ hX₁.le hshort hsum
  exact hU.2 θ w σ v hσlo hσhi p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hlong hg.1 hg.2 s mark hk hy hm

#print axioms actual_short_reference
end
end QRH.Cycle092.ReferenceShortP3
