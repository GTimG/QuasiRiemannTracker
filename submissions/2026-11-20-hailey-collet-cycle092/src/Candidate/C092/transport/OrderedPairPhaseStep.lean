/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual uncentered root from only the original signed centered estimate.
The reference bound is proved by P.3, never supplied as a hypothesis. -/
import Candidate.C092.transport.OrderedPairPhaseAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairPhase
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.ReferenceShortP3
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O

theorem pair_control_mono {a b : ℝ} (p : Profiles a b) {S T : Finset (ℕ×ℕ)} (h : S⊆T) :
    p.control S ≤ p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) _)
    (Seminorm.le_def.mp (Finset.sup_mono h) _) (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem actual_centered_reference_step (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (H Wmax ε bΦ expo Ccenter : ℝ) (dcenter : ℕ) (Scenter : Finset (ℕ×ℕ))
    (hH : 0 < H) (hH1 : H ≤ 1)
    (hreserve : 4*(shortWidth+Wmax) < H) (hε : 0 < ε) (hεH : ε ≤ H)
    (hexpo : H+ε ≤ expo) (hCc : 0 ≤ Ccenter)
    (hbΦ : 0 < bΦ) (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ ηshort₀ ηlong₀ : Character) (Q : Ideal O) (hQr : Q ≤ rayM)
    (hQ0 : internalQ Q ηlong₀ ≠ 0) (hQt : internalQ Q ηlong₀ ≠ ⊤)
    (hQ72 : internalQ Q ηlong₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (T : Finset ι) (θ : ι → RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ),
    (∀ i∈T, (33/50:ℝ) ≤ σ i) → (∀ i∈T, σ i ≤ (33/50:ℝ)) → (∑ i∈T,w i) ≤ Wmax →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → X₁*X₂ ≤ U^(H+shortWidth) →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₂ (internalQ Q ηlong₀) u.val) →
    (∀ u∈s,rowNorm u ≤ U^H) →
    (∀ u∈s, ∀ i∈T, ‖mark i u‖ =
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i) t₁ (U^(w i))‖) →
    alignedPairEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
      (U^shortWidth) (X₁*X₂/U^shortWidth) mark ≤
        Ccenter*(p.control Scenter)^2*(1+|t₁|+|t₂|+height)^dcenter*U^expo →
    finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*(1+|t₁|+|t₂|+height)^d*U^expo := by
  obtain ⟨dr,Sr,Cr,hCr,hsource⟩ := actual_short_reference_subsets ι hβ rayM Hr hHr W hW hWs
    H Wmax ε bΦ hH hH1 hreserve hε hεH hbΦ hΦs η₁ η₂ ηshort₀ ηlong₀ Q hQr hQ0 hQt hQ72
  refine ⟨max dr dcenter,Sr∪Scenter,2*Ccenter+2*Cr,by positivity,hsource.mono ?_⟩
  intro U hU
  refine ⟨hU.1,?_⟩
  intro T θ w σ v hσlo hσhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hprod s mark hk hy hm hcenter
  have hsc := reference_scales_of_product (zero_lt_one.trans hU.1) hX₁ hX₂ hprod
  have href := hU.2 T θ w σ v hσlo hσhi hsum p t₁ t₂ height
    (U^shortWidth) (X₁*X₂/U^shortWidth) hh hsc.1 hsc.2.1 le_rfl hsc.2.2.2 s mark hk hy hm
  have htri := phase_root_triangle T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
    (U^shortWidth) (X₁*X₂/U^shortWidth) mark hX₁ hX₂ hsc.1 hsc.2.1 hsc.2.2.1
  have hpR := pair_control_mono p (show Sr⊆Sr∪Scenter from Finset.subset_union_left)
  have hpC := pair_control_mono p (show Scenter⊆Sr∪Scenter from Finset.subset_union_right)
  have hpnR := p.control_nonneg Sr
  have hpnC := p.control_nonneg Scenter
  have hpn := p.control_nonneg (Sr∪Scenter)
  have hheight : 1 ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hheightR : 0 ≤ 1+|t₂|+height := by positivity
  have hpowR : (1+|t₂|+height)^dr ≤ (1+|t₁|+|t₂|+height)^(max dr dcenter) :=
    (pow_le_pow_left₀ hheightR (by linarith [abs_nonneg t₁]) _).trans
      (pow_le_pow_right₀ hheight (le_max_left _ _))
  have hpowC := pow_le_pow_right₀ hheight (le_max_right dr dcenter)
  have hup := Real.rpow_le_rpow_of_exponent_le hU.1.le hexpo
  have huexp : 0 ≤ U^expo := Real.rpow_nonneg (zero_lt_one.trans hU.1).le _
  have huref : 0 ≤ U^(H+ε) := Real.rpow_nonneg (zero_lt_one.trans hU.1).le _
  have href' : finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂
      (U^shortWidth) (X₁*X₂/U^shortWidth) mark ≤
      Cr*(p.control (Sr∪Scenter))^2*(1+|t₁|+|t₂|+height)^(max dr dcenter)*U^expo := by
    exact href.trans (by gcongr)
  have hcenter' : alignedPairEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
      (U^shortWidth) (X₁*X₂/U^shortWidth) mark ≤
      Ccenter*(p.control (Sr∪Scenter))^2*(1+|t₁|+|t₂|+height)^(max dr dcenter)*U^expo := by
    exact hcenter.trans (by gcongr)
  calc
    _ ≤ 2*(Ccenter*(p.control (Sr∪Scenter))^2*(1+|t₁|+|t₂|+height)^(max dr dcenter)*U^expo)+
        2*(Cr*(p.control (Sr∪Scenter))^2*(1+|t₁|+|t₂|+height)^(max dr dcenter)*U^expo) := by linarith
    _ = _ := by ring

#print axioms actual_centered_reference_step
end
end QRH.Cycle092.OrderedPairPhase
