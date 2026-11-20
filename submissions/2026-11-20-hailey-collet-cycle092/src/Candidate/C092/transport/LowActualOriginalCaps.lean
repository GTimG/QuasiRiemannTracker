/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The genuine low-response source uniformly across and above H. -/
import Candidate.C092.transport.LowActualNearRadii

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open QRH.Cycle092.NativeStrip QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle092.WholeSlot QRH.Cycle090 QRH.SourceCertificate
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open OAI.SevenEighths.Cycle61Moment CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

/-- Actual ordinary lengths at base U are unchanged data when the genuine
source is invoked at U^V; only their exponents are divided by V. -/
theorem ordinary_caps_rescale {N Y U V X₁ X₂ : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hbox : Box N Y 0 (length U X₁) (length U X₂) 0) :
    Box (N/V) (Y/V) 0 (length (U^V) X₁) (length (U^V) X₂) 0 := by
  rw [length_rpow_base U X₁ V hU,length_rpow_base U X₂ V hU]
  refine ⟨div_nonneg hbox.1 hV.le,div_nonneg hbox.2.1 hV.le,?_,by norm_num,by norm_num⟩
  rcases hbox.2.2.1 with h | h
  · exact Or.inl ⟨div_le_div_of_nonneg_right h.1 hV.le,div_le_div_of_nonneg_right h.2 hV.le⟩
  · exact Or.inr ⟨div_le_div_of_nonneg_right h.1 hV.le,div_le_div_of_nonneg_right h.2 hV.le⟩

/-- The entire near-radius low-response branch on the original U-labelled
ordinary box, with one actual finite bank and one set of early controls. -/
theorem low_original_near_radii {n y e Vmax : ℝ}
    (hmax : (98/100 : ℝ) ≤ Vmax)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (cover : EarlierCover OpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY)
    (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper : ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho : ℚ)) :
    ∃ mesh : ℝ, 0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ buffer : ℝ, 0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1 : ℝ) 2 →
    ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
      Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∀ Cslot : ℝ, 0 ≤ Cslot →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ V : ℝ, (98/100 : ℝ) ≤ V → V ≤ Vmax →
    ∀ (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ) (t height : ℝ),
      (∀ j, 0 ≤ w j) → (∀ j, w j ≤ mesh) →
      (∀ j, (33/50 : ℝ) ≤ σ j) → (∀ j, σ j ≤ (33/50 : ℝ)) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
    ∀ (Φ : 𝓢(ℝ,ℂ)), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
      (∀ x, 0 ≤ (Φ x).re) → ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),
      0 < X₁ → 0 < X₂ →
      Box n y 0 (length U X₁) (length U X₂) 0 →
      (∑ j, w j) ≤ sourceWidth n y-(u : ℝ) →
      energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
        (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
        (fun j => U^(w j)) X₁ X₂
        (fun z => initialKeep η (internalQ Q η₀) z ∧
          LowRows Finset.univ η (fixedBadMask*idealGenerator 1) 1 t U e (Cslot*U^buffer) w
            (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
            (fun j => U^(w j)) z) Φ (U^V) ≤
        C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree*U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V)) := by
  obtain ⟨mesh,hm,hstep⟩ := low_step_near_radii hmax hβ cover hy0 hy1 hn0 hn1 he0 he1 hp
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _
  obtain ⟨buffer,hbuffer,hsource⟩ := hstep Slot
  refine ⟨buffer,hbuffer,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72 Cslot hCslot
  obtain ⟨degree,controls,C,hC,hUlarge⟩ := hsource rayM Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72 Cslot hCslot
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hUlarge,eventually_ge_atTop (1 : ℝ)] with U hUlarge hU
  intro V hVmin hVmax θ w σ v t height hw hwm hσlo hσhi hh hv Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox hwidth
  have hV : 0 < V := (by norm_num : (0 : ℝ) < 98/100).trans_le hVmin
  exact hUlarge V hVmin hVmax θ w σ v t height hw hwm hσlo hσhi hh hv Φ hΦs hΦ p X₁ X₂ hX₁ hX₂
    (ordinary_caps_rescale (zero_lt_one.trans_le hU) hV hbox) hwidth

end
end QRH.Cycle092.LowActual
