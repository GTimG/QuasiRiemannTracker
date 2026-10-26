import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalNatural.State
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.FinalDictionary
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63FinalNatural
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRectangle
open CenteredMomentDivisorRetained CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondHeightFamily
open CenteredMomentAllocatedRayDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot HeckePrimeAnnular CenteredMomentInductionEnergy
open Cycle63Moment.LowBranch
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Both residual rectangles inherit the same actual relative ray slots;
the plain profiles include their own exact clipping dilations. -/
theorem actual_positive_ray_energy
    (s : Input α) (η₀ : Character) (θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R₀ : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (v : ℝ)
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R₀ B
    let X := Cycle63.Physical.sourcePlainScales d.toSource second
    let X₁ := X 0/(Ideal.absNorm (selectedPlain L a 0):ℝ)
    let X₂ := X 1/(Ideal.absNorm (selectedPlain L a 1):ℝ)
    finalPositiveEnergy d second L a keep Φ K =
      energy τ (fixedBadMask*idealGenerator (R₀*C)) 1 v
        (dilated s.W₁ (clipDilation X₁)) (dilated s.W₂ (clipDilation X₂))
        (fun j : CenteredMomentDivisorRaw.liveIndices L a =>
          primePool M H bslot (Z^(w j.val.val)))
        (fun (j : CenteredMomentDivisorRaw.liveIndices L a) I =>
          idealCoeff (relativeCharacter M H hH η₀ (θ j.val.val)) I*
            annularWeight W (Z^(w j.val.val)) (σ j.val.val) (freq j.val.val) I)
        (fun j : CenteredMomentDivisorRaw.liveIndices L a => Z^(w j.val.val))
        (clippedScale X₁) (clippedScale X₂) keep Φ K := by
  dsimp only
  rw [final_positive_energy_eq]
  have hpool : (commonData (withHeight s τ v) C R₀ B).slots =
      fun j : CenteredMomentCommonProfile.liveIndices B.val =>
        primePool M H bslot (Z^(w j.val)) := by
    funext j
    exact hm.pool j.val
  have hcoeff : (commonData (withHeight s τ v) C R₀ B).coefficient =
      fun (j : CenteredMomentCommonProfile.liveIndices B.val) I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ j.val)) I*
          annularWeight W (Z^(w j.val)) (σ j.val) (freq j.val) I := by
    funext j I
    exact common_coefficient hm τ v C R₀ B j I
  have hscale : (commonData (withHeight s τ v) C R₀ B).P =
      fun j : CenteredMomentCommonProfile.liveIndices B.val => Z^(w j.val) := by
    funext j
    exact hm.scale j.val
  rw [hpool,hcoeff,hscale]
  rfl

/-- The mask is the actual inherited hole ideal, not a divisor asserted for
the final radial frequency. -/
theorem actual_positive_natural_energy
    (s : Input α) (η₀ : Character) (θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z Bmask : ℝ) (hZ : 1<Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R₀ : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (v : ℝ)
    (Q : Ideal O) (hP : R₀*C≠0) (hPN : ((R₀*C).absNorm:ℝ)≤Z^Bmask)
    (R : ℝ) (C₂ D₂ : Ideal O) (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C₂ D₂))
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (low : O→Prop) :
    let st := retainedState Z Bmask hZ τ Q (R₀*C) hP hPN R C₂ D₂ U
    let d := commonData (withHeight s τ v) C R₀ B
    let X := Cycle63.Physical.sourcePlainScales d.toSource second
    let X₁ := X 0/(Ideal.absNorm (selectedPlain L a 0):ℝ)
    let X₂ := X 1/(Ideal.absNorm (selectedPlain L a 1):ℝ)
    finalPositiveEnergy d second L a (fun z => st.radial.keep z ∧ low z)
      st.radial.profile st.radial.scale =
      energy st.character st.mask 1 v
        (dilated s.W₁ (clipDilation X₁)) (dilated s.W₂ (clipDilation X₂))
        (fun j : CenteredMomentDivisorRaw.liveIndices L a =>
          primePool M H bslot (Z^(w j.val.val)))
        (fun (j : CenteredMomentDivisorRaw.liveIndices L a) I =>
          idealCoeff (relativeCharacter M H hH η₀ (θ j.val.val)) I*
            annularWeight W (Z^(w j.val.val)) (σ j.val.val) (freq j.val.val) I)
        (fun j : CenteredMomentDivisorRaw.liveIndices L a => Z^(w j.val.val))
        (clippedScale X₁) (clippedScale X₂)
        (fun z => st.radial.keep z ∧ low z) st.radial.profile st.radial.scale :=
  actual_positive_ray_energy M H hH s η₀ θ w σ freq W bslot Z hm C R₀ B τ v
    second L a _ _ _

end
end OAI.SevenEighths.Cycle63FinalNatural

end Record1252270103Bootstrap.PR67
