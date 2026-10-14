/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B088
import Candidate.Bundles.B095
import Candidate.Bundles.B122
import Candidate.Bundles.B127
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
import OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth

/- BEGIN ORIGINAL Cycle61.Physical.FinalErrorRadius; sha256 08948913de64bffa4aa2b51d85f950a6a57c132e63379afe45b71618d8488dae -/
section
                                   
                                                              
                                                                       

namespace OAI.SevenEighths.Cycle61FinalErrorRadius
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondHeightFamily CenteredMomentFirstMixedRoot CenteredMomentFirstPhysicalSource
open CenteredMomentSecondRetainedWidth CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn

/-- The volume bound used in the error cutoff applies to the actual twice
allocated child, including extraction from either plain factor. -/
theorem actual_error_radius_admissible {ι : Type*} [Fintype ι]
    (N : ℕ) (b : ℝ) (hb : 1≤ b)
    (s : Input ι) (hc : Fintype.card ι≤ N) (hs : s.upper≤ b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (p : O) (hp : p≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp : actualAllocations (child s C R B τ t).pools ((Ideal.span {p})^k))
    (υ : Character) (v K : ℝ) (hK : 0< K) :
    (volume (twiceChild s C R B τ t (Ideal.span {p}) k Bp υ v))^2/K ≤
      (b^N*volume s/((C.absNorm:ℝ)*(normValue p)^k))^2/K := by
  have hQ := Ideal.span_singleton_eq_bot.not.mpr hp
  have hnp := pow_pos (normValue_pos p hp) k
  have hv : volume (twiceChild s C R B τ t (Ideal.span {p}) k Bp υ v) ≤
      b^N*volume s/((C.absNorm:ℝ)*(normValue p)^k) := by
    rw [twiceChild,child_volume _ _ hQ k hslot]
    exact (div_le_div_of_nonneg_right
      (common_volume_le N b hb s hc hs C R B τ t hne) hnp.le).trans_eq (by ring)
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (volume_pos _).le hv 2) hK.le


/-- Exact cutoff identity for the extracted-prime branches, retaining the moving conductor cost. -/
theorem error_inverse_radius_log (η τ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b : ℝ) (N : ℕ) (p : O) (k : ℕ) (hp : p≠0)
    (hK : 0< K) (hV : 0< V) (hZ : 1< Z) (hb : 0< b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}) :
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kerror := errorCommonRadius Z d K0 c (3*a) δ reserve p k
    Real.logb Z (frequencyRadius ((b^N*V/((C.absNorm:ℝ)*(normValue p)^k))^2/Kerror) Z ξ)+
      Real.logb Z (τ.modulus.absNorm:ℝ)+errorMoving p Z k =
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-max (c-d+2*errorRemoval p Z k-errorMoving p Z k) 0-3*a-δ-reserve+
        Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2 := by
  dsimp only
  have hc := norm_pos C hC.1
  have hd := norm_pos D hD.1
  have hE := norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR := active_norm_pos C D
  have hz : 0< Z := zero_lt_one.trans hZ
  have hnp := normValue_pos p hp
  have hwidth := actual_reference_width η τ C D hC E K Z hK hZ hmod
  unfold frequencyRadius errorCommonRadius nominalLog
  rw [nominal_equal_support C D _ hC.1 hD.1 heq K V]
  simp (disch := positivity) only [Real.logb_mul, Real.logb_div, Real.logb_pow,
    Real.logb_rpow hz hZ.ne']
  unfold errorRemoval
  by_cases h : Real.logb Z (C.absNorm:ℝ)+2*((k:ℝ)*Real.logb Z (normValue p))-errorMoving p Z k ≤ Real.logb Z (D.absNorm:ℝ)
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    linarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    linarith

/-- The extracted character's moving conductor is paid exactly once. The
actual second natural conductor then cancels its radical in the retained ball. -/
theorem actual_error_final_width (η τ υ χ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b J : ℝ) (N : ℕ)
    (p : O) (k : ℕ) (hp : p≠0)
    (hK : 0< K) (hV : 0< V) (hZ : 1< Z) (hb : 0< b) (hJ : 0< J)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (hυ : (υ.modulus.absNorm:ℝ)≤ J*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))
    (G V₂ z : O) (U : Ideal O) (hU : U≠0)
    (hN : χ.modulus.absNorm≤υ.modulus.absNorm*fixedFactor*U.absNorm*(Ideal.span {V₂}).absNorm) :
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kerror := errorCommonRadius Z d K0 c (3*a) δ reserve p k
    let R := frequencyRadius ((b^N*V/((C.absNorm:ℝ)*(normValue p)^k))^2/Kerror) Z ξ
    retainedWeight R (normValue ((G*V₂)*z))≠0 →
      Real.logb Z (max 1 (4*R/(normValue G*normValue V₂)))+
        Real.logb Z (χ.modulus.absNorm:ℝ) ≤
      (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-
        max (c-d+2*errorRemoval p Z k-errorMoving p Z k) 0-3*a-δ-reserve-
        Real.logb Z (normValue G)+Real.logb Z (U.absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z J+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hrow
  have hh := retained_log_budget υ χ G V₂ z U hU hN _ Z hZ hrow
  have he := error_inverse_radius_log η τ C D hC hD heq E K V Z a δ reserve ξ b N
    p k hp hK hV hZ hb hmod
  dsimp only at he
  have hτ := norm_pos τ.modulus τ.modulus_ne_bot
  have hυpos := norm_pos υ.modulus υ.modulus_ne_bot
  have hl := Real.logb_le_logb_of_le hZ hυpos hυ
  rw [Real.logb_mul (mul_pos hJ hτ).ne' (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_mul hJ.ne' hτ.ne', Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  linarith

end
end OAI.SevenEighths.Cycle61FinalErrorRadius
#print axioms OAI.SevenEighths.Cycle61FinalErrorRadius.error_inverse_radius_log
#print axioms OAI.SevenEighths.Cycle61FinalErrorRadius.actual_error_final_width
#print axioms OAI.SevenEighths.Cycle61FinalErrorRadius.actual_error_radius_admissible

end
/- END ORIGINAL Cycle61.Physical.FinalErrorRadius -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalNatural.Energy; sha256 67721be2f12babafe9ae91a150bc6e163c29d0a792f76a4733cd97210c5f1100 -/
section
                                          
                                               

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalNatural
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRectangle
open CenteredMomentDivisorRetained CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondHeightFamily
open CenteredMomentAllocatedRayDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot HeckePrimeAnnular CenteredMomentInductionEnergy
open Cycle61Moment.LowBranch
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem childEnergy_eq_two_positive (s : Data α) (r : Radial) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α⊕Fin 2))) :
    childEnergy s r L a =
      finalPositiveEnergy s false L a r.keep r.profile r.scale+
      finalPositiveEnergy s true L a r.keep r.profile r.scale := by
  rw [child_energy_eq_radial]
  rfl

theorem actual_childEnergy_eq_natural_pair
    (s : Input α) (C₂ D₂ : Ideal O) (hC₂ : CanonicalQuadraticSieve.Supported C₂)
    (hD₂ : CanonicalQuadraticSieve.Supported D₂)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C₂ D₂))
    (τ : RayFourExpansion.RayCharacter→ Character)
    (hf : CenteredMomentSecondExceptionalFamily.Family s.η C₂ D₂ hC₂ hD₂ U τ)
    (Z Bmask : ℝ) (hZ : 1< Z) (χ : RayFourExpansion.RayCharacter)
    (Q C R₀ : Ideal O) (B : actualAllocations s.pools C) (v R : ℝ)
    (hP : R₀*C≠0) (hPN : ((R₀*C).absNorm:ℝ)≤ Z^Bmask)
    (m : O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    let st := retainedState Z Bmask hZ (τ χ) Q (R₀*C) hP hPN R C₂ D₂ U
    let d := commonData (withHeight s (τ χ) v) C R₀ B
    childEnergy d
      (CenteredMomentSecondOriginalChildren.sourceRadial
        (CenteredMomentRestrictedEnergy.nonexceptional s.η χ Q m
          (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂*
            CenteredMomentSecondCanonicalNonunit.nonunitFrequencyGenerator C₂ D₂ U))
        CenteredMomentFirstAmplificationChoice.ballProfile (retainedScale R C₂ D₂ U)
        (zero_lt_one.trans_le (le_max_left _ _))
        (fun _ => CenteredMomentFirstAmplificationChoice.ballProfile_nonneg _)) L a =
      finalPositiveEnergy d false L a st.radial.keep st.radial.profile st.radial.scale+
      finalPositiveEnergy d true L a st.radial.keep st.radial.profile st.radial.scale := by
  dsimp only
  rw [actual_sourceRadial_eq hf R Z Bmask hZ χ Q (R₀*C) hP hPN m hm hml hm2]
  exact childEnergy_eq_two_positive _ _ L a

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Both residual rectangles inherit the same actual relative ray slots;
the plain profiles include their own exact clipping dilations. -/
theorem actual_positive_ray_energy
    (s : Input α) (η₀ : Character) (θ : α→ RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R₀ : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (v : ℝ)
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (keep : O→ Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R₀ B
    let X := Cycle61.Physical.sourcePlainScales d.toSource second
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
    (s : Input α) (η₀ : Character) (θ : α→ RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z Bmask : ℝ) (hZ : 1< Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R₀ : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (v : ℝ)
    (Q : Ideal O) (hP : R₀*C≠0) (hPN : ((R₀*C).absNorm:ℝ)≤ Z^Bmask)
    (R : ℝ) (C₂ D₂ : Ideal O) (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C₂ D₂))
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (low : O→ Prop) :
    let st := retainedState Z Bmask hZ τ Q (R₀*C) hP hPN R C₂ D₂ U
    let d := commonData (withHeight s τ v) C R₀ B
    let X := Cycle61.Physical.sourcePlainScales d.toSource second
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
end OAI.SevenEighths.Cycle61FinalNatural
#print axioms OAI.SevenEighths.Cycle61FinalNatural.childEnergy_eq_two_positive
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_childEnergy_eq_natural_pair
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_positive_ray_energy
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_positive_natural_energy

end
/- END ORIGINAL Cycle61.Physical.FinalNatural.Energy -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalNatural.Error; sha256 0ed638c8fb1ca5837d5ac5a0580854793168f40d9b2a26587991e898da50f7bd -/
section
                                           
                                        
                                                  

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalNatural
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRetainedWidth CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open Cycle61Moment.LowBranch Cycle61Physical.ExtractedBranches
local notation "O" => HeckeFamily.O

theorem actual_error_retainedState_width
    (η₀ η₁ υ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b J : ℝ) (N : ℕ) (p : O) (k : ℕ) (hp : p≠0)
    (hK₀ : 0< K₀) (hV : 0< V) (hZ : 1< Z) (hb : 0< b) (hJ : 0< J)
    (hmod : η₁.modulus=η₀.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E*activeConductor C₁ D₁})
    (hυ : (υ.modulus.absNorm:ℝ)≤ J*(η₁.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayFourExpansion.RayCharacter→ Character)
    (hf : Family υ C D hC hD U τ)
    (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) (n : Fin 4→ℤ)
    (Bmask : ℝ) (χ : RayFourExpansion.RayCharacter) (Q P : Ideal O)
    (hP : P≠0) (hPN : (P.absNorm:ℝ)≤ Z^Bmask) :
    let c := Real.logb Z (C₁.absNorm:ℝ)
    let d := Real.logb Z (D₁.absNorm:ℝ)
    let k₀ := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E}) K₀ V Z
    let Kerror := errorCommonRadius Z d k₀ c (3*a) δ reserve p k
    let R := frequencyRadius ((b^N*V/((C₁.absNorm:ℝ)*(normValue p)^k))^2/Kerror) Z ξ
    physicalBlock υ t S β C D hC hD U R rows W K n≠0 →
    (retainedState Z Bmask hZ (τ χ) Q P hP hPN R C D U).width≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-
        max (c-d+2*errorRemoval p Z k-errorMoving p Z k) 0-3*a-δ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏q∈U,q.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z J+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hne
  obtain ⟨z,hz⟩ := actual_retained_witness t S β _ rows W K n hne
  have hU : (∏q∈U,q.val)≠0 := Finset.prod_ne_zero_iff.mpr
    (fun q _ => (commonPrime_supported_ideal C D hC q).1)
  exact Cycle61FinalErrorRadius.actual_error_final_width η₀ η₁ υ (τ χ) C₁ D₁ hC₁ hD₁ heq E
    K₀ V Z a δ reserve ξ b J N p k hp hK₀ hV hZ hb hJ hmod hυ _ _ z _ hU
    (actual_family_conductor hf t S β _ rows W K hK n hne χ) hz

theorem actual_error_source_budget
    (η₀ η₁ υ : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (heq : primeSupport C₁=primeSupport D₁) (E : Finset (CommonIndex C₁ D₁))
    (K₀ V Z a δ reserve ξ b J : ℝ) (N : ℕ) (p : O) (k : ℕ) (hp : p≠0)
    (hK₀ : 0< K₀) (hV : 0< V) (hZ : 1< Z) (hb : 0< b) (hJ : 0< J)
    (hmod : η₁.modulus=η₀.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E*activeConductor C₁ D₁})
    (hυ : (υ.modulus.absNorm:ℝ)≤ J*(η₁.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))
    (g₂ t₂ : ℝ) :
    let c := Real.logb Z (C₁.absNorm:ℝ)
    let d := Real.logb Z (D₁.absNorm:ℝ)
    let k₀ := nominalLog C₁ D₁
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex C₁ D₁ => q.val) E}) K₀ V Z
    let Kerror := errorCommonRadius Z d k₀ c (3*a) δ reserve p k
    let R := frequencyRadius ((b^N*V/((C₁.absNorm:ℝ)*(normValue p)^k))^2/Kerror) Z ξ
    Real.logb Z R+Real.logb Z (υ.modulus.absNorm:ℝ)-g₂+t₂+
      Real.logb Z (4*(fixedFactor:ℝ))≤
      (Real.logb Z K₀+Real.logb Z (η₀.modulus.absNorm:ℝ)-
        max (c-d+2*errorRemoval p Z k-errorMoving p Z k) 0-3*a-δ-reserve-g₂+t₂)+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z J+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  have he := Cycle61FinalErrorRadius.error_inverse_radius_log η₀ η₁ C₁ D₁ hC₁ hD₁ heq E
    K₀ V Z a δ reserve ξ b N p k hp hK₀ hV hZ hb hmod
  dsimp only at he
  have hη := CenteredMomentFirstScale.norm_pos η₁.modulus η₁.modulus_ne_bot
  have hυpos := CenteredMomentFirstScale.norm_pos υ.modulus υ.modulus_ne_bot
  have hl := Real.logb_le_logb_of_le hZ hυpos hυ
  rw [Real.logb_mul (mul_pos hJ hη).ne' (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_mul hJ.ne' hη.ne',Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  linarith

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_positive_original_energy
    (s : Input α) (η₀ : Character) (θ : α→ RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z Bmask : ℝ) (hZ : 1< Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R₀ : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (v : ℝ)
    (Q : Ideal O) (hP : R₀*C≠0) (hPN : ((R₀*C).absNorm:ℝ)≤ Z^Bmask)
    (R : ℝ) (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    let st := retainedState Z Bmask hZ τ Q (R₀*C) hP hPN R C₂ D₂ U
    let d := commonData (withHeight s τ v) C R₀ B
    let X₁ := finalPlain d second L a 0
    let X₂ := finalPlain d second L a 1
    let indices := (CenteredMomentDivisorRaw.liveIndices L a).map (originalEmbedding s C B)
    finalPositiveEnergy d second L a st.radial.keep st.radial.profile st.radial.scale =
      energy st.character st.mask 1 v
        (dilated s.W₁ (clipDilation (Cycle61.Physical.sourcePlainScales d.toSource second 0/
          (Ideal.absNorm (selectedPlain L a 0):ℝ))))
        (dilated s.W₂ (clipDilation (Cycle61.Physical.sourcePlainScales d.toSource second 1/
          (Ideal.absNorm (selectedPlain L a 1):ℝ))))
        (fun j : indices => primePool M H bslot (Z^(w j)))
        (fun (j : indices) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (freq j) I)
        (fun j : indices => Z^(w j)) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale := by
  dsimp only
  have he := actual_positive_natural_energy M H hH s η₀ θ w σ freq W bslot Z Bmask hZ
    hm C R₀ B τ v Q hP hPN R C₂ D₂ U second L a (fun _ => True)
  simp only [and_true] at he
  rw [he]
  exact CenteredMomentEnergyReindex.energy_subset_map (originalEmbedding s C B)
    (CenteredMomentDivisorRaw.liveIndices L a) τ (fixedBadMask*idealGenerator (R₀*C)) 1
    _ _ (fun j => primePool M H bslot (Z^(w j)))
    (fun j I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
      annularWeight W (Z^(w j)) (σ j) (freq j) I)
    (fun j => Z^(w j)) v _ _ _ _ _

/-- A fixed ambient dictionary bounds the genuine final positive row. Its
width cap is checked on the physical radius budget, before greedy deletion. -/
theorem actual_retained_positive_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hloss : 0< loss) (hmargin : 0< margin) (hbeta : 51/100≤ HeckeZeroSupremum.beta) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop, 1< Z ∧
    ∀(hZ : 1< Z)(s : Input α) (θ : α→ RayQuotient.Characters M H) (w σ freq : α→ℝ)
      (v height mesh : ℝ), Matches M H hH s η₀ θ w σ freq W B Z →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) →
    ∀(C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂))(τ : RayFourExpansion.RayCharacter→ Character),
      Family s.η C₂ D₂ hC₂ hD₂ U τ →
    ∀(R : ℝ)(cols : Finset (Ideal O))(β : Ideal O→ℂ)(rows : Finset O)
      (Wp : 𝓢(ℝ,ℂ))(K : ℝ),0< K → ∀n : Fin 4→ℤ,
      physicalBlock s.η s.t cols β C₂ D₂ hC₂ hD₂ U R rows Wp K n≠0 →
    ∀(χ : RayFourExpansion.RayCharacter)(C R₀ : Ideal O)
      (Ba : actualAllocations s.pools C)(hP : R₀*C≠0)
      (hPN : ((R₀*C).absNorm:ℝ)≤ Z^Bmask)(second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices Ba.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (τ χ) (internalQ Q η₀)
      (R₀*C) hP hPN R C₂ D₂ U
    let d := commonData (withHeight s (τ χ) v) C R₀ Ba
    let X₁ := finalPlain d second L₂ alloc 0
    let X₂ := finalPlain d second L₂ alloc 1
    let indices := (CenteredMomentDivisorRaw.liveIndices L₂ alloc).map (originalEmbedding s C Ba)
    let budget := Real.logb Z R+Real.logb Z (s.η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏q∈U,q.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))
    ∀p : Profiles ap bp,
      dilated s.W₁ (clipDilation (Cycle61.Physical.sourcePlainScales d.toSource second 0/
        (Ideal.absNorm (selectedPlain L₂ alloc 0):ℝ)))=p.profile 0 →
      dilated s.W₂ (clipDilation (Cycle61.Physical.sourcePlainScales d.toSource second 1/
        (Ideal.absNorm (selectedPlain L₂ alloc 1):ℝ)))=p.profile 1 →
      X₁≤ Z^L → X₂≤ Z^L → budget≤ Mcap →
    finalPositiveEnergy d second L₂ alloc st.radial.keep st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
        (1+|v|+height)^degree*
        Z^(budget+εold+loss*(Fintype.card α:ℝ)+(1/6)*
          max (length Z X₁+length Z X₂+(9/2)*(∑j∈indices,w j)-budget) 0+(3/4)*mesh) := by
  obtain ⟨degree,Sp,hglobal⟩ := actual_global_main_uniform (α:=α) M H hH W A B ap bp
    2 Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp (by norm_num)
    hBmask hMcap hεold hloss hmargin hbeta
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hglobal η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh hm hw hwL hmesh hwm hσlo hσhi hheight hfreq
    C₂ D₂ hC₂ hD₂ U τ hf R cols β rows Wp K hK n hne χ C R₀ Ba hP hPN second L₂ alloc
    st d X₁ X₂ indices budget p hp₁ hp₂ hXcap₁ hXcap₂ hbudget
  have hwidth : st.width≤ budget := actual_retainedState_width hf s.t cols β R rows Wp K
    hK n hne Z Bmask hZ.1 χ (internalQ Q η₀) (R₀*C) hP hPN
  have hX₁ : 0< X₁ := zero_lt_one.trans_le (clippedScale_ge_one _)
  have hX₂ : 0< X₂ := zero_lt_one.trans_le (clippedScale_ge_one _)
  have he := hZ.2 indices θ w σ freq v height mesh hw hwL hmesh (fun j _ => hwm j)
    hσlo hσhi hheight hfreq st rfl (hwidth.trans hbudget) p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂
  have hpaid := paid_global_exponent (width:=st.width) (nominal:=budget) (allowance:=0)
    (total:=length Z X₁+length Z X₂+(9/2)*(∑j∈indices,w j)) (oldLoss:=εold)
    (slotLoss:=loss*(Fintype.card α:ℝ)) (mesh:=mesh) (by linarith) le_rfl
  have hd := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  calc
    _ = energy st.character st.mask 1 v (p.profile 0) (p.profile 1)
      (fun j : indices => primePool M H B (Z^(w j)))
      (fun (j : indices) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (freq j) I)
      (fun j : indices => Z^(w j)) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale := by
        rw [actual_positive_original_energy M H hH s η₀ θ w σ freq W B Z Bmask hZ.1
          hm C R₀ Ba (τ χ) v (internalQ Q η₀) hP hPN R C₂ D₂ U second L₂ alloc,hp₁,hp₂]
    _ ≤ _ := he.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by simpa only [add_zero] using hpaid))
      (by positivity))

end
end OAI.SevenEighths.Cycle61FinalNatural
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_error_retainedState_width
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_positive_original_energy
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_error_source_budget
#print axioms OAI.SevenEighths.Cycle61FinalNatural.actual_retained_positive_uniform

end
/- END ORIGINAL Cycle61.Physical.FinalNatural.Error -/

/- BEGIN ORIGINAL Cycle61.Physical.WidthLoss; sha256 2c7316cc2324a94be9e369f0948011e2145f4c61d6e45164bb6dd34a38a9dd89 -/
section
                                   

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalRadius
noncomputable section
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstPhysicalSource
open CenteredMomentSecondRadicalBudget Filter
open CenteredMomentFirstScale

/-- One threshold pays all fixed conductor, support and presentation losses.
The finite anchor family and ambient slot count are fixed before every live
mass, common allocation, row and height. `J` includes any fixed error cost. -/
theorem fixed_final_width_loss_uniform {Label : Type*} [Fintype Label]
    (η : Label→ Character) (N : ℕ) (b J ε Mmin : ℝ)
    (hb : 0< b) (hJ : 0< J) (hε : 0<ε) (hMmin : 0< Mmin) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀j:Label,∀M:ℝ,Mmin≤ M →
      Real.logb Z ((η j).modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+Real.logb Z J+
        Real.logb Z (4*(fixedFactor:ℝ))≤ε*M := by
  let A := fun j : Label => ((η j).modulus.absNorm:ℝ)*fixedPresentationCost*
    b^(2*N)*J*(4*(fixedFactor:ℝ))
  have ha (j:Label) : 0< A j := by
    have hn := norm_pos _ (η j).modulus_ne_bot
    have hf := fixedPresentationCost_pos
    have hg : (0:ℝ)< fixedFactor := by exact_mod_cast fixedFactor_pos
    dsimp [A]
    positivity
  have ht (j:Label) : ∀ᶠ Z : ℝ in atTop,A j≤ Z^(ε*Mmin) :=
    (tendsto_rpow_atTop (mul_pos hε hMmin)).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_all.mpr ht,eventually_gt_atTop (1:ℝ)] with Z hA hZ
  refine ⟨hZ,?_⟩
  intro j M hM
  have hh := Real.logb_le_logb_of_le hZ (ha j) (hA j)
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  have hn := norm_pos _ (η j).modulus_ne_bot
  have hf := fixedPresentationCost_pos
  have hg : (0:ℝ)< fixedFactor := by exact_mod_cast fixedFactor_pos
  dsimp [A] at hh
  simp (disch := positivity) only [Real.logb_mul, Real.logb_pow] at hh
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) hg.ne']
  have hm := mul_le_mul_of_nonneg_left hM hε.le
  linarith

end
end OAI.SevenEighths.Cycle61FinalRadius
#print axioms OAI.SevenEighths.Cycle61FinalRadius.fixed_final_width_loss_uniform

end
/- END ORIGINAL Cycle61.Physical.WidthLoss -/
