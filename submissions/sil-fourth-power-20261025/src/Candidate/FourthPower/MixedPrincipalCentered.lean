/- Copyright (c) 2026 Sil. Apache-2.0.
Exact principal normalization at the actual multiplied ordinary prefixes.
The lower ordinary scale is shortened by the larger prefix norm, and
both square-root normalizations are kept before any allocation sum.
-/
import Candidate.FourthPower.PrincipalQuantitative
import Candidate.FourthPower.MixedExceptionalDictionary
import Candidate.FourthPower.MixedLiveNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedPrincipalCentered
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open CenteredMomentLattice CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalRowSource CenteredMomentFixedRowMask CenteredMomentAllocatedNaturalRadial
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform
open MixedCenteredEnergy MixedExceptionalDictionary MixedCommonCoefficient MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

def prefixNormMax (e : Id×Id) : ℝ := max (e.1.absNorm:ℝ) (e.2.absNorm:ℝ)

theorem prefixNormMax_pos (e : Id×Id) (he : e.1≠0∧e.2≠0) : 0<prefixNormMax e :=
  (zero_lt_one.trans_le (ideal_norm_one_le he.1)).trans_le (le_max_left _ _)

/-- This identity is literal, before a norm or energy estimate. The
puncture is a sixth-power physical mask and the prefix remains e. -/
theorem centered_physical_identity {ι : Type*} [Fintype ι]
    (η : Character) (z : O) (hz : z≠0)
    (F : Id) (hF : F≠0) (S H : Finset PrimeIdeal)
    (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (e : Id×Id) :
    centeredRow (excluded (naturalCharacter η z) F) S H pool β P W₁ W₂ b X₁ X₂ Y₁ Y₂ e=
      (Real.sqrt (pairNorm e):ℂ)⁻¹*
        (PrincipalPhysical.row η (fixedBadMask*idealGenerator F) 1 z S H pool β P W₁ W₂
            b (X₁/e.1.absNorm) (X₂/e.2.absNorm)-
          PrincipalPhysical.row η (fixedBadMask*idealGenerator F) 1 z S H pool β P W₁ W₂
            b (Y₁/e.1.absNorm) (Y₂/e.2.absNorm)) := by
  unfold centeredRow
  change (Real.sqrt (pairNorm e):ℂ)⁻¹*
    (PrincipalMarked.row _ S H pool β P W₁ W₂ b (X₁/e.1.absNorm) (X₂/e.2.absNorm)-
      PrincipalMarked.row _ S H pool β P W₁ W₂ b (Y₁/e.1.absNorm) (Y₂/e.2.absNorm))=_
  rw [PrincipalPhysical.row_eq_character η (excluded (naturalCharacter η z) F)
      (fixedBadMask*idealGenerator F) 1 z (excluded_natural_presentation η z hz F hF),
    PrincipalPhysical.row_eq_character η (excluded (naturalCharacter η z) F)
      (fixedBadMask*idealGenerator F) 1 z (excluded_natural_presentation η z hz F hF)]

/-- Specialization to the inherited prefixes multiplied by the actual
ordinary allocation. No prefix is replaced by the genuine common ideal. -/
theorem extracted_centered_physical_identity {ι κ : Type*} [Fintype ι]
    (η : Character) (z : O) (hz : z≠0) (F : Id) (hF : F≠0)
    (S H : Finset PrimeIdeal) (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (B : Tuple κ) :
    centeredRow (excluded (naturalCharacter η z) F) S H pool β P W₁ W₂ b X₁ X₂ Y₁ Y₂
      (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))=
      (Real.sqrt (pairNorm d*plainNorm B):ℂ)⁻¹*
        (PrincipalPhysical.row η (fixedBadMask*idealGenerator F) 1 z S H pool β P W₁ W₂
            b (X₁/(d.1*B (Sum.inr 0)).absNorm) (X₂/(d.2*B (Sum.inr 1)).absNorm)-
          PrincipalPhysical.row η (fixedBadMask*idealGenerator F) 1 z S H pool β P W₁ W₂
            b (Y₁/(d.1*B (Sum.inr 0)).absNorm) (Y₂/(d.2*B (Sum.inr 1)).absNorm)) := by
  rw [centered_physical_identity η z hz F hF,
    MixedLiveNormalization.extracted_pair_norm]

theorem shortened_lower_left (e : Id×Id) (he : e.1≠0∧e.2≠0)
    (L X : ℝ) (hL : 0≤L) (hLX : L≤X) :
    L/prefixNormMax e≤X/e.1.absNorm :=
  (div_le_div_of_nonneg_left hL (zero_lt_one.trans_le (ideal_norm_one_le he.1))
    (le_max_left _ _)).trans
    (div_le_div_of_nonneg_right hLX (Nat.cast_nonneg _))

theorem shortened_lower_right (e : Id×Id) (he : e.1≠0∧e.2≠0)
    (L X : ℝ) (hL : 0≤L) (hLX : L≤X) :
    L/prefixNormMax e≤X/e.2.absNorm :=
  (div_le_div_of_nonneg_left hL (zero_lt_one.trans_le (ideal_norm_one_le he.2))
    (le_max_right _ _)).trans
    (div_le_div_of_nonneg_right hLX (Nat.cast_nonneg _))

theorem double_central_normalization (T V N : ℝ) (hT : 0≤T) (hV : 0≤V) (hN : 0<N) :
    (Real.sqrt N)⁻¹*Real.sqrt (T/N*V)=Real.sqrt (T*V)/N := by
  rw [show T/N*V=(T*V)/N by ring,Real.sqrt_div (mul_nonneg hT hV)]
  calc
    _ = (Real.sqrt (T*V)/Real.sqrt N)/Real.sqrt N := by ring
    _ = _ := by rw [div_div,←pow_two,Real.sq_sqrt hN.le]

/-- Pointwise principal cancellation on the actual centered source.
Only numeric support/conductor caps and the genuine inducing predicate
are assumptions. The constant precedes all profiles and prefix ideals.
For an extracted row take e=(d1*B0,d2*B1); the exact denominator is then
pairNorm(d)*plainNorm(B), by extracted_pair_norm. -/
theorem uniform_centered (α B a b ε : ℝ) (hα : 0≤α) (hα4 : α<4/5)
    (hB : 0≤B) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧ ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      ∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀Z : ℝ,1≤Z→∀Fhole F : Id,Fhole≠0→(Fhole.absNorm:ℝ)≤Z^B→F≠0→
      ∀S H : Finset PrimeIdeal,(∀P∈S,Supported P.val)→(∀P∈H,P.val∣Fhole)→
      ∀(η : Character)(z : O),z≠0→
      (HeckeRowClosure.rowConductorBound η (fixedBadMask*idealGenerator F) 1 z:ℝ)≤Z^B→
      CenteredExceptionalProfile.FixedInducingRow η Q fixedBadMask 1 z→
      ∀(ι : Type*) [Fintype ι],
      ∀(pool : ι→Finset Id)(β : ι→Id→ℂ)(P M : ι→ℝ),
      (∀i,0<P i)→(∀i,0≤M i)→
      (∀i I,I∈pool i→Supported I∧(I.absNorm:ℝ)≤2*P i)→
      (∀i I,I∈pool i→‖β i I‖≤M i)→(∏i,2*P i)≤Z^B→
      ∀(e : Id×Id),e.1≠0∧e.2≠0→
      ∀t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L : ℝ,0<L→
      L≤X₁→L≤X₂→L≤Y₁→L≤Y₂→X₁≤U₁→X₂≤U₂→Y₁≤U₁→Y₂≤U₂→
      X₁*X₂=T→Y₁*Y₂=T→
      (∀I,Supported I→((I.absNorm:ℝ)≤b*(U₁/e.1.absNorm)∨
        (I.absNorm:ℝ)≤b*(U₂/e.2.absNorm))→primeSupport I⊆primeValues S)→
      ‖centeredRow (excluded (naturalCharacter η z) F) S H pool β P
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) b X₁ X₂ Y₁ Y₂ e‖≤
        (C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
          (1+‖t₁‖+‖t₂‖)^J*(∏i,256*M i)*Real.sqrt (T*∏i,P i)/pairNorm e)*
          (L/prefixNormMax e)^(-α) := by
  obtain ⟨J,control,h00,hbound⟩ := PrincipalQuantitative.uniform_physical
    α B a b ε hα hα4 hB ha hb hε
  refine ⟨J,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCbound⟩ := hbound Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ Fhole F hFhole hFcut hF S H hS hH η z hz hcond hex
    ι instι pool β P M hP hM hp hβ hV e he
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  have heN := pairNorm_pos he.1 he.2
  have hshort : 0<L/prefixNormMax e := div_pos hL (prefixNormMax_pos e he)
  have hprod (V₁ V₂ : ℝ) (hv : V₁*V₂=T) :
      (V₁/e.1.absNorm)*(V₂/e.2.absNorm)=T/pairNorm e := by
    rw [pairNorm,←hv]
    ring
  have hex' := (fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator F) 1 z
    fixedBadMask_ne_zero (idealGenerator_ne_zero F hF) one_ne_zero hz
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hex
  have hml : goodLambda∣fixedBadMask*idealGenerator F :=
    (show goodLambda∣fixedBadMask from dvd_mul_right _ _).trans (dvd_mul_right _ _)
  have hm2 : (2:O)∣fixedBadMask*idealGenerator F :=
    (show (2:O)∣fixedBadMask from dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have h := hCbound W₁ W₂ hs₁ hs₂ Z hZ Fhole hFhole hFcut S H hS hH
    η (fixedBadMask*idealGenerator F) 1 z
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero F hF)) one_ne_zero hz
    hml hm2
    (by simpa only [one_mul] using hcond) hex' ι pool β P M hP hM hp hβ hV
    t₁ t₂ (X₁/e.1.absNorm) (X₂/e.2.absNorm) (Y₁/e.1.absNorm) (Y₂/e.2.absNorm)
    (U₁/e.1.absNorm) (U₂/e.2.absNorm) (T/pairNorm e) (L/prefixNormMax e) hshort
    (shortened_lower_left e he L X₁ hL.le hX₁) (shortened_lower_right e he L X₂ hL.le hX₂)
    (shortened_lower_left e he L Y₁ hL.le hY₁) (shortened_lower_right e he L Y₂ hL.le hY₂)
    (div_le_div_of_nonneg_right hXU₁ (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_right hXU₂ (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_right hYU₁ (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_right hYU₂ (Nat.cast_nonneg _)) (hprod _ _ hpX) (hprod _ _ hpY) henclose
  rw [centered_physical_identity η z hz F hF,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  calc
    _ = (C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
        (1+‖t₁‖+‖t₂‖)^J*(∏i,256*M i))*
        ((Real.sqrt (pairNorm e))⁻¹*Real.sqrt (T/pairNorm e*∏i,P i))*
        (L/prefixNormMax e)^(-α) := by ring
    _ = _ := by
      rw [double_central_normalization T (∏i,P i) (pairNorm e) hT.le
        (Finset.prod_nonneg (fun i _=>(hP i).le)) heN]
      ring

end
end Candidate.FourthPower.MixedPrincipalCentered
