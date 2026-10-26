/- Copyright (c) 2026 Sil. Apache-2.0.
actual second common labels, their canonical character families,
and full norm/radical caps. No unrestricted Input source is used.
The independent first supplier identity is not asserted in this module.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedCanonicalEnvelope
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedOriginalNormCap
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedOriginalCoprimality
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedActualFamily
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCompleteCommon CenteredMomentActiveSource
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock
open CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open QRH.Record1252270103KernelMass
open MixedHeightEnergy MixedOriginalNormCap MixedOriginalCoprimality
open MixedCanonicalSource MixedSourceAssembly MixedLiteralAllocation MixedCompletedRows
open ReferencePrimeEnclosure
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Equality of the genuine common supports is a property of actual
label membership, independent of the shape of the source coefficients. -/
theorem active_equal_support (Q : Finset Id) (β : Id→ℂ) (p : ActiveLabel Q β) :
    CompletedGauss.primeSupport p.val.1=CompletedGauss.primeSupport p.val.2 := by
  obtain ⟨I,_hi,J,_hj,_hI,_hJ,_hβI,_hβJ,hleft,hright⟩ :=
    commonLabel_witnesses Q β p.val.1 p.val.2 p.property
  rw [←hleft,←hright]
  exact commonParts_equal_support I J

/-- Choose the actual Family for every common label before any Fourier
height, dyadic block, artificial divisor or retained row is selected.
Its inherited fields include the exact height presentation, keep
equivalence and nonzero-block conductor/row-width budget. -/
theorem exists_actual_families (η : Character) (Q : Finset Id) (β : Id→ℂ) :
    ∃τ : (p : ActiveLabel Q β)→Finset (CommonIndex p.val.1 p.val.2)→RayCharacter→Character,
      ∀p U,Family η p.val.1 p.val.2
        (commonLabels_supported (activeSource Q β) _ _ p.property).1
        (commonLabels_supported (activeSource Q β) _ _ p.property).2 U (τ p U) := by
  choose τ hτ using fun (p : ActiveLabel Q β) (U : Finset (CommonIndex p.val.1 p.val.2))=>
    exists_exceptional_family η p.val.1 p.val.2
      (commonLabels_supported (activeSource Q β) _ _ p.property).1
      (commonLabels_supported (activeSource Q β) _ _ p.property).2
      (active_equal_support Q β p) U
  exact ⟨τ,hτ⟩

section Original
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (S H : Finset PrimeIdeal) (pool : α→Finset Id)
  (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id) (ν : α→Id→ℂ)
  (W : ℝ→ℂ) (σ freq P : α→ℝ) (W₁ W₂ : ℝ→ℂ) (a b : ℝ)
  (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ)
local notation "Qsource" => finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
local notation "βoriginal" => originalColumn S H pool d hd R seed ν
  (fun i=>slotProfile W (σ i) (freq i)) P
  (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂

/-- Actual weighted common-label gates, including the full prime-power
norms and the original squarefree seed. The original prefix remains in
sourceNormCap; no radical is substituted for either full common norm. -/
theorem original_active_gates
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hP : ∀i,0<P i) (ha : 0<a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (hseed : Squarefree seed)
    (p : ActiveLabel Qsource βoriginal) :
    p.val.1≠0 ∧ p.val.2≠0 ∧
      CompletedGauss.primeSupport p.val.1=CompletedGauss.primeSupport p.val.2 ∧
      seed∣p.val.1 ∧ seed∣p.val.2 ∧
      (p.val.1.absNorm:ℝ)≤sourceNormCap P b (X₁*X₂) d ∧
      (p.val.2.absNorm:ℝ)≤sourceNormCap P b (X₁*X₂) d := by
  have hs := commonLabels_supported (activeSource Qsource βoriginal) _ _ p.property
  have hm := original_active_common_seed S H pool d hd R seed ν
    (fun i=>slotProfile W (σ i) (freq i)) P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂)
    b X₁ X₂ Y₁ Y₂ Qsource hseed p
  have hn := commonLabel_norm_bounds Qsource βoriginal (sourceNormCap P b (X₁*X₂) d)
    (fun I _ hi=>(MixedOriginalNormCap.original_column_norm S H pool d hd R seed ν W hWs
      σ freq P hP W₁ W₂ a b ha hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hXY I hi).2) p.val.1 p.val.2 p.property
  exact ⟨hs.1.1,hs.2.1,active_equal_support Qsource βoriginal p,hm.1,hm.2,hn⟩

end Original

/-- The divisor range in the actual physical window gives both full
norm caps required by the canonical envelope, and then its radical cap.
The hole-product cap is retained explicitly and is not replaced by an
unjustified uniformly bounded number of first-artificial support holes. -/
theorem active_mask_caps (Q : Finset Id) (β : Id→ℂ) (p : ActiveLabel Q β)
    (Hsource Z B BR BH : ℝ) (hHsource : 0≤Hsource) (hZ : 0<Z)
    (hcolumns : ∀I∈Q,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hsource : Hsource≤Z^B) (R L : Id) (hR : R≠0) (hL : Squarefree L)
    (hRN : (R.absNorm:ℝ)≤Z^BR)
    (hLN : (L.absNorm:ℝ)≤Hsource/(p.val.2.absNorm:ℝ)) (H : Finset PrimeIdeal)
    (hholes : ((∏I∈holes H,I).absNorm:ℝ)≤Z^BH) :
    (p.val.1.absNorm:ℝ)≤Z^B ∧ (p.val.2.absNorm:ℝ)≤Z^B ∧
      (L.absNorm:ℝ)≤Z^B ∧ Hsource/(p.val.2.absNorm:ℝ)≤Z^B ∧
      ((∏I∈QRH.Record1252270103KernelMass.primeSupport ((R*p.val.1)*L)∪holes H,I).absNorm:ℝ)
        ≤Z^((BR+B)+B+BH) ∧
      ((∏I∈QRH.Record1252270103KernelMass.primeSupport ((R*p.val.2)*L)∪holes H,I).absNorm:ℝ)
        ≤Z^((BR+B)+B+BH) := by
  have hs := commonLabels_supported (activeSource Q β) _ _ p.property
  have hn := commonLabel_norm_bounds Q β Hsource hcolumns p.val.1 p.val.2 p.property
  have hleft := hn.1.trans hsource
  have hright := hn.2.trans hsource
  have hnorm : (1:ℝ)≤(p.val.2.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hs.2.1)
  have hdiv := (div_le_self hHsource hnorm).trans hsource
  have hln := hLN.trans hdiv
  have hprod (G : Id) (hgn : (G.absNorm:ℝ)≤Z^B) :
      ((R*G).absNorm:ℝ)≤Z^(BR+B) := by
    rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
    exact mul_le_mul hRN hgn (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
  refine ⟨hleft,hright,hln,hdiv,?_,?_⟩
  · exact radical_union_cap (R*p.val.1) L (mul_ne_zero hR hs.1.1) hL.ne_zero H
      Z (BR+B) B BH hZ (hprod p.val.1 hleft) hln hholes
  · exact radical_union_cap (R*p.val.2) L (mul_ne_zero hR hs.2.1) hL.ne_zero H
      Z (BR+B) B BH hZ (hprod p.val.2 hright) hln hholes

/-- A coarse full conductor cap uniform in every actual physical block.
The sharper row/conductor ledger remains available from Family itself;
this bound is only for fixed polynomial admissibility parameters. -/
theorem active_family_conductor_cap
    (η : Character) (Q : Finset Id) (β : Id→ℂ) (p : ActiveLabel Q β)
    (U : Finset (CommonIndex p.val.1 p.val.2)) (τ : RayCharacter→Character)
    (hτ : Family η p.val.1 p.val.2
      (commonLabels_supported (activeSource Q β) _ _ p.property).1
      (commonLabels_supported (activeSource Q β) _ _ p.property).2 U τ)
    (Hsource : ℝ) (hcolumns : ∀I∈Q,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (t radius : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (hne : physicalBlock η t Q β p.val.1 p.val.2
      (commonLabels_supported (activeSource Q β) _ _ p.property).1
      (commonLabels_supported (activeSource Q β) _ _ p.property).2 U radius rows W K n≠0)
    (χ : RayCharacter) :
    ((τ χ).modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*Hsource := by
  have hn := commonLabel_norm_bounds Q β Hsource hcolumns p.val.1 p.val.2 p.property
  have hh := (hτ.physical_conductor_bounds (active_equal_support Q β p)
    t Q β radius rows W K hK n hne χ).1
  have hh' : ((τ χ).modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*p.val.1.absNorm := by
    exact_mod_cast hh
  exact hh'.trans (mul_le_mul_of_nonneg_left hn.1 (by positivity))

end
end Candidate.FourthPower.MixedActualFamily
