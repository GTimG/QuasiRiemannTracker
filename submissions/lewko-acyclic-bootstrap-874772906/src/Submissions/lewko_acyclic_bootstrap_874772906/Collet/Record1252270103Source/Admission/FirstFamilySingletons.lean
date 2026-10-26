/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full singleton families after actual common extraction are exact image subsets
of the original slots. Coefficients, lengths and all natural zeros are retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialSubsets
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredPositive
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilyLabels
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalBalancedColumns
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Reindex
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.InitialInput
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.FirstFamily
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentEnergyReindex CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile Record1252270103Second QRH.Record1252270103Low
local notation "O" => HeckeFamily.O
universe u v
variable {ι : Type u} [Fintype ι] {J : Type v} [Fintype J]

def childEmbedding (B : CenteredMomentAddedZeroUniform.Tuple ι) (f : J↪liveIndices B) : J↪ι :=
  ⟨fun j=>(f j).val,fun x y h=>f.injective (Subtype.ext h)⟩

theorem full_slots_image (η : Character) (m A z : O) (t : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (f : J↪ι) :
    (∏j,normalizedSlot η m A z (S (f j)) (β (f j)) t (P (f j)))=
      ∏i : slotRange f,normalizedSlot η m A z (S i) (β i) t (P i) :=
  (slotRangeEquiv f).prod_comp (fun i=>normalizedSlot η m A z (S i) (β i) t (P i))

/-- The literal common child's live slots are full original pools. -/
theorem child_slots_original (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (i : liveIndices B.val) :
    (child s C R B τ t).slots i=s.slots i.val ∧
    restoredSlotCoeff (child s C R B τ t) i=restoredSlotCoeff s i.val ∧
    (child s C R B τ t).P i=s.P i.val := ⟨rfl,rfl,rfl⟩

theorem child_full_slots_image (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (f : J↪liveIndices B.val)
    (η : Character) (m A z : O) (v : ℝ) :
    (∏j,normalizedSlot η m A z ((child s C R B τ t).slots (f j))
      (restoredSlotCoeff (child s C R B τ t) (f j)) v ((child s C R B τ t).P (f j)))=
    ∏i : slotRange (childEmbedding B.val f),normalizedSlot η m A z
      (s.slots i) (restoredSlotCoeff s i) v (s.P i) :=
  full_slots_image η m A z v s.slots (restoredSlotCoeff s) s.P (childEmbedding B.val f)

/-- An arbitrary full singleton representative family after TWO common
allocations is still one image subset of the original ambient type. -/
theorem second_child_full_slots_image (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (D : Ideal O)
    (E : actualAllocations (child s C R B τ t).pools D) (ψ : Character) (v : ℝ)
    (f : J↪liveIndices E.val) (η : Character) (m A z : O) (w : ℝ) :
    (∏j,normalizedSlot η m A z ((child (child s C R B τ t) D (R*C) E ψ v).slots (f j))
      (restoredSlotCoeff (child (child s C R B τ t) D (R*C) E ψ v) (f j)) w
      ((child (child s C R B τ t) D (R*C) E ψ v).P (f j)))=
    ∏i : slotRange (childEmbedding B.val (childEmbedding E.val f)),normalizedSlot η m A z
      (s.slots i) (restoredSlotCoeff s i) w (s.P i) :=
  full_slots_image η m A z w s.slots (restoredSlotCoeff s) s.P
    (childEmbedding B.val (childEmbedding E.val f))

/-- The HIGH live-budget definitions are the same literal column objects. -/
theorem balanced_columnIdeal_eq [DecidableEq ι] (reflected : Bool) (s : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : OAI.SevenEighths.Cycle61InitialMass.FirstColumnIndex
      (QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource s modifier R seed K Z ξ hK key)) :
    columnIdeal reflected s modifier R seed K Z ξ hK key j=
      QRH.Record1252270103Source.High.CoupledFirst.geometryColumnIdeal reflected s modifier R seed K Z ξ hK key j := rfl

theorem balanced_columnCharacter_eq [DecidableEq ι] (reflected : Bool) (s : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : OAI.SevenEighths.Cycle61InitialMass.FirstColumnIndex
      (QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource s modifier R seed K Z ξ hK key)) :
    columnCharacter reflected s modifier R seed K Z ξ hK key j=
      QRH.Record1252270103Source.High.CoupledFirst.geometryColumnCharacter reflected s modifier R seed K Z ξ hK key j := rfl

section Canonical
open ConcretePrimeRowBridge CenteredMomentNaturalFixedRaySource CenteredMomentSourceRectangle
open CenteredMomentFiniteProfileExceptional CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily
open scoped ContDiff
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal O)
variable (θ : ι→RayQuotient.Characters rayM H) (w v : ι→ℝ) (t : ℝ)
variable {a b : ℝ} (p : Profiles a b) (ha : 0<a)
variable (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hprod : Y₁*Y₂=X₁*X₂)
local notation "canonical" => initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
  p ha X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

/-- Any full singleton representative family after two literal common
allocations is exactly a canonical FULL original subfamily. The original
relative character, annular frequency, scale and natural zeros are retained. -/
theorem canonical_second_child_full_slots_image
    (C R : Ideal O) (B : actualAllocations (canonical).pools C)
    (τ : Character) (u : ℝ) (D : Ideal O)
    (E : actualAllocations (child (canonical) C R B τ u).pools D) (ψ : Character) (q : ℝ)
    (f : J↪liveIndices E.val) (χ : Character) (m A z : O) (height : ℝ) :
    (∏j,normalizedSlot χ m A z ((child (child (canonical) C R B τ u) D (R*C) E ψ q).slots (f j))
      (restoredSlotCoeff (child (child (canonical) C R B τ u) D (R*C) E ψ q) (f j)) height
      ((child (child (canonical) C R B τ u) D (R*C) E ψ q).P (f j)))=
    ∏i : slotRange (childEmbedding B.val (childEmbedding E.val f)),
      normalizedSlot χ m A z (primePool rayM H 2 (Z^(w i)))
        (fun I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (v i) I)
        height (Z^(w i)) :=
  second_child_full_slots_image (canonical) C R B τ u D E ψ q f χ m A z height

end Canonical

end
end QRH.Record1252270103Source.Admission.FirstFamily
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.full_slots_image
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.child_slots_original
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.child_full_slots_image
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.second_child_full_slots_image

#print axioms QRH.Record1252270103Source.Admission.FirstFamily.balanced_columnIdeal_eq
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.balanced_columnCharacter_eq

#print axioms QRH.Record1252270103Source.Admission.FirstFamily.canonical_second_child_full_slots_image
