import WeightedQRH.NumeratorActualBin
import WeightedQRH.NumeratorFreeScalarBound
import OAI.NumberTheory.DirichletL.Detector.CentralClassPartition

/-! The literal finite row/error-subset collection after numerator bounds. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => HeckeFamily.O

theorem finite_array_weight_bound {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι→ℂ) (F : ι→κ→ℂ) (A : ℝ) (B : κ→ℝ) (hA : 0≤A)
    (ha : ∀i∈s,‖a i‖≤A) (hB : ∀j∈t,(∑i∈s,‖F i j‖)≤B j) :
    ‖∑i∈s,a i*(∑j∈t,F i j)‖≤A*(∑j∈t,B j) := by
  calc
    _ ≤ ∑i∈s,‖a i*(∑j∈t,F i j)‖ := norm_sum_le _ _
    _ ≤ ∑i∈s,A*(∑j∈t,‖F i j‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul (ha i hi) (norm_sum_le _ _) (norm_nonneg _) hA
    _ = A*(∑j∈t,∑i∈s,‖F i j‖) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hB) hA

theorem reconstructedDyadValue_norm_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (A : ℝ) (B : Finset (Fin K)→ℝ) (hA : 0≤A)
    (ha : ∀u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar S hS hmax η u x z‖≤A)
    (hb : ∀J∈Finset.univ.powerset,
      (∑u∈R,‖errorLabelNumerator S hS η u J T hT W Yp x z W1 Y*
        (∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
          (-star (idealRowHom u.val P.val.val)))‖)≤B J) :
    ‖reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y‖≤A*(∑J∈Finset.univ.powerset,B J) :=
  finite_array_weight_bound R Finset.univ.powerset _ _ A B hA ha hb


open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem reconstructedDyadValue_amplitude_partition {K : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (slots : Finset Slot) (U cap mesh : ℝ) (hm : 0 < mesh)
    (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) :
    reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y =
      ∑bin : BinLabel slots cap mesh,reconstructedDyadValue S hS hmax η
        (amplitudeRows R slots U cap mesh hm widths Q bin) T hT W Yp x z W1 Y := by
  unfold reconstructedDyadValue
  exact sum_amplitudeRows R slots U cap mesh hm widths Q _

theorem reconstructedDyadValue_class_uniform {K : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (slots : Finset Slot) (U cap mesh : ℝ) (hm : 0 < mesh) (hcap : cap≤1/2)
    (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) (A : ℝ) (hA : 0≤A)
    (hclass : ∀bin : BinLabel slots cap mesh,
      (amplitudeRows R slots U cap mesh hm widths Q bin).Nonempty →
      ‖reconstructedDyadValue S hS hmax η
        (amplitudeRows R slots U cap mesh hm widths Q bin) T hT W Yp x z W1 Y‖≤A) :
    ‖reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y‖≤
      (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^slots.card*A := by
  rw [reconstructedDyadValue_amplitude_partition S hS hmax η R T hT W Yp x z W1 Y
    slots U cap mesh hm widths Q]
  calc
    _ ≤ ∑bin : BinLabel slots cap mesh,A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro bin _
      by_cases hn : (amplitudeRows R slots U cap mesh hm widths Q bin).Nonempty
      · exact hclass bin hn
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he,reconstructedDyadValue,Finset.sum_empty,norm_zero] using hA
    _ = (Fintype.card (BinLabel slots cap mesh):ℝ)*A := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast HeckeDetectorClassBudget.bin_card_le slots cap mesh hcap hm


/-- Empty physical prime pools already make the original integrated numerator
zero; no arbitrary coefficient choice is made in this case. -/
theorem integratedDyadValue_zero_of_no_labels {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : SchwartzMap ℝ ℂ) (Y : ℝ)
    (hempty : ¬Nonempty (∀i,T i)) :
    FullWContour.integratedDyadValue S hS hmax η R T hT W Yp W1 Y x z = 0 := by
  letI : IsEmpty (∀i,T i) := not_nonempty_iff.mp hempty
  simp only [FullWContour.integratedDyadValue,Finset.univ_eq_empty,Finset.sum_empty,Finset.sum_const_zero]

end WeightedQRH.Numerator
