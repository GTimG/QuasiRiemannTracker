/- Copyright (c) 2026 Sil. Apache-2.0.
Identify the literal Sum-indexed restricted coefficient with the natural
marked row. Finite domains, injectivity, ordinary punctures, character
zeros and all central square-root factors are retained exactly.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedArtificialRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedTupleRows
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowProfiles KernelRowExpansion
open MixedCommonRestriction MixedCommonAllocation MixedCommonCoefficient
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def pack (p : ι→Id) (n : Id×Id) : Tuple ι := Sum.elim p ![n.1,n.2]
def pools (p : ι→Finset Id) (A B : Finset Id) : (ι⊕Fin 2)→Finset Id := Sum.elim p ![A,B]

theorem pack_product (p : ι→Id) (n : Id×Id) :
    finiteTupleProduct (pack p n)=n.1*n.2*∏i,p i := by
  simp only [finiteTupleProduct,pack,Fintype.prod_sum_type,Fin.prod_univ_two,Sum.elim_inl,
    Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

theorem split_tuple_sum (p : ι→Finset Id) (A B : Finset Id) (f : Tuple ι→ℂ) :
    (∑v∈Fintype.piFinset (pools p A B),f v)=
      ∑q∈Fintype.piFinset p,∑n∈A×ˢB,f (pack q n) := by
  have he : Fintype.piFinset (pools p A B)=
      ((Fintype.piFinset p)×ˢ(A×ˢB)).image (fun x=>pack x.1 x.2) := by
    ext v
    constructor
    · intro hv
      have hh := Fintype.mem_piFinset.mp hv
      refine Finset.mem_image.mpr ⟨(fun i=>v (Sum.inl i),(v (Sum.inr 0),v (Sum.inr 1))),?_,?_⟩
      · exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun i=>hh (Sum.inl i)),
          Finset.mem_product.mpr ⟨hh (Sum.inr 0),hh (Sum.inr 1)⟩⟩
      · funext j
        cases j with
        | inl i=>rfl
        | inr j=>fin_cases j <;> rfl
    · intro hv
      obtain ⟨⟨q,n⟩,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hq,hn⟩ := Finset.mem_product.mp hx
      obtain ⟨hn₁,hn₂⟩ := Finset.mem_product.mp hn
      apply Fintype.mem_piFinset.mpr
      intro j
      cases j with
      | inl i=>exact Fintype.mem_piFinset.mp hq i
      | inr j=>fin_cases j;exact hn₁;exact hn₂
  rw [he,Finset.sum_image,Finset.sum_product]
  intro x hx y hy hxy
  apply Prod.ext
  · funext i;exact congrFun hxy (Sum.inl i)
  · exact Prod.ext (congrFun hxy (Sum.inr 0)) (congrFun hxy (Sum.inr 1))

theorem prime_tuple_sum (S : Finset PrimeIdeal) (f : (ι→Id)→ℂ) :
    (∑p∈Fintype.piFinset (fun _ : ι=>primeValues S),f p)=
      ∑slot : ι→S,f (fun i=>(slot i).val.val) := by
  symm
  apply Finset.sum_bij (fun slot _=>fun i=>(slot i).val.val)
  · intro slot hs
    exact Fintype.mem_piFinset.mpr (fun i=>Finset.mem_image.mpr ⟨(slot i).val,(slot i).property,rfl⟩)
  · intro s hs t ht he
    funext i
    exact Subtype.ext (Subtype.ext (congrFun he i))
  · intro p hp
    have he (i : ι) : ∃Q : PrimeIdeal,Q∈S ∧ Q.val=p i :=
      Finset.mem_image.mp (Fintype.mem_piFinset.mp hp i)
    choose Q hQ hval using he
    exact ⟨fun i=>⟨Q i,hQ i⟩,Finset.mem_univ _,funext hval⟩
  · intro s hs;rfl

theorem packed_weight (S H : Finset PrimeIdeal) (slot : ι→S) (n : Id×Id) :
    tupleWeight (punctureProduct S H) (pack (fun i=>(slot i).val.val) n)=
      if Function.Injective slot then restrictedValue S (KernelPunctureRows.augmented S H
        (KernelLabelledSlots.marked S slot)) n else 0 := by
  have hi : Function.Injective (fun i=>(slot i).val.val) ↔ Function.Injective slot := by
    constructor
    · intro h i j he;exact h (congrArg (fun x : S=>x.val.val) he)
    · intro h i j he;exact h (Subtype.ext (Subtype.ext he))
  have hr := labelled_restriction S H slot n.1 n.2
  change _ ↔ restriction (punctureProduct S H) (∏i,(slot i).val.val) n.1 n.2 at hr
  unfold tupleWeight tupleRestriction slotProduct
  simp only [pack,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [hi,←hr]
  unfold restrictedValue
  split_ifs <;> first | rfl | (exfalso;tauto)

def slotWeight (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ) (i : ι) (I : Id) : ℂ :=
  if I∈pool i then (Real.sqrt (P i):ℂ)⁻¹*β i I else 0

theorem natural_product_all (χ : Character) (S : Finset PrimeIdeal)
    (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ) (slot : ι→S) :
    (∏i,naturalCoefficients χ S pool β P i (slot i))=
      (∏i,slotWeight pool β P i (slot i).val.val)*idealCoeff χ (∏i,(slot i).val.val) := by
  rw [map_prod,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hp : (slot i).val.val∈pool i
  · simp only [naturalCoefficients,slotTerm,slotWeight,ite_eq_left hp]
    ring
  · simp only [naturalCoefficients,slotTerm,slotWeight,ite_eq_right hp,zero_mul]

def rectangleCoefficient (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (v : Tuple ι) : ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*pairProfile W₁ W₂ X₁ X₂ (v (Sum.inr 0),v (Sum.inr 1))*
    ∏i,slotWeight pool β P i (v (Sum.inl i))

/-- Equality before any norm: the same finite rectangle and marked
enclosure occur on both sides. Natural zeros are part of the character. -/
theorem normalized_character_sum (χ : Character) (S H : Finset PrimeIdeal)
    (pool : ι→Finset Id) (A B : Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) :
    (∑v∈Fintype.piFinset (pools (fun _ : ι=>primeValues S) A B),
      tupleWeight (punctureProduct S H) v*rectangleCoefficient pool β P W₁ W₂ X₁ X₂ v*
        idealCoeff χ (finiteTupleProduct v))=
      weightedSum (naturalCoefficients χ S pool β P)
        (fun slot=>normalizedRow χ (A×ˢB)
          (restrictedValue S (KernelPunctureRows.augmented S H (KernelLabelledSlots.marked S slot)))
          W₁ W₂ X₁ X₂) := by
  rw [split_tuple_sum,prime_tuple_sum]
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro slot hs
  simp_rw [packed_weight]
  by_cases hi : Function.Injective slot
  · simp only [hi,ite_true]
    rw [normalizedRow,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pack_product,map_mul,natural_product_all]
    unfold rectangleCoefficient pairCharacter
    simp only [pack,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  · simp only [hi,ite_false,zero_mul,Finset.sum_const_zero]

def centeredCoefficient (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (v : Tuple ι) : ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (pairProfile W₁ W₂ X₁ X₂ (d.1*v (Sum.inr 0),d.2*v (Sum.inr 1))-
      pairProfile W₁ W₂ Y₁ Y₂ (d.1*v (Sum.inr 0),d.2*v (Sum.inr 1)))*
    ∏i,slotWeight pool β P i (v (Sum.inl i))

/-- The same extracted normalization multiplies both sides of the
centered rectangle. Its square is the full paired divisor saving. -/
theorem centered_extraction (pool : ι→Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (hX : 0<X₁*X₂) (hXY : X₁*X₂=Y₁*Y₂) (hd : d.1≠0 ∧ d.2≠0) (v : Tuple ι) :
    centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d v=
      (Real.sqrt (pairNorm d):ℂ)⁻¹*
        (rectangleCoefficient pool β P W₁ W₂ (X₁/d.1.absNorm) (X₂/d.2.absNorm) v-
          rectangleCoefficient pool β P W₁ W₂ (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) v) := by
  have hx : (X₁/(d.1.absNorm:ℝ))*(X₂/(d.2.absNorm:ℝ))=
      (X₁*X₂)/pairNorm d := by unfold pairNorm;ring
  have hy : (Y₁/(d.1.absNorm:ℝ))*(Y₂/(d.2.absNorm:ℝ))=
      (X₁*X₂)/pairNorm d := by rw [hXY];unfold pairNorm;ring
  have hp (A B : ℝ) :
      pairProfile W₁ W₂ A B (d.1*v (Sum.inr 0),d.2*v (Sum.inr 1))=
        pairProfile W₁ W₂ (A/d.1.absNorm) (B/d.2.absNorm) (v (Sum.inr 0),v (Sum.inr 1)) :=
    profile_multiply W₁ W₂ A B d (v (Sum.inr 0),v (Sum.inr 1))
  unfold centeredCoefficient rectangleCoefficient
  rw [hp,hp,hx,hy,central_normalization (X₁*X₂) (pairNorm d) hX (pairNorm_pos hd.1 hd.2)]
  ring

open CenteredMomentSourceProfileMass CenteredMomentRectangle

/-- Centralize the literal inherited profile, including its common
puncture. The support premise is only an exact finite-pool identity. -/
theorem profile_centralization (pool : ι→Finset Id) (ν : ι→Id→ℂ)
    (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (R : Id)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (v : Tuple ι)
    (hs : ∀i,v (Sum.inl i)∉pool i→
      ν i (v (Sum.inl i))*Wslot i ((v (Sum.inl i)).absNorm/P i)=0) :
    ((Real.sqrt (X₁*X₂):ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹)*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v=
      (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
        centeredCoefficient pool (fun i I=>ν i I*Wslot i (I.absNorm/P i)) P
          W₁ W₂ X₁ X₂ Y₁ Y₂ d v := by
  have hp : (∏i,slotWeight pool (fun i I=>ν i I*Wslot i (I.absNorm/P i)) P i (v (Sum.inl i)))=
      (∏i,(Real.sqrt (P i):ℂ)⁻¹)*∏i,ν i (v (Sum.inl i))*Wslot i ((v (Sum.inl i)).absNorm/P i) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : v (Sum.inl i)∈pool i
    · simp only [slotWeight,ite_eq_left h]
    · simp only [slotWeight,ite_eq_right h,hs i h,mul_zero]
  unfold profileCoefficient centeredCoefficient
  rw [hp]
  simp only [one_dvd,ite_true,mul_one]
  unfold idealRectangle pairProfile
  ring

theorem centered_character_sum (χ : Character) (S H : Finset PrimeIdeal)
    (pool : ι→Finset Id) (A B : Finset Id) (β : ι→Id→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (hX : 0<X₁*X₂) (hXY : X₁*X₂=Y₁*Y₂) (hd : d.1≠0 ∧ d.2≠0) :
    (∑v∈Fintype.piFinset (pools (fun _ : ι=>primeValues S) A B),
      tupleWeight (punctureProduct S H) v*centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d v*
        idealCoeff χ (finiteTupleProduct v))=
      (Real.sqrt (pairNorm d):ℂ)⁻¹*
        (weightedSum (naturalCoefficients χ S pool β P)
          (fun slot=>normalizedRow χ (A×ˢB)
            (restrictedValue S (KernelPunctureRows.augmented S H (KernelLabelledSlots.marked S slot)))
            W₁ W₂ (X₁/d.1.absNorm) (X₂/d.2.absNorm))-
        weightedSum (naturalCoefficients χ S pool β P)
          (fun slot=>normalizedRow χ (A×ˢB)
            (restrictedValue S (KernelPunctureRows.augmented S H (KernelLabelledSlots.marked S slot)))
            W₁ W₂ (Y₁/d.1.absNorm) (Y₂/d.2.absNorm))) := by
  simp_rw [centered_extraction pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d hX hXY hd]
  rw [←normalized_character_sum,←normalized_character_sum,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem central_scalar_sq (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) :
    ‖(Real.sqrt (pairNorm d):ℂ)⁻¹‖^2=(pairNorm d)⁻¹ := by
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow,Real.sq_sqrt (pairNorm_pos hd.1 hd.2).le]

theorem common_character_mask (χ : Character) (R : Finset Id) (hR : ∀I∈R,Prime I) (I : Id) :
    (if IsCoprime I (∏J∈R,J) then (1:ℂ) else 0)*idealCoeff χ I=
      idealCoeff (χ.excludePrimes R hR) I := by
  rw [idealCoeff_excludePrimes,IsCoprime.prod_right_iff]
  split_ifs <;> simp only [one_mul,zero_mul]

/-- Exact conversion of the original punctured, centered profile to
the same natural character with its common finite prime exclusions.
No estimate for arbitrary replacement coefficients is used here. -/
theorem punctured_profile_character_sum (χ : Character) (S H : Finset PrimeIdeal)
    (R : Finset Id) (hR : ∀I∈R,Prime I)
    (pool : ι→Finset Id) (A B : Finset Id) (ν : ι→Id→ℂ)
    (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (hs : ∀i,∀I∈primeValues S,I∉pool i→ν i I*Wslot i (I.absNorm/P i)=0) :
    ((Real.sqrt (X₁*X₂):ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹)*
      (∑v∈Fintype.piFinset (pools (fun _ : ι=>primeValues S) A B),
        tupleWeight (punctureProduct S H) v*
          profileCoefficient (∏I∈R,I) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v*
          idealCoeff χ (finiteTupleProduct v))=
      ∑v∈Fintype.piFinset (pools (fun _ : ι=>primeValues S) A B),
        tupleWeight (punctureProduct S H) v*
          centeredCoefficient pool (fun i I=>ν i I*Wslot i (I.absNorm/P i)) P
            W₁ W₂ X₁ X₂ Y₁ Y₂ d v*
          idealCoeff (χ.excludePrimes R hR) (finiteTupleProduct v) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hpool (i : ι) : v (Sum.inl i)∈primeValues S :=
    Fintype.mem_piFinset.mp hv (Sum.inl i)
  have he := profile_centralization pool ν Wslot P (∏I∈R,I) W₁ W₂ X₁ X₂ Y₁ Y₂ d v
    (fun i=>hs i _ (hpool i))
  rw [←common_character_mask]
  calc
    _ = tupleWeight (punctureProduct S H) v*
        (((Real.sqrt (X₁*X₂):ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹)*
          profileCoefficient (∏I∈R,I) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v)*
        idealCoeff χ (finiteTupleProduct v) := by ring
    _ = _ := by rw [he];ring

end
end Candidate.FourthPower.MixedTupleRows
