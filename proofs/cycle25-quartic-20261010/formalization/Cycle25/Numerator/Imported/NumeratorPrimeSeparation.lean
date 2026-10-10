import Cycle25.Numerator.Imported.NumeratorTupleRestoration

/-! Separate the error-prime labels only after the exact quotient-free expansion. -/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem sum_split_slots {α : Type*} [Fintype α] [DecidableEq α] (β : α→Type*) [∀i,Fintype (β i)]
    (p : α→Prop) [DecidablePred p]
    (F : (∀i:{i//p i},β i.val)→ℂ) (g : ∀i:{i//¬p i},β i.val→ℂ) :
    (∑v:(∀i,β i),F (fun i=>v i.val)*(∏j:{i//¬p i},g j (v j.val)))=
      (∑v:(∀i:{i//p i},β i.val),F v)*(∏j:{i//¬p i},∑v:β j.val,g j v) := by
  calc
    _ = ∑v:((∀i:{i//p i},β i.val)×(∀i:{i//¬p i},β i.val)),F v.1*(∏j,g j (v.2 j)) :=
      Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd p β) _ _ (fun _=>rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul,←Fintype.prod_sum]

def partialErrorTuple {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (P : ∀i:I,T i.val) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
    (markedSourceExclusions S hS _) η u x w z*
    ∏i:I,physicalSlotWeight (P i).val (W i.val) (Y i.val) z*
      rawErrorSlot η u (P i).val
        (outside_prime_supported S hS.bad (P i).val (hT i.val _ (P i).property)) x w z

lemma restricted_tuple_image {K : ℕ} (I : Finset (Fin K)) (P : Fin K→PrimeIdeal) :
    Finset.univ.image (fun i:I=>P i.val)=I.image P := by
  ext Q
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i.val,i.property,hi⟩
  · rintro ⟨i,hi,heq⟩
    exact ⟨⟨i,hi⟩,heq⟩

theorem weightedErrorTuple_restrict {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (P : ∀i,T i) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    weightedErrorTuple S hS η u I (fun i=>(P i).val) (fun i=>hT i _ (P i).property) W Y x w z=
      partialErrorTuple S hS η u I T hT (fun i=>P i.val) W Y x w z := by
  unfold weightedErrorTuple partialErrorTuple
  simp only [restricted_tuple_image I (fun i=>(P i).val)]
  congr 1
  exact (Finset.prod_coe_sort I _).symm

theorem physicalMainTuple_restrict {K : ℕ} (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→PrimeIdeal) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (z : ℂ) :
    physicalMainTuple u I P W Y z=
      ∏j:{i:Fin K//i∉I},physicalSlotWeight (P j.val) (W j.val) (Y j.val) z*
        (-star (idealRowHom u.val (P j.val).val)) := by
  exact Finset.prod_subtype (Finset.univ\I) (by simp)
    (fun i=>physicalSlotWeight (P i) (W i) (Y i) z*(-star (idealRowHom u.val (P i).val)))

theorem weightedErrorTuple_main_sum {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    (∑P:(∀i,T i),weightedErrorTuple S hS η u I (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) W Y x w z*
      physicalMainTuple u I (fun i=>(P i).val) W Y z)=
      (∑P:(∀i:I,T i.val),partialErrorTuple S hS η u I T hT P W Y x w z)*
      (∏j:{i:Fin K//i∉I},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Y j.val) z*
        (-star (idealRowHom u.val P.val.val))) := by
  simp_rw [weightedErrorTuple_restrict,physicalMainTuple_restrict]
  convert! sum_split_slots (fun i=>T i) (fun i=>i∈I)
    (fun P=>partialErrorTuple S hS η u I T hT P W Y x w z)
    (fun j P=>physicalSlotWeight P.val (W j.val) (Y j.val) z*(-star (idealRowHom u.val P.val.val))) using 1
  congr 1
  apply Finset.sum_congr
  · ext P
    simp
  · intro P hP
    rfl

theorem calibrated_prime_error_slots_separate {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) W Y x w z)=
      numeratorFreeRowScalar S hS hmax η u x z*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        (∑I∈Finset.univ.powerset,
          (∑P:(∀i:I,T i.val),partialErrorTuple S hS η u I T hT P W Y x w z)*
          (∏j:{i:Fin K//i∉I},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Y j.val) z*
            (-star (idealRowHom u.val P.val.val)))) := by
  calc
    _ = ∑P:(∀i,T i),numeratorFreeRowScalar S hS hmax η u x z*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        (∑I∈Finset.univ.powerset,weightedErrorTuple S hS η u I (fun i=>(P i).val)
          (fun i=>hT i _ (P i).property) W Y x w z*
          physicalMainTuple u I (fun i=>(P i).val) W Y z) := by
      apply Finset.sum_congr rfl
      intro P hP
      exact calibratedTupleValue_error_subsets eps S hS htail hmax _ (hdis P) _ η u W Y x w z hx hz hw hxw
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro I hI
      exact weightedErrorTuple_main_sum S hS η u I T hT W Y x w z

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
