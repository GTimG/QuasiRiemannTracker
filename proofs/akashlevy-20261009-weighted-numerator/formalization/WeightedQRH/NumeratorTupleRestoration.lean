import WeightedQRH.NumeratorActualError
import OAI.NumberTheory.DirichletL.PrimeRows.WeightedTuple

/-! Exact finite error expansion of the original numerator, without division
by a local correction factor or changing any selected-prime zero extension. -/
noncomputable section
open scoped Classical BigOperators
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem quotient_free_finite_expansion {α : Type*} [DecidableEq α]
    (T : Finset α) (C : Finset α→ℂ) (G E H M : α→ℂ)
    (hrestore : ∀I⊆T,C I=C T*(∏i∈T\I,H i))
    (hlocal : ∀i∈T,G i=E i+H i*M i) :
    C T*(∏i∈T,G i)=∑I∈T.powerset,C I*(∏i∈I,E i)*(∏i∈T\I,M i) := by
  rw [Finset.prod_congr rfl hlocal,Finset.prod_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrestore I (Finset.mem_powerset.mp hI),Finset.prod_mul_distrib]
  ring

lemma markExclusions_mark (S : Finset (Ideal O)) (I J : Finset PrimeIdeal) :
    markExclusions (markExclusions S I) J=markExclusions S (I∪J) := by
  simp only [markExclusions,Finset.image_union,Finset.union_assoc]

theorem continuedCorrection_restore_indexed {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) (I : Finset (Fin K)) :
    continuedCorrection (markExclusions S (I.image P)) (markedSourceExclusions S hS (I.image P)) η u x w z=
      continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i∈Finset.univ\I,supportedCorrection η u (P i) x w z := by
  have hj : ∀Q∈(Finset.univ\I).image P,Q.val∉markExclusions S (I.image P) := by
    intro Q hQ
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hQ
    rw [mem_markExclusions]
    rintro (hs|hi)
    · exact hPS j hs
    · obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_sdiff.mp hj).2 (hP hkj ▸ hk)
  have heq : markExclusions (markExclusions S (I.image P)) ((Finset.univ\I).image P)=
      markExclusions S (Finset.univ.image P) := by
    rw [markExclusions_mark,←Finset.image_union,
      Finset.union_sdiff_of_subset (Finset.subset_univ I)]
  have hh := continuedCorrection_restore eps (markExclusions S (I.image P))
    (markedSourceExclusions S hS (I.image P)) (marked_firstTail eps S htail (I.image P))
    ((Finset.univ\I).image P) hj η u x w z hx hz hw hxw
  simpa only [heq,Finset.prod_image hP.injOn] using hh

def rawPhysicalSlot (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
    (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))

theorem rawPhysicalSlot_split (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    rawPhysicalSlot η u P hs x w z = rawErrorSlot η u P hs x w z +
      supportedCorrection η u P x w z*(-star (idealRowHom u.val P.val)) := by
  unfold rawPhysicalSlot rawErrorSlot
  ring

theorem actual_quotient_free_expansion {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
      (∏i,rawPhysicalSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)=
      ∑I∈Finset.univ.powerset,
        continuedCorrection (markExclusions S (I.image P))
          (markedSourceExclusions S hS (I.image P)) η u x w z*
        (∏i∈I,rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)*
        (∏i∈Finset.univ\I,(-star (idealRowHom u.val (P i).val))) := by
  apply quotient_free_finite_expansion Finset.univ
    (fun I=>continuedCorrection (markExclusions S (I.image P))
      (markedSourceExclusions S hS (I.image P)) η u x w z)
    (fun i=>rawPhysicalSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)
    (fun i=>rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)
    (fun i=>supportedCorrection η u (P i) x w z)
    (fun i=>-star (idealRowHom u.val (P i).val))
  · intro I hI
    exact continuedCorrection_restore_indexed eps S hS htail P hP hPS η u x w z hx hz hw hxw I
  · intro i hi
    exact rawPhysicalSlot_split η u (P i) _ x w z

def physicalSlotWeight (P : PrimeIdeal) (W : ℝ→ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)

def weightedErrorTuple {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  continuedCorrection (markExclusions S (I.image P))
    (markedSourceExclusions S hS (I.image P)) η u x w z*
    ∏i∈I,physicalSlotWeight (P i) (W i) (Y i) z*
      rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z

def physicalMainTuple {K : ℕ} (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→PrimeIdeal) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (z : ℂ) : ℂ :=
  ∏i∈Finset.univ\I,physicalSlotWeight (P i) (W i) (Y i) z*(-star (idealRowHom u.val (P i).val))

def numeratorFreeRowScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x

theorem actual_weighted_quotient_free_expansion {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
      (∏i,physicalSlotWeight (P i) (W i) (Y i) z*
        rawPhysicalSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)=
      ∑I∈Finset.univ.powerset,weightedErrorTuple S hS η u I P hPS W Y x w z*
        physicalMainTuple u I P W Y z := by
  apply quotient_free_finite_expansion Finset.univ
    (fun I=>continuedCorrection (markExclusions S (I.image P))
      (markedSourceExclusions S hS (I.image P)) η u x w z)
    (fun i=>physicalSlotWeight (P i) (W i) (Y i) z*
      rawPhysicalSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)
    (fun i=>physicalSlotWeight (P i) (W i) (Y i) z*
      rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)
    (fun i=>supportedCorrection η u (P i) x w z)
    (fun i=>physicalSlotWeight (P i) (W i) (Y i) z*(-star (idealRowHom u.val (P i).val)))
  · intro I hI
    exact continuedCorrection_restore_indexed eps S hS htail P hP hPS η u x w z hx hz hw hxw I
  · intro i hi
    rw [rawPhysicalSlot_split]
    ring

/-- Exact expansion of the actual calibrated tuple: the reciprocal and
principal factor are independent of w; all selected-prime factors are retained. -/
theorem calibratedTupleValue_error_subsets {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      numeratorFreeRowScalar S hS hmax η u x z*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      (∑I∈Finset.univ.powerset,weightedErrorTuple S hS η u I P hPS W Y x w z*
        physicalMainTuple u I P W Y z) := by
  rw [←actual_weighted_quotient_free_expansion eps S hS htail P hP hPS η u W Y x w z hx hz hw hxw,
    calibratedTupleValue_factor S hS hmax η u P hP hPS W Y x w z]
  unfold numeratorFreeRowScalar physicalSlotWeight rawPhysicalSlot
  ring

end WeightedQRH.Numerator
end
