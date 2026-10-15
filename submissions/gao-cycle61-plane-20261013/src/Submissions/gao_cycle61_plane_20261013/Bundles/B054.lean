/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B050
import Submissions.gao_cycle61_plane_20261013.Bundles.B051
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.WeightedTuple

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorPrimeSum; sha256 1502c784706a8910e45abd7c199cc534de3693d21d61137b477f7b8a396126aa -/
section
                                                      
                                                                

/-! Summing actual positive error coefficient majorants over a physical prime slot. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem errorSize_nonneg (u : FreeRow) (P : ProbePhysical.PrimeIdeal) :
    0 ≤ errorSize u P := by
  unfold errorSize
  split_ifs <;> positivity

theorem error_coefficient_slot_sum (epsilon c d B : ℝ) (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
      (Y : ℝ), 1 ≤ Y → ∀ (W : ℝ → ℂ), Function.support W ⊆ Set.Icc c d →
      (∀ y, ‖W y‖ ≤ B) → ∀ z : ℂ, z.re = 17 / 50 →
      (∑ P : T, ‖W ((P.val.val.absNorm : ℝ) / Y) * (P.val.val.absNorm : ℂ)^(z-1)‖ *
        errorSize u P.val) ≤ C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon *
          Y^(-(4 / 25 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed
    epsilon c d (-(4 / 25 : ℝ)) 1 B 1 hepsilon hc hd (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro u T Y hY W hWS hWB z hz
  let f : T → Ideal O := fun P => P.val.val
  have hf : Function.Injective f := fun P Q h => Subtype.ext (Subtype.ext h)
  let E : T → ℂ := fun P => (errorSize u P.val : ℂ)
  let G : T → ℂ := fun P => ((f P).absNorm : ℂ)^(1 / 2 : ℂ) * E P
  have hnorm (P : T) : ‖G P‖ ≤ 1 *
      (if f P ∣ Ideal.span {u.val} then ((f P).absNorm : ℝ)^(1 : ℝ) else 1) := by
    have hQ0 : (0 : ℝ) < (f P).absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero)
    have hQ1 : (1 : ℝ) ≤ (f P).absNorm := by
      exact_mod_cast Nat.succ_le_of_lt (show 0 < (f P).absNorm from by exact_mod_cast hQ0)
    have hn : ‖((f P).absNorm : ℂ)^(1 / 2 : ℂ)‖ = ((f P).absNorm : ℝ)^(1 / 2 : ℝ) := by
      rw [show ((f P).absNorm : ℂ) = (((f P).absNorm : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
      norm_num
    dsimp only [G,E]
    rw [norm_mul,hn,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (errorSize_nonneg u P.val)]
    change ((f P).absNorm : ℝ)^(1 / 2 : ℝ) *
      (if f P ∣ Ideal.span {u.val} then ((f P).absNorm : ℝ)^(1 / 2 : ℝ)
       else ((f P).absNorm : ℝ)^(-(51 / 100 : ℝ))) ≤ _
    by_cases hdiv : f P ∣ Ideal.span {u.val}
    · rw [ite_eq_left hdiv,ite_eq_left hdiv,one_mul,←Real.rpow_add hQ0]
      norm_num
    · rw [ite_eq_right hdiv,ite_eq_right hdiv,one_mul,←Real.rpow_add hQ0]
      exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num :
        (1 / 2 : ℝ) + -(51 / 100 : ℝ) ≤ 0)).trans_eq (Real.rpow_zero _)
  have hb := hbound f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _ => P.val.property.ne_zero) W hWS hWB G (fun P _ => hnorm P)
    (z - 1 / 2) (by simp only [Complex.sub_re]; rw [hz]; norm_num)
  have heq (P : T) :
      W (((f P).absNorm : ℝ) / Y) * ((f P).absNorm : ℂ)^((z - 1 / 2) - 1) * G P =
      W (((f P).absNorm : ℝ) / Y) * ((f P).absNorm : ℂ)^(z - 1) * E P := by
    have hn : ((f P).absNorm : ℂ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero
    dsimp only [G]
    rw [←mul_assoc,mul_assoc (W _),←Complex.cpow_add _ _ hn]
    rw [show (z - 1 / 2) - 1 + 1 / 2 = z - 1 by ring]
  simp only [heq,norm_mul,E,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (errorSize_nonneg u _)] at hb
  simpa only [f,norm_mul] using hb

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorPrimeSum -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorTupleRestoration; sha256 51758d9c1c2fe0e5d07c8400505263b0b180aba217f64cb17a6c194440f2c3dc -/
section
                                                      
                                                          

/-! Exact finite error expansion of the original numerator, without division
by a local correction factor or changing any selected-prime zero extension. -/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Weighted.Numerator
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

lemma markExclusions_mark (S : Finset (Ideal O)) (I J : Finset ProbePhysical.PrimeIdeal) :
    markExclusions (markExclusions S I) J=markExclusions S (I∪J) := by
  simp only [markExclusions,Finset.image_union,Finset.union_assoc]

theorem continuedCorrection_restore_indexed {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
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

def rawPhysicalSlot (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
    (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))

theorem rawPhysicalSlot_split (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    rawPhysicalSlot η u P hs x w z = rawErrorSlot η u P hs x w z +
      supportedCorrection η u P x w z*(-star (idealRowHom u.val P.val)) := by
  unfold rawPhysicalSlot rawErrorSlot
  ring

theorem actual_quotient_free_expansion {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
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

def physicalSlotWeight (P : ProbePhysical.PrimeIdeal) (W : ℝ→ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)

def weightedErrorTuple {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  continuedCorrection (markExclusions S (I.image P))
    (markedSourceExclusions S hS (I.image P)) η u x w z*
    ∏i∈I,physicalSlotWeight (P i) (W i) (Y i) z*
      rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z

def physicalMainTuple {K : ℕ} (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→ProbePhysical.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (z : ℂ) : ℂ :=
  ∏i∈Finset.univ\I,physicalSlotWeight (P i) (W i) (Y i) z*(-star (idealRowHom u.val (P i).val))

def numeratorFreeRowScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x

theorem actual_weighted_quotient_free_expansion {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
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
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
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

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorTupleRestoration -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorPrimeSeparation; sha256 ebcb47bd9280bf8d33ede9b1efdbcb820ab47e436ce066205dc484948073d00a -/
section
                                                           

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
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (P : ∀i:I,T i.val) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
    (markedSourceExclusions S hS _) η u x w z*
    ∏i:I,physicalSlotWeight (P i).val (W i.val) (Y i.val) z*
      rawErrorSlot η u (P i).val
        (outside_prime_supported S hS.bad (P i).val (hT i.val _ (P i).property)) x w z

lemma restricted_tuple_image {K : ℕ} (I : Finset (Fin K)) (P : Fin K→ProbePhysical.PrimeIdeal) :
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
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (P : ∀i,T i) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    weightedErrorTuple S hS η u I (fun i=>(P i).val) (fun i=>hT i _ (P i).property) W Y x w z=
      partialErrorTuple S hS η u I T hT (fun i=>P i.val) W Y x w z := by
  unfold weightedErrorTuple partialErrorTuple
  simp only [restricted_tuple_image I (fun i=>(P i).val)]
  congr 1
  exact (Finset.prod_coe_sort I _).symm

theorem physicalMainTuple_restrict {K : ℕ} (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→ProbePhysical.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (z : ℂ) :
    physicalMainTuple u I P W Y z=
      ∏j:{i:Fin K//i∉I},physicalSlotWeight (P j.val) (W j.val) (Y j.val) z*
        (-star (idealRowHom u.val (P j.val).val)) := by
  exact Finset.prod_subtype (Finset.univ\I) (by simp)
    (fun i=>physicalSlotWeight (P i) (W i) (Y i) z*(-star (idealRowHom u.val (P i).val)))

theorem weightedErrorTuple_main_sum {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
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
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
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

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorPrimeSeparation -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorLabels; sha256 a4ab9d58b61d3ba6e3374f170a21bd828df344255d5cf9e4c8759981b38a8fa9 -/
section
                                                        
                                                      
                                                          

/-! Summing positive coefficient masses over all independent error-prime labels. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

theorem finite_label_damped_mass {ι : Type*} [Fintype ι] {α : ι → Type*}
    (A : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ) (hN : ∀ i e, 0 < N i e)
    (weight : ι → ℂ) (B : ι → ℝ) (L rho M : ℝ)
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L*N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L*N i e)^rho) ≤ M*B i) :
    Summable (fun e : Σ i, α i => ‖weight e.1 * A e.1 e.2‖ *
      (N e.1 e.2)^(-(1 / 2 : ℝ)) * max 1 (L*N e.1 e.2)^rho) ∧
    (∑' e : Σ i, α i, ‖weight e.1 * A e.1 e.2‖ *
      (N e.1 e.2)^(-(1 / 2 : ℝ)) * max 1 (L*N e.1 e.2)^rho) ≤
      M * ∑ i, ‖weight i‖*B i := by
  have he (i : ι) (e : α i) : ‖weight i*A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L*N i e)^rho = ‖weight i‖ *
      (‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L*N i e)^rho) := by
    rw [norm_mul]
    ring
  have hfs (i : ι) : Summable (fun e => ‖weight i*A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L*N i e)^rho) := by
    simp_rw [he]
    exact (hs i).mul_left _
  have hsum : Summable (fun e : Σ i, α i => ‖weight e.1 * A e.1 e.2‖ *
      (N e.1 e.2)^(-(1 / 2 : ℝ)) * max 1 (L*N e.1 e.2)^rho) := by
    apply (summable_sigma_of_nonneg (fun e => by have := hN e.1 e.2; positivity)).mpr
    exact ⟨hfs,(hasSum_fintype _).summable⟩
  refine ⟨hsum,?_⟩
  rw [hsum.tsum_sigma,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simp_rw [he,tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left (hm i) (norm_nonneg _)).trans_eq (by ring)

theorem errorProductSize_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : FreeRow) (P : ι → ProbePhysical.PrimeIdeal) (hP : Function.Injective P) :
    errorProductSize u (Finset.univ.image P) = ∏ i, 2880 * errorSize u (P i) := by
  unfold errorProductSize
  calc
    _ = ∏ Q ∈ Finset.univ.image P, 2880 * errorSize u Q :=
      Finset.prod_coe_sort _ _
    _ = _ := Finset.prod_image hP.injOn

theorem error_label_mass_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
    (weight : ∀ i, T i → ℂ) :
    (∑ P : ∀ i, T i, ‖∏ i, weight i (P i)‖ *
      errorProductSize u (Finset.univ.image (fun i => (P i).val))) =
      ∏ i, ∑ P : T i, 2880 * ‖weight i P‖ * errorSize u P.val := by
  calc
    _ = ∑ P : ∀ i, T i, ∏ i, 2880 * ‖weight i (P i)‖ * errorSize u (P i).val := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [norm_prod,errorProductSize_image u _ (hdis P),←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ = _ := (Fintype.prod_sum (fun i => fun P : T i =>
      2880 * ‖weight i P‖ * errorSize u P.val)).symm

theorem error_label_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
    (weight : ∀ i, T i → ℂ) (B : ι → ℝ)
    (hm : ∀ i, (∑ P : T i, ‖weight i P‖ * errorSize u P.val) ≤ B i) :
    (∑ P : ∀ i, T i, ‖∏ i, weight i (P i)‖ *
      errorProductSize u (Finset.univ.image (fun i => (P i).val))) ≤
      ∏ i, 2880 * B i := by
  rw [error_label_mass_factor u T hdis weight]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg (fun P hP => mul_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg _)) (errorSize_nonneg u P.val))
  · intro i hi
    calc
      _ = 2880 * ∑ P : T i, ‖weight i P‖ * errorSize u P.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P hP
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hm i) (by norm_num)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorErrorLabels -/
