/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Forced squarefree seed: extract every occurrence of its prime ideals.
The exponent cap permits repeated marked primes and overlapping slot pools. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Forcing

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonRadialData CenteredMomentSupport CenteredMomentForcing
open CenteredExceptionalCount Record1252270103Source QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O
local notation "coefficient" => QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι : Type*} [Fintype ι]
local instance restoredDivisorDecidable : DecidableEq ι := Classical.decEq _
local instance restoredDivisorSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def forcedPart (L I : Ideal O) : Ideal O := supportExtract I (primeSupport L)

theorem tuple_valuation_slot_cap (s : Input ι) (v : Tuple ι)
    (hv : v∈Fintype.piFinset s.pools)
    (hs : Squarefree (v (Sum.inr 0)*v (Sum.inr 1))) (Q : Ideal O) :
    valuation (finiteTupleProduct v) Q≤Fintype.card ι+1 := by
  have hp (i : ι) : Prime (v (Sum.inl i)) :=
    s.prime i _ (Fintype.mem_piFinset.mp hv (Sum.inl i))
  have hn := Finset.prod_ne_zero_iff.mpr (fun i (_ : i∈(Finset.univ : Finset ι))=>(hp i).ne_zero)
  have hmark : valuation (∏i,v (Sum.inl i)) Q≤Fintype.card ι := by
    rw [valuation_product Finset.univ _ (fun i _=>(hp i).ne_zero)]
    calc
      _≤∑_i : ι,1 := Finset.sum_le_sum (fun i _=>by rw [valuation_prime _ _ (hp i)];split_ifs <;> omega)
      _=Fintype.card ι := by simp
  have hord : valuation (v (Sum.inr 0)*v (Sum.inr 1)) Q≤1 :=
    Multiset.nodup_iff_count_le_one.mp
      ((squarefree_iff_nodup_normalizedFactors hs.ne_zero).mp hs) Q
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two]
  rw [valuation_mul _ _ _ hn hs.ne_zero]
  exact Nat.add_le_add hmark hord

theorem forcedPart_contains_seed (L I : Ideal O) (hL : L≠0) (hI : I≠0) (hLI : L∣I) :
    L∣forcedPart L I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hL (supportExtract_ne_zero I _)).mpr
  apply Multiset.le_iff_count.mpr
  intro Q
  have hle := Multiset.le_iff_count.mp
    ((dvd_iff_normalizedFactors_le_normalizedFactors hL hI).mp hLI) Q
  rw [supportExtract_count]
  split_ifs with hQ
  · exact hle
  · have hz : (normalizedFactors L).count Q=0 :=
      Multiset.count_eq_zero.mpr (fun hm=>hQ (Multiset.mem_toFinset.mpr hm))
    rw [hz]

theorem forcedPart_dvd_power (L I : Ideal O) (hL : Squarefree L) (n : ℕ)
    (hb : ∀Q,valuation I Q≤n) : forcedPart L I∣L^n := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (supportExtract_ne_zero I _)
    (pow_ne_zero n hL.ne_zero)).mpr
  apply Multiset.le_iff_count.mpr
  intro Q
  change valuation (forcedPart L I) Q≤valuation (L^n) Q
  rw [valuation_pow]
  change (normalizedFactors (supportExtract I (primeSupport L))).count Q≤_
  rw [supportExtract_count]
  split_ifs with hQ
  · have hval : valuation L Q=1 :=
      Multiset.nodup_iff_count_eq_one.mp
        ((squarefree_iff_nodup_normalizedFactors hL.ne_zero).mp hL)
          Q (Multiset.mem_toFinset.mp hQ)
    rw [hval,mul_one]
    exact hb Q
  · exact Nat.zero_le _

theorem forcedPart_support (L I : Ideal O) (hL : L≠0) (hI : I≠0) (hLI : L∣I) :
    primeSupport (forcedPart L I)=primeSupport L := by
  rw [forcedPart,supportExtract_support]
  apply Finset.inter_eq_right.mpr
  intro Q hQ
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors hL hI).mp hLI)
      (Multiset.mem_toFinset.mp hQ))

theorem forcedPart_norm_saving (L I : Ideal O) (hL : L≠0) (hI : I≠0) (hLI : L∣I) :
    1/(forcedPart L I).absNorm≤(1:ℝ)/L.absNorm := by
  have hC0 : (forcedPart L I).absNorm≠0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (supportExtract_ne_zero I _)
  have hL0 : (0:ℝ)<L.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL)
  have hn : L.absNorm≤(forcedPart L I).absNorm :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hC0)
      (map_dvd Ideal.absNorm (forcedPart_contains_seed L I hL hI hLI))
  exact one_div_le_one_div_of_le hL0 (Nat.cast_le.mpr hn)

/-- The source's actual nonzero summand supplies every premise. No disjoint
slot hypothesis is used: repeated marked primes cost the fixed slot cap. -/
theorem actual_forced_part_bounds (s : Input ι) (A₁ A₂ D R L I : Ideal O)
    (F : Ideal O→ℂ) (hL : Squarefree L)
    (hne : coefficient s (sourceModifier A₁ A₂ D F) R L I≠0) :
    L∣forcedPart L I ∧ forcedPart L I∣L^(Fintype.card ι+1) ∧
      IsCoprime (forcedPart L I) (supportResidual I (primeSupport L)) := by
  unfold QRH.Record1252270103Source.High.CoupledFirst.coefficient
    QRH.Record1252270103Source.High.CoupledFirst.tupleCoefficient finiteColumnCoefficient at hne
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  have hmod : sourceModifier A₁ A₂ D F v≠0 := left_ne_zero_of_mul hvn
  have hprof : profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L v≠0 :=
    right_ne_zero_of_mul hvn
  have hsf : Squarefree (v (Sum.inr 0)*v (Sum.inr 1)) := squarefree_residual_pair A₁ A₂ _ _
    (by simpa only [mul_assoc] using (sourceModifier_nonzero A₁ A₂ D F v hmod).2.1)
  have hseed : L∣finiteTupleProduct v := by
    by_contra hbad
    exact hprof (by simp [profileCoefficient,hbad])
  have hv0 : finiteTupleProduct v≠0 := by
    unfold finiteTupleProduct
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>s.pools_ne i _ (Fintype.mem_piFinset.mp hv i))
  rw [←he]
  exact ⟨forcedPart_contains_seed L _ hL.ne_zero hv0 hseed,
    forcedPart_dvd_power L _ hL _ (tuple_valuation_slot_cap s v hv hsf),
    extracted_residual_coprime _ _ _⟩

end
end OAI.SevenEighths.Record1252270103Second

#print axioms OAI.SevenEighths.Record1252270103Second.tuple_valuation_slot_cap
#print axioms OAI.SevenEighths.Record1252270103Second.actual_forced_part_bounds
