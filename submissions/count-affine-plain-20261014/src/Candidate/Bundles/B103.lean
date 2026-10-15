/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B101
import Candidate.Bundles.B102
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeScale
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ChildRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RankinRadical

/- BEGIN ORIGINAL Cycle61.Moment.CanonicalFirstDictionary; sha256 db9bc362bdf3fdaf847fb295129780248526a12b29a1e7966123eb20343a29aa -/
section
                                          
                                                    
                                                   

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstColumns CenteredMomentFixedRay
open CenteredMomentChildRows
open RayFourExpansion
local notation "O" => HeckeFamily.O

/-- The table varies with live labels; the sixteen-character index set does not. -/
def firstPhaseTable (C D : Ideal O) (t : ActiveIndex C D → ℕ) (r : RayRing) : ℂ :=
  ∏ P, (QuadraticAllOddCRT.quadraticRaySign
    (ActualEisensteinCoordinates.residue (firstSignedPrime C D P))
    (QuadraticGaussRay.residueQuotientFour r) : ℂ)^(t P)

theorem firstPhaseTable_mk (C D : Ideal O) (t : ActiveIndex C D → ℕ) (n : O) :
    firstPhaseTable C D t (Ideal.Quotient.mk _ n) =
      ∏ P, sexticReciprocityPhase (firstSignedPrime C D P) n^(t P) := by
  simp only [firstPhaseTable, sexticReciprocityPhase,
    QuadraticGaussRay.residueQuotientFour_mk]

theorem firstPhaseTable_norm (C D : Ideal O) (t : ActiveIndex C D → ℕ) (r : RayRing) :
    ‖firstPhaseTable C D t r‖ ≤ 1 := by
  have hsign (a b : EisensteinEPrimaryPhase.Coord) :
      ‖(QuadraticAllOddCRT.quadraticRaySign a b : ℂ)‖ ≤ 1 := by
    unfold QuadraticAllOddCRT.quadraticRaySign
    split_ifs <;> norm_num
  rw [firstPhaseTable, norm_prod]
  calc
    _ ≤ ∏ P : ActiveIndex C D, (1:ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hsign _ _)
    _ = 1 := by simp only [Finset.prod_const_one]

theorem actual_first_phase_dictionary (C D : Ideal O) (t : ActiveIndex C D → ℕ)
    (n : O) (hn : CanonicalQuadraticSieve.Supported (Ideal.span {n})) :
    (∏ P, sexticReciprocityPhase (firstSignedPrime C D P) n^(t P)) =
      ∑ χ : RayCharacter, phaseCoeff (firstPhaseTable C D t) χ * rayCharacter χ n := by
  have hh := phase_expansion (firstPhaseTable C D t) n
  simpa only [supported_rayMask n hn, one_mul, firstPhaseTable_mk] using hh

theorem actual_first_phase_dictionary_mass (C D : Ideal O) (t : ActiveIndex C D → ℕ) :
    (∑ χ : RayCharacter, ‖phaseCoeff (firstPhaseTable C D t) χ‖) ≤ 16 := by
  simpa only [mul_one] using phaseCoeff_sum_norm_le (firstPhaseTable C D t) 1
    (fun _ => firstPhaseTable_norm C D t _)

theorem actual_first_left_fixed_dictionary (η : Character) (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    ∃ u : Oˣ, ∀ e n : O, CanonicalQuadraticSieve.Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      elementCoeff η n * leftCoefficient e (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      ∑ χ : RayCharacter, phaseCoeff (firstPhaseTable C D (activeExponent C D)) χ *
        elementCoeff (childCharacter η χ) n *
        (∏ P ∈ firstLeftCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom ((u:O)*e*firstLeftUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_left_signed C D hC
  refine ⟨u, ?_⟩
  intro e n hn hnp
  rw [hu e n hn hnp, actual_first_phase_dictionary C D (activeExponent C D) n hn,
    idealRowHom_argument_mul, actual_first_left_holes C D n hn]
  simp only [Finset.mul_sum, Finset.sum_mul, childCharacter_primary η _ n hn hnp,
    idealRowHom_argument_mul]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem actual_first_right_fixed_dictionary (η : Character) (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    ∃ u : Oˣ, ∀ e n : O, CanonicalQuadraticSieve.Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      elementCoeff η n * rightCoefficient e (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      ∑ χ : RayCharacter,
        phaseCoeff (firstPhaseTable C D (fun P => 6-activeExponent C D P)) χ *
        elementCoeff (childCharacter η χ) n *
        (∏ P ∈ firstRightCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom ((u:O)*e*firstRightUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_right_signed C D hC
  refine ⟨u, ?_⟩
  intro e n hn hnp
  rw [hu e n hn hnp,
    actual_first_phase_dictionary C D (fun P => 6-activeExponent C D P) n hn,
    idealRowHom_argument_mul, actual_first_right_holes C D n hn]
  simp only [Finset.mul_sum, Finset.sum_mul, childCharacter_primary η _ n hn hnp,
    idealRowHom_argument_mul]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem first_dictionary_modulus_bound (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus.absNorm ≤
      η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm := by
  simpa only [childCharacter, primaryRayCharacter_modulus] using
    HeckePrimeScale.product_modulus_bound η (primaryRayCharacter χ)

/-- The live parent row remains a numerator. It does not become an
additional member of the fixed dictionary. -/
theorem actual_first_left_original_row (η : Character) (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    ∃ u : Oˣ, ∀ u₀ e n : O, CanonicalQuadraticSieve.Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      (elementCoeff η n * idealRowHom u₀ (Ideal.span {n})) *
        leftCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      ∑ χ : RayCharacter, phaseCoeff (firstPhaseTable C D (activeExponent C D)) χ *
        elementCoeff (childCharacter η χ) n *
        (∏ P ∈ firstLeftCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom (u₀*(u:O)*e*firstLeftUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_left_fixed_dictionary η C D hC
  refine ⟨u, ?_⟩
  intro u₀ e n hn hnp
  have hh := congrArg (fun x : ℂ => idealRowHom u₀ (Ideal.span {n})*x) (hu e n hn hnp)
  simp only [Finset.mul_sum, idealRowHom_argument_mul] at hh ⊢
  convert hh using 1
  · ring
  · apply Finset.sum_congr rfl
    intro χ _
    ring

theorem actual_first_right_original_row (η : Character) (C D : Ideal O)
    (hC : CanonicalQuadraticSieve.Supported C) :
    ∃ u : Oˣ, ∀ u₀ e n : O, CanonicalQuadraticSieve.Supported (Ideal.span {n}) →
      ConcretePrimeRowBridge.goodLambda^2 ∣ n-1 →
      (elementCoeff η n * idealRowHom u₀ (Ideal.span {n})) *
        rightCoefficient e (activeConductor C D)
          (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      ∑ χ : RayCharacter,
        phaseCoeff (firstPhaseTable C D (fun P => 6-activeExponent C D P)) χ *
        elementCoeff (childCharacter η χ) n *
        (∏ P ∈ firstRightCancelled C D,
          if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
        idealRowHom (u₀*(u:O)*e*firstRightUncancelled C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_right_fixed_dictionary η C D hC
  refine ⟨u, ?_⟩
  intro u₀ e n hn hnp
  have hh := congrArg (fun x : ℂ => idealRowHom u₀ (Ideal.span {n})*x) (hu e n hn hnp)
  simp only [Finset.mul_sum, idealRowHom_argument_mul] at hh ⊢
  convert hh using 1
  · ring
  · apply Finset.sum_congr rfl
    intro χ _
    ring

#print axioms actual_first_phase_dictionary
#print axioms actual_first_phase_dictionary_mass
#print axioms actual_first_left_fixed_dictionary
#print axioms actual_first_right_fixed_dictionary
#print axioms first_dictionary_modulus_bound
#print axioms actual_first_left_original_row
#print axioms actual_first_right_original_row
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.CanonicalFirstDictionary -/

/- BEGIN ORIGINAL Cycle61.Moment.ActualRowDensity; sha256 6584fc0f277b0918c47ccdddda87de6da8bb1c5ded687b3b4562545c5960077e -/
section
                                              
                                           
                                                                     

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentChildRows CenteredMomentFixedRay
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily LocalMoment
open ProbePhysical
open RayFourExpansion CanonicalRowCompletion
open ConcretePrimeRowBridge HeckeRowClosure
local notation "O" => HeckeFamily.O

def secondFixedDictionary (η : Character) (j : RayCharacter × RayCharacter) : Character :=
  childCharacter (childCharacter η j.1) j.2

theorem second_fixed_dictionary_modulus_bound (η : Character)
    (j : RayCharacter × RayCharacter) :
    (secondFixedDictionary η j).modulus.absNorm ≤
      η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm^2 := by
  exact (first_dictionary_modulus_bound (childCharacter η j.1) j.2).trans
    (by
      calc
        _ ≤ (η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
            (Ideal.span {(12:O)}).absNorm :=
          Nat.mul_le_mul_right _ (first_dictionary_modulus_bound η j.1)
        _ = _ := by ring)

def actualMaskedRowFamily (η : Character)
    (puncture : (RayCharacter × RayCharacter) → NonzeroFrequency → Ideal O)
    (j : RayCharacter × RayCharacter) (w : NonzeroFrequency) : Character :=
  excluded (naturalRow (secondFixedDictionary η j) w.val w.property).character (puncture j w)

theorem actual_masked_row_ideal (η : Character)
    (puncture : (RayCharacter × RayCharacter) → NonzeroFrequency → Ideal O)
    (j : RayCharacter × RayCharacter) (w : NonzeroFrequency)
    (hp : puncture j w ≠ 0) (I : Ideal O) :
    idealCoeff (actualMaskedRowFamily η puncture j w) I =
      idealCoeff (secondFixedDictionary η j) I *
        idealRowHom ((fixedBadMask*idealGenerator (puncture j w))^6*w.val) I :=
  (naturalRow (secondFixedDictionary η j) w.val w.property).masked_ideal _ hp I

theorem actual_masked_row_element (η : Character)
    (puncture : (RayCharacter × RayCharacter) → NonzeroFrequency → Ideal O)
    (j : RayCharacter × RayCharacter) (w : NonzeroFrequency)
    (hp : puncture j w ≠ 0) (n : O) :
    elementCoeff (actualMaskedRowFamily η puncture j w) n =
      rowTwist (elementHom (secondFixedDictionary η j))
        (fixedBadMask*idealGenerator (puncture j w)) 1 w.val n :=
  (naturalRow (secondFixedDictionary η j) w.val w.property).masked_element _ hp n

/-- Both finite ray expansions are fixed before the live first and second labels.
The Euler puncture is paid by deletion, rather than by a conductor bound. -/
theorem actual_signed_dictionary_density (η : Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ puncture : (RayCharacter × RayCharacter) → NonzeroFrequency → Ideal O,
      ∀ reverse : (RayCharacter × RayCharacter) → Bool,
      ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ w ∈ rows, rawFrequencyNorm w ≤ H ∧
        maskedActualZeroRow (actualMaskedRowFamily η puncture) reverse a T w) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hbound⟩ := fixed_natural_dictionary_masked_raw_density
    (secondFixedDictionary η) loss hloss
  refine ⟨J,C,hC,?_⟩
  intro puncture reverse a T ha ha' hT H hH rows hrows
  apply hbound (actualMaskedRowFamily η puncture) _ reverse a T ha ha' hT H hH rows hrows
  intro j w I
  exact excludePrimes_mask _ _ (support_prime (puncture j w)) I

#print axioms second_fixed_dictionary_modulus_bound
#print axioms actual_masked_row_ideal
#print axioms actual_masked_row_element
#print axioms actual_signed_dictionary_density
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.ActualRowDensity -/

/- BEGIN ORIGINAL Cycle61.Moment.CanonicalFirstNorm; sha256 a438ee466d15eec0c09dab13305cfa102f13b16d625bc5f6f15ff9d6cd0066c0 -/
section
                                          

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion ActualEisensteinCubic CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentActive
local notation "O" => HeckeFamily.O

theorem powered_numerator_norm {ι : Type*} (S : Finset ι) (p : ι → O) (t : ι → ℕ) :
    (Ideal.span {∏ i ∈ S, p i^(t i)}).absNorm =
      ∏ i ∈ S, (Ideal.span {p i}).absNorm^(t i) := by
  change Ideal.absNorm (principalIdealHom (∏ i ∈ S, p i^(t i))) = _
  rw [map_prod]
  simp only [map_prod, map_pow]
  rfl

theorem powered_numerator_norm_bound {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (k : ℕ)
    (hp : ∀ i ∈ S, Supported (Ideal.span {p i})) (ht : ∀ i ∈ S, t i ≤ k) :
    (Ideal.span {∏ i ∈ S, p i^(t i)}).absNorm ≤
      (∏ i ∈ S, (Ideal.span {p i}).absNorm)^k := by
  rw [powered_numerator_norm, ← Finset.prod_pow]
  apply Finset.prod_le_prod
  intro i hi
  exact pow_le_pow_right'
    (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i hi).1))
    (ht i hi)

def firstLeftRadical (C D : Ideal O) : Ideal O :=
  ∏ P ∈ Finset.univ.filter (fun P => 1+activeExponent C D P ≠ 6), activePrime C D P

def firstRightRadical (C D : Ideal O) : Ideal O :=
  ∏ P ∈ Finset.univ.filter (fun P => 7-activeExponent C D P ≠ 6), activePrime C D P

def firstLeftCancelledRadical (C D : Ideal O) : Ideal O :=
  ∏ P ∈ firstLeftCancelled C D, activePrime C D P

def firstRightCancelledRadical (C D : Ideal O) : Ideal O :=
  ∏ P ∈ firstRightCancelled C D, activePrime C D P

theorem actual_first_left_norm (C D : Ideal O) (hC : Supported C) :
    (Ideal.span {firstLeftUncancelled C D}).absNorm ≤ (firstLeftRadical C D).absNorm^5 := by
  have hh := powered_numerator_norm_bound
    (Finset.univ.filter (fun P => 1+activeExponent C D P ≠ 6))
    (firstSignedPrime C D) (fun P => 1+activeExponent C D P) 5
    (fun P _ => firstSignedPrime_supported C D hC P) (by
      intro P hP
      have he := (Finset.mem_filter.mp hP).2
      have h6 : activeExponent C D P < 6 := netExponent_lt_six _ _
      omega)
  simpa only [firstLeftUncancelled, firstLeftRadical, map_prod,
    firstSignedPrime_span C D hC] using hh

theorem actual_first_right_norm (C D : Ideal O) (hC : Supported C) :
    (Ideal.span {firstRightUncancelled C D}).absNorm ≤ (firstRightRadical C D).absNorm^5 := by
  have hh := powered_numerator_norm_bound
    (Finset.univ.filter (fun P => 7-activeExponent C D P ≠ 6))
    (firstSignedPrime C D) (fun P => 7-activeExponent C D P) 5
    (fun P _ => firstSignedPrime_supported C D hC P) (by
      intro P hP
      have he := (Finset.mem_filter.mp hP).2
      have hp : 0 < activeExponent C D P := Nat.pos_of_ne_zero (netExponent_ne_zero _ _ _ P)
      omega)
  simpa only [firstRightUncancelled, firstRightRadical, map_prod,
    firstSignedPrime_span C D hC] using hh

theorem actual_first_left_radical_split (C D : Ideal O) :
    Ideal.span {activeConductor C D} =
      firstLeftCancelledRadical C D * firstLeftRadical C D := by
  rw [activeConductor, span_finitePrimeModulus]
  exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun P => 1+activeExponent C D P = 6) (activePrime C D)).symm

theorem actual_first_right_radical_split (C D : Ideal O) :
    Ideal.span {activeConductor C D} =
      firstRightCancelledRadical C D * firstRightRadical C D := by
  rw [activeConductor, span_finitePrimeModulus]
  exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun P => 7-activeExponent C D P = 6) (activePrime C D)).symm

theorem firstSubsetNorm_pos (C D : Ideal O) (hC : Supported C)
    (S : Finset (ActiveIndex C D)) :
    0 < (∏ P ∈ S, activePrime C D P).absNorm := by
  rw [map_prod]
  apply Finset.prod_pos
  intro P _
  rw [← firstSignedPrime_span C D hC P]
  exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (firstSignedPrime_supported C D hC P).1)

theorem powered_numerator_norm_pos {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (hp : ∀ i ∈ S, Supported (Ideal.span {p i})) :
    0 < (Ideal.span {∏ i ∈ S, p i^(t i)}).absNorm := by
  rw [powered_numerator_norm]
  apply Finset.prod_pos
  intro i hi
  exact pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i hi).1)) _

theorem norm_log_defect (Z : ℝ) (hZ : 1 < Z) (N F K U : ℕ)
    (hF : 0 < F) (hK : 0 < K) (hU : 0 < U)
    (hN : N = K*U) (hFU : F ≤ U^5) :
    Real.logb Z F ≤ 5*(Real.logb Z N-Real.logb Z K) := by
  have hh := Real.logb_le_logb_of_le hZ (by exact_mod_cast hF)
    (show (F:ℝ) ≤ (U:ℝ)^5 by exact_mod_cast hFU)
  rw [Real.logb_pow] at hh
  have he : Real.logb Z (N:ℝ) = Real.logb Z (K:ℝ)+Real.logb Z (U:ℝ) := by
    rw [hN, Nat.cast_mul, Real.logb_mul (by exact_mod_cast hK.ne')
      (by exact_mod_cast hU.ne')]
  rw [he]
  simpa only [add_sub_cancel_left, Nat.cast_ofNat] using hh

theorem actual_first_left_log_bound (C D : Ideal O) (hC : Supported C)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.span {firstLeftUncancelled C D}).absNorm ≤
      5*(Real.logb Z (Ideal.span {activeConductor C D}).absNorm-
        Real.logb Z (firstLeftCancelledRadical C D).absNorm) := by
  apply norm_log_defect Z hZ
    (Ideal.span {activeConductor C D}).absNorm
    (Ideal.span {firstLeftUncancelled C D}).absNorm
    (firstLeftCancelledRadical C D).absNorm (firstLeftRadical C D).absNorm
  · exact powered_numerator_norm_pos _ _ _ (fun P _ => firstSignedPrime_supported C D hC P)
  · exact firstSubsetNorm_pos C D hC _
  · exact firstSubsetNorm_pos C D hC _
  · rw [actual_first_left_radical_split, map_mul]
  · exact actual_first_left_norm C D hC

theorem actual_first_right_log_bound (C D : Ideal O) (hC : Supported C)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.span {firstRightUncancelled C D}).absNorm ≤
      5*(Real.logb Z (Ideal.span {activeConductor C D}).absNorm-
        Real.logb Z (firstRightCancelledRadical C D).absNorm) := by
  apply norm_log_defect Z hZ
    (Ideal.span {activeConductor C D}).absNorm
    (Ideal.span {firstRightUncancelled C D}).absNorm
    (firstRightCancelledRadical C D).absNorm (firstRightRadical C D).absNorm
  · exact powered_numerator_norm_pos _ _ _ (fun P _ => firstSignedPrime_supported C D hC P)
  · exact firstSubsetNorm_pos C D hC _
  · exact firstSubsetNorm_pos C D hC _
  · rw [actual_first_right_radical_split, map_mul]
  · exact actual_first_right_norm C D hC

#print axioms actual_first_left_norm
#print axioms actual_first_right_norm
#print axioms actual_first_left_radical_split
#print axioms actual_first_right_radical_split
#print axioms actual_first_left_log_bound
#print axioms actual_first_right_log_bound
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.CanonicalFirstNorm -/

/- BEGIN ORIGINAL Cycle61.Moment.CanonicalFirstSupport; sha256 05fe858e557467d48a3b7e571a9a14a02499635253291814e2ce9526e165a88c -/
section
                                        
                                                               
                                                        

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic CanonicalRowCompletion
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCommonSupport
open CenteredMomentCompleteCommon
open CenteredMomentFirstDiscardedEnergy CenteredMomentRankinRadical
open UniqueFactorizationMonoid
open IdealMobiusDivisorSum hiding primeSupport
local notation "O" => HeckeFamily.O

def firstRetainedCommon (C D : Ideal O) (left : Bool) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P =>
    netExponent (leftExponent C D P) (rightExponent C D P) ≠ 0 ∧
      (if left then 1+netExponent (leftExponent C D P) (rightExponent C D P)
        else 7-netExponent (leftExponent C D P) (rightExponent C D P)) ≠ 6)

def firstProjectorRadical (C D : Ideal O) (E : Finset (CommonIndex C D)) : Ideal O :=
  ∏ P ∈ E, P.val

def firstRetainedCommonRadical (C D : Ideal O) (left : Bool) : Ideal O :=
  ∏ P ∈ firstRetainedCommon C D left, P.val

def firstMissingCommon (C D : Ideal O) (E : Finset (CommonIndex C D))
    (left : Bool) : Finset (CommonIndex C D) :=
  Finset.univ \ (E ∪ firstRetainedCommon C D left)

def firstMissingRadical (C D : Ideal O) (E : Finset (CommonIndex C D))
    (left : Bool) : Ideal O := ∏ P ∈ firstMissingCommon C D E left, P.val

theorem first_projector_retained_disjoint (C D : Ideal O)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) (left : Bool) :
    Disjoint E (firstRetainedCommon C D left) := by
  apply Finset.disjoint_left.mpr
  intro P hP hR
  have hp := Finset.mem_powerset.mp hE hP
  have hzero := (Finset.mem_filter.mp hp).2
  exact (Finset.mem_filter.mp hR).2.1 hzero

theorem first_common_radical_product (C D : Ideal O) :
    commonRadical C D = ∏ P : CommonIndex C D, P.val := by
  change (∏ P ∈ commonSupport C D, P) = _
  exact (Finset.prod_coe_sort (s := commonSupport C D) (f := fun P : Ideal O => P)).symm

/-- The first projector is counted once; the remainder is precisely the
radical not already visible in the retained signed row. -/
theorem actual_first_radical_partition (C D : Ideal O) (E : Finset (CommonIndex C D))
    (hE : E ∈ inactiveSubsets C D) (left : Bool) :
    commonRadical C D = firstProjectorRadical C D E *
      firstRetainedCommonRadical C D left * firstMissingRadical C D E left := by
  rw [first_common_radical_product]
  dsimp only [firstProjectorRadical, firstRetainedCommonRadical,
    firstMissingRadical, firstMissingCommon]
  rw [← Finset.prod_union (first_projector_retained_disjoint C D E hE left)]
  exact (Finset.prod_sdiff (Finset.subset_univ (E ∪ firstRetainedCommon C D left))).symm.trans
    (by ring)

theorem first_retained_left_radical (C D : Ideal O) :
    firstRetainedCommonRadical C D true = firstLeftRadical C D := by
  let S := firstRetainedCommon C D true
  have hs : S.subtype (fun P => P ∈ ActiveIndex C D) =
      Finset.univ.filter (fun P : ActiveIndex C D => 1+activeExponent C D P ≠ 6) := by
    ext P
    have hp := netExponent_ne_zero _ _ _ P
    simp only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [S, firstRetainedCommon, Finset.mem_filter, Finset.mem_univ, true_and, ite_true]
    change (netExponent (leftExponent C D P.val) (rightExponent C D P.val) ≠ 0 ∧
      1+activeExponent C D P ≠ 6) ↔ 1+activeExponent C D P ≠ 6
    exact and_iff_right hp
  have hh := Finset.prod_subtype_eq_prod_filter (s := S) (fun P : CommonIndex C D => P.val)
    (p := fun P => P ∈ ActiveIndex C D)
  have ht : S.filter (fun P => P ∈ ActiveIndex C D) = S := by
    apply Finset.filter_true_of_mem
    intro P hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hP).2.1⟩
  rw [hs, ht] at hh
  exact hh.symm

theorem first_retained_right_radical (C D : Ideal O) :
    firstRetainedCommonRadical C D false = firstRightRadical C D := by
  let S := firstRetainedCommon C D false
  have hs : S.subtype (fun P => P ∈ ActiveIndex C D) =
      Finset.univ.filter (fun P : ActiveIndex C D => 7-activeExponent C D P ≠ 6) := by
    ext P
    have hp := netExponent_ne_zero _ _ _ P
    simp only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [S, firstRetainedCommon, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_eq_true, ite_false]
    change (netExponent (leftExponent C D P.val) (rightExponent C D P.val) ≠ 0 ∧
      7-activeExponent C D P ≠ 6) ↔ 7-activeExponent C D P ≠ 6
    exact and_iff_right hp
  have hh := Finset.prod_subtype_eq_prod_filter (s := S) (fun P : CommonIndex C D => P.val)
    (p := fun P => P ∈ ActiveIndex C D)
  have ht : S.filter (fun P => P ∈ ActiveIndex C D) = S := by
    apply Finset.filter_true_of_mem
    intro P hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hP).2.1⟩
  rw [hs, ht] at hh
  exact hh.symm

theorem first_projector_span (C D : Ideal O) (E : Finset (CommonIndex C D)) :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} =
      firstProjectorRadical C D E := by
  rw [primeSubsetGenerator, span_idealGenerator]
  rfl

theorem powered_numerator_radical_dvd {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (ht : ∀ i ∈ S, 0 < t i) :
    (∏ i ∈ S, Ideal.span {p i}) ∣ Ideal.span {∏ i ∈ S, p i^(t i)} := by
  change _ ∣ principalIdealHom (∏ i ∈ S, p i^(t i))
  rw [map_prod]
  simp only [map_pow]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i hi =>
    dvd_pow_self _ (Nat.ne_zero_of_lt (ht i hi)))

theorem first_left_radical_dvd_numerator (C D : Ideal O) (hC : Supported C) :
    firstLeftRadical C D ∣ Ideal.span {firstLeftUncancelled C D} := by
  have hh := powered_numerator_radical_dvd
    (Finset.univ.filter (fun P => 1+activeExponent C D P ≠ 6))
    (firstSignedPrime C D) (fun P => 1+activeExponent C D P) (fun _ _ => by omega)
  simpa only [firstLeftRadical, firstLeftUncancelled, firstSignedPrime_span C D hC] using hh

theorem first_right_radical_dvd_numerator (C D : Ideal O) (hC : Supported C) :
    firstRightRadical C D ∣ Ideal.span {firstRightUncancelled C D} := by
  have hh := powered_numerator_radical_dvd
    (Finset.univ.filter (fun P => 7-activeExponent C D P ≠ 6))
    (firstSignedPrime C D) (fun P => 7-activeExponent C D P) (by
      intro P _
      have h6 : activeExponent C D P < 6 := netExponent_lt_six _ _
      omega)
  simpa only [firstRightRadical, firstRightUncancelled, firstSignedPrime_span C D hC] using hh

theorem actual_first_left_radical_visible (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) :
    commonRadical C D ∣
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
        firstLeftUncancelled C D} * firstMissingRadical C D E true := by
  rw [actual_first_radical_partition C D E hE true, first_retained_left_radical,
    ← Ideal.span_singleton_mul_span_singleton, first_projector_span]
  exact mul_dvd_mul (mul_dvd_mul dvd_rfl (first_left_radical_dvd_numerator C D hC)) dvd_rfl

theorem actual_first_right_radical_visible (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) :
    commonRadical C D ∣
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
        firstRightUncancelled C D} * firstMissingRadical C D E false := by
  rw [actual_first_radical_partition C D E hE false, first_retained_right_radical,
    ← Ideal.span_singleton_mul_span_singleton, first_projector_span]
  exact mul_dvd_mul (mul_dvd_mul dvd_rfl (first_right_radical_dvd_numerator C D hC)) dvd_rfl

theorem firstCommonSubsetNorm_pos (C D : Ideal O) (hC : Supported C)
    (S : Finset (CommonIndex C D)) : 0 < (∏ P ∈ S, P.val).absNorm := by
  rw [map_prod]
  exact Finset.prod_pos (fun P _ => Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr
      (CenteredMomentSecondCanonical.commonPrime_supported_ideal C D hC P).1))

theorem actual_first_missing_width (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D)
    (left : Bool) (Z : ℝ) :
    Real.logb Z (firstMissingRadical C D E left).absNorm =
      Real.logb Z (commonRadical C D).absNorm-
      Real.logb Z (firstRetainedCommonRadical C D left).absNorm-
      Real.logb Z (firstProjectorRadical C D E).absNorm := by
  have hp : 0 < ((firstProjectorRadical C D E).absNorm:ℝ) := by
    exact_mod_cast firstCommonSubsetNorm_pos C D hC E
  have hr : 0 < ((firstRetainedCommonRadical C D left).absNorm:ℝ) := by
    exact_mod_cast firstCommonSubsetNorm_pos C D hC (firstRetainedCommon C D left)
  have hm : 0 < ((firstMissingRadical C D E left).absNorm:ℝ) := by
    exact_mod_cast firstCommonSubsetNorm_pos C D hC (firstMissingCommon C D E left)
  rw [actual_first_radical_partition C D E hE left]
  simp only [map_mul, Nat.cast_mul]
  rw [Real.logb_mul (mul_ne_zero hp.ne' hr.ne') hm.ne',
    Real.logb_mul hp.ne' hr.ne']
  ring

theorem actual_first_left_missing_width (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) (Z : ℝ) :
    Real.logb Z (firstMissingRadical C D E true).absNorm =
      Real.logb Z (commonRadical C D).absNorm-
      Real.logb Z (Ideal.span {activeConductor C D}).absNorm-
      Real.logb Z (firstProjectorRadical C D E).absNorm+
      Real.logb Z (firstLeftCancelledRadical C D).absNorm := by
  rw [actual_first_missing_width C D hC E hE true, first_retained_left_radical]
  have hk : 0 < ((firstLeftCancelledRadical C D).absNorm:ℝ) := by
    exact_mod_cast firstSubsetNorm_pos C D hC (firstLeftCancelled C D)
  have hr : 0 < ((firstLeftRadical C D).absNorm:ℝ) := by
    exact_mod_cast firstSubsetNorm_pos C D hC
      (Finset.univ.filter (fun P => 1+activeExponent C D P ≠ 6))
  rw [actual_first_left_radical_split]
  simp only [map_mul, Nat.cast_mul]
  rw [Real.logb_mul hk.ne' hr.ne']
  ring

theorem actual_first_right_missing_width (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D) (Z : ℝ) :
    Real.logb Z (firstMissingRadical C D E false).absNorm =
      Real.logb Z (commonRadical C D).absNorm-
      Real.logb Z (Ideal.span {activeConductor C D}).absNorm-
      Real.logb Z (firstProjectorRadical C D E).absNorm+
      Real.logb Z (firstRightCancelledRadical C D).absNorm := by
  rw [actual_first_missing_width C D hC E hE false, first_retained_right_radical]
  have hk : 0 < ((firstRightCancelledRadical C D).absNorm:ℝ) := by
    exact_mod_cast firstSubsetNorm_pos C D hC (firstRightCancelled C D)
  have hr : 0 < ((firstRightRadical C D).absNorm:ℝ) := by
    exact_mod_cast firstSubsetNorm_pos C D hC
      (Finset.univ.filter (fun P => 7-activeExponent C D P ≠ 6))
  rw [actual_first_right_radical_split]
  simp only [map_mul, Nat.cast_mul]
  rw [Real.logb_mul hk.ne' hr.ne']
  ring

theorem literal_effective_row_visible (u₀ e F G V h : O) (K R : Ideal O)
    (hR : R ∣ Ideal.span {e*F}*K) :
    R ∣ Ideal.span {effectiveRow u₀ e F G V h}*K := by
  have hd : e*F ∣ effectiveRow u₀ e F G V h := ⟨u₀*G*V*h, by dsimp [effectiveRow]; ring⟩
  have hi : Ideal.span {e*F} ∣ Ideal.span {effectiveRow u₀ e F G V h} :=
    Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)
  exact hR.trans (mul_dvd_mul hi dvd_rfl)

theorem primeSupport_subset_of_dvd (R N : Ideal O) (hN : N ≠ 0) (hd : R ∣ N) :
    primeSupport R ⊆ primeSupport N := by
  intro P hP
  have hp := support_prime hP
  have hdiv := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  simpa only [primeSupport, Multiset.mem_toFinset, mem_normalizedFactors_iff hN, hp, true_and]
    using hdiv.trans hd

theorem actual_first_left_support_visible (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D)
    (u₀ G V h : O)
    (hw : effectiveRow u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
      (firstLeftUncancelled C D) G V h ≠ 0) :
    primeSupport C ⊆ primeSupport
      (Ideal.span {effectiveRow u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (firstLeftUncancelled C D) G V h} * firstMissingRadical C D E true) := by
  have hm : firstMissingRadical C D E true ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mp
      (Nat.ne_of_gt (firstCommonSubsetNorm_pos C D hC (firstMissingCommon C D E true)))
  have hn := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hw) hm
  have hd := literal_effective_row_visible u₀
    (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
    (firstLeftUncancelled C D) G V h _ _ (actual_first_left_radical_visible C D hC E hE)
  have hs := primeSupport_subset_of_dvd _ _ hn hd
  have hc : primeSupport (commonRadical C D) = primeSupport C ∩ primeSupport D :=
    commonRadical_support C D
  rwa [hc, ← hCD, Finset.inter_self] at hs

theorem actual_first_right_support_visible (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (hE : E ∈ inactiveSubsets C D)
    (u₀ G V h : O)
    (hw : effectiveRow u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
      (firstRightUncancelled C D) G V h ≠ 0) :
    primeSupport C ⊆ primeSupport
      (Ideal.span {effectiveRow u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (firstRightUncancelled C D) G V h} * firstMissingRadical C D E false) := by
  have hm : firstMissingRadical C D E false ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mp
      (Nat.ne_of_gt (firstCommonSubsetNorm_pos C D hC (firstMissingCommon C D E false)))
  have hn := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hw) hm
  have hd := literal_effective_row_visible u₀
    (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
    (firstRightUncancelled C D) G V h _ _ (actual_first_right_radical_visible C D hC E hE)
  have hs := primeSupport_subset_of_dvd _ _ hn hd
  have hc : primeSupport (commonRadical C D) = primeSupport C ∩ primeSupport D :=
    commonRadical_support C D
  rwa [hc, ← hCD, Finset.inter_self] at hs

#print axioms actual_first_radical_partition
#print axioms first_retained_left_radical
#print axioms first_retained_right_radical
#print axioms actual_first_left_radical_visible
#print axioms actual_first_right_radical_visible
#print axioms actual_first_left_missing_width
#print axioms actual_first_right_missing_width
#print axioms actual_first_left_support_visible
#print axioms actual_first_right_support_visible
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.CanonicalFirstSupport -/
