/- Packaging rehearsal. Original notices retained; separate replay required. -/
import OAI.NumberTheory.DirichletL.Detector.PrimeConstants
import OAI.NumberTheory.DirichletL.Moments.AmplificationShortening
import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily
import OAI.NumberTheory.DirichletL.Moments.FirstColumns
import OAI.NumberTheory.DirichletL.Moments.Mask
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
import OAI.NumberTheory.DirichletL.Moments.SecondCanonical
import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
import OAI.NumberTheory.DirichletL.Moments.SecondSourceMask

/- BEGIN ORIGINAL LocalMoment.SignedRows; sha256 0c71c83f4ca774cdfe48684ef74d38c03674c003b8e935f5d8cf1c1e9aaf64ba -/
section
                                                          
                                                       
                                                                  
                                                           
                                                                 

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.LocalMomentSignedRows
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSupportedCorrelation CenteredMomentFirstColumns
open CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O
set_option autoImplicit false

/-- Reciprocity fixes the sign: the left coefficient uses exponent 1+t. -/
theorem left_local (p n : O) (t : ℕ)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * idealRowHom n (Ideal.span {p})^t =
      sexticReciprocityPhase p n^t * idealRowHom (p^(1+t)) (Ideal.span {n}) := by
  rw [idealRowHom_primary_reciprocity p n hpp hnp hp hn, mul_pow,
      idealRowHom_argument_pow p (1+t) _ hn, pow_add, pow_one]
  ring

/-- A sixth power retains its original puncture, including on nonunits. -/
theorem left_canceled (p n : O)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * idealRowHom n (Ideal.span {p})^5 =
      sexticReciprocityPhase p n^5 *
        (if IsCoprime n p then (1:ℂ) else 0) := by
  rw [left_local p n 5 hp hn hpp hnp]
  norm_num only
  rw [idealRowHom_sixth_mask _ _ hn, Ideal.isCoprime_span_singleton_iff]

/-- Conjugation reverses the first active exponent. The raw representative
7-t is positive, so the nonunit zero is never replaced by 0^0. -/
theorem right_local (p n : O) [(Ideal.span {p}).IsMaximal] (t : ℕ)
    (ht : 0<t) (ht6 : t<6)
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * star (idealRowHom n (Ideal.span {p})^t) =
      sexticReciprocityPhase p n^(6-t) * idealRowHom (p^(7-t)) (Ideal.span {n}) := by
  let χ := ActualEisensteinCubic.canonicalSextic (Ideal.span {p}) hg
  have hinv : (χ^t)⁻¹=χ^(6-t) := by
    apply inv_eq_of_mul_eq_one_right
    rw [←pow_add,Nat.add_sub_of_le ht6.le]
    exact ProbePrimePower.actualSextic_six _ hg hc
  have hs : star (idealRowHom n (Ideal.span {p})^t) =
      idealRowHom n (Ideal.span {p})^(6-t) := by
    rw [idealRowHom_prime n _ hg]
    change star (χ (Ideal.Quotient.mk _ n)^t)=χ (Ideal.Quotient.mk _ n)^(6-t)
    rw [←MulChar.pow_apply' χ (by omega : t≠0),MulChar.star_apply',hinv,
      MulChar.pow_apply' χ (by omega : 6-t≠0)]
  rw [hs,left_local p n (6-t) hp hn hpp hnp]
  rw [show 1+(6-t)=7-t by omega]

/-- At t=1 the right coefficient is exactly a puncture, not one. -/
theorem right_canceled (p n : O) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * star (idealRowHom n (Ideal.span {p})) =
      sexticReciprocityPhase p n^5 *
        (if IsCoprime n p then (1:ℂ) else 0) := by
  have h := right_local p n 1 (by decide) (by decide) hg hc hp hn hpp hnp
  norm_num only [pow_one] at h
  rw [h,idealRowHom_sixth_mask _ _ hn,Ideal.isCoprime_span_singleton_iff]

/-- Multiplying all already retained row numerators is literal, before
reducing any sixth powers and before taking absolute values. -/
theorem effective_row (e F G V h : O) (I : Ideal O) :
    idealRowHom (e*F) I * idealRowHom ((G*V)*h) I =
      idealRowHom ((e*F)*(G*V)*h) I := by
  simp only [idealRowHom_argument_mul]
  ring

#print axioms left_local
#print axioms left_canceled
#print axioms right_local
#print axioms right_canceled
#print axioms effective_row
end SevenEighths.LocalMomentSignedRows
end
end OAI

end
/- END ORIGINAL LocalMoment.SignedRows -/

/- BEGIN ORIGINAL Cycle61.Moment.SignedSourceDictionary; sha256 b30e559c5a07f23a1c56c1662007a0a148da1cf51f49d29a9227b505055cab4a -/
section
                             
                                                                          
                                               

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

/-- The original row is retained in the literal second-transform numerator. -/
def effectiveRow (u₀ e F G V h : O) : O := u₀ * e * F * G * V * h

theorem effectiveRow_coefficient (u₀ e F G V h : O) (I : Ideal O) :
    idealRowHom u₀ I * idealRowHom e I * idealRowHom F I *
      idealRowHom G I * idealRowHom V I * idealRowHom h I =
      idealRowHom (effectiveRow u₀ e F G V h) I := by
  simp only [effectiveRow, idealRowHom_argument_mul]

/-- This is an actual natural character, with its natural conductor bound.
The fixed sixth-power factor remains an Euler puncture. -/
theorem effectiveRow_natural (η : Character) (u₀ e F G V h : O)
    (hne : effectiveRow u₀ e F G V h ≠ 0) :
    ∃ χ : Character,
      χ.modulus.absNorm ≤ η.modulus.absNorm * fixedConductorFactor *
        (Ideal.span {effectiveRow u₀ e F G V h}).absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I = idealCoeff η I *
        idealRowHom (fixedBadMask^6) I * idealRowHom u₀ I *
          idealRowHom e I * idealRowHom F I * idealRowHom G I *
          idealRowHom V I * idealRowHom h I := by
  let Frow := naturalRow η (effectiveRow u₀ e F G V h) hne
  refine ⟨Frow.character, Frow.natural_modulus_bound, ?_⟩
  intro I
  rw [Frow.ideal]
  simp only [idealRowHom_argument_mul, effectiveRow]
  ring

/-- Regroup the signed coefficient before applying a norm or a row bound. -/
theorem signed_regroup {Label Row : Type*} [DecidableEq Label] [DecidableEq Row]
    (labels : Finset Label) (row : Label → Row) (coefficient : Label → ℂ)
    (character : Row → ℂ) :
    (∑ j ∈ labels, coefficient j * character (row j)) =
      ∑ w ∈ labels.image row,
        (∑ j ∈ labels.filter (fun j => row j = w), coefficient j) * character w := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem row hj)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

/-- First labels can remain inside each signed Hilbert coordinate. There is
no cardinality factor for the first-label set in this inequality. -/
theorem joint_signed_cauchy {Label Row : Type*}
    (labels : Finset Label) (rows : Finset Row)
    (left right : Label → Row → ℂ) :
    ‖∑ w ∈ rows, (∑ j ∈ labels, left j w) *
      star (∑ j ∈ labels, right j w)‖^2 ≤
      (∑ w ∈ rows, ‖∑ j ∈ labels, left j w‖^2) *
        ∑ w ∈ rows, ‖∑ j ∈ labels, right j w‖^2 := by
  have hn := norm_sum_le rows
    (fun w => (∑ j ∈ labels, left j w) * star (∑ j ∈ labels, right j w))
  simp only [norm_mul, norm_star] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq rows
      (fun w => ‖∑ j ∈ labels, left j w‖)
      (fun w => ‖∑ j ∈ labels, right j w‖))

/-- Arbitrary valuations are allowed: every factor of an exact product is
an ideal divisor. No squarefree hypothesis occurs. -/
theorem exact_product_factor_divisor {ι : Type*} [Fintype ι]
    (f : ι → Ideal O) (N : Ideal O) (h : ∏ i, f i = N) (i : ι) : f i ∣ N := by
  rw [← h]
  exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)

theorem exact_product_fibre_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tuples : Finset (ι → Ideal O)) (N : Ideal O) (hN : N ≠ 0) :
    (tuples.filter (fun f => ∏ i, f i = N)).card ≤
      (IdealMobiusDivisorSum.idealDivisors N).card ^ Fintype.card ι := by
  have hsub : tuples.filter (fun f => ∏ i, f i = N) ⊆
      Fintype.piFinset (fun _ : ι => IdealMobiusDivisorSum.idealDivisors N) := by
    intro f hf
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (IdealMobiusDivisorSum.mem_idealDivisors hN).mpr
      (exact_product_factor_divisor f N (Finset.mem_filter.mp hf).2 i)
  apply (Finset.card_le_card hsub).trans_eq
  simp

theorem exact_product_fibre_small_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ (tuples : Finset (ι → Ideal O)) (N : Ideal O), N ≠ 0 →
        (N.absNorm : ℝ) ≤ Z^B →
        ((tuples.filter (fun f => ∏ i, f i = N)).card : ℝ) ≤ C*Z^ε := by
  let k := Fintype.card ι
  let δ := ε / (k+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hdiv⟩ := CenteredMomentMask.polynomial_mask_divisor_bound δ B hδ hB
  refine ⟨C^k, pow_pos hC _, ?_⟩
  intro Z hZ tuples N hN hNZ
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hc : ((tuples.filter (fun f => ∏ i, f i = N)).card : ℝ) ≤
      ((IdealMobiusDivisorSum.idealDivisors N).card : ℝ)^k := by
    exact_mod_cast exact_product_fibre_card tuples N hN
  have hd := pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv Z hZ N hN hNZ) k
  have hexp : δ*(k:ℝ) ≤ ε := by
    dsimp [δ]
    have hk : (0:ℝ) < k+1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hk]
    nlinarith
  apply hc.trans (hd.trans ?_)
  rw [mul_pow, ← Real.rpow_mul_natCast hZp.le]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ hexp) (pow_nonneg hC.le _)

#print axioms effectiveRow_natural
#print axioms signed_regroup
#print axioms joint_signed_cauchy
#print axioms exact_product_fibre_card
#print axioms exact_product_fibre_small_power
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.SignedSourceDictionary -/

/- BEGIN ORIGINAL Cycle61.Moment.SignedPrimeProducts; sha256 c24996521addea8252e9a556a9f06ea92bc84eeb5321c4eb6dce9ddfef084c26 -/
section
                                            

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentFirstColumns
local notation "O" => HeckeFamily.O

theorem numerator_product {ι : Type*} (S : Finset ι) (p : ι → O)
    (n : O) (hn : Supported (Ideal.span {n})) :
    idealRowHom (∏ i ∈ S, p i) (Ideal.span {n}) =
      ∏ i ∈ S, idealRowHom (p i) (Ideal.span {n}) :=
  map_prod (movingNumeratorRow n hn) _ _

/-- The complete left column is encoded before taking absolute values. -/
theorem left_column_signed_product {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (e n : O)
    (hp : ∀ i ∈ S, Supported (Ideal.span {p i}))
    (hn : Supported (Ideal.span {n}))
    (hpp : ∀ i ∈ S, goodLambda^2 ∣ p i - 1) (hnp : goodLambda^2 ∣ n - 1) :
    leftCoefficient e (∏ i ∈ S, p i)
      (fun x => ∏ i ∈ S, idealRowHom x (Ideal.span {p i})^(t i)) n =
      (∏ i ∈ S, sexticReciprocityPhase (p i) n^(t i)) *
        idealRowHom (e * ∏ i ∈ S, (p i)^(1+t i)) (Ideal.span {n}) := by
  unfold leftCoefficient
  rw [idealRowHom_argument_mul, numerator_product S p n hn]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  have he := Finset.prod_congr rfl (fun i hi =>
    LocalMomentSignedRows.left_local (p i) n (t i) (hp i hi) hn (hpp i hi) hnp)
  rw [he, Finset.prod_mul_distrib, ← numerator_product S (fun i => (p i)^(1+t i)) n hn,
    idealRowHom_argument_mul]
  ring

/-- The complete right column uses positive representatives `7-t`, retaining
the nonunit zero even when the active exponent cancels modulo six. -/
theorem right_column_signed_product {ι : Type*} (S : Finset ι)
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (t : ι → ℕ) (e n : O)
    (ht : ∀ i ∈ S, 0 < t i) (ht6 : ∀ i ∈ S, t i < 6)
    (hg : ∀ i ∈ S, goodLambda ∉ Ideal.span {p i})
    (hc : ∀ i ∈ S, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hp : ∀ i ∈ S, Supported (Ideal.span {p i}))
    (hn : Supported (Ideal.span {n}))
    (hpp : ∀ i ∈ S, goodLambda^2 ∣ p i - 1) (hnp : goodLambda^2 ∣ n - 1) :
    rightCoefficient e (∏ i ∈ S, p i)
      (fun x => ∏ i ∈ S, idealRowHom x (Ideal.span {p i})^(t i)) n =
      (∏ i ∈ S, sexticReciprocityPhase (p i) n^(6-t i)) *
        idealRowHom (e * ∏ i ∈ S, (p i)^(7-t i)) (Ideal.span {n}) := by
  unfold rightCoefficient
  rw [idealRowHom_argument_mul, numerator_product S p n hn, star_prod]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  have he := Finset.prod_congr rfl (fun i hi =>
    LocalMomentSignedRows.right_local (p i) n (t i) (ht i hi) (ht6 i hi)
      (hg i hi) (hc i hi) (hp i hi) hn (hpp i hi) hnp)
  rw [he, Finset.prod_mul_distrib, ← numerator_product S (fun i => (p i)^(7-t i)) n hn,
    idealRowHom_argument_mul]
  ring

/-- Cancelled residues become the exact original Euler holes, never exponent
zero at a nonunit. The remaining numerator uses the uncancelled prime powers. -/
theorem sixth_product_retains_holes {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (n : O) (hn : Supported (Ideal.span {n})) :
    idealRowHom (∏ i ∈ S, (p i)^(t i)) (Ideal.span {n}) =
      (∏ i ∈ S.filter (fun i => t i = 6),
        if IsCoprime n (p i) then (1:ℂ) else 0) *
      idealRowHom (∏ i ∈ S.filter (fun i => t i ≠ 6), (p i)^(t i))
        (Ideal.span {n}) := by
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun i => t i = 6)
    (fun i => (p i)^(t i)), idealRowHom_argument_mul]
  congr 1
  rw [numerator_product _ _ n hn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2, idealRowHom_sixth_mask _ _ hn,
    Ideal.isCoprime_span_singleton_iff]

#print axioms left_column_signed_product
#print axioms right_column_signed_product
#print axioms sixth_product_retains_holes
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.SignedPrimeProducts -/

/- BEGIN ORIGINAL Cycle61.Moment.CanonicalFirstSigned; sha256 b5a73cd93ab808d0dc627479dcc0d704157cfc880ae97ea1169f849a23c4c613 -/
section
                                         
                                                               
                                                          

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ActualEisensteinCubic CompletedGauss CenteredMomentFirstColumns
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentSecondCanonical
local notation "O" => HeckeFamily.O

def firstSignedPrime (C D : Ideal O) (P : CenteredMomentCanonicalFirst.ActiveIndex C D) : O :=
  commonPrime C D P.val

theorem firstSignedPrime_span (C D : Ideal O) (hC : Supported C)
    (P : CenteredMomentCanonicalFirst.ActiveIndex C D) :
    Ideal.span {firstSignedPrime C D P} = activePrime C D P :=
  commonPrime_span C D hC P.val

theorem firstSignedPrime_supported (C D : Ideal O) (hC : Supported C)
    (P : CenteredMomentCanonicalFirst.ActiveIndex C D) :
    Supported (Ideal.span {firstSignedPrime C D P}) :=
  commonPrime_supported C D hC P.val

theorem firstSignedPrime_primary (C D : Ideal O) (hC : Supported C)
    (P : CenteredMomentCanonicalFirst.ActiveIndex C D) :
    goodLambda^2 ∣ firstSignedPrime C D P - 1 :=
  (primaryGenerator_spec P.val.val
    (supported_primaryGenerator_ne_zero _
      (commonPrime_supported_ideal C D hC P.val))).2

/-- The choice of ideal generator contributes a unit, from the fixed six
units of O, while the prime factors are the actual canonical active primes. -/
theorem actual_first_conductor_unit (C D : Ideal O) (hC : Supported C) :
    ∃ u : Oˣ, activeConductor C D =
      (u : O) * ∏ P, firstSignedPrime C D P := by
  have hs : Ideal.span {∏ P, firstSignedPrime C D P} =
      Ideal.span {activeConductor C D} := by
    change principalIdealHom (∏ P, firstSignedPrime C D P) = _
    rw [map_prod]
    simp only [principalIdealHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    simp_rw [firstSignedPrime_span C D hC]
    exact (span_finitePrimeModulus (activePrime C D)).symm
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by rw [← hu]; ring⟩

/-- The actual canonical first active character is the signed prime product;
its positive exponents preserve all nonunit zeros. -/
theorem actual_first_active_product (C D : Ideal O) (hC : Supported C) (n : O) :
    finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) n =
      ∏ P, idealRowHom n (Ideal.span {firstSignedPrime C D P})^(activeExponent C D P) := by
  unfold finiteSexticRow
  apply Finset.prod_congr rfl
  intro P hP
  rw [firstSignedPrime_span C D hC, idealRowHom_prime _ _ (activeGood C D hC P)]
  exact MulChar.pow_apply' _ (netExponent_ne_zero _ _ _ P) _

def firstLeftNumerator (C D : Ideal O) : O :=
  ∏ P, firstSignedPrime C D P ^ (1 + activeExponent C D P)

def firstRightNumerator (C D : Ideal O) : O :=
  ∏ P, firstSignedPrime C D P ^ (7 - activeExponent C D P)

theorem actual_first_left_signed (C D : Ideal O) (hC : Supported C) :
    ∃ u : Oˣ, ∀ e n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
      leftCoefficient e (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      (∏ P, sexticReciprocityPhase (firstSignedPrime C D P) n^(activeExponent C D P)) *
        idealRowHom ((u:O)*e*firstLeftNumerator C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_conductor_unit C D hC
  refine ⟨u, ?_⟩
  intro e n hn hnp
  have hρ : finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) =
      fun x => ∏ P, idealRowHom x (Ideal.span {firstSignedPrime C D P})^(activeExponent C D P) :=
    funext (actual_first_active_product C D hC)
  rw [hρ, hu]
  have he : e*((u:O)*∏ P,firstSignedPrime C D P) =
      ((u:O)*e)*(∏ P,firstSignedPrime C D P) := by ring
  have hh := left_column_signed_product Finset.univ (firstSignedPrime C D)
    (activeExponent C D) ((u:O)*e) n (fun P _ => firstSignedPrime_supported C D hC P)
    hn (fun P _ => firstSignedPrime_primary C D hC P) hnp
  simpa only [leftCoefficient, firstLeftNumerator, he] using hh

theorem actual_first_right_signed (C D : Ideal O) (hC : Supported C) :
    ∃ u : Oˣ, ∀ e n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
      rightCoefficient e (activeConductor C D)
        (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n =
      (∏ P, sexticReciprocityPhase (firstSignedPrime C D P) n^(6-activeExponent C D P)) *
        idealRowHom ((u:O)*e*firstRightNumerator C D) (Ideal.span {n}) := by
  obtain ⟨u,hu⟩ := actual_first_conductor_unit C D hC
  refine ⟨u, ?_⟩
  intro e n hn hnp
  let (P : ActiveIndex C D) : (Ideal.span {firstSignedPrime C D P}).IsMaximal := by
    rw [firstSignedPrime_span C D hC]; infer_instance
  have hρ : finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) =
      fun x => ∏ P, idealRowHom x (Ideal.span {firstSignedPrime C D P})^(activeExponent C D P) :=
    funext (actual_first_active_product C D hC)
  rw [hρ, hu]
  have he : e*((u:O)*∏ P,firstSignedPrime C D P) =
      ((u:O)*e)*(∏ P,firstSignedPrime C D P) := by ring
  have hh := right_column_signed_product Finset.univ (firstSignedPrime C D)
    (activeExponent C D) ((u:O)*e) n
    (fun P _ => Nat.pos_of_ne_zero (netExponent_ne_zero _ _ _ P))
    (fun P _ => netExponent_lt_six _ _)
    (fun P _ => by rw [firstSignedPrime_span C D hC]; exact activeGood C D hC P)
    (fun P _ => by
      rw [firstSignedPrime_span C D hC]
      exact common_odd C D hC P.val)
    (fun P _ => firstSignedPrime_supported C D hC P) hn
    (fun P _ => firstSignedPrime_primary C D hC P) hnp
  simpa only [rightCoefficient, firstRightNumerator, he] using hh

def firstLeftCancelled (C D : Ideal O) : Finset (ActiveIndex C D) :=
  Finset.univ.filter (fun P => 1+activeExponent C D P = 6)

def firstRightCancelled (C D : Ideal O) : Finset (ActiveIndex C D) :=
  Finset.univ.filter (fun P => 7-activeExponent C D P = 6)

def firstLeftUncancelled (C D : Ideal O) : O :=
  ∏ P ∈ Finset.univ.filter (fun P => 1+activeExponent C D P ≠ 6),
    firstSignedPrime C D P^(1+activeExponent C D P)

def firstRightUncancelled (C D : Ideal O) : O :=
  ∏ P ∈ Finset.univ.filter (fun P => 7-activeExponent C D P ≠ 6),
    firstSignedPrime C D P^(7-activeExponent C D P)

theorem actual_first_left_holes (C D : Ideal O) (n : O)
    (hn : Supported (Ideal.span {n})) :
    idealRowHom (firstLeftNumerator C D) (Ideal.span {n}) =
      (∏ P ∈ firstLeftCancelled C D,
        if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
      idealRowHom (firstLeftUncancelled C D) (Ideal.span {n}) := by
  exact sixth_product_retains_holes Finset.univ (firstSignedPrime C D)
    (fun P => 1+activeExponent C D P) n hn

theorem actual_first_right_holes (C D : Ideal O) (n : O)
    (hn : Supported (Ideal.span {n})) :
    idealRowHom (firstRightNumerator C D) (Ideal.span {n}) =
      (∏ P ∈ firstRightCancelled C D,
        if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) *
      idealRowHom (firstRightUncancelled C D) (Ideal.span {n}) := by
  exact sixth_product_retains_holes Finset.univ (firstSignedPrime C D)
    (fun P => 7-activeExponent C D P) n hn

theorem firstLeftCancelled_residue (C D : Ideal O) :
    firstLeftCancelled C D = Finset.univ.filter (fun P => activeExponent C D P = 5) := by
  apply Finset.filter_congr
  intro P _
  omega

theorem firstRightCancelled_residue (C D : Ideal O) :
    firstRightCancelled C D = Finset.univ.filter (fun P => activeExponent C D P = 1) := by
  apply Finset.filter_congr
  intro P _
  have hp : 0 < activeExponent C D P := Nat.pos_of_ne_zero (netExponent_ne_zero _ _ _ P)
  have h6 : activeExponent C D P < 6 := netExponent_lt_six _ _
  omega

#print axioms actual_first_conductor_unit
#print axioms actual_first_active_product
#print axioms actual_first_left_signed
#print axioms actual_first_right_signed
#print axioms actual_first_left_holes
#print axioms actual_first_right_holes
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.CanonicalFirstSigned -/
