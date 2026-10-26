/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact first-common ideal identities for the squarefree ordinary source. -/
import Submissions.hailey_collet_1252270103.Record1252270103CommonGeometry.ColumnTypes
import Submissions.hailey_collet_1252270103.Cycle61.Moment.CanonicalFirstSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103CommonGeometry
noncomputable section
open scoped Classical BigOperators
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstCanonicalAllowance CenteredMomentSecondCanonical
open CenteredMomentRankinRadical CanonicalQuadraticSieve Cycle61Moment
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

def stratumRadical (C D : Ideal O) (m n : ℕ) : Ideal O :=
  ∏ P ∈ (Finset.univ : Finset (CommonIndex C D)).filter
    (fun P=>leftExponent C D P=m ∧ rightExponent C D P=n),P.val

theorem stratumRadical_ne_zero (C D : Ideal O) (m n : ℕ) :
    stratumRadical C D m n≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact (prime_of_normalized_factor P.val
    (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).ne_zero

theorem common_left_four_strata (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    commonPart C D=stratumRadical C D 1 1*stratumRadical C D 1 2*
      stratumRadical C D 2 1^2*stratumRadical C D 2 2^2 := by
  rw [commonPart_left_product]
  simp only [stratumRadical,Finset.prod_filter,←Finset.prod_pow,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rcases common_four_types C D hC hD P with ⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩ <;>
    simp [hc,hd,Ideal.top_pow]

theorem common_right_four_strata (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    commonPart D C=stratumRadical C D 1 1*stratumRadical C D 1 2^2*
      stratumRadical C D 2 1*stratumRadical C D 2 2^2 := by
  rw [commonPart_right_product]
  simp only [stratumRadical,Finset.prod_filter,←Finset.prod_pow,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rcases common_four_types C D hC hD P with ⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩ <;>
    simp [hc,hd,Ideal.top_pow]

theorem common_radical_four_strata (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    commonRadical C D=stratumRadical C D 1 1*stratumRadical C D 1 2*
      stratumRadical C D 2 1*stratumRadical C D 2 2 := by
  rw [first_common_radical_product]
  simp only [stratumRadical,Finset.prod_filter,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rcases common_four_types C D hC hD P with ⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩ <;>
    simp [hc,hd,Ideal.top_pow]

theorem active_conductor_two_strata (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    Ideal.span {activeConductor C D}=stratumRadical C D 1 2*stratumRadical C D 2 1 := by
  rw [activeConductor_span_product]
  simp only [activeSupport,stratumRadical,Finset.prod_filter,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rcases common_four_types C D hC hD P with ⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩ <;>
    norm_num [hc,hd,netExponent,Ideal.top_pow]

private theorem active_product {M : Type*} [CommMonoid M]
    (C D : Ideal O) (f : CommonIndex C D→M) :
    (∏P : ActiveIndex C D,f P.val)=∏P : CommonIndex C D,
      if netExponent (leftExponent C D P) (rightExponent C D P)≠0 then f P else 1 := by
  rw [Finset.prod_coe_sort]
  simp only [activeSupport,Finset.prod_filter]

theorem left_cancelled_stratum (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    firstLeftCancelledRadical C D=stratumRadical C D 1 2 := by
  unfold firstLeftCancelledRadical firstLeftCancelled
  rw [Finset.prod_filter]
  change (∏P : ActiveIndex C D, if 1+netExponent (leftExponent C D P.val)
    (rightExponent C D P.val)=6 then P.val.val else 1)=_
  rw [active_product C D (fun P=>if 1+netExponent (leftExponent C D P)
    (rightExponent C D P)=6 then P.val else 1)]
  simp only [stratumRadical,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro P hP
  rcases common_four_types C D hC hD P with ⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩ <;>
    norm_num [hc,hd,netExponent,Ideal.top_pow]

theorem right_cancelled_stratum (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    firstRightCancelledRadical C D=stratumRadical C D 2 1 := by
  unfold firstRightCancelledRadical firstRightCancelled
  rw [Finset.prod_filter]
  change (∏P : ActiveIndex C D, if 7-netExponent (leftExponent C D P.val)
    (rightExponent C D P.val)=6 then P.val.val else 1)=_
  rw [active_product C D (fun P=>if 7-netExponent (leftExponent C D P)
    (rightExponent C D P)=6 then P.val else 1)]
  simp only [stratumRadical,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro P hP
  rcases common_four_types C D hC hD P with ⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩ <;>
    norm_num [hc,hd,netExponent,Ideal.top_pow]

theorem left_numerator_stratum (C D : Ideal O) (hCs : Supported C)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    Ideal.span {firstLeftUncancelled C D}=(stratumRadical C D 2 1)^2 := by
  change CanonicalRowCompletion.principalIdealHom (firstLeftUncancelled C D)=_
  unfold firstLeftUncancelled
  simp only [map_prod,map_pow]
  change (∏P ∈ Finset.univ.filter (fun P=>1+activeExponent C D P≠6),
    (Ideal.span {firstSignedPrime C D P})^(1+activeExponent C D P))=_
  simp only [firstSignedPrime_span C D hCs]
  rw [Finset.prod_filter]
  change (∏P : ActiveIndex C D, if 1+netExponent (leftExponent C D P.val)
    (rightExponent C D P.val)≠6 then P.val.val^(1+netExponent (leftExponent C D P.val)
    (rightExponent C D P.val)) else 1)=_
  rw [active_product C D (fun P=>if 1+netExponent (leftExponent C D P)
    (rightExponent C D P)≠6 then P.val^(1+netExponent (leftExponent C D P)
    (rightExponent C D P)) else 1)]
  simp only [stratumRadical,Finset.prod_filter,←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro P hP
  rcases common_four_types C D hC hD P with ⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩ <;>
    norm_num [hc,hd,netExponent,Ideal.top_pow]

/-- The opposite signed numerator cancels type (2,1), retaining exponent
two at type (1,2), together with the original sixth-power holes. -/
theorem right_numerator_stratum (C D : Ideal O) (hCs : Supported C)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    Ideal.span {firstRightUncancelled C D}=(stratumRadical C D 1 2)^2 := by
  change CanonicalRowCompletion.principalIdealHom (firstRightUncancelled C D)=_
  unfold firstRightUncancelled
  simp only [map_prod,map_pow]
  change (∏P ∈ Finset.univ.filter (fun P=>7-activeExponent C D P≠6),
    (Ideal.span {firstSignedPrime C D P})^(7-activeExponent C D P))=_
  simp only [firstSignedPrime_span C D hCs]
  rw [Finset.prod_filter]
  change (∏P : ActiveIndex C D, if 7-netExponent (leftExponent C D P.val)
    (rightExponent C D P.val)≠6 then P.val.val^(7-netExponent (leftExponent C D P.val)
    (rightExponent C D P.val)) else 1)=_
  rw [active_product C D (fun P=>if 7-netExponent (leftExponent C D P)
    (rightExponent C D P)≠6 then P.val^(7-netExponent (leftExponent C D P)
    (rightExponent C D P)) else 1)]
  simp only [stratumRadical,Finset.prod_filter,←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro P hP
  rcases common_four_types C D hC hD P with ⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩|⟨hc,hd⟩ <;>
    norm_num [hc,hd,netExponent,Ideal.top_pow]

end
end OAI.SevenEighths.Record1252270103CommonGeometry

#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.common_left_four_strata
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.common_right_four_strata
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.active_conductor_two_strata
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.left_cancelled_stratum
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.left_numerator_stratum
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.right_numerator_stratum
