import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.SignedPrimeProducts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonical

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
