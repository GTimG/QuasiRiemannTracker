/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The supported-primary dictionary argument is adapted from Cycle61's
FirstUniformDictionary; the fixed parent here is arbitrary. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometrySecondDictionary

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentChildRows CenteredMomentNaturalRowSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonSupport RayFourExpansion Cycle61Moment Cycle61InitialMass
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

/-- The initial parent may be any fixed character. Its supported first
column is a natural row of a fixed ray twist, with a unit chosen before
the ray and every live physical selector. -/
theorem uniform_fixed_parent_left_mask (η : Character) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D)) :
    ∃u : Oˣ, ∀(ξ : RayCharacter)(χ : Character),
      χ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D} →
      (∀n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff χ n=elementCoeff η n*coprimalityMask m n*
          leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*
          rayCharacter ξ n) →
      ∀F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC (activeExponent C D)*ξ))
        (1*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*firstLeftUncancelled C D),
      ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := uniform_first_left_single_dictionary η C D hC
  refine ⟨u,?_⟩
  intro ξ χ hmod hcoeff F I
  have h72 : χ.modulus≤Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus≤Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus≤Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏P∈firstLeftCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0)=1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right (first_signed_prime_dvd_conductor C D hC P))
  rw [hcoeff n hn hp,show coprimalityMask m n=(1:ℂ) from ite_eq_left hmn,mul_one]
  have hh:=hu ξ 1 (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E) n hn hp
  simpa only [idealRowHom_one_supported _ hn,mul_one,hholes,one_mul] using hh

theorem uniform_fixed_parent_right_mask (η : Character) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D)) :
    ∃u : Oˣ, ∀(ξ : RayCharacter)(χ : Character),
      χ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D} →
      (∀n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        elementCoeff χ n=elementCoeff η n*coprimalityMask m n*
          rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*
          rayCharacter ξ n) →
      ∀F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (fun P=>6-activeExponent C D P)*ξ))
        (1*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*firstRightUncancelled C D),
      ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := uniform_first_right_single_dictionary η C D hC
  refine ⟨u,?_⟩
  intro ξ χ hmod hcoeff F I
  have h72 : χ.modulus≤Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus≤Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus≤Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏P∈firstRightCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0)=1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right (first_signed_prime_dvd_conductor C D hC P))
  rw [hcoeff n hn hp,show coprimalityMask m n=(1:ℂ) from ite_eq_left hmn,mul_one]
  have hh:=hu ξ 1 (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E) n hn hp
  simpa only [idealRowHom_one_supported _ hn,mul_one,hholes,one_mul] using hh

def fixedParentUnit (left : Bool)(η : Character)(l : FirstSourceLabel) : Oˣ :=
  if h : Supported l.1.1 then
    if left then Classical.choose (uniform_fixed_parent_left_mask η fixedBadMask l.1.1 l.1.2 h l.2.val)
    else Classical.choose (uniform_fixed_parent_right_mask η fixedBadMask l.1.1 l.1.2 h l.2.val)
  else 1

/-- Literal first column with arbitrary parent character, with no natural
representation or equality of the parent and slot characters assumed. -/
theorem actual_fixed_parent_column_dictionary {ι : Type*}[Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (G : NaturalRow (childCharacter s.η (geometryDictionaryRay reflected s R seed K Z ξ hK key j))
      (1*(fixedParentUnit (!reflected) s.η (geometryFirstLabel s R seed K Z ξ hK key j):O)*
        primeSubsetGenerator (fun p : CommonIndex
          (geometryFirstLabel s R seed K Z ξ hK key j).1.1
          (geometryFirstLabel s R seed K Z ξ hK key j).1.2=>p.val)
          (geometryFirstLabel s R seed K Z ξ hK key j).2.val*
        firstSourceNumerator (!reflected) (geometryFirstLabel s R seed K Z ξ hK key j)))
    (I : Ideal O) :
    let χ:=geometryColumnCharacter reflected s R seed K Z ξ hK key j
    idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff G.character I else 0 := by
  let src:=geometryFirstSource s R seed K Z ξ hK key j.1
  let F:=fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  cases reflected
  · have hu:=Classical.choose_spec (uniform_fixed_parent_left_mask s.η fixedBadMask
      src.C src.D src.hC src.inactive)
    change idealCoeff F.left I=if IsCoprime I F.left.modulus then idealCoeff G.character I else 0
    revert G
    unfold fixedParentUnit
    have hc : Supported (geometryFirstLabel s R seed K Z ξ hK key j).1.1:=src.hC
    rw [dif_pos hc]
    intro G
    exact hu j.2.2.1 F.left F.left_modulus (fixed_pair_left_element F) G I
  · have hu:=Classical.choose_spec (uniform_fixed_parent_right_mask s.η fixedBadMask
      src.C src.D src.hC src.inactive)
    change idealCoeff F.right I=if IsCoprime I F.right.modulus then idealCoeff G.character I else 0
    revert G
    unfold fixedParentUnit
    have hc : Supported (geometryFirstLabel s R seed K Z ξ hK key j).1.1:=src.hC
    rw [dif_pos hc]
    intro G
    exact hu j.2.2.2⁻¹ F.right F.right_modulus (fixed_pair_right_element F) G I

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.uniform_fixed_parent_left_mask
#print axioms OAI.SevenEighths.Record12518109Raw.uniform_fixed_parent_right_mask
#print axioms OAI.SevenEighths.Record12518109Raw.actual_fixed_parent_column_dictionary
