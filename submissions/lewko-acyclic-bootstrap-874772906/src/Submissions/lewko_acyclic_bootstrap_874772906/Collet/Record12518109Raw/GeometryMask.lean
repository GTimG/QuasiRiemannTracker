/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.NaturalMask
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryLowAdmission
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryNaturalDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryWidth
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryExceptionalSplit

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option quotPrecheck false

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredExceptionalProfile
open CenteredMomentDetectorEnergyInitialState Cycle61InitialMass
local notation "O" => HeckeFamily.O

/-- This factor is fixed before the first and second row labels are chosen. -/
def geometryRawFixedMask {α : Type*} [Fintype α] (s : Input α) (R : Ideal O) : Ideal O :=
  s.η.modulus * Ideal.span {fixedBadMask} * Ideal.span {(72 : O)} * R

section Actual
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (reflected : Bool) (η₀ : Character) (u₀ : O)
  (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (hu₀ : u₀ ≠ 0)
  (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1 < Z) (bin : ℤ × (Fin 5 → ℤ))
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
  (hw₁ : s.W₁ 0 = 0) (hw₂ : s.W₂ 0 = 0)
  (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
local notation "datum" => geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
local notation "Kpos" => (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow)
local notation "firstLabel" => geometryFirstLabel s R seed (Z^Mrow) Z ξ Kpos bin q.1.val
local notation "unitMap" => (fun l => (firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l : O))
local notation "baseRay" => geometryDictionaryRay reflected s R seed (Z^Mrow) Z ξ Kpos bin q.1.val

/-- The key is constructed from the literal retained datum, including its
proved nonzero row and canonical partition. The second sign is exact. -/
def geometryLowRawKey (r : secondLiveRows (fun _ : Unit => (datum).block))
    (second : Bool) : NonzeroJointSourceLabel (!reflected) u₀ unitMap :=
  let hf := geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed
    (Z^Mrow) Z ξ Kpos bin q.1.val (fun _ : Unit => datum)
    (fun _ => firstLabel) r rfl
  let key := secondEncodedNonzeroRow (fun _ : Unit => (datum).block)
    (fun _ => firstLabel) r (!reflected) u₀ unitMap hf
  if second then reflectedNonzeroJointLabel key else key

local notation "rawKey" => geometryLowRawKey reflected η₀ u₀ F₀ R₀ hu₀ s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n

/-- The actual moving mask, in both orientations, is exactly the fixed mask
times the first missing radical modulo natural row zeros. The relation
`datum.R = R * C₁` is derived from `geometryLowSecondDatum`, not assumed. -/
theorem actual_geometry_low_common_mask (hη : s.η = excluded F₀.character R₀)
    (hR : R ≠ 0) (r : secondLiveRows (fun _ : Unit => (datum).block))
    (second : Bool) (ψ : RayCharacter) :
    let key := rawKey r second
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let hz : z ≠ 0 := by
      dsimp only [z]; split
      · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
      · exact (datum).rows_ne _ r.val.2.2.2.property
    let puncture := (datum).R * (if second then (datum).D else (datum).C)
    let commonMask := geometryRawFixedMask s R * firstSourceMissing (!reflected) firstLabel
    commonMask ≠ 0 ∧ ∀ I : Ideal O,
      idealCoeff (excluded (naturalRow ((datum).τ ψ) z hz).character puncture) I =
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ (baseRay, ψ))
        (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character commonMask) I := by
  intro key z hz puncture commonMask
  let src := geometryFirstSource s R seed (Z^Mrow) Z ξ Kpos bin q.1.val.1
  have hfixed : geometryRawFixedMask s R ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero s.η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72 : O) ≠ 0))) hR
  have hmissing : firstSourceMissing (!reflected) firstLabel ≠ 0 := by
    have hd := first_missing_dvd (!reflected) firstLabel src.hC.1
    intro hh
    rw [hh] at hd
    exact src.hC.1 (zero_dvd_iff.mp hd)
  have hdR : (datum).R ≠ 0 := actual_geometry_child_puncture_ne_zero
    reflected s R seed hR (Z^Mrow) Z ξ Kpos bin q.1.val
  refine ⟨mul_ne_zero hfixed hmissing, ?_⟩
  intro I
  have hd := actual_geometry_natural_dictionary reflected second η₀ u₀ F₀ R₀ hu₀ s hη
    R seed (Z^Mrow) Z ξ Kpos bin q.1.val (fun _ : Unit => datum)
    (fun _ => firstLabel) r rfl rfl hdR ψ
  apply (hd.2 I).trans
  change idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ (baseRay, ψ))
    (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character
      ((datum).input.η.modulus * puncture)) I = _
  have hc₁ : Supported key.val.1.1.1 := by cases second <;> exact src.hC
  have hd₁ : Supported key.val.1.1.2 := by cases second <;> exact src.hD
  have hs₁ : CompletedGauss.primeSupport key.val.1.1.1 =
      CompletedGauss.primeSupport key.val.1.1.2 := by cases second <;> exact src.sameSupport
  have hc₂ : Supported key.val.2.1.1 := by cases second <;> exact (datum).hC
  have hd₂ : Supported key.val.2.1.2 := by cases second <;> exact (datum).hD
  have hs₂ : CompletedGauss.primeSupport key.val.2.1.1 =
      CompletedGauss.primeSupport key.val.2.1.2 := by cases second <;> exact (datum).sameSupport
  have hm := actual_joint_common_mask (!reflected) second u₀ unitMap key
    hc₁ hd₁ hs₁ hc₂ hd₂ hs₂ (secondFixedDictionary η₀ (baseRay, ψ))
    (naturalRow _ _ (nonzeroJointSourceRow key).property) (geometryRawFixedMask s R) hfixed I
  have hp : (datum).input.η.modulus = s.η.modulus * Ideal.span {fixedBadMask} *
      Ideal.span {(72 : O)} * Ideal.span {
        primeSubsetGenerator (fun P : CommonIndex src.C src.D => P.val) src.inactive *
        activeConductor src.C src.D} :=
    actual_geometry_column_modulus reflected s R seed (Z^Mrow) Z ξ Kpos bin q.1.val
  have hr : (datum).R = R * geometryColumnIdeal reflected s R seed
      (Z^Mrow) Z ξ Kpos bin q.1.val := rfl
  have hfirst : key.val.1 = firstLabel := by cases second <;> rfl
  have hpair : key.val.2.1 = ((datum).C, (datum).D) := by cases second <;> rfl
  have hmask : (datum).input.η.modulus * puncture =
      geometryRawFixedMask s R *
        (Ideal.span {primeSubsetGenerator
          (fun P : CommonIndex key.val.1.1.1 key.val.1.1.2 => P.val) key.val.1.2.val *
          activeConductor key.val.1.1.1 key.val.1.1.2} *
        ((if !reflected then key.val.1.1.1 else key.val.1.1.2) *
          (if second then key.val.2.1.2 else key.val.2.1.1))) := by
    rw [hp]
    dsimp only [puncture]
    rw [hr, hfirst, hpair]
    change (s.η.modulus * Ideal.span {fixedBadMask} * Ideal.span {(72 : O)} *
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D => P.val) src.inactive *
          activeConductor src.C src.D}) *
        ((R * (if reflected then src.D else src.C)) *
          (if second then (datum).D else (datum).C)) =
      (s.η.modulus * Ideal.span {fixedBadMask} * Ideal.span {(72 : O)} * R) *
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D => P.val) src.inactive *
          activeConductor src.C src.D} *
          ((if !reflected then src.C else src.D) *
            (if second then (datum).D else (datum).C)))
    have hc : (if reflected then src.D else src.C) =
        (if !reflected then src.C else src.D) := by cases reflected <;> rfl
    rw [hc]
    ring
  rw [hmask]
  simpa only [hfirst, commonMask] using hm

/-- The fixed-inducing sector is transported exactly, with the same `Q`.
In particular, no principal or centered terminal branch is dropped. -/
theorem actual_geometry_low_fixed_inducing (hη : s.η = excluded F₀.character R₀)
    (hR : R ≠ 0) (r : secondLiveRows (fun _ : Unit => (datum).block))
    (second : Bool) (ψ : RayCharacter) (Q : Ideal O) :
    FixedInducingRow (secondFixedDictionary η₀ (baseRay, ψ)) Q fixedBadMask 1
        (nonzeroJointSourceRow (rawKey r second)).val ↔
      FixedInducingRow ((datum).τ ψ) Q fixedBadMask 1
        (if second then -r.val.2.2.2.val else r.val.2.2.2.val) := by
  let key := rawKey r second
  let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
  have hz : z ≠ 0 := by
    cases second
    · exact (datum).rows_ne _ r.val.2.2.2.property
    · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
  have hm := actual_geometry_low_common_mask reflected η₀ u₀ F₀ R₀ hu₀ s R seed
    Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n hη hR r second ψ
  have hp := actual_geometry_low_second_puncture reflected s R seed Z Mrow amp ξ reserve
    b t N hZ bin q hw₁ hw₂ n hR second
  exact natural_fixed_inducing_of_masked_ideal_eq
    (naturalRow (secondFixedDictionary η₀ (baseRay, ψ))
      (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property)
    (naturalRow ((datum).τ ψ) z hz) _ _ hm.1 hp (fun I => (hm.2 I).symm) Q

/-- Ordinary rows retain the original initialKeep predicate after the exact
dictionary transport. Both sign choices use the same fixed-inducing sector. -/
theorem actual_geometry_low_initialKeep (hη : s.η = excluded F₀.character R₀)
    (hR : R ≠ 0) (r : secondLiveRows (fun _ : Unit => (datum).block))
    (second : Bool) (ψ : RayCharacter) (Q : Ideal O) :
    initialKeep (secondFixedDictionary η₀ (baseRay, ψ)) Q
        (nonzeroJointSourceRow (rawKey r second)).val ↔
      (if second then -r.val.2.2.2.val else r.val.2.2.2.val) ≠ 0 ∧
        ¬FixedInducingRow ((datum).τ ψ) Q fixedBadMask 1
          (if second then -r.val.2.2.2.val else r.val.2.2.2.val) := by
  let key := rawKey r second
  let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
  have hz : z ≠ 0 := by
    cases second
    · exact (datum).rows_ne _ r.val.2.2.2.property
    · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
  have hm := actual_geometry_low_common_mask reflected η₀ u₀ F₀ R₀ hu₀ s R seed
    Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n hη hR r second ψ
  have hp := actual_geometry_low_second_puncture reflected s R seed Z Mrow amp ξ reserve
    b t N hZ bin q hw₁ hw₂ n hR second
  exact natural_initialKeep_of_masked_ideal_eq
    (naturalRow (secondFixedDictionary η₀ (baseRay, ψ))
      (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property)
    (naturalRow ((datum).τ ψ) z hz) (nonzeroJointSourceRow key).property hz
    _ _ hm.1 hp (fun I => (hm.2 I).symm) Q

/-- Membership in the literal ordinary second-row branch supplies initialKeep
for the raw row. The physical ordinary/exceptional split is not assumed as a
new analytic premise. -/
theorem actual_geometry_low_ordinary_keep (hη : s.η = excluded F₀.character R₀)
    (hR : R ≠ 0) (r : secondLiveRows (fun _ : Unit => (datum).block))
    (second : Bool) (χ₀ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) (m : O) (hm : m ≠ 0)
    (hml : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (hordinary : r.val.2.2.2.val ∈ CenteredMomentSecondEnergySplit.partRows false
      (datum).input.η χ₀ Q m (datum).C (datum).D (datum).inactive (datum).radius) :
    initialKeep (secondFixedDictionary η₀ (baseRay, ψ)) Q
      (nonzeroJointSourceRow (rawKey r second)).val := by
  apply (actual_geometry_low_initialKeep reflected η₀ u₀ F₀ R₀ hu₀ s R seed
    Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n hη hR r second ψ Q).mpr
  have ho := geometry_nonexceptional_reduced_pair (datum).input.η χ₀ ψ (ψ⁻¹) Q hQ
    m hm hml hm2 (datum).C (datum).D (datum).hC (datum).hD (datum).inactive
    (datum).τ (datum).family (datum).radius r.val.2.2.2.val hordinary
  cases second
  · exact ho.1
  · simpa only [inv_inv, ite_true] using ho.2

end Actual
end
end OAI.SevenEighths.Record12518109Raw

#print axioms OAI.SevenEighths.Record12518109Raw.actual_geometry_low_common_mask
#print axioms OAI.SevenEighths.Record12518109Raw.actual_geometry_low_fixed_inducing
#print axioms OAI.SevenEighths.Record12518109Raw.actual_geometry_low_initialKeep
#print axioms OAI.SevenEighths.Record12518109Raw.actual_geometry_low_ordinary_keep
