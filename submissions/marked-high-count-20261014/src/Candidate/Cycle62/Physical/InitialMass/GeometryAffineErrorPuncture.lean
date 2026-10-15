/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorAbsoluteBox
import Candidate.Cycle62.Physical.InitialMass.GeometryMainHighSourceCaps
import Candidate.Cycle62.Physical.InitialMass.GeometryAffinePrimeGates

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondBlockAggregate
open CenteredMomentFirstCanonicalFamily Cycle62Moment
open CompletedGauss CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAnnularInput
local notation "O" => HeckeFamily.O

/-- A fixed error-puncture exponent follows from the actual first ideal,
amplifier prime and extracted second ideal. It has no slot-count parameter. -/
theorem geometry_error_puncture_norm (Z : ℝ) (hZ : 1<Z)
    (C E : Ideal O) (p : O) (k : ℕ) (hk : k≤7)
    (hC : (C.absNorm:ℝ)≤Z^(4:ℝ))
    (hp : ((Ideal.span {p}).absNorm:ℝ)≤Z^(3:ℝ))
    (hE : (E.absNorm:ℝ)≤Z^(3:ℝ)) :
    (((C*(Ideal.span {p})^k)*E).absNorm:ℝ)≤Z^(28:ℝ) := by
  have hpow : (((Ideal.span {p})^k).absNorm:ℝ)≤Z^(21:ℝ) := by
    rw [map_pow,Nat.cast_pow]
    calc
      _≤(Z^(3:ℝ))^k := pow_le_pow_left₀ (Nat.cast_nonneg _) hp k
      _=Z^((3:ℝ)*k) := (Real.rpow_mul_natCast (zero_lt_one.trans hZ).le _ _).symm
      _≤Z^(21:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le (by exact_mod_cast Nat.mul_le_mul_left 3 hk)
  rw [map_mul,Nat.cast_mul,map_mul,Nat.cast_mul]
  calc
    _≤(Z^(4:ℝ)*Z^(21:ℝ))*Z^(3:ℝ) :=
      mul_le_mul (mul_le_mul hC hpow (Nat.cast_nonneg _) (by positivity)) hE
        (Nat.cast_nonneg _) (by positivity)
    _=Z^(28:ℝ) := by rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)];norm_num

/-- The literal twice-extracted datum has both second ideals bounded by
a fixed exponent. The threshold may depend on the slot cap; the exponent
does not, and the Fourier scale below is the actual card α. -/
theorem eventual_actual_geometry_error_second_caps (N : ℕ)(b bs : ℝ)
    (hb : 1≤b)(hbs : 1≤bs) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)
      (M amp ξ reserve t : ℝ)(hZ : 1<Z),
      Fintype.card α≤N → Endpoints b bs bs s → volume s≤Z^(2:ℝ) →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
        (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0 →
      ∀(p : O),p≠0 → ∀(i : Fin 3),
      (∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→IsCoprime (Ideal.span {p}) I) →
      ∀(Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
        ((Ideal.span {p})^(errorIndex i+1))) (υ : Character)(v : ℝ)
        (n : GeometryErrorSecondIndex reflected s R seed Z M amp ξ reserve b t
          (Fintype.card α) hZ bin q p i Bp υ v),
      let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v hz₁ hz₂ n
      (d.C.absNorm:ℝ)≤Z^(3:ℝ) ∧ (d.D.absNorm:ℝ)≤Z^(3:ℝ) := by
  filter_upwards [eventual_geometry_error_child_source_cap N b bs 1 hb hbs (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s R seed M amp ξ reserve t hZ hn hend hvolume hz₁ hz₂ bin q hf p hp i hcop Bp υ v n d
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  have hchild := hz.2 s 2 hn hend hvolume _ R q.2 _ t hf p hp (errorIndex i+1) hcop
    (errorActiveAllocation _ _ Bp) υ v
  have hchild3 : sourceRadius (geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v)≤Z^(3:ℝ) := by
    convert hchild using 1 <;> norm_num
    rfl
  have hseed1 := actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
    (fun _=>logAnnulus) q.1.val q.1.property
  have hrad := actual_geometry_error_source_radius_pos reflected s R seed Z M amp ξ reserve hZ bin q p i
  have hg := actual_retained_block_gates _
    (geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v)
    ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin q.1.val)*(Ideal.span {p})^(errorIndex i+1))
    q.1.val.2.1.val hseed1 hz₁ hz₂
    (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i)
    (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ bin q p i)
    Z ξ hrad n
  exact ⟨hg.2.2.1.trans hchild3,hg.2.2.2.trans hchild3⟩

/-- The actual affine error datum admits the common mask exponent 28.
Only source and arithmetic gates occur here; no energy estimate is assumed. -/
theorem actual_geometry_error_puncture {α : Type}[Fintype α][DecidableEq α]
    (reflected : Bool)(s : Input α)(seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ)(hZ : 1<Z)
    (hseed : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^(3:ℝ))(bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s 1 seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O)(hp : p≠0)(hpN : ((Ideal.span {p}).absNorm:ℝ)≤Z^(3:ℝ))(i : Fin 3)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s 1 seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
      ((Ideal.span {p})^(errorIndex i+1))) (υ : Character)(v : ℝ)
    (n : GeometryErrorSecondIndex reflected s 1 seed Z M amp ξ reserve b t
      (Fintype.card α) hZ bin q p i Bp υ v)(second : Bool)
    (hsecond :
      let d:=geometryErrorSecondDatum reflected s 1 seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v hz₁ hz₂ n
      (d.C.absNorm:ℝ)≤Z^(3:ℝ) ∧ (d.D.absNorm:ℝ)≤Z^(3:ℝ)) :
    let d:=geometryErrorSecondDatum reflected s 1 seed Z M amp ξ reserve b t
      (Fintype.card α) hZ bin q p i Bp υ v hz₁ hz₂ n
    let puncture:=d.R*(if second then d.D else d.C)
    puncture≠0 ∧ (puncture.absNorm:ℝ)≤Z^(28:ℝ) := by
  intro d puncture
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  let C:=geometryColumnIdeal reflected s 1 seed (Z^M) Z ξ hK bin q.1.val
  have hc:=actual_geometry_main_first_norm_caps s 1 seed (Z^M) Z ξ hK hZ.le
    hseed hz₁ hz₂ hsource bin q.1.val
  have hC : (C.absNorm:ℝ)≤Z^(4:ℝ) := by
    cases reflected
    · exact hc.1
    · exact hc.2
  have hCn : C≠0 := by
    cases reflected
    · exact (geometryFirstSource s 1 seed (Z^M) Z ξ hK bin q.1.val.1).hC.1
    · exact (geometryFirstSource s 1 seed (Z^M) Z ξ hK bin q.1.val.1).hD.1
  have hE : ((if second then d.D else d.C).absNorm:ℝ)≤Z^(3:ℝ) := by
    cases second
    · exact hsecond.1
    · exact hsecond.2
  have hR : d.R=C*(Ideal.span {p})^(errorIndex i+1) := by
    change (1*C)*(Ideal.span {p})^(errorIndex i+1)=_
    rw [one_mul]
  have hk : errorIndex i+1≤7 := by
    rcases error_extracted_index_cases i with h|h|h <;> omega
  constructor
  · apply mul_ne_zero
    · rw [hR]
      exact mul_ne_zero hCn (pow_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr hp))
    · cases second
      · exact d.hC.1
      · exact d.hD.1
  · change ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤_
    rw [hR]
    exact geometry_error_puncture_norm Z hZ C _ p _ hk hC hpN hE

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_error_puncture_norm
#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_actual_geometry_error_second_caps
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_puncture
