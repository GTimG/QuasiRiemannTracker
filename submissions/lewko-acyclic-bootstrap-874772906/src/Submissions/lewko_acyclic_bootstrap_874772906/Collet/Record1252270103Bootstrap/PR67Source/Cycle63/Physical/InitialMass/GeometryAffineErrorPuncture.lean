import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorAbsoluteBox
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePrimeGates
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondBlockAggregate
open CenteredMomentFirstCanonicalFamily Cycle63Moment
open CompletedGauss CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAnnularInput

/-- A fixed error-puncture exponent follows from the actual first puncture, first
ideal, amplifier prime and extracted second ideal. It has no slot-count parameter. -/
theorem geometry_error_puncture_norm (Z Rcap : ℝ) (hZ : 1<Z)
    (R C E : Ideal O) (p : O) (k : ℕ) (hk : k≤7)
    (hR : (R.absNorm:ℝ)≤Z^Rcap)
    (hC : (C.absNorm:ℝ)≤Z^(4:ℝ))
    (hp : ((Ideal.span {p}).absNorm:ℝ)≤Z^(3:ℝ))
    (hE : (E.absNorm:ℝ)≤Z^(3:ℝ)) :
    ((((R*C)*(Ideal.span {p})^k)*E).absNorm:ℝ)≤Z^(28+Rcap) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hpow : (((Ideal.span {p})^k).absNorm:ℝ)≤Z^(21:ℝ) := by
    rw [map_pow,Nat.cast_pow]
    calc
      _≤(Z^(3:ℝ))^k := pow_le_pow_left₀ (Nat.cast_nonneg _) hp k
      _=Z^((3:ℝ)*k) := (Real.rpow_mul_natCast hz.le _ _).symm
      _≤Z^(21:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le (by exact_mod_cast Nat.mul_le_mul_left 3 hk)
  simp only [map_mul,Nat.cast_mul]
  calc
    _≤((Z^Rcap*Z^(4:ℝ))*Z^(21:ℝ))*Z^(3:ℝ) :=
      mul_le_mul (mul_le_mul (mul_le_mul hR hC (Nat.cast_nonneg _) (by positivity)) hpow
        (Nat.cast_nonneg _) (by positivity)) hE (Nat.cast_nonneg _) (by positivity)
    _=Z^(28+Rcap) := by
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      ring

/-- The actual affine error datum at a first puncture of norm at most `Z^Rcap` admits
the common mask exponent `28 + Rcap`. Only source and arithmetic gates occur here; no
energy estimate is assumed. -/
theorem actual_geometry_error_puncture {α : Type}[Fintype α][DecidableEq α]
    (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z M amp ξ reserve b t Rcap : ℝ)(hZ : 1<Z)
    (hR : R≠0)(hRcap : (R.absNorm:ℝ)≤Z^Rcap)
    (hseed : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^(3:ℝ))(bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O)(hp : p≠0)(hpN : ((Ideal.span {p}).absNorm:ℝ)≤Z^(3:ℝ))(i : Fin 3)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
      ((Ideal.span {p})^(errorIndex i+1))) (υ : Character)(v : ℝ)
    (n : GeometryErrorSecondIndex reflected s R seed Z M amp ξ reserve b t
      (Fintype.card α) hZ bin q p i Bp υ v)(second : Bool)
    (hsecond :
      let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v hz₁ hz₂ n
      (d.C.absNorm:ℝ)≤Z^(3:ℝ) ∧ (d.D.absNorm:ℝ)≤Z^(3:ℝ)) :
    let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t
      (Fintype.card α) hZ bin q p i Bp υ v hz₁ hz₂ n
    let puncture:=d.R*(if second then d.D else d.C)
    puncture≠0 ∧ (puncture.absNorm:ℝ)≤Z^(28+Rcap) := by
  intro d puncture
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  let C:=geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin q.1.val
  have hc:=actual_geometry_main_first_norm_caps s R seed (Z^M) Z ξ hK hZ.le
    hseed hz₁ hz₂ hsource bin q.1.val
  have hC : (C.absNorm:ℝ)≤Z^(4:ℝ) := by
    cases reflected
    · exact hc.1
    · exact hc.2
  have hCn : C≠0 := by
    cases reflected
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hK bin q.1.val.1).hC.1
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hK bin q.1.val.1).hD.1
  have hE : ((if second then d.D else d.C).absNorm:ℝ)≤Z^(3:ℝ) := by
    cases second
    · exact hsecond.1
    · exact hsecond.2
  have hRd : d.R=(R*C)*(Ideal.span {p})^(errorIndex i+1) := rfl
  have hk : errorIndex i+1≤7 := by
    rcases error_extracted_index_cases i with h|h|h <;> omega
  constructor
  · apply mul_ne_zero
    · rw [hRd]
      exact mul_ne_zero (mul_ne_zero hR hCn) (pow_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr hp))
    · cases second
      · exact d.hC.1
      · exact d.hD.1
  · change ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤_
    rw [hRd]
    exact geometry_error_puncture_norm Z Rcap hZ R C _ p _ hk hRcap hC hpN hE

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
