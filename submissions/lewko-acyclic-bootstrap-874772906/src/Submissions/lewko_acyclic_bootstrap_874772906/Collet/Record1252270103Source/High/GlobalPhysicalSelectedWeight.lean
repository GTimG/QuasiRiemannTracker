/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The selected MAIN weight retains the original volume and pays the actual
first frozen allocation before entering the second cofactor family. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondWeight
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SecondSectorDatumFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedHighCoordinatesScalar
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceSecondZeroEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceMass CenteredMomentActiveSource CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSectorLocalization
open Cycle61InitialMass Record1252270103Second SecondSectorDatum
open OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O
local instance selectedWeightDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem actual_second_block_weight_norm {ι:Type*}[Fintype ι]
    (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(H Tsec Z ξ:ℝ)
    (q:BlockIndex s modifier R seed H Tsec Z ξ):
    ‖blockWeight s modifier R seed H Tsec Z ξ q‖≤1 := by
  have hb (I:Ideal O):‖CenteredMomentHeckeColumnWindow.heightCoeff s.η s.t I‖≤1 := by
    by_cases hI:I=0
    · rw [hI,CenteredMomentHeckeColumnWindow.heightCoeff,HeckeFamily.idealCoeff_zero,zero_mul,norm_zero]
      exact zero_le_one
    · exact heightCoeff_norm_le_one s.η s.t I hI
  rw [blockWeight,norm_mul,norm_star]
  exact (mul_le_mul (hb _) (hb _) (norm_nonneg _) zero_le_one).trans_eq (by ring)

theorem selected_frozen_volume_mass {ι:Type*}[Fintype ι]
    (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t ε:ℝ)(hε:0≤ε):
    ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
      (volume (child s C R B τ t)/volume s)≤forcedProfileCost s*(C.absNorm:ℝ)^(ε-1) := by
  have hC:=allocation_ne s C B
  have hN:(0:ℝ)<C.absNorm:=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hN1:(1:ℝ)≤C.absNorm:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hV:=volume_pos s
  have hf:=div_le_div_of_nonneg_right (frozen_child_volume_cost s C R hC B τ t) hV.le
  have hf':‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
      (volume (child s C R B τ t)/volume s)≤forcedProfileCost s/(C.absNorm:ℝ):=by
    convert hf using 1 <;> field_simp
  apply hf'.trans
  rw [Real.rpow_sub hN,Real.rpow_one,←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hN.le
  exact le_mul_of_one_le_right (forcedProfileCost_nonneg s) (Real.one_le_rpow hN1 hε)

/-- The residual-row weight is the actual second physical weight. Its
finite cap carries the entire selected first coefficient; no norm estimate
is used here. Both allocation cardinalities may be retained in extra/card2. -/
theorem selected_two_allocation_weight {ι:Type*}[Fintype ι]
    (s:Input ι)(C₁ R:Ideal O)(B₁:actualAllocations s.pools C₁)(τ₁:Character)(t₁:ℝ)
    (C₂ D₂:Ideal O)(hC₂:Supported C₂)(U:Finset (CommonIndex C₂ D₂))(second:Bool)
    (B₂:actualAllocations (child s C₁ R B₁ τ₁ t₁).pools (if second then D₂ else C₂))
    (τ₂:Character)(t₂:ℝ)(scalar:ℂ)(extra card2 H lower Z amp ε ω:ℝ)
    (he:0≤extra)(hH:0≤H)(hl:0<lower)(hZ:0<Z)(hε:0≤ε)
    (hω:ω≤(‖scalar‖^2*extra*‖frozenCoefficient B₁.val C₁ R s.ν s.W s.P‖^2/volume s)*
      (H/lower)*normalizer C₂ D₂ U):
    let s₁:=child s C₁ R B₁ τ₁ t₁
    let Cchosen:=if second then D₂ else C₂
    let s₂:=child s₁ Cchosen (R*C₁) B₂ τ₂ t₂
    let secondCost:=‖frozenCoefficient B₂.val Cchosen (R*C₁) s₁.ν s₁.W s₁.P‖^2*
      (volume s₂/volume s₁)*forcedProfileCost s₂
    card2^2*secondCost*ω≤
      (extra*card2^2*Z^amp/lower*forcedProfileCost s)*
        (‖scalar‖^2*(C₁.absNorm:ℝ)^(ε-1))*
        (Z^(-amp)*(H/volume s₁)*normalizer C₂ D₂ U*secondCost) := by
  intro s₁ Cchosen s₂ secondCost
  have hv:=volume_pos s
  have hv₁:=volume_pos s₁
  have hn:0≤normalizer C₂ D₂ U:=(normalizer_pos C₂ D₂ hC₂ U).le
  have hcst:0≤secondCost:=by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg (volume_pos s₂).le hv₁.le))
      (forcedProfileCost_nonneg s₂)
  have hh:=mul_le_mul_of_nonneg_left hω (mul_nonneg (sq_nonneg card2) hcst)
  have hf:=selected_frozen_volume_mass s C₁ R B₁ τ₁ t₁ ε hε
  have factor:0≤extra*card2^2*‖scalar‖^2/lower*(H/volume s₁)*normalizer C₂ D₂ U*secondCost:=by positivity
  have hf':=mul_le_mul_of_nonneg_left hf factor
  have hp:Z^amp*Z^(-amp)=1:=by rw [←Real.rpow_add hZ]; simp
  apply hh.trans
  calc
    _=(extra*card2^2*‖scalar‖^2/lower*(H/volume s₁)*normalizer C₂ D₂ U*secondCost)*
      (‖frozenCoefficient B₁.val C₁ R s.ν s.W s.P‖^2*(volume s₁/volume s)):=by field_simp
    _≤_:=hf'
    _=_:=by
      calc
        _=(extra*card2^2/lower*forcedProfileCost s)*
          (‖scalar‖^2*(C₁.absNorm:ℝ)^(ε-1))*
          ((H/volume s₁)*normalizer C₂ D₂ U*secondCost)*(Z^amp*Z^(-amp)):=by rw [hp]; ring
        _=_:=by ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_second_block_weight_norm
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.selected_frozen_volume_mass
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.selected_two_allocation_weight
