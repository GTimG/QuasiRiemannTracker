/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The complete selected second-family phase has the original parent normalizer.
Both sectors and every subsequent ratio restriction retain this bound. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedWeight
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonProfile CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondInputCapacitySource
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentSecondPhysicalBlock
open Cycle61InitialMass Record1252270103Second SecondSectorDatum
local notation "O"=>HeckeFamily.O

/-- Removing the phase and finite height characters costs no multiplicity. -/
theorem actual_family_weight_parent {α Label:Type*}
    [Fintype α][DecidableEq α][Fintype Label]
    (slots:Label→Finset α)(s:∀l,Input (slots l))(modifier:∀l,Tuple (slots l)→ℂ)
    (R seed:Label→Ideal O)(W:𝓢(ℝ,ℂ))(H Tsec Z ξ T a:Label→ℝ)
    (hT:∀l,0<T l)(ha:∀l,0≤a l)
    (keep:∀l,BlockIndex (s l) (modifier l) (R l) (seed l) (H l) (Tsec l) (Z l) (ξ l)→O→Prop)
    (q:CompleteFamily slots s modifier R seed W H Tsec Z ξ):
    ‖familyWeight slots s modifier R seed W H Tsec Z ξ T a keep q‖≤a q.1/T q.1 := by
  apply (familyWeight_norm_le slots s modifier R seed W H Tsec Z ξ T a hT ha keep q).trans
  have hb:=actual_second_block_weight_norm (s q.1) (modifier q.1) (R q.1) (seed q.1)
    (H q.1) (Tsec q.1) (Z q.1) (ξ q.1) q.2.val
  have hh:=mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (hT q.1).le) (ha q.1)
  simpa only [mul_one_div] using hh

/-- A scalar bound on the original phase weight passes through the actual
modified-block lower-support gate, including a zero selected block. -/
theorem actual_effective_weight_parent_bound {α Label:Type*}
    [Fintype α][DecidableEq α]
    (N:ℕ)(lo ap:ℝ)(hlo:0<lo)(hap:0<ap)
    (d:Label→SecondInputDatum α)(modifier:∀l,Tuple (d l).slots→ℂ)
    (w:Label→ℂ)(W:𝓢(ℝ,ℂ))(hN:Fintype.card α≤N)
    (hlower:∀l,lo≤(d l).input.lower)
    (hW₁:∀l x,(d l).input.W₁ x≠0→ap≤x)(hW₂:∀l x,(d l).input.W₂ x≠0→ap≤x)
    (a T:Label→ℝ)(hT:∀l,0<T l)(hw:∀l,‖w l‖≤a l/T l)
    (r:SecondRow (fun l=>modifiedDatumBlock (d l) (modifier l))):
    ‖secondEffectiveWeight (fun l=>modifiedDatumBlock (d l) (modifier l)) w W r.1‖*
      (d r.1).block.outside*volume (d r.1).input.toData≤
      (a r.1/T r.1)*((d r.1).K/lowerFactor N lo ap)*
        normalizer (d r.1).C (d r.1).D (d r.1).inactive := by
  apply (actual_modified_effective_physical_weight N lo ap hlo hap d modifier w W hN
    hlower hW₁ hW₂ r).trans
  apply mul_le_mul_of_nonneg_right _ (normalizer_pos _ _ (d r.1).hC _).le
  exact mul_le_mul_of_nonneg_right (hw r.1) (div_pos (d r.1).K_pos (lowerFactor_pos N lo ap hlo hap)).le

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_family_weight_parent
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_effective_weight_parent_bound
