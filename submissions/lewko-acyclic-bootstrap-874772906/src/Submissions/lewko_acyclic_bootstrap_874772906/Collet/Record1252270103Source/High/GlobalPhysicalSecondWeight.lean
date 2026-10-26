/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual modified second block supplies the lower-support witness that
pays its outside scalar. A vanished selected block has zero effective weight. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondContraction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSupport
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondInputCapacitySource
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem modified_column_lower_support {ι:Type*}[Fintype ι][DecidableEq ι]
    (N:ℕ)(a ap:ℝ)(ha:0<a)(hap:0<ap)(s:Input ι)
    (modifier:Tuple ι→ℂ)(hcard:Fintype.card ι≤N)(hlower:a≤s.lower)
    (hW₁:∀x,s.W₁ x≠0→ap≤x)(hW₂:∀x,s.W₂ x≠0→ap≤x)
    (R seed I:Ideal O)(hne:CoupledFirst.coefficient s modifier R seed I≠0):
    lowerFactor N a ap*volume s.toData≤(I.absNorm:ℝ) := by
  have hm:0≤min 1 a:=(lt_min zero_lt_one ha).le
  have hprod:(min 1 a)^N≤∏i,s.lo i := by
    apply (pow_le_pow_of_le_one hm (min_le_left _ _) hcard).trans
    have h:=Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun _:ι=>min 1 a) (g:=fun i=>s.lo i)
      (fun _ _=>hm) (fun i _=>(min_le_right _ _).trans (hlower.trans (s.lower_le i)))
    simpa only [Finset.prod_const,Finset.card_univ] using h
  have h:=CoupledFirst.original_column_lower s modifier R seed I ap ap hap.le hap.le hW₁ hW₂ hne
  apply le_trans _ h
  have hV:0≤volume s.toData:=(volume_pos _).le
  unfold lowerFactor
  nlinarith only [mul_le_mul_of_nonneg_right hprod (mul_nonneg (sq_nonneg ap) hV)]

theorem actual_modified_second_outside {α:Type*}[Fintype α][DecidableEq α]
    (N:ℕ)(a ap:ℝ)(ha:0<a)(hap:0<ap)(d:SecondInputDatum α)
    (modifier:Tuple d.slots→ℂ)(W:𝓢(ℝ,ℂ))(hcard:Fintype.card α≤N)
    (hlower:a≤d.input.lower)
    (hW₁:∀x,d.input.W₁ x≠0→ap≤x)(hW₂:∀x,d.input.W₂ x≠0→ap≤x)
    (hne:(modifiedDatumBlock d modifier).value W≠0):
    d.block.outside≤d.K/(lowerFactor N a ap*volume d.input.toData)*
      normalizer d.C d.D d.inactive := by
  apply actual_second_outside_volume (modifiedDatumBlock d modifier) W
    (lowerFactor N a ap) (volume d.input.toData)
    (lowerFactor_pos N a ap ha hap) (volume_pos _) _ hne
  intro I hi
  have hc:Fintype.card d.slots≤Fintype.card α := by simpa using Finset.card_le_univ d.slots
  exact modified_column_lower_support N a ap ha hap d.input modifier
    (hc.trans hcard) hlower hW₁ hW₂ d.R d.seed I hi

/-- The coefficient is modified before testing the effective-block zero.
No nonvanishing assertion about the ordinary coefficient is used. -/
theorem actual_modified_effective_physical_weight {α Label:Type*}
    [Fintype α][DecidableEq α]
    (N:ℕ)(a ap:ℝ)(ha:0<a)(hap:0<ap)
    (d:Label→SecondInputDatum α)(modifier:∀l,Tuple (d l).slots→ℂ)
    (w:Label→ℂ)(W:𝓢(ℝ,ℂ))(hcard:Fintype.card α≤N)
    (hlower:∀l,a≤(d l).input.lower)
    (hW₁:∀l x,(d l).input.W₁ x≠0→ap≤x)(hW₂:∀l x,(d l).input.W₂ x≠0→ap≤x)
    (r:SecondRow (fun l=>modifiedDatumBlock (d l) (modifier l))):
    ‖secondEffectiveWeight (fun l=>modifiedDatumBlock (d l) (modifier l)) w W r.1‖*
      (d r.1).block.outside*volume (d r.1).input.toData≤
      ‖w r.1‖*((d r.1).K/lowerFactor N a ap)*normalizer (d r.1).C (d r.1).D (d r.1).inactive := by
  have hp:=lowerFactor_pos N a ap ha hap
  have hv:=volume_pos (d r.1).input.toData
  have hn:=normalizer_pos (d r.1).C (d r.1).D (d r.1).hC (d r.1).inactive
  by_cases h:(modifiedDatumBlock (d r.1) (modifier r.1)).value W=0
  · simp only [secondEffectiveWeight,h,ite_true,norm_zero,zero_mul]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (div_pos (d r.1).K_pos hp).le) hn.le
  · have ho:=actual_modified_second_outside N a ap ha hap (d r.1) (modifier r.1) W hcard
      (hlower r.1) (hW₁ r.1) (hW₂ r.1) h
    simp only [secondEffectiveWeight,h,ite_false]
    have hm:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ho (norm_nonneg (w r.1))) hv.le
    apply hm.trans_eq
    field_simp

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_column_lower_support
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_modified_second_outside
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_modified_effective_physical_weight
