/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual retained rows, not a substituted width hypothesis, supply the natural
state width. The fixed factor is absorbed before all moving row labels. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularRetainedNaturalState
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularSelectedStateCaps
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonical
open CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth CenteredMomentSupport
open OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O

theorem eventually_actual_enlarged_width (ηwidth:ℝ)(hηwidth:0<ηwidth) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{α Label:Type*}[Fintype α][DecidableEq α][Fintype Label]
      (d:Label→SecondInputDatum α)(r:secondLiveRows (fun l=>(d l).block))(second:Bool)
      (Bmask Bradius Bchar Binactive:ℝ)(ψ:RayCharacter)(Q J:Ideal O)
      (hR:(d r.val.1).R≠0)(hJ:J≠0)
      (hPN:((enlargedRetainedPuncture (d r.val.1) second J).absNorm:ℝ)≤Z^Bmask),
      (d r.val.1).radius≤Z^Bradius→
      ((d r.val.1).input.η.modulus.absNorm:ℝ)≤Z^Bchar→
      ((∏p∈(d r.val.1).inactive,p.val).absNorm:ℝ)≤Z^Binactive→
      (enlargedRetainedState (d r.val.1) second Z Bmask hZ ψ Q J hR hJ hPN).width≤
        Bradius+Bchar+Binactive+ηwidth := by
  filter_upwards [fixed_width_cost_eventually ηwidth hηwidth] with Z hfixed
  refine ⟨hfixed.1,?_⟩
  intro hZ α Label instα instDec instLabel d r second Bmask Bradius Bchar Binactive ψ Q J hR hJ hPN
    hradius hchar hinactive
  let v:=d r.val.1
  have hret:=actual_second_live_retained_weight (fun l=>(d l).block) r.val r.property
  have hrpos:0<v.radius:=by
    have hh:=retainedWeight_enclosure _ _ hret
    change 0< (d r.val.1).block.radius
    linarith [hh.1,hh.2]
  have hcharpos:(0:ℝ)<v.input.η.modulus.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.input.η.modulus_ne_bot)
  have hinactive0:(∏p∈v.inactive,p.val)≠0:=Finset.prod_ne_zero_iff.mpr
    (fun p _=>(commonPrime_supported_ideal v.C v.D v.hC p).1)
  have hinactivepos:(0:ℝ)<(∏p∈v.inactive,p.val).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hinactive0)
  have hradlog:Real.logb Z v.radius≤Bradius:=(Real.logb_le_iff_le_rpow hZ hrpos).mpr hradius
  have hcharlog:Real.logb Z (v.input.η.modulus.absNorm:ℝ)≤Bchar:=
    (Real.logb_le_iff_le_rpow hZ hcharpos).mpr hchar
  have hinactivelog:Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ)≤Binactive:=
    (Real.logb_le_iff_le_rpow hZ hinactivepos).mpr hinactive
  have hcommonlog:0≤Real.logb Z (normValue (commonFrequencyGenerator v.C v.D)):=
    Real.logb_nonneg hZ (normValue_ge_one _ (commonFrequencyGenerator_ne_zero v.C v.D v.hC))
  have hw:=actual_second_live_state_width d r Z Bmask hZ ψ Q
    (enlargedRetainedPuncture v second J) (enlarged_retained_puncture_ne v second J hR hJ) hPN
  change (enlargedRetainedState v second Z Bmask hZ ψ Q J hR hJ hPN).width≤
    Real.logb Z v.radius+Real.logb Z (v.input.η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
      Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) at hw
  linarith [hfixed.2]

end
end QRH.Record1252270103Source.RegularSelectedStateCaps
#print axioms QRH.Record1252270103Source.RegularSelectedStateCaps.eventually_actual_enlarged_width
