/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal nonexceptional second-sector filter supplies both actual ray directions.
The original complete-block nonzero carrier and all modified coefficients remain intact. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedSecondFibersRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularRetainedNaturalState
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedSecondNatural
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
open ConcretePrimeRowBridge CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondLiveBlock CenteredMomentSectorLocalization CenteredMomentSecondRadicalBudget
open CenteredMomentRestrictedEnergy Cycle61FinalNatural Cycle61InitialMass
open OAI.SevenEighths.Record1252270103Source
open SecondSectorDatum High.GlobalPhysical SelectedSecondFibers
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
variable {α Label:Type*} [Fintype α] [Fintype Label]
variable (slots:Label→Finset α)(s:∀l,Input (slots l))(modifier:∀l,Tuple (slots l)→ℂ)
    (R seed:Label→Ideal O)(K Tsec:Label→ℝ)(Z ξ:ℝ)(W:𝓢(ℝ,ℂ))

/-- Exactly one reference ray is filtered. The varying physical ray is supplied
by a proved equivalence, not by strengthening the filter to all rays. -/
def regularKeep (χ₀:Label→RayCharacter)(Q:Ideal O)(m:O)
    (l:Label)(q:Record1252270103Second.BlockIndex (s l) (modifier l) (R l) (seed l) (K l) (Tsec l) Z ξ)
    (z:O):Prop :=
  nonexceptional (s l).η (χ₀ l) Q m
    (commonFrequencyGenerator q.1.val.val.1 q.1.val.val.2*
      nonunitFrequencyGenerator q.1.val.val.1 q.1.val.val.2 q.2.1) z

variable (hseed:∀l,Squarefree (seed l))(hz₁:∀l,(s l).W₁ 0=0)(hz₂:∀l,(s l).W₂ 0=0)
    (hK:∀l,0<K l)(χ₀:Label→RayCharacter)(Q:Ideal O)(m:O)

def regularDatum (q:CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ)):
    SecondInputDatum α :=
  familyDatum slots s modifier R seed hseed hz₁ hz₂ W K Tsec (fun _=>Z) (fun _=>ξ) hK
    (regularKeep slots s modifier R seed K Tsec Z ξ χ₀ Q m) q

/-- Membership in the actual twice-filtered row carrier implies the original
reference-ray keep gate. No nonvanishing of the restricted block is used. -/
theorem reference_row_nonexceptional
    (r:secondLiveRows (fun q=>(regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).block)):
    nonexceptional (s r.val.1.1).η (χ₀ r.val.1.1) Q m
      (regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1).block.frequency
      r.val.2.2.2.val := by
  exact (Finset.mem_filter.mp r.val.2.2.2.property).2

/-- The original keep filter admits the actual ray at either sign. -/
theorem actual_row_nonexceptional
    (r:secondLiveRows (fun q=>(regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).block))
    (ψ:RayCharacter)(second:Bool)(hQ:Q≤Ideal.span {(72:O)})(hml:goodLambda∣m)(hm2:(2:O)∣m):
    nonexceptional (regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1).input.η
      ψ Q m (regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1).block.frequency
      (if second then -r.val.2.2.2.val else r.val.2.2.2.val) := by
  have hk:=reference_row_nonexceptional slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r
  cases second
  · exact (nonexceptional_ray_independent (s r.val.1.1).η (χ₀ r.val.1.1) ψ Q hQ m _ _ hml hm2).mp hk
  · exact (nonexceptional_reflection (s r.val.1.1).η (χ₀ r.val.1.1) ψ Q hQ m _ _ hml hm2).mp hk

/-- Actual selected rows produce the enlarged natural state directly. The
only extra-puncture premise is its genuine nonzero polynomial norm cap. -/
theorem actual_kept_retained_state
    (r:secondLiveRows (fun q=>(regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).block))
    (second:Bool)(Bmask:ℝ)(hZ:1<Z)(ψ:RayCharacter)(J:Ideal O)
    (hR:R r.val.1.1≠0)(hJ:J≠0)
    (hPN:((enlargedRetainedPuncture
      (regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1) second J).absNorm:ℝ)≤Z^Bmask)
    (hm:m≠0)(hQ:Q≤Ideal.span {(72:O)})(hml:goodLambda∣m)(hm2:(2:O)∣m):
    let d:=regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1
    let st:=enlargedRetainedState d second Z Bmask hZ ψ Q J hR hJ hPN
    let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
    st.radial.keep z ∧ 1≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re ∧
      st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 ∧
      st.width≤Real.logb Z d.radius+Real.logb Z (d.input.η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator d.C d.D))+
        Real.logb Z ((∏p∈d.inactive,p.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  exact actual_enlarged_retained_state
    (regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m) r
    second Z Bmask hZ ψ Q J hR hJ hPN m hm hml hm2
    (actual_row_nonexceptional slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r ψ second hQ hml hm2)

end
end QRH.Record1252270103Source.Admission.SelectedSecondNatural
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondNatural.reference_row_nonexceptional
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondNatural.actual_row_nonexceptional
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondNatural.actual_kept_retained_state
