/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual kept complete second rows receive enlarged natural states and a buffered
zero partition, without an assumed keep gate or any extra row multiplicity. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedSecondNaturalState
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularRetainedNaturalFamily
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedSecondNatural
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT LocalMoment
open ConcretePrimeRowBridge CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondLiveBlock CenteredMomentSectorLocalization
open CenteredMomentSecondRadicalBudget CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredMomentNaturalFixedRaySource Cycle61Moment.LowBranch
open CenteredMomentRestrictedEnergy Cycle61FinalNatural Cycle61InitialMass
open OAI.SevenEighths.Record1252270103Source
open SecondSectorDatum High.GlobalPhysical SelectedSecondFibers
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
variable {α Label:Type*} [Fintype α] [Fintype Label]
variable (slots:Label→Finset α)(s:∀l,Input (slots l))(modifier:∀l,Tuple (slots l)→ℂ)
    (R seed:Label→Ideal O)(K Tsec:Label→ℝ)(Z ξ:ℝ)(W:𝓢(ℝ,ℂ))
variable (hseed:∀l,Squarefree (seed l))(hz₁:∀l,(s l).W₁ 0=0)(hz₂:∀l,(s l).W₂ 0=0)
    (hK:∀l,0<K l)(χ₀:Label→RayCharacter)(Q:Ideal O)(m:O)
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

/-- The complete original block filter remains in the carrier. All further
finite selections or ratio restrictions may be represented by the map r.
Only actual puncture/source geometry and the fixed arithmetic mask gates remain. -/
theorem actual_kept_retained_family {Row:Type*}(rows:Finset Row)
    (r:rows→secondLiveRows (fun q=>(regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).block))
    (second:Bool)(Bmask bΦ:ℝ)(hZ:1<Z)(hbΦ:2≤bΦ)
    (ψ:rows→RayCharacter)(J:rows→Ideal O)
    (hR:∀u,R (r u).val.1.1≠0)(hJ:∀u,J u≠0)
    (hPN:∀u,((enlargedRetainedPuncture
      (regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m (r u).val.1)
      second (J u)).absNorm:ℝ)≤Z^Bmask)
    (hm:m≠0)(hQ:Q≤Ideal.span {(72:O)})(hml:goodLambda∣m)(hm2:(2:O)∣m)
    (η₀:Character)(hQM:Q≤M)(hQη:Q≤η₀.modulus)
    (e T q:ℝ)(he:0<e)(hT:2<T)(hq:1/2≤q)
    (hβlo:51/100≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8):
    let d:=regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m
    let base:=fun u=>enlargedRetainedState (d (r u).val.1) second Z Bmask hZ
      (ψ u) Q (J u) (hR u) (hJ u) (hPN u)
    let st:=fun u=>widenHighState (base u) bΦ hbΦ
    let z:=fun u=>if second then -(r u).val.2.2.2.val else (r u).val.2.2.2.val
    ∃keep:∀u,(st u).radial.keep (z u),
    ∃select:rows→BufferIndex e,∀u,
      1≤((st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)).re ∧
      (st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)≠0 ∧
      (st u).width≤Real.logb Z (d (r u).val.1).radius+
        Real.logb Z ((d (r u).val.1).input.η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator (d (r u).val.1).C (d (r u).val.1).D))+
        Real.logb Z ((∏p∈(d (r u).val.1).inactive,p.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) ∧
      RetainedZeroBin M H hH (st u) η₀ hQM hQη (z u) (keep u) e T (select u) ∧
      (bufferValue e (select u)<(q+1)/2→
        ActualLow M H hH (st u) η₀ hQM hQη ((q+1)/2) e
          (3*((select u).1.val+1:ℕ)*T) (z u)) ∧
      ((q+1)/2≤bufferValue e (select u)→
        3/4≤bufferValue e (select u) ∧ bufferValue e (select u)≤7/8 ∧
        q≤2*bufferValue e (select u)-1 ∧ 2*bufferValue e (select u)-1≤3/4 ∧
        2*bufferValue e (select u)-1≤2*HeckeZeroSupremum.beta-1) := by
  exact actual_enlarged_retained_family M H hH rows
    (regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m) r
    second Z Bmask bΦ hZ hbΦ ψ Q J hR hJ hPN m hm hml hm2
    (fun u=>actual_row_nonexceptional slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m
      (r u) (ψ u) second hQ hml hm2)
    η₀ hQM hQη e T q he hT hq hβlo hβhi

end
end QRH.Record1252270103Source.Admission.SelectedSecondNatural
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondNatural.actual_kept_retained_family
