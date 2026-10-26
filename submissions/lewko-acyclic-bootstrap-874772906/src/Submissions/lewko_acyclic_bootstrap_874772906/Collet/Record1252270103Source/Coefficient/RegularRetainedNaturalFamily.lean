/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The retained family is built from actual geometric row data and the original
nonexceptional filter. Enlarged punctures and selected bins may vary by row. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularRetainedNaturalBins
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryHighAdmission

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion LocalMoment
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentNaturalFixedRaySource Cycle61Moment.LowBranch
open Cycle61FinalNatural Cycle61InitialMass
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The complete finite family receives actual natural states and one buffered
selector. No coefficient-dependent row is replaced by an ordinary block. -/
theorem actual_enlarged_retained_family {Row : Type*} (rows : Finset Row)
    (d : Label → SecondInputDatum α)
    (r : rows → secondLiveRows (fun l => (d l).block))
    (second : Bool) (Z Bmask bΦ : ℝ) (hZ : 1 < Z) (hbΦ : 2 ≤ bΦ)
    (ψ : rows → RayCharacter) (Q : Ideal O) (J : rows → Ideal O)
    (hR : ∀ u, (d (r u).val.1).R ≠ 0) (hJ : ∀ u, J u ≠ 0)
    (hPN : ∀ u, ((enlargedRetainedPuncture (d (r u).val.1) second (J u)).absNorm : ℝ) ≤ Z ^ Bmask)
    (m : O) (hm : m ≠ 0) (hml : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (hkeep : ∀ u, CenteredMomentRestrictedEnergy.nonexceptional (d (r u).val.1).input.η
      (ψ u) Q m (d (r u).val.1).block.frequency
      (if second then -(r u).val.2.2.2.val else (r u).val.2.2.2.val))
    (η₀ : Character) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (e T q : ℝ) (he : 0 < e) (hT : 2 < T) (hq : 1 / 2 ≤ q)
    (hβlo : 51 / 100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    let base := fun u => enlargedRetainedState (d (r u).val.1) second Z Bmask hZ
      (ψ u) Q (J u) (hR u) (hJ u) (hPN u)
    let st := fun u => widenHighState (base u) bΦ hbΦ
    let z := fun u => if second then -(r u).val.2.2.2.val else (r u).val.2.2.2.val
    ∃ keep : ∀ u, (st u).radial.keep (z u),
    ∃ select : rows → BufferIndex e, ∀ u,
      1 ≤ ((st u).radial.profile (‖eisEmbedding (z u)‖ ^ 2 / (st u).radial.scale)).re ∧
      (st u).radial.profile (‖eisEmbedding (z u)‖ ^ 2 / (st u).radial.scale) ≠ 0 ∧
      (st u).width ≤ Real.logb Z (d (r u).val.1).radius +
        Real.logb Z ((d (r u).val.1).input.η.modulus.absNorm : ℝ) -
        Real.logb Z (normValue (commonFrequencyGenerator (d (r u).val.1).C (d (r u).val.1).D)) +
        Real.logb Z ((∏ p ∈ (d (r u).val.1).inactive, p.val).absNorm : ℝ) +
        Real.logb Z (4 * (fixedFactor : ℝ)) ∧
      RetainedZeroBin M H hH (st u) η₀ hQM hQη (z u) (keep u) e T (select u) ∧
      (bufferValue e (select u) < (q + 1) / 2 →
        ActualLow M H hH (st u) η₀ hQM hQη ((q + 1) / 2) e
          (3 * ((select u).1.val + 1 : ℕ) * T) (z u)) ∧
      ((q + 1) / 2 ≤ bufferValue e (select u) →
        3 / 4 ≤ bufferValue e (select u) ∧ bufferValue e (select u) ≤ 7 / 8 ∧
        q ≤ 2 * bufferValue e (select u) - 1 ∧ 2 * bufferValue e (select u) - 1 ≤ 3 / 4 ∧
        2 * bufferValue e (select u) - 1 ≤ 2 * HeckeZeroSupremum.beta - 1) := by
  intro base st z
  have had (u : rows) := actual_enlarged_retained_state d (r u) second Z Bmask hZ
    (ψ u) Q (J u) (hR u) (hJ u) (hPN u) m hm hml hm2 (hkeep u)
  let keep : ∀ u, (st u).radial.keep (z u) := fun u => (had u).1
  have hp (u : rows) := actual_retained_zero_partition M H hH (st u) η₀ hQM hQη
    (z u) (keep u) e T he hT hβlo hβhi
  let select : rows → BufferIndex e := fun u => Classical.choose (hp u)
  refine ⟨keep, select, ?_⟩
  intro u
  have hbin := Classical.choose_spec (hp u)
  refine ⟨(had u).2.1, (had u).2.2.1, (had u).2.2.2, hbin, ?_, ?_⟩
  · intro hlow
    exact retained_zero_bin_low M H hH (st u) η₀ hQM hQη (z u) (keep u) e T q
      (select u) hbin hlow (had u).2.2.1
  · exact retained_zero_bin_high M H hH (st u) η₀ hQM hQη (z u) (keep u) e T q
      (select u) hbin hq

#print axioms actual_enlarged_retained_family
end
end OAI.SevenEighths.Record1252270103Source
