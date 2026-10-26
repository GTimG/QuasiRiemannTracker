/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The normalized residual sum uses exactly the first allocated Input consumed
by the selected Newton family. This transport changes no weight or row. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedNewton
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalCorrectedResidual
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion CenteredMomentCanonicalFirst
open CenteredMomentExceptionalAmplitudePair
open Cycle61InitialMass Cycle61Moment OAI.SevenEighths.Record1252270103Source
open Record1252270103Second SecondRemainder Collision
local notation "O"=>HeckeFamily.O
local instance residualDictionaryDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem fixed_plain_energy_input_transport {α:Type}[Fintype α]
    (S T:Finset α)(hST:S=T)(s:Input S)(v:Input T)(hsv:HEq s v)
    (A₁ A₂ D K C R seed L:Ideal O)(F:Ideal O→ℂ)(hC:Supported C)
    (τ:Character)(t:ℝ)(z:O):
    fixedPlainEnergy s A₁ A₂ D K C R seed L F hC τ t z=
      fixedPlainEnergy v A₁ A₂ D K C R seed L F hC τ t z := by
  cases hST
  cases eq_of_heq hsv
  rfl

private theorem oriented_common_support {α:Type}[Fintype α]
    (d:SecondInputDatum α)(second:Bool):Supported (if second then d.D else d.C) := by
  cases second
  · exact d.hC
  · exact d.hD

/-- Both orientations keep the actual ray, signed row, Mellin height and
phase/outside/volume weight. The first common ideal appears only in Rchild. -/
theorem corrected_residual_first_child {α Label:Type}[Fintype α][Fintype Label]
    (s:Input α)(reflected second:Bool)(first:Label→FirstSourceLabel)(R:Ideal O)
    (B₁:∀l,actualAllocations s.pools (if reflected then (first l).1.2 else (first l).1.1))
    (τ₁:Label→Character)(t₁:Label→ℝ)(d:Label→SecondInputDatum α)
    (hslots:∀l,(d l).slots=liveIndices (B₁ l).val)
    (hinput:∀l,HEq (d l).input
      (child s (if reflected then (first l).1.2 else (first l).1.1) R (B₁ l) (τ₁ l) (t₁ l)))
    (hR:∀l,(d l).R=R*(if reflected then (first l).1.2 else (first l).1.1))
    (P:Finset (Ideal O))(w:Label→ℂ)(t u:ℝ):
    let A₁:=fun l=>(B₁ l).val (Sum.inr 0)
    let A₂:=fun l=>(B₁ l).val (Sum.inr 1)
    let K:=fun l=>markedProduct (B₁ l).val
    ∀(r:SecondRow (fun l=>(d l).block))(L:Ideal O),
    let common:=if second then (d r.1).D else (d r.1).C
    let hc:Supported common:=oriented_common_support (d r.1) second
    let τ:=if second then (d r.1).τ r.2.2.1⁻¹ else (d r.1).τ r.2.1
    let height:=(d r.1).input.t+2*Real.pi*(u-(if second then -t else t))
    let z:=if second then -r.2.2.2.val else r.2.2.2.val
    @correctedResidualTerm α Label _ _ _ second d P A₁ A₂ (fun _=>1) K w t u r L=
      fixedPlainEnergy
        (child s (if reflected then (first r.1).1.2 else (first r.1).1.1) R (B₁ r.1) (τ₁ r.1) (t₁ r.1))
        (A₁ r.1) (A₂ r.1) 1 (K r.1) common
        (R*(if reflected then (first r.1).1.2 else (first r.1).1.1)) (d r.1).seed L
        (poolCorrection P) hc τ height z*
          (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData) := by
  intro A₁ A₂ K r L common hc τ height z
  unfold correctedResidualTerm
  rw [hR r.1]
  have he:=fixed_plain_energy_input_transport _ _ (hslots r.1) _ _ (hinput r.1)
    (A₁ r.1) (A₂ r.1) 1 (K r.1) common
    (R*(if reflected then (first r.1).1.2 else (first r.1).1.1)) (d r.1).seed L
    (poolCorrection P) hc τ height z
  exact congrArg (fun v:ℝ=>v*(‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)) he

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.fixed_plain_energy_input_transport
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.corrected_residual_first_child
