/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The same-key source family is used at the literal common second Mellin
height. Empty families vanish before any nonempty source invocation. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularCofactor
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open Admission.SelectedRegularSourceData Admission.SelectedHighCofactorFamily
local notation "O"=>HeckeFamily.O
local instance regularCofactorBridgeDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- This is the finite transport into the normalized collector. Its point
estimate is the common LOW/HIGH conclusion, with all true data unchanged. -/
theorem regular_cofactor_of_centered
    {α Label:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}(F:Family a Label)
    (second:Bool)(P:Finset (Ideal O))(depth:ℕ)(weight:F.Complete→ℂ)
    (origin t u E:ℝ)(hE:0≤E)(hstage:∀l,(F.stage l).t=origin)
    (hpoint:∀{Row:Type}[Fintype Row](rows:Finset Row)[Nonempty rows]
      (G:Selected F Row rows second),Function.Injective G.key→Squarefree G.L→
      (G.L.absNorm:ℝ)≤Z^(4:ℝ)→(∀r,G.ψ r=regularRowRay F second (G.row r))→
      ∀S∈P.powerset.filter (fun S=>S.card≤depth),∀A∈S.powerset,∀T:Finset α,
      (∀r,T⊆(G.sel r).full)→
      (∑r:rows,‖regularSelectedCentered G S A T (mellinShift origin second t u) r‖^2*
        selectedPaidWeight (G.sel r) (residualWeight F.datum weight (G.row r).val))≤E):
    RegularCofactorBound F second P depth weight t u (9/4) 4 E:=by
  intro Row inst rows G hinj hL hLcap hψ S hS A hA T hT
  by_cases hn:Nonempty rows
  · letI:=hn
    have h:=hpoint rows G hinj hL hLcap hψ S hS A hA T hT
    simp only [regularSelectedCentered,regularSelectedSlots] at h
    simpa only [regular_common_residual_height F origin t u second hstage] using h
  · letI:IsEmpty rows:=not_nonempty_iff.mp hn
    simpa using hE

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_cofactor_of_centered
