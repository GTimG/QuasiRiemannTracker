/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual marked coefficient vanishes on a nonsquarefree frozen ordinary pair. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalPhysical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.Projector
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSourceMass CenteredMomentRowNorm
open HeckeFamily CanonicalQuadraticSieve Record1252270103Second
open CenteredMomentRemainingBox CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentRestrictedSource
open CenteredMomentSourceLiveColumn CenteredMomentRestrictedEnergy CanonicalRowCompletion
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance maskedZeroDecidable : DecidableEq ι:=Classical.decEq _

def ordinarySquarefree (B:Tuple ι):Prop:=Squarefree (B (Sum.inr 0)*B (Sum.inr 1))

theorem pulled_marked_modifier_zero (B:Tuple ι)(A₁ A₂ D K:Ideal O)(F:Ideal O→ℂ)
    (hB:¬ordinarySquarefree B)(v:Tuple (liveIndices B)):
    pulledModifier B (Collision.markedSourceModifier A₁ A₂ D K F) v=0:=by
  by_contra hn
  have hs:Squarefree ((B (Sum.inr 0)*restoreTuple B v (Sum.inr 0))*
      (B (Sum.inr 1)*restoreTuple B v (Sum.inr 1))):=
    (Collision.markedSourceModifier_nonzero A₁ A₂ D K F _ hn).2
  rw [show (B (Sum.inr 0)*restoreTuple B v (Sum.inr 0))*
      (B (Sum.inr 1)*restoreTuple B v (Sum.inr 1))=
      (B (Sum.inr 0)*B (Sum.inr 1))*(restoreTuple B v (Sum.inr 0)*restoreTuple B v (Sum.inr 1)) by ring] at hs
  exact hB hs.of_mul_left

theorem child_divisor_energy_zero (s:Input ι)(X R L:Ideal O)(B:actualAllocations s.pools X)
    (A₁ A₂ D K:Ideal O)(F:Ideal O→ℂ)(τ:Character)(t:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(H:ℝ)(hB:¬ordinarySquarefree B.val):
    childDivisorEnergy s (Collision.markedSourceModifier A₁ A₂ D K F) X R L B τ t keep Φ H=0:=by
  have hc:QRH.Record1252270103Source.High.CoupledFirst.coefficient
      (child s X R B τ t) (pulledModifier B.val (Collision.markedSourceModifier A₁ A₂ D K F)) (R*X) L=0:=by
    funext I
    simp [QRH.Record1252270103Source.High.CoupledFirst.coefficient,
      QRH.Record1252270103Source.High.CoupledFirst.tupleCoefficient,finiteColumnCoefficient,
      pulled_marked_modifier_zero B.val A₁ A₂ D K F hB]
  unfold childDivisorEnergy
  rw [hc]
  simp [sourceRestrictedEnergy,restrictedEnergy,rowPolynomial]

def maskedAllocatedBudget (s:Input ι)(X R:Ideal O)(B:actualAllocations s.pools X)
    (S:Finset (ℕ×ℕ))(W₁ W₂ Φ:𝓢(ℝ,ℂ))(Q C D seed:Ideal O)
    (U:Finset (CommonIndex C D))(Z ε εL α Lraw Cr Mrow C₀ K₀:ℝ):ℝ:=
  if ordinarySquarefree B.val then
    correctedAllocatedBudget s X R B S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ else 0
end
end OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.pulled_marked_modifier_zero
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.child_divisor_energy_zero
