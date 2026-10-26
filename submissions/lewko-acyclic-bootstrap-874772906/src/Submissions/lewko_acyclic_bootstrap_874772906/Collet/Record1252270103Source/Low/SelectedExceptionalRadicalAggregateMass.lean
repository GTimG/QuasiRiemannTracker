/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full original second blocks inject into the actual radical mass family. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.SelectedExceptionalNormalizedMaskedAudit
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalRadicalMass
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open Cycle61InitialMass Record1252270103Second Record1252270103CommonGeometry
open OAI.SevenEighths.Record1252270103Source ExceptionalRadical
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical SecondSectorDatum
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma sum_injective_le {α β:Type*}[Fintype α][Fintype β]
    (g:α→β)(hg:Function.Injective g)(f:β→ℝ)(hf:∀b,0≤f b):
    (∑a,f (g a))≤∑b,f b := by
  calc
    _=∑b∈Finset.univ.image g,f b:=by rw [Finset.sum_image];exact hg.injOn
    _≤_:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _=>hf b)

section Complete
variable {ι:Type*}[Fintype ι](s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)
    (W:𝓢(ℝ,ℂ))(K Tsec Z ξ:ℝ)

def completeToActive (q:CompleteBlock s modifier R seed W K Tsec Z ξ):
    ActiveBlocks (finiteColumns (Fintype.piFinset s.pools)) (CoupledFirst.coefficient s modifier R seed)
      K (frequencyRadius Tsec Z ξ) (sourceRadius s) :=
  ⟨⟨q.val.1.val,q.val.2.1⟩,q.val.2.2⟩

theorem completeToActive_injective:
    Function.Injective (completeToActive s modifier R seed W K Tsec Z ξ) := by
  rintro ⟨⟨⟨p,hp⟩,U,n⟩,hq⟩ ⟨⟨⟨p',hp'⟩,U',n'⟩,hq'⟩ h
  change (⟨⟨p,U⟩,n⟩:ActiveBlocks _ _ _ _ _) = ⟨⟨p',U'⟩,n'⟩ at h
  have he:=Sigma.mk.inj_iff.mp h
  have hpU:=Sigma.mk.inj_iff.mp he.1
  rcases hpU with ⟨rfl,heU⟩
  have heU':U=U':=eq_of_heq heU
  cases heU'
  have hen:n=n':=eq_of_heq he.2
  cases hen
  rfl

end Complete

def allocationRadical {ι:Type*}[Fintype ι](s:Input ι)(C D:Ideal O):ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ)*
    (Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)^(2*(499/1000:ℝ)-2)

lemma allocationRadical_nonneg {ι:Type*}[Fintype ι](s:Input ι)(C D:Ideal O):0≤allocationRadical s C D:=by
  unfold allocationRadical
  positivity

/-- Actual two projectors supply the valuation hypotheses on every active
common label, before restricting to nonzero original physical blocks. -/
theorem active_marked_valuations {ι:Type*}[Fintype ι]
    (s:Input ι)(A₁ A₂ Df K R seed:Ideal O)(F:Ideal O→ℂ)
    (p:ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s (Collision.markedSourceModifier A₁ A₂ Df K F) R seed)):
    ValuationAtMostTwo p.val.1 ∧ ValuationAtMostTwo p.val.2 := by
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩:=commonLabel_witnesses _ _ _ _ p.property
  have hh:=marked_common_valuations s A₁ A₂ Df K R seed I J F hIs hJs hβi hβj
  simpa only [hC,hD] using hh

theorem actual_complete_allocation_radical_mass (N:ℕ)(B L Cr ε:ℝ)
    (hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hε:0<ε):
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in atTop,
    ∀{ι:Type*}[Fintype ι],Fintype.card ι≤N→∀s:Input ι,
    s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
    ∀(A₁ A₂ Df Kmarked R seed:Ideal O)(F:Ideal O→ℂ),Squarefree seed→seed≠0→
    ∀(W:𝓢(ℝ,ℂ))(K Tsec ξ:ℝ),0<K→frequencyRadius Tsec Z ξ≤Cr*Z^L→
    (∑q:CompleteBlock s (Collision.markedSourceModifier A₁ A₂ Df Kmarked F) R seed W K Tsec Z ξ,
      allocationRadical s q.val.1.val.val.1 q.val.1.val.val.2)≤A*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨A,hA,hbound⟩:=actual_allocation_block_radical_mass N B L Cr ε hB hL hCr hε
  refine ⟨A,hA,?_⟩
  filter_upwards [hbound] with Z hz
  intro ι inst hι s hz₁ hz₂ hsource A₁ A₂ Df Kmarked R seed F hs hs0 W K Tsec ξ hK hR
  let modifier:Tuple ι→ℂ:=Collision.markedSourceModifier A₁ A₂ Df Kmarked F
  have hh:=hz (ι:=ι) hι s seed hs hs0 (finiteColumns (Fintype.piFinset s.pools))
    (CoupledFirst.coefficient s modifier R seed)
    (fun I _ hi=>CoupledFirst.original_column_mask s modifier R seed I hi)
    (fun I _ hi=>(CoupledFirst.original_column_norm s modifier R seed I hz₁ hz₂ hi).2.trans hsource)
    (active_marked_valuations s A₁ A₂ Df Kmarked R seed F)
    K (frequencyRadius Tsec Z ξ) (sourceRadius s) hK hR hsource
  apply le_trans _ hh
  exact sum_injective_le (completeToActive s modifier R seed W K Tsec Z ξ)
    (completeToActive_injective s modifier R seed W K Tsec Z ξ)
    (fun q=>allocationRadical s q.1.1.val.1 q.1.1.val.2)
    (fun q=>allocationRadical_nonneg s _ _)
end
end QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.completeToActive_injective
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.active_marked_valuations
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalRadicalAggregate.actual_complete_allocation_radical_mass
