/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full padded child columns reconstruct into original columns before any
coefficient filter. Thus fixed polynomial pool caps survive every extraction. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.LiveSupport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondProjectorShell

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentLiveSupport CenteredMomentRemainingBox
open CenteredMomentOriginalCommonHarmonic Cycle61InitialMass
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq ι:=Classical.decEq _
local instance {σ : Type*} : DecidableEq (σ⊕Fin 2):=Classical.decEq _

theorem child_padded_column_restores (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (I : Ideal O)
    (hI : I∈finiteColumns (Fintype.piFinset (child s C R B τ t).pools)) :
    C*I∈finiteColumns (Fintype.piFinset s.pools) := by
  have hcols : finiteColumns (liveBox s.pools B (alloc_ne s C B))=
      finiteColumns (Fintype.piFinset (child s C R B τ t).pools) := by
    apply congrArg finiteColumns
    ext v
    have hh:=Finset.ext_iff.mp (child_tuplePool s C R B τ t) v
    simpa only [Fintype.mem_piFinset] using hh
  rw [←hcols] at hI
  obtain ⟨v,hv,he⟩:=Finset.mem_image.mp hI
  have hm:=restored_original_mem s.pools s.prime C B (alloc_ne s C B)
    (Finset.mem_filter.mp B.property).1 v hv
  refine Finset.mem_image.mpr ⟨(fun j=>B.val j*restoreTuple B.val v j),?_,?_⟩
  · simpa only [Fintype.mem_piFinset] using hm
  rw [finiteTupleProduct,Finset.prod_mul_distrib]
  change finiteTupleProduct B.val*finiteTupleProduct (restoreTuple B.val v)=C*I
  have hb : finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2
  rw [hb,restore_product,he]

/-- No nonzero coefficient is needed. Every stored child column divides
an actual stored parent column, so the full cap contracts. -/
theorem child_full_column_cap (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t Y : ℝ)
    (hpool : ∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Y) :
    ∀I∈finiteColumns (Fintype.piFinset (child s C R B τ t).pools),(I.absNorm:ℝ)≤Y := by
  intro I hI
  have hm:=child_padded_column_restores s C R B τ t I hI
  have hn : C*I≠0 := by
    obtain ⟨v,hv,he⟩:=Finset.mem_image.mp hm
    rw [←he,finiteTupleProduct]
    exact Finset.prod_ne_zero_iff.mpr (fun j _=>s.pools_ne j (v j) (Fintype.mem_piFinset.mp hv j))
  exact (CenteredMomentFirstSourceConductorCaps.divisor_norm_le I (C*I) hn
    (dvd_mul_left I C)).trans (hpool (C*I) hm)

theorem two_child_full_column_cap (s : Input ι) (C₁ R₁ : Ideal O)
    (B₁ : actualAllocations s.pools C₁) (τ₁ : Character) (t₁ : ℝ)
    (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ Y : ℝ)
    (hpool : ∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Y) :
    ∀I∈finiteColumns (Fintype.piFinset (child (child s C₁ R₁ B₁ τ₁ t₁) C₂ R₂ B₂ τ₂ t₂).pools),
      (I.absNorm:ℝ)≤Y :=
  child_full_column_cap _ C₂ R₂ B₂ τ₂ t₂ Y
    (child_full_column_cap s C₁ R₁ B₁ τ₁ t₁ Y hpool)

end
end QRH.Record1252270103Source.InitialPhysical
#print axioms QRH.Record1252270103Source.InitialPhysical.child_padded_column_restores
#print axioms QRH.Record1252270103Source.InitialPhysical.child_full_column_cap
#print axioms QRH.Record1252270103Source.InitialPhysical.two_child_full_column_cap
