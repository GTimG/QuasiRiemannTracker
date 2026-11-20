/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original weighted source supplies the actual fixed Q and both anchor
keeps on every later source fiber. Native bounded exceptional-row support is
used before the live scale or source label; no exclusion is postulated. -/
import Candidate.C092.transport.SourceWindowCompactUniform
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.CertifiedFourier
set_option autoImplicit false
namespace QRH.Cycle092.SourceWindowCompact
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyBands
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open Cycle25ProbeFinalAssembly
local notation "O" => ActualEisensteinCubic.O
local notation "fixedQ" => Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal

/-- Actual original source data fix BOTH Q dictionaries. The native infimum
ideal is nonzero, proper and below span72, before any live reference or fiber.
The original modulus also contains the fixed bad-prime mask. -/
theorem original_source_dictionary_gates {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) :
    fixedQ F≤F.modulus ∧ fixedQ F≠0 ∧ fixedQ F≠⊤ ∧
      fixedQ F≤Ideal.span {(72:O)} ∧ F.modulus≤Ideal.span {fixedBadMask} ∧
      ∀ eta : Character,internalQ (fixedQ F) eta≠0 ∧
        internalQ (fixedQ F) eta≠⊤ ∧ internalQ (fixedQ F) eta≤Ideal.span {(72:O)} := by
  have hQ0 := Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_ne_zero F
  have hQt := Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_ne_top F
  have hQ72 := Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_le_72 F
  refine ⟨Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_le_modulus F,
    hQ0,hQt,hQ72,?_,?_⟩
  · simpa only [WeightedSourceData.modulus,rowMaskElement_eq_fixed] using source_product_le_rowMask F.S F.exclusions.bad
  · intro eta
    exact ⟨internalQ_ne_zero _ hQ0 eta,internalQ_ne_top _ hQt eta,inf_le_left.trans hQ72⟩

/-- Native bounded exceptional support disappears on the genuine original
large free rows. The same eventual event gives the fixed principal anchor and
EVERY actual original sourceMomentBase label, before a live fiber is chosen.
In particular QL=QW=fixedQ F is a concrete dictionary, not a source premise. -/
theorem original_source_keeps {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (etaOuter : Character) :
    ∀ᶠ Z : ℝ in atTop,
      ∀ label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤rowNorm u →
      initialKeep (fixedSourcePrincipal F.S F.exclusions.prime)
        (internalQ (fixedQ F) (fixedSourcePrincipal F.S F.exclusions.prime)) u.val ∧
      initialKeep (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime etaOuter label)
        (internalQ (fixedQ F)
          (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime etaOuter label)) u.val := by
  have hw (label : Sum Bool (RayQuotient.Characters F.modulus ⊤)) :=
    Cycle25WeightedNumeratorPhysical.eventually_fixed_source_keep F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime etaOuter label)
  filter_upwards [Filter.eventually_all.mpr hw,
    Cycle25WeightedNumeratorPhysical.eventually_fixed_source_keep F
      (fixedSourcePrincipal F.S F.exclusions.prime)] with Z hW hL
  intro label u hu
  exact ⟨hL u hu,hW label u hu⟩

/-- The two original keeps restrict to any later original same-row subclass,
including source Batch fibers and all offset-bank common intersections. -/
theorem original_source_keeps_on_rows {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (etaOuter : Character) :
    ∀ᶠ Z : ℝ in atTop,∀rows : Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u) →
      ∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (∀u∈rows,initialKeep (fixedSourcePrincipal F.S F.exclusions.prime)
        (internalQ (fixedQ F) (fixedSourcePrincipal F.S F.exclusions.prime)) u.val) ∧
      (∀u∈rows,initialKeep (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime etaOuter label)
        (internalQ (fixedQ F)
          (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime etaOuter label)) u.val) := by
  filter_upwards [original_source_keeps F etaOuter] with Z hZ
  intro rows hrows label
  exact ⟨fun u hu=>(hZ label u (hrows u hu)).1,fun u hu=>(hZ label u (hrows u hu)).2⟩

end
end QRH.Cycle092.SourceWindowCompact
#print axioms QRH.Cycle092.SourceWindowCompact.original_source_dictionary_gates
#print axioms QRH.Cycle092.SourceWindowCompact.original_source_keeps
#print axioms QRH.Cycle092.SourceWindowCompact.original_source_keeps_on_rows
