/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/ChosenPlaceIntegralBlockEquiv.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceAction
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Adele.FinitePlaceTensorBlock

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The chosen integral tensor equivalence

This file constructs the equivalence between the chosen integral tensor block
and the induced module of chosen local integer units.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

/-- Outside a finite exceptional set, the actual integral tensor-unit
subgroup at a finite place is the induced module of the
integer units at the chosen extension. -/
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w₀ ≃*
      ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀ :=
  by
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (chosenFinitePlaceExtension (L := L) w₀).1)
        𝒪[ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀]ˣ :=
      chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀
    exact
      (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
        (K := K) (L := L) w₀).trans
        (completionProductIntegerUnitsEquivInducedModule
          (K := K) (L := L)
          (HeightOneSpectrum.adicAbv K w₀)
          (RayClass.adicAbv_isNontrivial w₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)
          (chosenFinitePlaceExtension (L := L) w₀))
end ChosenFinitePlace

end
