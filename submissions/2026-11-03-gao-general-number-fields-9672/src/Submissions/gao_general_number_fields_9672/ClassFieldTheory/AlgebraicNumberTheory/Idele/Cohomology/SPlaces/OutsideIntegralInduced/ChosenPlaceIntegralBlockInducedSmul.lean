/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/ChosenPlaceIntegralBlockInducedSmul.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Equivariance of the induced integral block

This file proves that the inclusion of the chosen integral induced block is
equivariant for the global Galois action.
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

omit [NumberField L] in
/-- The embedding of the chosen integral induced block is equivariant for
the full global Galois action. -/
theorem chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_smul
    (w₀ : HeightOneSpectrum (𝓞 K))
    (τ : L ≃ₐ[K] L) :
    ∀ f : ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀,
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
        (K := K) (L := L) w₀
        ((chosenFinitePlaceInducedIntegerUnitsAction
          (K := K) (L := L) w₀).smul τ f) =
      (chosenFinitePlaceLocalPlaceBlockAction
        (K := K) (L := L) w₀).smul τ
        (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
          (K := K) (L := L) w₀ f) := by
  intro f
  rfl

end ChosenFinitePlace

end
