/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/AbelianConductorFiniteUnramified.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.EmbedsInRayClassFieldIffConductorLe
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.IsAbelianConductorUnique
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Zero finite exponent and unramifiedness
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- A finite place has exponent zero in the public conductor exactly when
every place above it is unramified. -/
theorem IsAbelianConductor.finiteExponent_eq_zero_iff_unramified
    {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    {c : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (v : HeightOneSpectrum (𝓞 K)) :
    c.finitePart v = 0 ↔
      ∀ W : HeightOneSpectrum (𝓞 L),
        W.asIdeal.LiesOver v.asIdeal →
          Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
  let H := GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
    (K := K) (L := L)
  have heq : c =
      ({ finitePart := H.fullConductor.finitePart
         infinitePart := H.fullConductor.infinitePart } : RayClassModulus K) :=
    hc.unique (normFullConductor_isAbelianConductor K L)
  have hsupport : c.finitePart.support =
      _root_.ramifiedBaseFinitePlaces (K := K) (L := L) := by
    rw [heq]
    change H.narrowFiniteConductor.support = _
    exact
      GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces
        (K := K) (L := L)
  calc
    c.finitePart v = 0 ↔ v ∉ c.finitePart.support :=
      (Finsupp.notMem_support_iff).symm
    _ ↔ v ∉ _root_.ramifiedBaseFinitePlaces (K := K) (L := L) := by
      rw [hsupport]
    _ ↔
        ∀ W : HeightOneSpectrum (𝓞 L),
          W.asIdeal.LiesOver v.asIdeal →
            Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
      rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
      constructor
      · intro h W hW
        by_contra hram
        exact h ⟨W, hW, hram⟩
      · intro h hram
        obtain ⟨W, hW, hnot⟩ := hram
        exact hnot (h W hW)

end ClassFieldTheory

end
