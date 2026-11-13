/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardDominatingExtension.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardLubinTate
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Characteristic-independent dominating standard extensions

Every finite abelian local extension embeds into the fixed field represented
by a compositum of a canonical unramified factor and a canonical standard
Lubin--Tate factor.  Reverse inclusion of norm subgroups supplies the
embedding.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation CyclicCohomology
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- Source-producing form retaining the unramified degree, positive
principal-unit level, and the named characteristic-independent standard
compositum. -/
theorem exists_finiteAbelianDominatingStandardLubinTateCompositum
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ (d n : ℕ) (hd : 0 < d) (_hn : 0 < n),
      Nonempty
        (L →ₐ[K]
          abstractFixedField K (SeparableClosure K)
            (standardLubinTateFiniteAbelianCompositum K d n hd).field) := by
  let ϖ := inverseIntegerRingUniformizerFieldUnit K
  obtain ⟨d, n, hd, hn, hstandard⟩ :=
    exists_uniformizerPrincipalSubgroup_le_normSubgroup K L ϖ
  let P := standardLubinTateFiniteAbelianCompositum K d n hd
  have hP :
      finiteAbelianNormSubgroup K P ≤ localNormSubgroup K L := by
    simpa [P, ϖ] using
      (standardLubinTateFiniteAbelianCompositum_nativeNormSubgroup_le
        K (localNormSubgroup K L) d n hd hn hstandard)
  refine ⟨d, n, hd, hn, ?_⟩
  let E := abstractFixedField K (SeparableClosure K) P.field
  let : Finite
      ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
        extensionSubgroup
          (baseField (intrinsicAbsoluteGalois K)) P.field
          (le_baseField P.field)) :=
    finiteAbelianSubextension_finite_over_absoluteBase K P
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) P.field inferInstance
  let : IsAbelianGalois K E :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K P
  apply nonempty_algHom_of_normSubgroup_le K L E
  simpa [E, P, finiteAbelianNormSubgroup] using hP

/-- Every finite abelian local extension embeds in a represented finite
abelian fixed field obtained from the standard unramified/Lubin--Tate
construction. -/
theorem exists_finiteAbelianDominatingStandardFixedField
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ P : FiniteAbelianSubextension (intrinsicAbstractBase K),
      Nonempty
        (L →ₐ[K]
          abstractFixedField K (SeparableClosure K) P.field) := by
  obtain ⟨d, n, hd, _hn, hEmbed⟩ :=
    exists_finiteAbelianDominatingStandardLubinTateCompositum K L
  exact
    ⟨standardLubinTateFiniteAbelianCompositum K d n hd, hEmbed⟩

end LocalClassFieldTheory

end
