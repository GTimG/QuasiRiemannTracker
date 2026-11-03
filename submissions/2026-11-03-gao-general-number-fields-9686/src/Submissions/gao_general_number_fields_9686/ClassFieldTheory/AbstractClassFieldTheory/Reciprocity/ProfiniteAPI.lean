/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ProfiniteAPI.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Profinite reciprocity facade

This module specializes the three principal finite reciprocity endpoints to a
bundled profinite group.  The bundle supplies the ambient topology, compactness,
separation, and total disconnectedness instances required by the generic
theorems.
-/

noncomputable section

namespace ClassFormation.Profinite

open CyclicCohomology KummerTheory

/-- The finite abelian norm-subgroup classification for a bundled profinite
group.  This is the thin specialization of the existing generic order
isomorphism; the profinite bundle supplies all ambient topological instances. -/
noncomputable def normSubgroupOrderIso
    (P : ProfiniteGrp) {D : DegreeData P} {A : Rep ℤ P}
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField P) :
    FiniteAbelianSubextension K.field ≃o
      (FiniteAbelianSubextension.NormOpenAddSubgroup A K.field)ᵒᵈ :=
  FiniteAbelianSubextension.normSubgroupOrderIso v hcf K

/-- The class field attached to a norm-open subgroup for a bundled profinite
group.  This thin specialization consumes the profinite norm-subgroup facade,
so callers do not enumerate ambient topological instances. -/
noncomputable def classField
    (P : ProfiniteGrp) {D : DegreeData P} {A : Rep ℤ P}
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField P)
    (N : FiniteAbelianSubextension.NormOpenAddSubgroup A K.field) :
    FiniteAbelianSubextension K.field :=
  (normSubgroupOrderIso P v hcf K).symm (OrderDual.toDual N)

/-- The finite norm-residue symbol for a bundled profinite group.  This is the
thin specialization of the existing generic symbol; the profinite bundle
supplies all ambient topological instances. -/
noncomputable def normResidueSymbol
    (P : ProfiniteGrp) (D : DegreeData P) (A : Rep ℤ P)
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField P) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    FiniteNormQuotient A K.field L.field L.below ≃+
      Additive (Abelianization L.extensionQuotient) :=
  D.normResidueSymbol A v hcf K L

end ClassFormation.Profinite

end
