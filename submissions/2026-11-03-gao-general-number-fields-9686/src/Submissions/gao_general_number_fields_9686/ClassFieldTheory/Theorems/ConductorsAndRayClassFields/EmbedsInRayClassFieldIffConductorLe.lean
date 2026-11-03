/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/EmbedsInRayClassFieldIffConductorLe.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The full conductor as a minimal modulus

Let `L/K` be finite abelian.  Its conductor is the least modulus whose ray
class field contains `L`.  Since the public interface makes no global choice
of ray class fields, the theorem asserts existence of this least modulus.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- A finite abelian extension has a conductor characterized by containment
in ray class fields. -/
theorem embedsInRayClassField_iff_conductor_le
    (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    ∃ c : RayClassModulus K, IsAbelianConductor K L c := by
  let H := GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
    (K := K) (L := L)
  let c : RayClassModulus K :=
    { finitePart := H.fullConductor.finitePart
      infinitePart := H.fullConductor.infinitePart }
  exact ⟨c, normFullConductor_isAbelianConductor K L⟩

end ClassFieldTheory

end
