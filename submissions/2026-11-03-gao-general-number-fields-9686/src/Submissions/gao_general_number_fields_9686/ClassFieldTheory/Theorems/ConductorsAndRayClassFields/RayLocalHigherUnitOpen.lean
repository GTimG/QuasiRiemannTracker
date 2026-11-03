/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayLocalHigherUnitOpen.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Openness of local higher-unit groups

For every depth, including zero, the higher-unit subgroup is open in the
multiplicative group of the finite completion.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

open NumberField IsDedekindDomain

/-- Every local higher-unit group is open in the local multiplicative group. -/
theorem isOpen_rayLocalHigherUnitGroup
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    IsOpen ((rayLocalHigherUnitGroup v n :
      Subgroup (v.adicCompletion K)ˣ) : Set (v.adicCompletion K)ˣ) := by
  change IsOpen ((RayClass.localHigherUnitGroup v n :
    Subgroup (v.adicCompletion K)ˣ) : Set (v.adicCompletion K)ˣ)
  exact RayClass.isOpen_localHigherUnitGroup v n

end ClassFieldTheory

end
