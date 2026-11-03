/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayLocalHigherUnitAntitone.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Monotonicity of local higher-unit groups
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

open NumberField IsDedekindDomain

/-- Deeper local congruence conditions give smaller higher-unit groups. -/
theorem rayLocalHigherUnitGroup_antitone
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    {m n : ℕ} (hmn : m ≤ n) :
    rayLocalHigherUnitGroup v n ≤ rayLocalHigherUnitGroup v m := by
  change RayClass.localHigherUnitGroup v n ≤
    RayClass.localHigherUnitGroup v m
  exact RayClass.localHigherUnitGroup_antitone v hmn

end ClassFieldTheory

end
