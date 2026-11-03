/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/NormedModules/ContinuousTrace.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/Analysis/Normed/Module/Trace.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace DedekindZetaZeroFree.TauCeti

variable (𝕜 V : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

noncomputable def traceCLM : (V →L[𝕜] V) →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace 𝕜 V).comp (ContinuousLinearMap.coeLM 𝕜))

variable {𝕜 V}

@[simp]
theorem traceCLM_apply (T : V →L[𝕜] V) :
    traceCLM 𝕜 V T = LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) := by
  rw [traceCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

end DedekindZetaZeroFree.TauCeti
