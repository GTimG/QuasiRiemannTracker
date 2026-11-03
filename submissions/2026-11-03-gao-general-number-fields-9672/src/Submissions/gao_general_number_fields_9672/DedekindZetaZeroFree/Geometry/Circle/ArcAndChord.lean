/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Geometry/Circle/ArcAndChord.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/Topology/Circle/Metric.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
Source Lean v4.35.0-rc3 / Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2;
Target Lean v4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Port: module surface/import paths and TauCeti namespace adapted; root extensions
and mathematical proof bodies retained unless an API adaptation is noted below.
-/

namespace DedekindZetaZeroFree.TauCeti

open Metric Set

open scoped Real

theorem exp_mul_I_sub_exp_mul_I (α β : ℝ) :
    Complex.exp (α * Complex.I) - Complex.exp (β * Complex.I) =
      2 * (Real.sin ((α - β) / 2) : ℂ) * Complex.I *
        Complex.exp ((((α + β) / 2 : ℝ) : ℂ) * Complex.I) := by
  have hsin : Complex.exp ((((α - β) / 2 : ℝ) : ℂ) * Complex.I) -
      Complex.exp (-(((α - β) / 2 : ℝ) : ℂ) * Complex.I) =
      2 * Complex.sin (((α - β) / 2 : ℝ) : ℂ) * Complex.I := by
    have h2 := Complex.two_sin ((((α - β) / 2 : ℝ) : ℂ))
    linear_combination (-Complex.I) * h2 +
      (Complex.exp ((((α - β) / 2 : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((α - β) / 2 : ℝ) : ℂ) * Complex.I)) * Complex.I_sq
  have h1 : (α : ℂ) * Complex.I =
      ((α + β) / 2 : ℝ) * Complex.I + (((α - β) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : (β : ℂ) * Complex.I =
      ((α + β) / 2 : ℝ) * Complex.I + -(((α - β) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add, ← mul_sub, hsin, ← Complex.ofReal_sin]
  ring

end DedekindZetaZeroFree.TauCeti
