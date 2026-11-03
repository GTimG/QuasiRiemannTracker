/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Algebra.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.HasseArf
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.KroneckerWeber.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.KummerTheory.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LocalClassFieldTheory.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LocalFieldTheory.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.RamificationTheory.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/















set_option autoImplicit false

/-!
# Class field theory

This is the canonical entry point for the class field theory library.
Its import closure is the complete production-library inventory.

The library contains local class field theory and global class field theory
for number fields, including the Hilbert product formula, general
power-residue reciprocity, and Gauss quadratic reciprocity, together with the
Hasse--Arf and Kronecker--Weber theorems. Shared valuation, ramification,
cohomology, Kummer, local-field, and Lubin--Tate infrastructure lives beside
those theories rather than under a theorem-specific directory.

For a smaller production dependency closure, import
`LocalClassFieldTheory`, `GlobalClassFieldTheory`, `HasseArf`, or
`KroneckerWeber` directly.
-/
