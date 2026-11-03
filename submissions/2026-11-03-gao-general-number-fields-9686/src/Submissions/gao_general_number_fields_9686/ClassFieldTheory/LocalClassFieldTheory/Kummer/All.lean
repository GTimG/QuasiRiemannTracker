/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LocalClassFieldTheory/Kummer/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.CanonicalKummerNorm
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerExponentTower
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerNormPowerClassDegree
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertExponentCompatibility
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairingNondegeneracy
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbolLaws
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.MaximalLocalKummerPairing
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/














set_option autoImplicit false

/-!
# Local Kummer reciprocity

Aggregate for the local Hilbert symbol, its laws, and the maximal local Kummer
pairing, including the tame power-residue formula.
-/
