/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LocalClassFieldTheory/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Infinite.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Kummer.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Local class field theory

This is the canonical root of the complete local class field theory library.
It reaches every supported implementation layer. Clients that need a smaller
dependency closure should import the semantic owner aggregate for the result
they use:

- `LocalClassFieldTheory.Finite.LocalReciprocity` for finite reciprocity;
- `LocalClassFieldTheory.Finite.Existence` for finite existence;
- `LocalClassFieldTheory.Infinite` for absolute and profinite reciprocity;
- `LocalClassFieldTheory.Kummer` for the local Kummer pairing;
- `LocalClassFieldTheory.LubinTateApplication` for Lubin--Tate applications.

The principal declarations live in the `LocalClassFieldTheory` namespace.
The abstract class-formation layer uses the `ClassFormation` namespace.

## Headline API

The finite reciprocity isomorphism and continuous Artin map:
- `LocalClassFieldTheory.localReciprocityEquiv`
- `LocalClassFieldTheory.localArtinMap`
- `LocalClassFieldTheory.localArtinMap_surjective`
- `LocalClassFieldTheory.localArtinMap_ker`

Finite local existence:
- `LocalClassFieldTheory.finiteAbelianNormSubgroupOrderIso`

Absolute and profinite reciprocity:
- `LocalClassFieldTheory.absoluteLocalArtinMap`
- `LocalClassFieldTheory.profiniteLocalReciprocity`
-/
