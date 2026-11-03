/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/NormLimitationStatement.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormLimitation
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinMap

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Statement boundary for ideal norm limitation

This leaf packages the ideal norm-limitation equality behind a named
proposition.  Keeping the expanded normal-closure expression out of later
declaration signatures avoids repeatedly normalizing the full finite tower.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

variable
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The proposition asserting ideal norm limitation for one defining
modulus. -/
@[irreducible] noncomputable def idealNormSubgroupMaximalAbelianStatement
    (m : RayClass.Modulus K)
    (_hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) : Prop :=
  RayClass.idealNormSubgroup (K := K) (L := L) m =
    RayClass.idealNormSubgroup
      (K := K)
      (L := finiteNormalClosureMaximalAbelianSubfield K L)
      m

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
