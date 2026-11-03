/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/KroneckerWeber/GlobalCompositumGlobalEmbedding.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.KroneckerWeber.GlobalCompositumLeftFactors

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The global cyclotomic factor inside the common local target

The global conductor cyclotomic field embeds, after base change and enlargement
of the order, into the common `p`-adic cyclotomic target used by the synchronized
valued compositum construction.
-/

noncomputable section

namespace KroneckerWeber

open AlgebraicNumberTheory
open AlgebraicNumberTheory.Valuations

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- The global conductor cyclotomic factor embedded after base change to
`ℚ_p` and enlargement of the cyclotomic order. -/
noncomputable def kroneckerWeberGlobalRightEmbeddingProperty
    (p : Nat.Primes) : Prop := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  exact Nonempty
    (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ →ₐ[ℚ]
      CyclotomicField (kroneckerWeberLocalCompositumOrder (L := L) p)
        ℚ_[p.1])

/-- At a ramified prime, the global conductor cyclotomic field embeds into
the common local cyclotomic target. -/
theorem kroneckerWeberGlobalRightEmbedding
    (p : Nat.Primes)
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) :
    kroneckerWeberGlobalRightEmbeddingProperty (L := L) p := by
  let : Fact p.1.Prime := ⟨p.2⟩
  exact ⟨cyclotomicFieldEmbeddingOfBaseAndDvd ℚ ℚ_[p.1]
    (kroneckerWeberConductorCandidate (L := L))
    (kroneckerWeberLocalCompositumOrder (L := L) p)
    (kroneckerWeberConductorCandidate_pos (L := L))
    (kroneckerWeberLocalCompositumOrder_pos (L := L) p)
    (kroneckerWeberConductorCandidate_dvd_localCompositumOrder
      (L := L) p hp)⟩

end KroneckerWeber

end
