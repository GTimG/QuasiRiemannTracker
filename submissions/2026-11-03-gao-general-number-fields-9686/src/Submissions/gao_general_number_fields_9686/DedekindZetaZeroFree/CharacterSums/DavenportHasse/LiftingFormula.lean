/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/CharacterSums/DavenportHasse/LiftingFormula.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.CharacterSums.DavenportHasse.IrreduciblePolynomialSum
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.CharacterSums.DavenportHasse.ExtensionFieldCharacterSum

@[expose] public section

namespace DedekindZetaZeroFree

theorem davenportHasse :
  ∀ (k E : Type) [Field k] [Fintype k] [Field E] [Fintype E] [Algebra k E]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (χE : MulChar E ℂ) (ψE : AddChar E ℂ),
    (∃ x : k, ψ x ≠ 1) →
    (∀ x : E, χE x = χ (Algebra.norm k x)) →
    (∀ x : E, ψE x = ψ (Algebra.trace k E x)) →
    gaussSum χE ψE = -(-gaussSum χ ψ) ^ Module.finrank k E := by
  intro k E _ _ _ _ _ χ ψ χE ψE hψ hχE hψE
  have hn : 0 < Module.finrank k E := Module.finrank_pos
  rw [← DavenportHasse.b_eq χ ψ hψ hn, ← DavenportHasse.sum_lifted_eq_b E χ ψ]
  simp only [gaussSum, hχE, hψE]

end DedekindZetaZeroFree
