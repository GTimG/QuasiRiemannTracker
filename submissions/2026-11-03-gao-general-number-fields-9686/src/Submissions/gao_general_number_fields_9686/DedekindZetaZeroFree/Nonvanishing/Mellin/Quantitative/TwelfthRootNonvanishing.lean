/-
2026-11-03 refinement by Zhongpai Gao (https://github.com/Gaozhongpai).
The following header records the PR #114 source provenance at 09afbb4ce6570c1615d58509dc197fc9f0956b7d.
This file now contains the native parameter refinement at
829193272c1eaf223bb7228fbfb9003f414808e9; local imports are relocated under Submissions.gao_general_number_fields_9686.
Original declaration namespaces and all source attribution are retained.
Native compilation and tracker admission remain pending; see Candidate.Provenance.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/Quantitative/TwelfthRootNonvanishing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LFunctions.Dedekind.AbelianContinuation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LFunctions.Dedekind.TwelfthRootPointwiseNonvanishing
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.PrincipalNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

theorem mu12_continuation_ne_zero (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (hmu : ∃ ζ : F, IsPrimitiveRoot ζ 12) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta F s) ∧
      ∀ s : ℂ, 4843 / 5000 < s.re → s ≠ 1 → f s ≠ 0 := by
  obtain ⟨f, hf, hmatch⟩ := DedekindZetaZeroFree.dedekindZeta_continuation F
  refine ⟨f, hf, hmatch, ?_⟩
  obtain ⟨ζ, hζ⟩ := hmu
  obtain ⟨S, _, hmod⟩ :=
    PrincipalMu12Pointwise.trivial_modulus_arithmetic_data_exists F ζ hζ
  have hchar : ∃ η : RayClassCharacter F S.modulus,
      η.IsPrincipal ∧ η.IsPrimitive := by
    rw [hmod]
    exact PrincipalMu12Pointwise.principal_primitive_top_character_exists F
  obtain ⟨η, hη, hprim⟩ := hchar
  obtain ⟨P⟩ := principalRayHeckeData_exists F htc S.modulus
    S.modulus_ne_zero η hprim hη
  have hLf : ∀ s : ℂ, 0 < s.re → s ≠ 1 → P.L s = f s := by
    clear hprim
    revert η hη P
    rw [hmod]
    intro η hη P
    exact PrincipalPointwise.principal_top_continuation_eq F η hη P f hf hmatch
  intro s hs hs1 hfs
  apply comparisonPrincipalIncompleteL_ne_zero F S η hη P s hs hs1
  simp [comparisonPrincipalIncompleteL, hLf s (by linarith) hs1, hfs]

end DedekindZetaZeroFree.Quantitative
