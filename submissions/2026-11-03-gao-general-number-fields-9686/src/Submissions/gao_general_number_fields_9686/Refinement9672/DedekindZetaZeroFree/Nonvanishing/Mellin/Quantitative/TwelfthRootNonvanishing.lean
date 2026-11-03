/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/Quantitative/TwelfthRootNonvanishing.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LFunctions.Dedekind.AbelianContinuation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LFunctions.Dedekind.TwelfthRootPointwiseNonvanishing
public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.PrincipalNonvanishing

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree

theorem mu12_continuation_ne_zero (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (hmu : ∃ ζ : F, IsPrimitiveRoot ζ 12) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta F s) ∧
      ∀ s : ℂ, 1209 / 1250 < s.re → s ≠ 1 → f s ≠ 0 := by
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

end Refinement9672
