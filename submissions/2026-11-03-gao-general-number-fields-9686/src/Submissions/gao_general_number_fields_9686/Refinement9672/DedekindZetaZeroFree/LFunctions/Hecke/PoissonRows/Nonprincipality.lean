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
Original path: DedekindZetaZeroFree/LFunctions/Hecke/PoissonRows/Nonprincipality.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.RowNonprincipal

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField
open PrincipalMellinComparison.NonprincipalContinuation

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem inducers_nonprincipal (u : D.Row) (hu : u.u ≠ 1) :
    ¬ (D.inducers u).plus.character.IsPrincipal ∧ ¬ (D.omega u).character.IsPrincipal := by
  classical
  obtain ⟨h0, hmem⟩ := u.isRep
  let f : PrincipalMellinComparison.Frequency D.recipe := ⟨⟨u.u, h0⟩, hmem⟩
  have hf : f ≠ PrincipalMellinComparison.principalFrequency D.recipe := by
    intro h
    apply hu
    have := congrArg (fun x : PrincipalMellinComparison.Frequency D.recipe => x.val.val) h
    simpa [f, PrincipalMellinComparison.principalFrequency] using this
  let U : AllRowEuler.InitialSeparation.RawFrequency D.recipe.A :=
    { u := u.u, ideal := u.toFrequency.ideal, generates := u.toFrequency.generates,
      sixthFree := u.toFrequency.sixthFree }
  have hU : U.u = f.val.val := rfl
  have hP : ∀ I : D.recipe.A.Exterior,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient D.recipe.σ U I =
        Detector.deletedPrimitiveIdealCoefficient F (D.inducers u).plus
          (RawHeckeRows.rawDeletionSet U) I.val := by
    intro I
    have h := (D.inducers u).plus_mask I.val
    unfold FrequencyCharacterMasks.plusCoefficient at h
    rw [dif_pos I.property] at h
    exact h
  have hM : ∀ I : D.recipe.A.Exterior,
      AllRowEuler.InitialSeparation.minusExteriorCoefficient D.recipe.σ D.recipe.target U I =
        Detector.deletedPrimitiveIdealCoefficient F (D.inducers u).minus
          (RawHeckeRows.rawDeletionSet U) I.val := by
    intro I
    have h := (D.inducers u).minus_mask I.val
    unfold FrequencyCharacterMasks.minusCoefficient FrequencyCharacterMasks.plusCoefficient at h
    rw [dif_pos I.property] at h
    exact h
  exact RawHeckeRows.actual_raw_inducers_nonprincipal D.recipe f U hU hf
    (D.inducers u).plus (D.inducers u).minus hP hM

end

end DedekindZetaZeroFree.Quantitative.RowNonprincipal

end Refinement9672
