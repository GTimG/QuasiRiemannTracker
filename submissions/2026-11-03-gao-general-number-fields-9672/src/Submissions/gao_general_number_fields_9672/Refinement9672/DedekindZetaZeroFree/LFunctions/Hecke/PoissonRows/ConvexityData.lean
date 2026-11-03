/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/LFunctions/Hecke/PoissonRows/ConvexityData.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Identification

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.ConvexBridge

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem conductor_bound' :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, 1 ≤ D.q u →
      (1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ) ≤ C * D.q u) ∧
      (1 + (Ideal.absNorm (D.omega u).conductor : ℝ) ≤ C * D.q u) := by
  obtain ⟨C, hC, h⟩ := RowHeckeBridge.conductor_bound D
  exact ⟨C, hC, fun u hu => ⟨(h u hu).1, (h u hu).2⟩⟩

theorem entire_eq_mask_mul (u : D.Row)
    (hnp : ¬ (D.inducers u).plus.character.IsPrincipal)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h : ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) :
    ∀ s : ℂ, 0 < s.re → g s =
      Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
        (fun v => (D.inducers u).plus.character v.asIdeal) s *
        (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnp).L s :=
  RowHeckeBridge.entire_eq_mask_mul_Lpsi D u hnp hg h

end

end DedekindZetaZeroFree.Quantitative.ConvexBridge

end Refinement9672
