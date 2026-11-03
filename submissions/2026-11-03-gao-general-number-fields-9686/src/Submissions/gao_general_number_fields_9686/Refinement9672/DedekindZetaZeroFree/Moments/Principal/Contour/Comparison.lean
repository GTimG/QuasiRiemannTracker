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
Original path: DedekindZetaZeroFree/Moments/Principal/Contour/Comparison.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Principal.Contour.ZShift
public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Principal.Contour.ResidueNonvanishing

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.Principal

noncomputable section

open _root_.DedekindZetaZeroFree.Quantitative.PoissonKernel
open DedekindZetaZeroFree.Quantitative.PoissonKernel

variable {F : Type} [Field F] [NumberField F]
variable {S : DedekindZetaZeroFree.SArithmeticData F}
variable {η : DedekindZetaZeroFree.RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem savings_gt : (1 / 32 : ℝ) < 37439867 / 1000000000 ∧ (1 / 32 : ℝ) < 384999 / 10000000 := by
  norm_num

theorem principal_comparison :
    Spectral.c₀ D ≠ 0 ∧
    (∀ Z : ℝ, 2 ≤ Z →
      Jpr D Z = Spectral.c₀ D * Spectral.f D Z + PrincipalWShift.Rw D Z +
        PrincipalZShift.Rz D Z) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖PrincipalWShift.Rw D Z‖ ≤ C * Z ^ (Scales.mainExponent - 37439867 / 1000000000)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖PrincipalZShift.Rz D Z‖ ≤ C * Z ^ (Scales.mainExponent - 384999 / 10000000)) ∧
    (1 / 32 : ℝ) < 37439867 / 1000000000 ∧ (1 / 32 : ℝ) < 384999 / 10000000 := by
  refine ⟨ResidueNonzero.c₀_ne_zero D, fun Z hZ => ?_, PrincipalWShift.Rw_bound D,
    PrincipalZShift.Rz_bound D, savings_gt.1, savings_gt.2⟩
  rw [PrincipalWShift.Jpr_eq D Z hZ, PrincipalZShift.Jwres_eq D Z hZ]
  ring

end

end DedekindZetaZeroFree.Quantitative.Principal

end Refinement9672
