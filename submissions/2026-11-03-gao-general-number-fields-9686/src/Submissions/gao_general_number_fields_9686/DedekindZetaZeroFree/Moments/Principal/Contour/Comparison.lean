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
Original path: DedekindZetaZeroFree/Moments/Principal/Contour/Comparison.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Moments.Principal.Contour.ZShift
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Moments.Principal.Contour.ResidueNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Principal

noncomputable section

open DedekindZetaZeroFree.Quantitative.PoissonKernel

variable {F : Type} [Field F] [NumberField F]
variable {S : DedekindZetaZeroFree.SArithmeticData F}
variable {η : DedekindZetaZeroFree.RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem savings_gt : (1 / 32 : ℝ) < 37719867 / 1000000000 ∧ (1 / 32 : ℝ) < 384999 / 10000000 := by
  norm_num

theorem principal_comparison :
    Spectral.c₀ D ≠ 0 ∧
    (∀ Z : ℝ, 2 ≤ Z →
      Jpr D Z = Spectral.c₀ D * Spectral.f D Z + PrincipalWShift.Rw D Z +
        PrincipalZShift.Rz D Z) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖PrincipalWShift.Rw D Z‖ ≤ C * Z ^ (Scales.mainExponent - 37719867 / 1000000000)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖PrincipalZShift.Rz D Z‖ ≤ C * Z ^ (Scales.mainExponent - 384999 / 10000000)) ∧
    (1 / 32 : ℝ) < 37719867 / 1000000000 ∧ (1 / 32 : ℝ) < 384999 / 10000000 := by
  refine ⟨ResidueNonzero.c₀_ne_zero D, fun Z hZ => ?_, PrincipalWShift.Rw_bound D,
    PrincipalZShift.Rz_bound D, savings_gt.1, savings_gt.2⟩
  rw [PrincipalWShift.Jpr_eq D Z hZ, PrincipalZShift.Jwres_eq D Z hZ]
  ring

end

end DedekindZetaZeroFree.Quantitative.Principal
