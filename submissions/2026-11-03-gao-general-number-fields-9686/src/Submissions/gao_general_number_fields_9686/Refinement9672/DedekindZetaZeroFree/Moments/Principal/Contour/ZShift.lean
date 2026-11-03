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
Original path: DedekindZetaZeroFree/Moments/Principal/Contour/ZShift.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Principal.Contour.ZResidueBounds

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.PrincipalZShift

noncomputable section

open _root_.DedekindZetaZeroFree _root_.DedekindZetaZeroFree.Quantitative.PoissonKernel _root_.DedekindZetaZeroFree.Quantitative.PrincipalWShift
open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel DedekindZetaZeroFree.Quantitative.PrincipalWShift
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def Rz (Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ principalRows D, comparisonVerticalIntegral Scales.rightLine (fun ξ =>
    comparisonVerticalIntegral (1 / 20) (fun z => wResidue D u ξ z Z))

theorem E_remainder :
    Scales.kernelExponent Scales.rightLine 1 (1 / 20) = Scales.mainExponent - 384999 / 10000000 := by
  unfold Scales.kernelExponent Scales.rightLine Scales.contourOffset Scales.xExponent Scales.smoothingExponent Scales.yExponent Scales.mainExponent
  norm_num

theorem Jwres_eq (Z : ℝ) (hZ : 2 ≤ Z) :
    Jwres D Z = Spectral.c₀ D * Spectral.f D Z + Rz D Z := by
  have h1 := PrincipalZShiftAux.Jwres_sub_Rz D Z hZ
  rw [PrincipalZShiftAux.zResidue_sum_eq D Z hZ] at h1
  unfold Rz
  linear_combination h1

theorem Rz_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖Rz D Z‖ ≤ C * Z ^ (Scales.mainExponent - 384999 / 10000000) := by
  unfold Rz
  exact PrincipalZShiftAux.Rz_integral_bound D

end

end DedekindZetaZeroFree.Quantitative.PrincipalZShift

end Refinement9672
