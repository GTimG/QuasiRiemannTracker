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
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/AllowedRows/LowContourShifts.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.ZControls
public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.WControls
public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.XiControls

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.LowRowContourShifts

noncomputable section

open _root_.DedekindZetaZeroFree _root_.DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions
open DedekindZetaZeroFree DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem Iwz_z_shift (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    Iwz D u ξ 4 2 Z = Iwz D u ξ 4 Scales.zLine Z := by
  unfold Iwz comparisonVerticalIntegral
  congr 2
  funext t
  exact LowRowZControls.Iz_shift D u hu Z hZ ξ _ hξ (by simp)

theorem Iwz_zw_shift (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ) (hξ : ξ.re = 4) :
    Iwz D u ξ 4 2 Z = Iwz D u ξ Scales.wLine Scales.zLine Z :=
  (Iwz_z_shift D u hu Z hZ ξ hξ).trans (LowRowWControls.Iwz_shift D u hu Z hZ ξ hξ)

theorem triple_shift (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    triple D u 4 4 2 Z = triple D u Scales.rightLine Scales.wLine Scales.zLine Z := by
  have h1 : triple D u 4 4 2 Z = triple D u 4 Scales.wLine Scales.zLine Z := by
    unfold triple comparisonVerticalIntegral
    congr 2
    funext t
    exact Iwz_zw_shift D u hu Z hZ _ (by simp)
  exact h1.trans (LowRowXiControls.triple_xi_shift D u hu Z hZ)

theorem triple_shift_K (u : D.Row) (hu : u.u ≠ 1) (Z : ℝ) (hZ : 0 < Z) :
    comparisonVerticalIntegral 4 (fun ξ => comparisonVerticalIntegral 4
        (fun w => comparisonVerticalIntegral 2 (fun z => PoissonKernel.K D u ξ w z Z))) =
      comparisonVerticalIntegral Scales.rightLine (fun ξ => comparisonVerticalIntegral Scales.wLine
        (fun w => comparisonVerticalIntegral Scales.zLine (fun z => PoissonKernel.K D u ξ w z Z))) :=
  triple_shift D u hu Z hZ

end

end DedekindZetaZeroFree.Quantitative.LowRowContourShifts

end Refinement9672
