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
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/AllowedRows/LowKernel.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.Kernel

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def Iz (u : D.Row) (ξ w : ℂ) (v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral v (fun z => PoissonKernel.K D u ξ w z Z)

def Iwz (u : D.Row) (ξ : ℂ) (y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral y (fun w => Iz D u ξ w v Z)

def triple (u : D.Row) (x y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral x (fun ξ => Iwz D u ξ y v Z)

def explicitFactor (u : D.Row) (ξ w z : ℂ) : ℂ :=
  D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ

theorem explicitFactor_eq_rowFactor (u : D.Row) (ξ w z : ℂ) :
    explicitFactor D u ξ w z = PoissonKernel.rowFactor D u ξ w z := by
  unfold explicitFactor PoissonKernel.rowFactor
  ring

theorem explicitFactor_funext : explicitFactor D = PoissonKernel.rowFactor D := by
  funext u ξ w z
  exact explicitFactor_eq_rowFactor D u ξ w z

theorem K_eq_kernelWith (u : D.Row) (ξ w z : ℂ) (Z : ℝ) :
    PoissonKernel.K D u ξ w z Z = PoissonKernel.kernelWith D (explicitFactor D) u ξ w z Z := by
  rw [explicitFactor_funext]
  rfl

theorem Iz_eq_kernelWith (u : D.Row) (ξ w : ℂ) (v Z : ℝ) :
    Iz D u ξ w v Z = comparisonVerticalIntegral v
      (fun z => PoissonKernel.kernelWith D (explicitFactor D) u ξ w z Z) := by
  unfold Iz
  simp only [K_eq_kernelWith]

theorem Iwz_eq_wzIntegral (u : D.Row) (ξ : ℂ) (y v Z : ℝ) :
    Iwz D u ξ y v Z = PoissonKernel.wzIntegral D u ξ y v Z := rfl

theorem triple_eq_J (u : D.Row) (x y v Z : ℝ) :
    triple D u x y v Z = comparisonVerticalIntegral x
      (fun ξ => PoissonKernel.wzIntegral D u ξ y v Z) := rfl

end

end DedekindZetaZeroFree.Quantitative.LowRowKernelDefinitions

end Refinement9672
