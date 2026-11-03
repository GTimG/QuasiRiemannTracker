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
Original path: DedekindZetaZeroFree/Moments/Principal/Contour/Kernel.lean
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

namespace DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions

noncomputable section

open _root_.DedekindZetaZeroFree _root_.DedekindZetaZeroFree.Quantitative.PoissonKernel
open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowContLocal (u : D.Row) (ξ w z : ℂ) : ℂ :=
  D.zetaSCont (6 * z) * D.Lpsi u w * EulerDomain.Hu D u ξ w z / D.Llam u ξ

def wResidueLocal (u : D.Row) (ξ z : ℂ) (Z : ℝ) : ℂ :=
  Filter.limUnder (nhdsWithin (1 : ℂ) {1}ᶜ)
    (fun w : ℂ => (w - 1) * kernelWith D (rowContLocal D) u ξ w z Z)

def zResidueLocal (u : D.Row) (ξ : ℂ) (Z : ℝ) : ℂ :=
  Filter.limUnder (nhdsWithin (1 / 6 : ℂ) {1 / 6}ᶜ)
    (fun z : ℂ => (z - 1 / 6) * wResidueLocal D u ξ z Z)

end

end DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions

end Refinement9672
