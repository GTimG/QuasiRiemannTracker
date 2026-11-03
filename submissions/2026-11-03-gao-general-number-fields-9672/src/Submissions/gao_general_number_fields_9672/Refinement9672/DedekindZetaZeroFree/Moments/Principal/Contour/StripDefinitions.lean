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
Original path: DedekindZetaZeroFree/Moments/Principal/Contour/StripDefinitions.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Principal.Contour.Kernel

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.PrincipalStripBasicDefinitions

noncomputable section

open _root_.DedekindZetaZeroFree _root_.DedekindZetaZeroFree.Quantitative.PoissonKernel _root_.DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions
open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel
  DedekindZetaZeroFree.Quantitative.PrincipalKernelDefinitions Set Filter Complex
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def DecayOn (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C T0 : ℝ, ∀ x ∈ Icc a b, ∀ y : ℝ, T0 ≤ |y| →
    ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-B)

def kern (u : D.Row) (Z : ℝ) (ξ w z : ℂ) : ℂ := kernelWith D (rowContLocal D) u ξ w z Z

def Iz (u : D.Row) (Z v : ℝ) (ξ w : ℂ) : ℂ :=
  comparisonVerticalIntegral v (fun z => kern D u Z ξ w z)

def Iwz (u : D.Row) (Z y v : ℝ) (ξ : ℂ) : ℂ :=
  comparisonVerticalIntegral y (fun w => Iz D u Z v ξ w)

end

end DedekindZetaZeroFree.Quantitative.PrincipalStripBasicDefinitions

end Refinement9672
