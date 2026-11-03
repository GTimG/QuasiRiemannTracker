/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Principal/Contour/StripDefinitions.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Moments.Principal.Contour.Kernel

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalStripBasicDefinitions

noncomputable section

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
