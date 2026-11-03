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
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/TwistedRows.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.InitialIntegralIdentity

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.TwistedProbeRowDefinitions

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

abbrev TwistedRow : Type :=
  {f : PrincipalMellinComparison.Frequency D.recipe //
    f ∉ Set.range (PoissonInitialBridge.toProbeFrequency D)}

def rawIntegrand (f : PrincipalMellinComparison.Frequency D.recipe) (Z : ℝ)
    (t : ℝ × ℝ × ℝ) : ℂ :=
  ∑' a : ExteriorSquarefreeIdeal D.recipe.A.cS × D.recipe.A.Exterior ×
      D.recipe.A.Exterior × D.recipe.A.Exterior,
    NormalizedProbe.initialTripleMellinSummand D.recipe.probe
      (Scales.xScale Z) (Scales.yScale Z) Z (f, a) t

def rawRowIntegral (f : PrincipalMellinComparison.Frequency D.recipe) (Z : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, rawIntegrand D f Z t

def omittedSum (Z : ℝ) : ℂ :=
  ∑' f : TwistedRow D, rawRowIntegral D f.val Z

def omittedKernel (Z : ℝ) (t : ℝ × ℝ × ℝ) : ℂ :=
  ∑' f : TwistedRow D, rawIntegrand D f.val Z t

end

end DedekindZetaZeroFree.Quantitative.TwistedProbeRowDefinitions

end Refinement9672
