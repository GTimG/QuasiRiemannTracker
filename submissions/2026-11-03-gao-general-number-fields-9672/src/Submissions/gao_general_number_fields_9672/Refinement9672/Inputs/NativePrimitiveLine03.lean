/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Noncircular successor input module, 2026-11-03, Zhongpai Gao with AI assistance.
Apache-2.0. Original theorem/dependency attribution below is retained.
Input module paths are relocated only; declaration namespaces stay original.
The old Hecke endpoint is supplied from the disjoint frozen original proof DAG.
Full native-import checking and successor endpoint verification remain pending.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.Inputs.NativePrimitivePositiveFE

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.BaselinePrimitive97

noncomputable section
open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

/-- Uniform primitive .03 bound. All growth, Euler-log, functional-equation,
root-number, and gamma-factor inputs are actual native theorems. The sole
remaining external parameter is the independently frozen original endpoint. -/
theorem primitive_line_03 (hF : NumberField.IsTotallyComplex F)
    (hbase : OldHeckeZeroFree31 F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Detector.PrimitiveFrequencyCharacter F) (_ : ¬ ν.character.IsPrincipal)
        (g : ℂ → ℂ), Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) →
        ∀ t : ℝ,
          ‖g (((3 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * (1 + (Ideal.absNorm ν.conductor : ℝ)) ^ ((47 : ℝ) / 100 + ε) *
              (2 + |t|) ^ A :=
  PrimitivePositiveFE.primitive_line_03_of_97 hF
    (fun ν hν => RawPrimitiveGrowth31.heckeData hF ν hν)
    (primitive_line_97 hF hbase)

#print axioms primitive_line_03

end
end DedekindZetaZeroFree.Quantitative.BaselinePrimitive97
