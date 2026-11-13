/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/ComplexTraceMeasureParameters.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.LocalFields.SignedTraceUniformizer
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.HarmonicAnalysis.Haar.BalancedSectionDisintegration
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Adeles.Characters.StandardComplexCharacter

@[expose] public section

noncomputable section
open scoped NumberField Classical ENNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.TraceHaarTransport
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem traceHaarTransport_exists (R : PrincipalMellin.ActualRecipe S η) :
    Nonempty (MomentSources.TraceHaarTransport R) := by
  obtain ⟨μ, ν, hμ, hν, he⟩ := probe_polar_factors R
  letI : ∀ p, (μ p).IsHaarMeasure := hμ
  letI : ∀ w, (ν w).IsHaarMeasure := hν
  refine ⟨{
    signedUniformizer := signedUniformizer R
    finiteHaar := localNormalizedHaar F
    finiteHaar_add := fun p => inferInstance
    finite_mass := finite_trace_mass
    complexHaar := KPCplxCharacterHaar.characterHaar standardComplexParameter
    complex_mass := standard_complex_mass
    finiteMultHaar := μ
    finiteMultHaar_isHaar := hμ
    angularHaar := ν
    angularHaar_isHaar := hν
    groupHaar := ThetaPositiveSheetMellin.productHaar R.A μ ν
    groupHaar_isHaar := inferInstance
    polar_transport := rfl
    disintegration := he
    section_independent := section_integral R }⟩
end DedekindZetaZeroFree.TraceHaarTransport

end
