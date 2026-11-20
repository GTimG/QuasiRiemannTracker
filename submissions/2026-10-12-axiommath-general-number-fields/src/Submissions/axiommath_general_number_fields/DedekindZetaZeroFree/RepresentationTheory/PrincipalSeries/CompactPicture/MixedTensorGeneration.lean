/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/CompactPicture/MixedTensorGeneration.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.IndependentSlicesAndUniformBands
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Algebra.TensorProducts.SeparatingEvaluations
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.TensorSectionSamplingGeneration

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPLiteralScalarMixedTensorGeneration
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPCplxIntertwinerEigenvalues
open KPLiteralScalarArchIndependentSlices KPLiteralScalarArchUniformBands
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices renaming harmonicBand_finite → harmonicBand_finite
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices renaming finite_interpolation → finite_interpolation

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι]

def familyTranslate (k : ι → ComplexSU2) :
    (Y → multiPrincipalSeries positiveParameter ι) →ₗ[ℂ]
      (Y → multiPrincipalSeries positiveParameter ι) :=
  LinearMap.pi (fun y => (multiTranslate positiveParameter k).comp (LinearMap.proj y))

def familyOrbit (h : Y → multiPrincipalSeries positiveParameter ι) :
    Submodule ℂ (Y → multiPrincipalSeries positiveParameter ι) :=
  Submodule.span ℂ (Set.range (fun k => familyTranslate k h))

open _root_.DedekindZetaZeroFree.KPLiteralScalarArchUniformBands renaming multiTranslate_mul → multiTranslate_mul
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchUniformBands renaming harmonicBand_mono → harmonicBand_mono

end DedekindZetaZeroFree.KPLiteralScalarMixedTensorGeneration

end
