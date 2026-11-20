/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/Global/FiniteSetEnlargement.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexStandardIntertwinerGerm
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.AdelicRestrictedProductTopology
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.Unramified.SphericalEulerNormalization
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.LFunctions.Dedekind.ExceptionalEulerNormalizer

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPGlobalFiniteSIntertwiner

open IsDedekindDomain Filter
open scoped NumberField Topology TensorProduct Classical

variable (F : Type) [Field F] [NumberField F]

def residueSize (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  Ideal.absNorm v.asIdeal

def goodFactor (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  KPGlobalGoodEulerFactor.sphericalCoefficient (residueSize F v) 1 s

def enlargementFactor (S T : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  ∏ v ∈ T \ S, goodFactor F v s

abbrev normalizer
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ → ℂ :=
  GlobalZetaNormalizer.exceptionalNormalizer  F ζ hζ S

def residueNormalizer
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  (PositiveZetaResidue.exteriorResidue F S : ℂ) /
    (6 * GlobalZetaNormalizer.exteriorZeta  F ζ hζ S 2)

theorem residueNormalizer_pos
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (residueNormalizer F  ζ hζ S).im = 0 ∧
    0 < (residueNormalizer F  ζ hζ S).re := by
  obtain ⟨ε, hε, hd, hm, hg, heq, hzero, him, hre, hrest⟩ :=
    GlobalZetaNormalizer.positive_simple_exceptional_normalizer  F ζ hζ S
  exact ⟨by simpa [residueNormalizer, hzero] using him,
    by simpa [residueNormalizer, hzero] using hre⟩

section TensorFormulas

universe u v
variable (V : KPHilbert.Place F → Type u) (W : KPHilbert.Place F → Type v)
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

end TensorFormulas

end DedekindZetaZeroFree.KPGlobalFiniteSIntertwiner

end
