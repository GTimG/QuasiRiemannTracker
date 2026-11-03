/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Weil/ThetaAndQuadraticOperators.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.DilationAndTranslation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalDifferentNormalization
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Weil.QuadraticFourierOperatorsAndPhases

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.QuadraticRawProduct

variable (F : Type) [Field F] [NumberField F]

def theta (T : Finset (HeightOneSpectrum (𝓞 F)))
    (f : PoissonS.Space F T → ℂ) : ℂ :=
  ∑' x : sIntegerRing F T, f (PoissonS.diagonalHom F T (x : F))

def chirp (T : Finset (HeightOneSpectrum (𝓞 F))) (b : F)
    (f : PoissonS.Space F T → ℂ) : PoissonS.Space F T → ℂ :=
  fun x => (sLocalTraceCharacter F T
    (sLocalDiagonal F T b * ((PoissonS.localProductToSpace F T).symm x) ^ 2) : ℂ) * f x

def dilation (T : Finset (HeightOneSpectrum (𝓞 F))) (c : F)
    (f : PoissonS.Space F T → ℂ) : PoissonS.Space F T → ℂ :=
  fun x => f (PoissonS.localProductToSpace F T
    (sLocalDiagonal F T c * (PoissonS.localProductToSpace F T).symm x))

local instance completionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

abbrev fourier (T : Finset (HeightOneSpectrum (𝓞 F))) :=
  PoissonS.fourierIntegral F T (fun v : T => localFiniteCharacter F v.val)
    (fun v : T => localNormalizedHaar F v.val)

def testSpace (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Submodule ℂ (PoissonS.Space F T → ℂ) :=
  Submodule.span ℂ {f | ∃ (fArch : SchwartzMap (PoissonArch.Space F) ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ),
    (∀ v, IsLocallyConstant (φ v)) ∧ (∀ v, HasCompactSupport (φ v)) ∧
    f = PoissonS.tensorFunction F T fArch φ}

theorem theta_const_mul (T : Finset (HeightOneSpectrum (𝓞 F)))
    (c : ℂ) (f : PoissonS.Space F T → ℂ) :
    theta F T (fun x => c * f x) = c * theta F T f := by
  exact tsum_mul_left

end DedekindZetaZeroFree.QuadraticRawProduct

end
