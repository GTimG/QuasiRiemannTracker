/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Poisson/TracePhaseScalarAction.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HarmonicAnalysis.Fourier.TensorTransformsAndLatticeSummability
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Characters.ArchimedeanAdditiveCharacters

@[expose] public section

noncomputable section
open scoped Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.ScaleShift

local instance completionMeasurable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def scalarAction (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a : F) (x : Space F S) : Space F S :=
  (PoissonArch.infiniteAdeleToSpace F
    ((algebraMap F (InfiniteAdeleRing F) a) *
      (PoissonArch.infiniteAdeleToSpace F).symm x.1),
    fun v => algebraMap F (v.val.adicCompletion F) a * x.2 v)

def rawPhase (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y : Space F S) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
      ∏ v : S, (e v (x.2 v * y.2 v) : ℂ)

end DedekindZetaZeroFree.PoissonS.ScaleShift

end
