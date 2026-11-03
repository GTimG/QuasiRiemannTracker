/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Poisson/SIntegerLatticeNormalization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Archimedean.TraceNormalization
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.FinitePlaces.IdealCosetDecomposition

@[expose] public section

noncomputable section
open scoped Classical nonZeroDivisors SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree
namespace PoissonS.Covolume

variable (F : Type) [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

abbrev Space (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  PoissonArch.Space F × PoissonFinite.Space F S

def diagonalHom (S : Finset (HeightOneSpectrum (RingOfIntegers F))) : F →+ Space F S where
  toFun m := ((NumberField.mixedEmbedding.euclidean.toMixed F).symm
    (NumberField.mixedEmbedding F m), PoissonFinite.diagonal F S m)
  map_zero' := by
    apply Prod.ext
    · simp
    · funext v
      exact map_zero (NumberField.FinitePlace.embedding v.val)
  map_add' m n := by
    ext
    · simp
    · simp [PoissonFinite.diagonal]

def lattice (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (a : F) :
    AddSubgroup (Space F S) :=
  AddSubgroup.map ((diagonalHom F S).comp
    { toFun := fun m : F => a * m
      map_zero' := mul_zero a
      map_add' := fun m n => mul_add a m n })
    ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F).toSubring.toAddSubgroup

def differentExponent (v : HeightOneSpectrum (RingOfIntegers F)) : ℤ :=
  FractionalIdeal.count F v (FractionalIdeal.coeIdeal (differentIdeal ℤ (RingOfIntegers F)))

end PoissonS.Covolume
end DedekindZetaZeroFree

end
