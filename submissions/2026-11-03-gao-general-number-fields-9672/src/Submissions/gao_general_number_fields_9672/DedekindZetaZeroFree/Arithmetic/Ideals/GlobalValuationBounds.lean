/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/GlobalValuationBounds.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Characters.SIntegerTraceAnnihilation
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegerTensorCosets

@[expose] public section

noncomputable section

open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

private theorem mem_sIntegerRing_iff_valuation' (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (t : F) :
    t ∈ sIntegerRing F S ↔
      ∀ v : HeightOneSpectrum (RingOfIntegers F), v ∉ S → v.valuation F t ≤ 1 := by
  rw [sIntegerRing, Set.integer_eq]
  simp only [Subring.mem_iInf, ValuationSubring.mem_toSubring,
    Valuation.mem_valuationSubring_iff, Finset.mem_coe]

def sGlobalBoundedIdealSet (F : Type) [Field F] [NumberField F]
    (P : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : P → ℤ) : Set F :=
  {x | x ∈ sIntegerRing F P ∧
    ∀ v : P, v.val.valuation F x ≤ WithZero.exp (-k v)}

theorem mem_sGlobalBoundedIdealSet_iff (F : Type) [Field F] [NumberField F]
    (P : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : P → ℤ) (x : F) :
    x ∈ sGlobalBoundedIdealSet F P k ↔
      ∀ w : HeightOneSpectrum (RingOfIntegers F),
        w.valuation F x ≤ WithZero.exp (-(if h : w ∈ P then k ⟨w, h⟩ else 0)) := by
  rw [sGlobalBoundedIdealSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hb⟩ w
    by_cases hw : w ∈ P
    · rw [dif_pos hw]; exact hb ⟨w, hw⟩
    · rw [dif_neg hw]
      have := (mem_sIntegerRing_iff_valuation' F P x).mp hx w hw
      simpa using this
  · intro h
    refine ⟨?_, ?_⟩
    · rw [mem_sIntegerRing_iff_valuation']
      intro w hw
      have hw' := h w
      rw [dif_neg hw] at hw'
      simpa using hw'
    · intro v
      have hv := h v.val
      rwa [dif_pos v.property] at hv

theorem sGlobalBoundedIdealSet_eq_ballFractionalIdeal
    (F : Type) [Field F] [NumberField F]
    (P : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : P → ℤ) :
    sGlobalBoundedIdealSet F P k = (PoissonS.ballFractionalIdeal F P k : Set F) := by
  ext x
  rw [mem_sGlobalBoundedIdealSet_iff, SetLike.mem_coe,
    PoissonS.ScaleShift.fractionalIdeal_mem_iff_valuations F _
      (PoissonS.ballFractionalIdeal_ne_zero F P k) x]
  simp only [PoissonS.ScaleShift.count_ballFractionalIdeal]

end DedekindZetaZeroFree

end
