import Candidate.Cycle63.Marked.NaturalSlotHeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeSlot

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators
open Set HeckeFamily CenteredMomentCommonMaskExpansion HeckePrimeAnnular
local notation "O" => HeckeFamily.O

/-- The finite source prime pool with the actual annular support exposed. -/
def annularPool (pool : Finset (Ideal O)) (P : ℝ) : Finset (Ideal O) :=
  pool.filter (fun I=>(I.absNorm:ℝ)/P∈Icc (1:ℝ) 2)

theorem annularPool_subset (pool : Finset (Ideal O)) (P : ℝ) : annularPool pool P⊆pool :=
  Finset.filter_subset _ _

theorem annularPool_ratio (pool : Finset (Ideal O)) (P : ℝ) (I : Ideal O)
    (hI : I∈annularPool pool P) : (I.absNorm:ℝ)/P∈Icc (1:ℝ) 2 :=
  (Finset.mem_filter.mp hI).2

theorem naturalSlot_annular_filter (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (hW : Function.support W⊆Icc (1:ℝ) 2)
    (P σ t : ℝ) :
    naturalSlot χ (annularPool pool P) (fun I=>ν I*annularWeight W P σ t I) P=
      naturalSlot χ pool (fun I=>ν I*annularWeight W P σ t I) P := by
  unfold naturalSlot annularPool
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  by_cases ha : (I.absNorm:ℝ)/P∈Icc (1:ℝ) 2
  · exact if_pos ha
  · rw [if_neg ha]
    have hw : W ((I.absNorm:ℝ)/P)=0 := by
      by_contra hn
      exact ha (hW hn)
    simp [annularWeight,hw]

theorem annularPool_pairwise {Slot : Type*} (slots : Set Slot)
    (pools : Slot→Finset (Ideal O)) (P : Slot→ℝ)
    (hdis : slots.PairwiseDisjoint pools) :
    slots.PairwiseDisjoint (fun s=>annularPool (pools s) (P s)) := by
  intro i hi j hj hij
  exact (hdis hi hj hij).mono (annularPool_subset _ _) (annularPool_subset _ _)

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.naturalSlot_annular_filter
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.annularPool_pairwise
