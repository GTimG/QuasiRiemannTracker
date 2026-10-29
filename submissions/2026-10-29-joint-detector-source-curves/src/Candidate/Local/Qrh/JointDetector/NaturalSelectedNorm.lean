/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Candidate.Local.Qrh.JointDetector.NaturalRowColours
import Candidate.Local.Qrh.JointDetector.FiveColourNorm
import Candidate.Local.Qrh.JointDetector.FiveColourPoisson
import Candidate.Local.Qrh.JointDetector.FiveColourIncidence

/-! Natural-row transport of the proved selected squarefree norm. The colour-one
fibres are selected before the ordinary source variable; fixing higher colours
changes only common coefficients. The final natural norm is not asserted until
the complete shared-table, radial and tail assembly is closed. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredExceptionalCount HeckeInverseAmplification NaturalRowColours
local notation "O" => ActualEisensteinCubic.O

abbrev ColourTuple := Fin 5 → Ideal O
abbrev HigherTuple := Fin 4 → Ideal O

def tupleRow (c : ColourTuple) : O := ∏ j : Fin 5, primaryGenerator (c j)^(j.val+1)
def higherTuple (c : ColourTuple) : HigherTuple := fun j => c j.succ
def higherRow (v : HigherTuple) : O := ∏ j : Fin 4, primaryGenerator (v j)^(j.val+2)

theorem tupleRow_pivot (c : ColourTuple) :
    tupleRow c = higherRow (higherTuple c)*primaryGenerator (c 0) := by
  unfold tupleRow
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero,zero_add,pow_one,Fin.val_succ]
  unfold higherRow higherTuple
  rw [mul_comm]

def pivotFamily (F : Finset ColourTuple) (v : HigherTuple) : Finset (Ideal O) :=
  (F.filter fun c => higherTuple c=v).image (fun c => c 0)

theorem mem_pivotFamily {F : Finset ColourTuple} {v : HigherTuple} {I : Ideal O} :
    I ∈ pivotFamily F v ↔ ∃ c ∈ F, higherTuple c=v ∧ c 0=I := by
  simp only [pivotFamily,Finset.mem_image,Finset.mem_filter]
  aesop

theorem pivotFamily_admissible (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (v : HigherTuple) :
    ∀ I ∈ pivotFamily F v, Admissible I := by
  intro I hI
  obtain ⟨c,hc,hv,rfl⟩ := mem_pivotFamily.mp hI
  exact hF c hc 0

theorem pivotFamily_selected {N : ℕ} (d : SelectedSlotData N) (Z : ℝ)
    (F : Finset ColourTuple) (hF : d.Selects Z (F.image tupleRow)) (v : HigherTuple) :
    (d.quotient (higherRow v)).Selects Z ((pivotFamily F v).image primaryGenerator) := by
  apply SelectedSlotData.quotient_selects hF
  intro z hz
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨c,hc,hv,rfl⟩ := mem_pivotFamily.mp hI
  apply Finset.mem_image.mpr
  exact ⟨c,hc,by rw [tupleRow_pivot,hv]⟩

/-- A complete selected-squarefree inlet for an actual higher-colour fibre.
The fibre need not be a Cartesian product of independent colour choices. -/
theorem pivotFamily_selectedSquarefree {N : ℕ} (d : SelectedSlotData N)
    (Z mesh Cslot wmin δ B : ℝ) (F : Finset ColourTuple) (v : HigherTuple)
    (hb : d.Bounded Z mesh Cslot) (hs : d.Selects Z (F.image tupleRow))
    (hδ : d.HasSlope δ) (hw : wmin ≤ ∑ i, d.width i)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hray : ∀ I ∈ pivotFamily F v, ∀ J ∈ pivotFamily F v,
      primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36:O)} : Ideal O))
    (hnorm : ∀ I ∈ pivotFamily F v, (Ideal.absNorm I:ℝ) ∈ Set.Icc B (2*B)) :
    SelectedSquarefreeFamily (d.quotient (higherRow v)) Z mesh Cslot wmin δ B
      (pivotFamily F v) :=
  ⟨SelectedSlotData.quotient_bounded hb _,pivotFamily_selected d Z F hs v,SelectedSlotData.quotient_hasSlope hδ _,hw,
    pivotFamily_admissible F hF v,hray,hnorm⟩

/-- The actual proved squarefree supplier, instantiated uniformly on every
nonrectangular higher-colour fibre. No additional operator estimate is assumed. -/
theorem pivotFamily_selected_norm (A P gap loss : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hgap : 0 < gap) (hgaphalf : gap < 1/2)
    (hloss : 0 < loss) :
    ∃ mesh₀ : ℝ, 0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),
      0 ≤ Cslot → 0 < wmin → ∃ C Z₀ : ℝ, 0 < C ∧
      ∀ (Z mesh δ : ℝ), Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
      1/2+gap ≤ δ → δ ≤ 3/4 →
      ∀ (d : SelectedSlotData N) (F : Finset ColourTuple) (v : HigherTuple)
        (S : Finset (Ideal O)) (B L : ℝ),
        d.Bounded Z mesh Cslot → d.Selects Z (F.image tupleRow) → d.HasSlope δ →
        wmin ≤ ∑ i, d.width i → (∀ c ∈ F, ∀ j, Admissible (c j)) →
        (∀ I ∈ pivotFamily F v, ∀ J ∈ pivotFamily F v,
          primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36:O)} : Ideal O)) →
        (∀ I ∈ pivotFamily F v, (Ideal.absNorm I:ℝ) ∈ Set.Icc B (2*B)) →
        1 ≤ B → B ≤ Z^A → 1 ≤ L → L ≤ Z^P →
        (∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L) →
        selectedNorm ((pivotFamily F v).image primaryGenerator) S ≤
          C*Z^loss*(L+B^(1-δ)*L^δ) := by
  obtain ⟨mesh₀,hm,hbound⟩ := squarefree_selected_norm A P gap loss hA hP hgap hgaphalf hloss
  refine ⟨mesh₀,hm,?_⟩
  intro N Cslot wmin hC hw
  obtain ⟨C,Z₀,hCpos,hbound⟩ := hbound N Cslot wmin hC hw
  refine ⟨C,Z₀,hCpos,?_⟩
  intro Z mesh δ hZ hm0 hmm hδlo hδhi d F v S B L hb hs hδ hwidth hF hray hnorm hB hBA hL hLP hS
  exact hbound Z mesh δ hZ hm0 hmm hδlo hδhi (d.quotient (higherRow v))
    (pivotFamily F v) S B L
    (pivotFamily_selectedSquarefree d Z mesh Cslot wmin δ B F v hb hs hδ hwidth hF hray hnorm)
    hB hBA hL hLP hS

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.pivotFamily_selected_norm
