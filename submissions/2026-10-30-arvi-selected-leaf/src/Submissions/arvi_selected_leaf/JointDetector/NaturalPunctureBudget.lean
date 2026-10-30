/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalActualTail
import Submissions.arvi_selected_leaf.JointDetector.NaturalTupleIdentity

/-! The literal bad/good decomposition of an original Poisson puncture.
Both parts are fixed before the two residual pivots; no divisor is omitted.
-/
namespace Qrh.JointDetector.NaturalPunctureBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum CenteredExceptionalCount
open NaturalSelectedNorm NaturalPairPackets NaturalSharedTables NaturalTupleIdentity
local notation "O" => ActualEisensteinCubic.O

def badPart (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) : Ideal O :=
  ∏ b ∈ (Finset.univ.filter fun b : Bool => Sum.inl b ∈ E),badPrime b

def goodPart (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) : Ideal O :=
  ∏ i ∈ goodPunctureSupport F E,i.val

def badScale (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) : ℝ :=
  Ideal.absNorm (badPart F E)

def goodScale (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) : ℝ :=
  Ideal.absNorm (goodPart F E)

theorem maskIdeal_eq_parts (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) :
    NaturalActualTail.maskIdeal F E=badPart F E*goodPart F E := by
  have he : (Finset.univ.filter fun i : SourceMaskIndex F => i ∈ E)=E := by
    ext i
    simp
  calc
    _ = ∏ i : SourceMaskIndex F, if i ∈ E then sourceMaskPrime F i else 1 := by
      rw [← Finset.prod_filter,he]
      rfl
    _ = (∏ b : Bool,if Sum.inl b ∈ E then badPrime b else 1)*
        (∏ i : PrimeIndex F,if Sum.inr i ∈ E then i.val else 1) := by
      rw [Fintype.prod_sum_type]
      rfl
    _ = _ := by simp only [badPart,goodPart,goodPunctureSupport,Finset.prod_filter]

theorem badPart_dvd (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) :
    badPart F E ∣ NaturalActualTail.badIdeal :=
  Finset.prod_dvd_prod_of_subset _ _ badPrime (Finset.filter_subset _ _)

theorem badPart_ne_zero (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) :
    badPart F E ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun b _ => NaturalActualTail.badPrime_ne_zero b)

theorem goodPart_ne_zero (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) :
    goodPart F E ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (NaturalActualTail.pool_prime F i).ne_zero)

theorem badScale_bounds (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) :
    badScale F E ∈ Set.Icc (1:ℝ) NaturalActualTail.badNorm := by
  constructor
  · have hn : 0 < Ideal.absNorm (badPart F E) := by
      exact_mod_cast norm_pos (badPart_ne_zero F E)
    change (1:ℝ) ≤ (Ideal.absNorm (badPart F E):ℝ)
    exact_mod_cast hn
  · exact norm_le_of_dvd NaturalActualTail.badIdeal_ne_zero (badPart_dvd F E)

theorem goodPart_dvd_diagonal (F : Finset ColourTuple) (g : SharedTable)
    (E : Finset (SourceMaskIndex F)) (hE : E ∈ (tableSourceMask F g).powerset) :
    goodPart F E ∣ diagonalProduct g := by
  apply goodPuncture_divides_diagonal
  intro i hi
  have hm := Finset.mem_powerset.mp hE ((Finset.mem_filter.mp hi).2)
  simpa [tableSourceMask] using hm

theorem goodScale_bounds (F : Finset ColourTuple) (g : SharedTable)
    (hgn : ∀ j k,g j k ≠ 0) (E : Finset (SourceMaskIndex F))
    (hE : E ∈ (tableSourceMask F g).powerset) :
    goodScale F E ∈ Set.Icc (1:ℝ) (Ideal.absNorm (diagonalProduct g):ℝ) := by
  constructor
  · have hn : 0 < Ideal.absNorm (goodPart F E) := by
      exact_mod_cast norm_pos (goodPart_ne_zero F E)
    change (1:ℝ) ≤ (Ideal.absNorm (goodPart F E):ℝ)
    exact_mod_cast hn
  · exact norm_le_of_dvd (Finset.prod_ne_zero_iff.mpr fun j _ => hgn j j)
      (goodPart_dvd_diagonal F g E hE)

theorem mask_norm_eq (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) :
    (Ideal.absNorm (NaturalActualTail.maskIdeal F E):ℝ)=badScale F E*goodScale F E := by
  rw [maskIdeal_eq_parts,map_mul,Nat.cast_mul]
  rfl

theorem puncture_norm_eq (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) :
    ‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2=badScale F E*goodScale F E := by
  rw [primeSubsetGenerator_norm_sq]
  exact mask_norm_eq F E

end
end Qrh.JointDetector.NaturalPunctureBudget

#print axioms Qrh.JointDetector.NaturalPunctureBudget.maskIdeal_eq_parts
#print axioms Qrh.JointDetector.NaturalPunctureBudget.goodScale_bounds
