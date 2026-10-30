/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalSharedTables
import Submissions.arvi_selected_leaf.JointDetector.NaturalPositiveGram
import Submissions.arvi_selected_leaf.JointDetector.FiveColourMellin
import Submissions.arvi_selected_leaf.JointDetector.NaturalTupleIdentity

/-! Actual colour-tuple pair packets on one prime universe fixed BEFORE
pairing. A pair uses only the union of its two original supports; unused
primes do not create spurious cancelled Euler holes. -/
namespace Qrh.JointDetector.NaturalPairPackets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge GaussGeneratorTransport FiniteGaussPhase
open MixedCrossSeparation MixedGaussConversion EisensteinSchwartzPoisson
open NaturalSelectedNorm FiveColourPoisson NaturalSharedTables
local notation "O" => ActualEisensteinCubic.O

/-- This prime universe is fixed from the ORIGINAL finite tuple family,
independently of the second row, source ideal, or Fourier frequency. -/
def colourIdeals (F : Finset ColourTuple) : Finset (Ideal O) :=
  F.biUnion (fun c => Finset.univ.image c)

abbrev PrimeIndex (F : Finset ColourTuple) := primePool (colourIdeals F)

theorem colour_mem {F : Finset ColourTuple} {c : ColourTuple} (hc : c ∈ F) (j : Fin 5) :
    c j ∈ colourIdeals F :=
  Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩

theorem colourIdeals_admissible (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) : ∀ I ∈ colourIdeals F, Admissible I := by
  intro I hI
  obtain ⟨c,hc,hI⟩ := Finset.mem_biUnion.mp hI
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hI
  exact hF c hc j

def tupleSupport (F : Finset ColourTuple) (c : ColourTuple) : Finset (PrimeIndex F) :=
  Finset.univ.biUnion (fun j => idealSupport (colourIdeals F) (c j))

def pairSupport (F : Finset ColourTuple) (c d : ColourTuple) : Finset (PrimeIndex F) :=
  tupleSupport F c ∪ tupleSupport F d

/-- Zero is absence; positive values are the original five colour exponents. -/
def colourExponent (F : Finset ColourTuple) (c : ColourTuple) (i : PrimeIndex F) : ℕ :=
  ∑ j : Fin 5, if i ∈ idealSupport (colourIdeals F) (c j) then j.val+1 else 0

theorem colourExponent_at (F : Finset ColourTuple) (c : ColourTuple)
    (hpair : Pairwise (fun j k => IsCoprime (c j) (c k))) (i : PrimeIndex F) (j : Fin 5)
    (hi : i ∈ idealSupport (colourIdeals F) (c j)) : colourExponent F c i=j.val+1 := by
  unfold colourExponent
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left hi]
  · intro k hk hkj
    have hn : i ∉ idealSupport (colourIdeals F) (c k) := by
      intro hik
      exact Finset.disjoint_left.mp
        (idealSupport_disjoint_of_coprime (colourIdeals F) (c j) (c k) (hpair hkj.symm)) hi hik
    exact ite_eq_right hn
  · simp

theorem colourExponent_outside (F : Finset ColourTuple) (c : ColourTuple) (i : PrimeIndex F)
    (hi : i ∉ tupleSupport F c) : colourExponent F c i=0 := by
  unfold colourExponent
  apply Finset.sum_eq_zero
  intro j hj
  apply ite_eq_right
  intro hij
  exact hi (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hij⟩)

theorem colourExponent_range (F : Finset ColourTuple) (c : ColourTuple)
    (hpair : Pairwise (fun j k => IsCoprime (c j) (c k))) (i : PrimeIndex F) :
    colourExponent F c i < 6 := by
  by_cases hi : i ∈ tupleSupport F c
  · obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
    rw [colourExponent_at F c hpair i j hij]
    omega
  · rw [colourExponent_outside F c i hi]
    decide

theorem colourExponent_positive (F : Finset ColourTuple) (c : ColourTuple)
    (hpair : Pairwise (fun j k => IsCoprime (c j) (c k))) (i : PrimeIndex F)
    (hi : i ∈ tupleSupport F c) : 0 < colourExponent F c i := by
  obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
  rw [colourExponent_at F c hpair i j hij]
  omega

theorem pairSupport_active (F : Finset ColourTuple) (c d : ColourTuple)
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : pairSupport F c d) :
    0 < colourExponent F c i.val+colourExponent F d i.val := by
  rcases Finset.mem_union.mp i.property with hi | hi
  · have h := colourExponent_positive F c hc i.val hi
    omega
  · have h := colourExponent_positive F d hd i.val hi
    omega

/-- Exact original weighted ideal, reconstructed on the common prime pool.
No squarefree projection of the weighted ideal is made. -/
theorem weightedIdeal_common_pool (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c : ColourTuple) (hc : c ∈ F) :
    NaturalRowColours.colourProduct c = ∏ i : PrimeIndex F, i.val^(colourExponent F c i) := by
  symm
  unfold colourExponent
  calc
    _ = ∏ i : PrimeIndex F, ∏ j : Fin 5,
        i.val^(if i ∈ idealSupport (colourIdeals F) (c j) then j.val+1 else 0) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.prod_pow_eq_pow_sum]
    _ = ∏ j : Fin 5, ∏ i : PrimeIndex F,
        i.val^(if i ∈ idealSupport (colourIdeals F) (c j) then j.val+1 else 0) := Finset.prod_comm
    _ = NaturalRowColours.colourProduct c := by
      unfold NaturalRowColours.colourProduct
      apply Finset.prod_congr rfl
      intro j hj
      have hif (i : PrimeIndex F) :
          i.val^(if i ∈ idealSupport (colourIdeals F) (c j) then j.val+1 else 0) =
            if i ∈ idealSupport (colourIdeals F) (c j) then i.val^(j.val+1) else 1 := by split_ifs <;> simp
      simp_rw [hif]
      rw [← Finset.prod_filter]
      have hfilter : Finset.univ.filter (fun i : PrimeIndex F => i ∈ idealSupport (colourIdeals F) (c j)) =
          idealSupport (colourIdeals F) (c j) := by ext i; simp
      rw [hfilter,Finset.prod_pow,idealSupport_product_eq (colourIdeals F) (colour_mem hc j) (hF c hc j).2.1]

theorem weightedIdeal_on_support (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c : ColourTuple) (hc : c ∈ F)
    (S : Finset (PrimeIndex F)) (hS : tupleSupport F c ⊆ S) :
    NaturalRowColours.colourProduct c = ∏ i ∈ S, i.val^(colourExponent F c i) := by
  rw [weightedIdeal_common_pool F hF c hc]
  symm
  apply Finset.prod_subset (Finset.subset_univ S)
  intro i hi hnot
  rw [colourExponent_outside F c i (fun hm => hnot (hS hm)),pow_zero]

/-- The original pair character on the exact used-prime pool, with unused
primes absent rather than converted into false cancelled source masks. -/
theorem pair_character_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F) (n : O) :
    naturalColourPairRow (fun i : pairSupport F c d => i.val.val)
      (fun i => poolGood (colourIdeals F) (colourIdeals_admissible F hF) i.val)
      (fun i => colourExponent F c i.val) (fun i => colourExponent F d i.val) n =
      idealRowHom n (NaturalRowColours.colourProduct c)*star (idealRowHom n (NaturalRowColours.colourProduct d)) := by
  rw [naturalColourPairRow_eq_idealRowHom]
  have hl : (∏ i : pairSupport F c d, i.val.val^(colourExponent F c i.val)) = NaturalRowColours.colourProduct c := by
    rw [Finset.prod_coe_sort (pairSupport F c d) (fun i : PrimeIndex F => i.val^(colourExponent F c i))]
    exact (weightedIdeal_on_support F hF c hc _ Finset.subset_union_left).symm
  have hr : (∏ i : pairSupport F c d, i.val.val^(colourExponent F d i.val)) = NaturalRowColours.colourProduct d := by
    rw [Finset.prod_coe_sort (pairSupport F c d) (fun i : PrimeIndex F => i.val^(colourExponent F d i))]
    exact (weightedIdeal_on_support F hF d hd _ Finset.subset_union_right).symm
  rw [hl,hr]


def primitivePrimes (F : Finset ColourTuple) (c d : ColourTuple) : Finset (PrimeIndex F) :=
  Finset.univ.filter (fun i => colourExponent F c i ≠ colourExponent F d i)

def cancelledPrimes (F : Finset ColourTuple) (c d : ColourTuple) : Finset (PrimeIndex F) :=
  Finset.univ.filter (fun i => colourExponent F c i=colourExponent F d i ∧ 0 < colourExponent F c i)

/-- Fixed bad primes and positive same-colour primes share ONE index universe,
independent of the pair. Unused both-zero primes add no source Euler hole. -/
abbrev SourceMaskIndex (F : Finset ColourTuple) := Bool ⊕ PrimeIndex F

def sourceMaskPrime (F : Finset ColourTuple) : SourceMaskIndex F → Ideal O :=
  Sum.elim badPrime (fun i => i.val)

def sourceMaskSupport (F : Finset ColourTuple) (c d : ColourTuple) : Finset (SourceMaskIndex F) :=
  (Finset.univ.image Sum.inl) ∪ ((cancelledPrimes F c d).image Sum.inr)

instance sourceMaskPrime_maximal (F : Finset ColourTuple) (i : SourceMaskIndex F) :
    (sourceMaskPrime F i).IsMaximal := by
  cases i with
  | inl b => change (badPrime b).IsMaximal; infer_instance
  | inr i => change i.val.IsMaximal; infer_instance

theorem pool_ne_badPrime (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (i : PrimeIndex F) (b : Bool) : badPrime b ≠ i.val := by
  cases b with
  | false =>
    intro he
    have hg := poolGood (colourIdeals F) (colourIdeals_admissible F hF) i
    apply hg
    rw [← he]
    exact Ideal.subset_span (by simp)
  | true =>
    intro he
    have hc := poolOdd (colourIdeals F) (colourIdeals_admissible F hF) i
    have htwo : i.val=cubicTwoIdeal := by simpa [badPrime,cubicTwoIdeal,Ideal.span_singleton_neg] using he.symm
    have hechar : ringChar (O⧸i.val)=2 := by rw [htwo]; exact cubicTwoIdeal_residue_char
    exact hc hechar

theorem sourceMaskPrime_injective (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) : Function.Injective (sourceMaskPrime F) := by
  intro i j he
  cases i with
  | inl b =>
    cases j with
    | inl b' => exact congrArg Sum.inl (badPrime_injective he)
    | inr j => exact False.elim (pool_ne_badPrime F hF j b he)
  | inr i =>
    cases j with
    | inl b => exact False.elim (pool_ne_badPrime F hF i b he.symm)
    | inr j => exact congrArg Sum.inr (Subtype.ext he)

/-- The original bad-source mask is paid together with the natural same-colour
mask, rather than omitted from the supported-ideal completion. -/
theorem sourceMask_factor (F : Finset ColourTuple) (c d : ColourTuple) (n : O) :
    rowCoprimeMask (sourceMaskPrime F) (sourceMaskSupport F c d) n =
      rowCoprimeMask badPrime Finset.univ n*
      rowCoprimeMask (fun i : PrimeIndex F => i.val) (cancelledPrimes F c d) n := by
  have hexists : (∃ i ∈ sourceMaskSupport F c d, n ∈ sourceMaskPrime F i) ↔
      (∃ b ∈ (Finset.univ : Finset Bool), n ∈ badPrime b) ∨
      (∃ i ∈ cancelledPrimes F c d, n ∈ i.val) := by
    constructor
    · rintro ⟨i,hi,hn⟩
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hi
        exact Or.inl ⟨b,hb,hn⟩
      · obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hi
        subst i
        exact Or.inr ⟨k,hk,hn⟩
    · rintro (⟨b,hb,hn⟩ | ⟨i,hi,hn⟩)
      · exact ⟨Sum.inl b,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩),hn⟩
      · exact ⟨Sum.inr i,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩),hn⟩
  unfold rowCoprimeMask
  by_cases hbad : ∃ b ∈ (Finset.univ : Finset Bool), n ∈ badPrime b
  · have hany := hexists.mpr (Or.inl hbad)
    simp only [ite_eq_left hany,ite_eq_left hbad,zero_mul]
  · by_cases hgood : ∃ i ∈ cancelledPrimes F c d,n ∈ i.val
    · have hany := hexists.mpr (Or.inr hgood)
      simp only [ite_eq_left hany,ite_eq_right hbad,ite_eq_left hgood,mul_zero]
    · have hany : ¬∃ i ∈ sourceMaskSupport F c d,n ∈ sourceMaskPrime F i :=
        fun h => (hexists.mp h).elim hbad hgood
      simp only [ite_eq_right hany,ite_eq_right hbad,ite_eq_right hgood,one_mul]

/-- The actual raw pair kernel consumed by supportedSmoothGram completion. -/
def actualPairKernel (c d : ColourTuple) (W : 𝓢(ℝ,ℂ)) (L : ℝ) : ℂ :=
  ∑' n : O, rowCoprimeMask badPrime Finset.univ n*
    (idealRowHom n (weightedIdeal c)*star (idealRowHom n (weightedIdeal d)))*W (‖eisEmbedding n‖^2/L)

theorem common_pair_character_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F) (n : O) :
    naturalColourPairRow (fun i : PrimeIndex F => i.val)
      (poolGood (colourIdeals F) (colourIdeals_admissible F hF))
      (colourExponent F c) (colourExponent F d) n =
      idealRowHom n (weightedIdeal c)*star (idealRowHom n (weightedIdeal d)) := by
  rw [naturalColourPairRow_eq_idealRowHom,
    ← weightedIdeal_common_pool F hF c hc,← weightedIdeal_common_pool F hF d hd]
  rfl

/-- Absence on both sides contributes ONE, not a false principal Euler hole. -/
theorem local_natural_with_absence (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (j k : ℕ) (hj : j < 6) (hk : k < 6) (n : O) :
    (canonicalSextic P hg (Ideal.Quotient.mk P n))^j*
      star ((canonicalSextic P hg (Ideal.Quotient.mk P n))^k) =
      (if j≠k then (canonicalSextic P hg (Ideal.Quotient.mk P n))^(quotientExponent j k) else 1)*
      (if j=k ∧ 0<j then (if n∈P then 0 else 1) else 1) := by
  by_cases hjk : j=k
  · by_cases hj0 : j=0
    · subst j
      have hk0 : k=0 := by omega
      subst k
      simp
    · have hact : 0 < j+k := by omega
      rw [local_natural_quotient P hg j k hj hk hact]
      simp [hjk,show 0 < k by omega]
  · rw [local_natural_quotient P hg j k hj hk (by omega)]
    simp [hjk]

/-- Exact primitive quotient on the COMMON prime pool. The original pair
character, all25 shared states, and the positive same-colour mask are derived
from the actual finite tuple family. -/
theorem pair_character_primitive_mask (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (n : O) :
    idealRowHom n (weightedIdeal c)*star (idealRowHom n (weightedIdeal d)) =
      rowCoprimeMask (fun i : PrimeIndex F => i.val) (cancelledPrimes F c d) n*
      finiteSexticRow (fun i : primitivePrimes F c d => i.val.val)
        (fun i => poolGood (colourIdeals F) (colourIdeals_admissible F hF) i.val)
        (fun i => quotientExponent (colourExponent F c i.val) (colourExponent F d i.val)) n := by
  let good := poolGood (colourIdeals F) (colourIdeals_admissible F hF)
  have hprim : finiteSexticRow (fun i : primitivePrimes F c d => i.val.val) (fun i => good i.val)
      (fun i => quotientExponent (colourExponent F c i.val) (colourExponent F d i.val)) n =
      ∏ i : PrimeIndex F, if colourExponent F c i≠colourExponent F d i then
        (canonicalSextic i.val (good i) (Ideal.Quotient.mk i.val n))^
          (quotientExponent (colourExponent F c i) (colourExponent F d i)) else 1 := by
    unfold finiteSexticRow
    have hp (i : primitivePrimes F c d) :
        (canonicalSextic i.val.val (good i.val)^quotientExponent (colourExponent F c i.val) (colourExponent F d i.val))
          (Ideal.Quotient.mk i.val.val n) =
        (canonicalSextic i.val.val (good i.val) (Ideal.Quotient.mk i.val.val n))^
          quotientExponent (colourExponent F c i.val) (colourExponent F d i.val) :=
      MulChar.pow_apply' _ (quotientExponent_range (colourExponent_range F c hcPair i.val)
        (colourExponent_range F d hdPair i.val) (Finset.mem_filter.mp i.property).2).1.ne' _
    simp_rw [hp]
    rw [Finset.prod_coe_sort (primitivePrimes F c d)
      (fun i : PrimeIndex F => (canonicalSextic i.val (good i) (Ideal.Quotient.mk i.val n))^
        quotientExponent (colourExponent F c i) (colourExponent F d i))]
    exact Finset.prod_filter _ _
  have hmask : rowCoprimeMask (fun i : PrimeIndex F => i.val) (cancelledPrimes F c d) n =
      ∏ i : PrimeIndex F, if colourExponent F c i=colourExponent F d i ∧ 0<colourExponent F c i then
        (if n∈i.val then (0 : ℂ) else 1) else 1 := by
    rw [← prod_puncture_mask]
    exact Finset.prod_filter _ _
  rw [← common_pair_character_actual F hF c d hc hd n]
  unfold naturalColourPairRow
  simp_rw [local_natural_with_absence _ _ _ _ (colourExponent_range F c hcPair _) (colourExponent_range F d hdPair _)]
  rw [Finset.prod_mul_distrib,← hprim,← hmask,mul_comm]

def primitivePrimary (F : Finset ColourTuple) (c d : ColourTuple) (i : primitivePrimes F c d) : O :=
  poolPrimary (colourIdeals F) i.val

def primitiveExponent (F : Finset ColourTuple) (c d : ColourTuple) (i : primitivePrimes F c d) : ℕ :=
  quotientExponent (colourExponent F c i.val) (colourExponent F d i.val)

theorem primitivePrimary_span (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (i : primitivePrimes F c d) :
    Ideal.span {primitivePrimary F c d i}=i.val.val :=
  poolPrimary_span (colourIdeals F) (colourIdeals_admissible F hF) i.val

theorem primitivePrimary_nonzero (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (i : primitivePrimes F c d) :
    primitivePrimary F c d i ≠ 0 := poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF) i.val

theorem primitivePrimary_maximal (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) :
    ∀ i : primitivePrimes F c d, (Ideal.span {primitivePrimary F c d i}).IsMaximal :=
  fun i => admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF) i.val

theorem primitivePrimary_coprime (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) :
    Pairwise (Function.onFun IsCoprime (fun i : primitivePrimes F c d => Ideal.span {primitivePrimary F c d i})) := by
  intro i j hij
  exact poolPrimary_coprime (colourIdeals F) (colourIdeals_admissible F hF) (fun he => hij (Subtype.ext he))

theorem primitivePrimary_good (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (i : primitivePrimes F c d) :
    lambda ∉ Ideal.span {primitivePrimary F c d i} :=
  poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF) i.val

theorem primitivePrimary_odd (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (i : primitivePrimes F c d) :
    ringChar (O⧸Ideal.span {primitivePrimary F c d i}) ≠ 2 :=
  poolPrimary_odd (colourIdeals F) (colourIdeals_admissible F hF) i.val

theorem primitiveExponent_range (F : Finset ColourTuple) (c d : ColourTuple)
    (hc : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hd : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : primitivePrimes F c d) :
    0 < primitiveExponent F c d i ∧ primitiveExponent F c d i < 6 :=
  quotientExponent_range (colourExponent_range F c hc i.val) (colourExponent_range F d hd i.val)
    (Finset.mem_filter.mp i.property).2

def primitiveGauss (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) : ℂ :=
  letI := primitivePrimary_maximal F hF c d
  canonicalProductGauss (primitivePrimary F c d) (primitivePrimary_nonzero F hF c d)
    (primitivePrimary_coprime F hF c d) (primitivePrimary_good F hF c d) (primitiveExponent F c d)

def primitiveRow (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (n : O) : ℂ :=
  letI := primitivePrimary_maximal F hF c d
  finiteSexticRow (fun i => Ideal.span {primitivePrimary F c d i})
    (primitivePrimary_good F hF c d) (primitiveExponent F c d) n

def primitiveElement (F : Finset ColourTuple) (c d : ColourTuple) : O :=
  ∏ i,primitivePrimary F c d i

theorem primitiveRow_eq (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (n : O) :
    primitiveRow F hF c d n =
      finiteSexticRow (fun i : primitivePrimes F c d => i.val.val)
        (fun i => poolGood (colourIdeals F) (colourIdeals_admissible F hF) i.val)
        (fun i => quotientExponent (colourExponent F c i.val) (colourExponent F d i.val)) n := by
  unfold primitiveRow
  have hP : (fun i : primitivePrimes F c d => Ideal.span {primitivePrimary F c d i}) =
      (fun i => i.val.val) := funext (primitivePrimary_span F hF c d)
  simp only [hP]
  rfl

/-- The original bad mask and the true primitive row appear BEFORE Poisson. -/
theorem actual_pair_integrand (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (n : O) :
    rowCoprimeMask badPrime Finset.univ n*
      (idealRowHom n (weightedIdeal c)*star (idealRowHom n (weightedIdeal d))) =
    rowCoprimeMask (sourceMaskPrime F) (sourceMaskSupport F c d) n*primitiveRow F hF c d n := by
  rw [pair_character_primitive_mask F hF c d hc hd hcPair hdPair n,primitiveRow_eq,sourceMask_factor]
  ring

/-- The exact complete divisor-labelled dual packet. Both original bad primes
and cancelled good primes remain in the source mask, before any source dyad,
bad-output sector or positive estimate is introduced. -/
def rawDualPacket (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (W : 𝓢(ℝ,ℂ)) (L : ℝ) : ℂ :=
  ((L : ℂ)*primitiveGauss F hF c d/(‖eisEmbedding (primitiveElement F c d)‖ : ℂ))*
    ∑ E ∈ (sourceMaskSupport F c d).powerset,
      let q := primeSubsetGenerator (sourceMaskPrime F) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E,sourceMaskPrime F i) : ℂ)*
        primitiveRow F hF c d q/(‖eisEmbedding q‖^2 : ℝ))*
      ∑' h : O,star (primitiveRow F hF c d h)*paperRadialFourier W
        (L*‖eisEmbedding h‖^2/(‖eisEmbedding q‖^2*‖eisEmbedding (primitiveElement F c d)‖^2))

/-- Actual original-tuple pair Poisson, not a packet input. The common prime
universe is fixed by F; all raw frequencies and all source punctures remain. -/
theorem actual_pair_poisson (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (W : 𝓢(ℝ,ℂ)) (L : ℝ) (hL : 0 < L) :
    actualPairKernel c d W L = rawDualPacket F hF c d W L := by
  letI := primitivePrimary_maximal F hF c d
  unfold actualPairKernel
  simp_rw [actual_pair_integrand F hF c d hc hd hcPair hdPair]
  exact canonical_masked_radial_poisson_product (sourceMaskPrime F) (sourceMaskPrime_injective F hF)
    (sourceMaskSupport F c d) (primitivePrimary F c d) (primitivePrimary_nonzero F hF c d)
    (primitivePrimary_coprime F hF c d) (primitivePrimary_good F hF c d) (primitivePrimary_odd F hF c d)
    (primitiveExponent F c d) (fun i => (primitiveExponent_range F c d hcPair hdPair i).1.ne')
    (fun i => (primitiveExponent_range F c d hcPair hdPair i).2) W L hL

/-- The actual supported-ideal pair source is now a complete explicit mixed
Poisson packet, including its ORIGINAL bad-source mask. -/
theorem supported_pair_packet_eq (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (hmod : primaryGenerator (weightedIdeal c)-primaryGenerator (weightedIdeal d) ∈
      (Ideal.span {(36 : O)} : Ideal O)) (W : 𝓢(ℝ,ℂ)) (L : ℝ) (hL : 0 < L) :
    selectedSupportedPairSource (weightedIdeal c) (weightedIdeal d) W L =
      (6 : ℂ)⁻¹*rawDualPacket F hF c d W L := by
  rw [supportedPairSource_eq_element _ _ (tuple_weighted_supported c (hF c hc))
    (tuple_weighted_supported d (hF d hd)) hmod W L hL]
  change (6 : ℂ)⁻¹*actualPairKernel c d W L = _
  rw [actual_pair_poisson F hF c d hc hd hcPair hdPair W L hL]

theorem commonPrime_prime (F : Finset ColourTuple) (i : PrimeIndex F) : Prime i.val := by
  obtain ⟨I,hI,hi⟩ := mem_primePool_iff.mp i.property
  exact UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi

/-- Membership in this common support remains literal ideal divisibility,
including ideals which are quotients or shared-table cells. -/
theorem mem_support_iff_dvd (F : Finset ColourTuple) (I : Ideal O) (hI : I ≠ 0)
    (i : PrimeIndex F) : i ∈ idealSupport (colourIdeals F) I ↔ i.val ∣ I := by
  rw [mem_idealSupport_iff,Ideal.mem_normalizedFactors_iff hI]
  simp only [show i.val.IsPrime from inferInstance, true_and, Ideal.dvd_iff_le]

theorem mem_support_gcd (F : Finset ColourTuple) (I J : Ideal O)
    (hI : I ≠ 0) (hJ : J ≠ 0) (i : PrimeIndex F) :
    i ∈ idealSupport (colourIdeals F) (gcd I J) ↔
      i ∈ idealSupport (colourIdeals F) I ∧ i ∈ idealSupport (colourIdeals F) J := by
  rw [mem_support_iff_dvd F _ (gcd_ne_zero_of_left hI),
    mem_support_iff_dvd F I hI,mem_support_iff_dvd F J hJ,dvd_gcd_iff]

/-- The cancelled source primes are determined by the FIVE DIAGONAL cells
of the fixed full shared table. No residual pivot or Fourier source enters
this support. The original bad-prime mask is added separately. -/
def diagonalPrimes (F : Finset ColourTuple) (g : SharedTable) : Finset (PrimeIndex F) :=
  Finset.univ.biUnion (fun j => idealSupport (colourIdeals F) (g j j))

theorem cancelledPrimes_eq_diagonal (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    cancelledPrimes F c d = diagonalPrimes F (table c d) := by
  ext i
  simp only [cancelledPrimes,Finset.mem_filter,Finset.mem_univ,true_and,
    diagonalPrimes,Finset.mem_biUnion]
  constructor
  · rintro ⟨he,hpos⟩
    have hci : i ∈ tupleSupport F c := by
      by_contra hn
      rw [colourExponent_outside F c i hn] at hpos
      omega
    have hdi : i ∈ tupleSupport F d := by
      by_contra hn
      rw [colourExponent_outside F d i hn] at he
      omega
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hci
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hdi
    have hjk : j=k := Fin.ext (by
      rw [colourExponent_at F c hcPair i j hij,colourExponent_at F d hdPair i k hik] at he
      omega)
    refine ⟨j,?_⟩
    change i ∈ idealSupport (colourIdeals F) (gcd (c j) (d j))
    exact (mem_support_gcd F _ _ (hF c hc j).1 (hF d hd j).1 i).mpr ⟨hij,hjk ▸ hik⟩
  · rintro ⟨j,hij⟩
    obtain ⟨hil,hir⟩ := (mem_support_gcd F _ _ (hF c hc j).1 (hF d hd j).1 i).mp hij
    rw [colourExponent_at F c hcPair i j hil,colourExponent_at F d hdPair i j hir]
    exact ⟨rfl,by omega⟩

def tableSourceMask (F : Finset ColourTuple) (g : SharedTable) : Finset (SourceMaskIndex F) :=
  Finset.univ.image Sum.inl ∪ (diagonalPrimes F g).image Sum.inr

theorem sourceMaskSupport_eq_table (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    sourceMaskSupport F c d = tableSourceMask F (table c d) := by
  unfold sourceMaskSupport tableSourceMask
  rw [cancelledPrimes_eq_diagonal F hF c d hc hd hcPair hdPair]

theorem primitivePrimes_empty_iff (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    primitivePrimes F c d = ∅ ↔ c=d :=
  NaturalTupleIdentity.primitiveSupport_empty_iff_tuple (hF c hc) (hF d hd) hcPair hdPair
    (fun i : PrimeIndex F => i.val) (commonPrime_prime F) Subtype.val_injective
    (colourExponent F c) (colourExponent F d)
    (weightedIdeal_common_pool F hF c hc) (weightedIdeal_common_pool F hF d hd)

/-- Zero frequency vanishes for every ACTUAL off-diagonal colour pair;
the identical-tuple principal contribution has not been deleted. -/
theorem primitiveRow_zero_offdiagonal (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (hne : c ≠ d) :
    primitiveRow F hF c d 0 = 0 := by
  rw [primitiveRow_eq]
  exact NaturalTupleIdentity.offdiagonal_zero_frequency (hF c hc) (hF d hd) hcPair hdPair
    (fun i : PrimeIndex F => i.val) (poolGood (colourIdeals F) (colourIdeals_admissible F hF))
    (commonPrime_prime F) Subtype.val_injective (colourExponent F c) (colourExponent F d)
    (weightedIdeal_common_pool F hF c hc) (weightedIdeal_common_pool F hF d hd) hne

theorem colourExponent_zero_iff (F : Finset ColourTuple) (c : ColourTuple)
    (hpair : Pairwise (fun j k => IsCoprime (c j) (c k))) (i : PrimeIndex F) :
    colourExponent F c i=0 ↔ i ∉ tupleSupport F c := by
  constructor
  · intro he hi
    have hp := colourExponent_positive F c hpair i hi
    omega
  · exact colourExponent_outside F c i

theorem prime_not_dvd_of_coprime {P I J : Ideal O} (hP : Prime P)
    (hIJ : IsCoprime I J) (hPI : P ∣ I) : ¬ P ∣ J := by
  intro hPJ
  exact hP.not_isUnit (hIJ.isRelPrime hPI hPJ)

/-- The free left colour is literally the part absent from EVERY right
colour. This derives the free pivot from the original gcd table. -/
theorem mem_leftResidual_support (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (j : Fin 5) (i : PrimeIndex F) :
    i ∈ idealSupport (colourIdeals F) (leftResidual c d j) ↔
      i ∈ idealSupport (colourIdeals F) (c j) ∧ i ∉ tupleSupport F d := by
  have hres := admissible_of_dvd (hF c hc j) (leftResidual_dvd hdPair j)
  rw [mem_support_iff_dvd F _ hres.1,mem_support_iff_dvd F _ (hF c hc j).1]
  constructor
  · intro hi
    refine ⟨hi.trans (leftResidual_dvd hdPair j),?_⟩
    intro hdi
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hdi
    exact prime_not_dvd_of_coprime (commonPrime_prime F i)
      (leftResidual_coprime_right (hF c hc) hdPair j k) hi
      ((mem_support_iff_dvd F _ (hF d hd k).1 i).mp hik)
  · rintro ⟨hi,hn⟩
    have hre : rowProduct (table c d) j*leftResidual c d j=c j := congrFun (recover_left hdPair) j
    rw [← hre] at hi
    rcases (commonPrime_prime F i).dvd_or_dvd hi with hg | hr
    · obtain ⟨k,hk,hik⟩ := (Prime.dvd_finsetProd_iff (commonPrime_prime F i)
        (fun k : Fin 5 => table c d j k)).mp hg
      have hdk : i ∈ idealSupport (colourIdeals F) (d k) :=
        (mem_support_iff_dvd F _ (hF d hd k).1 i).mpr (hik.trans (gcd_dvd_right _ _))
      exact (hn (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hdk⟩)).elim
    · exact hr

theorem mem_rightResidual_support (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k))) (k : Fin 5) (i : PrimeIndex F) :
    i ∈ idealSupport (colourIdeals F) (rightResidual c d k) ↔
      i ∈ idealSupport (colourIdeals F) (d k) ∧ i ∉ tupleSupport F c := by
  have hres := admissible_of_dvd (hF d hd k) (rightResidual_dvd hcPair k)
  rw [mem_support_iff_dvd F _ hres.1,mem_support_iff_dvd F _ (hF d hd k).1]
  constructor
  · intro hi
    refine ⟨hi.trans (rightResidual_dvd hcPair k),?_⟩
    intro hci
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hci
    exact prime_not_dvd_of_coprime (commonPrime_prime F i)
      (rightResidual_coprime_left (hF d hd) hcPair j k) hi
      ((mem_support_iff_dvd F _ (hF c hc j).1 i).mp hij)
  · rintro ⟨hi,hn⟩
    have hre : columnProduct (table c d) k*rightResidual c d k=d k := congrFun (recover_right hcPair) k
    rw [← hre] at hi
    rcases (commonPrime_prime F i).dvd_or_dvd hi with hg | hr
    · obtain ⟨j,hj,hij⟩ := (Prime.dvd_finsetProd_iff (commonPrime_prime F i)
        (fun j : Fin 5 => table c d j k)).mp hg
      have hcj : i ∈ idealSupport (colourIdeals F) (c j) :=
        (mem_support_iff_dvd F _ (hF c hc j).1 i).mpr (hij.trans (gcd_dvd_left _ _))
      exact (hn (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hcj⟩)).elim
    · exact hr

theorem mem_leftResidual_code (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (j : Fin 5) (i : PrimeIndex F) :
    i ∈ idealSupport (colourIdeals F) (leftResidual c d j) ↔
      colourExponent F c i=j.val+1 ∧ colourExponent F d i=0 := by
  rw [mem_leftResidual_support F hF c d hc hd hdPair j i,← colourExponent_zero_iff F d hdPair i]
  constructor
  · rintro ⟨hi,hz⟩
    exact ⟨colourExponent_at F c hcPair i j hi,hz⟩
  · rintro ⟨he,hz⟩
    have hm : i ∈ tupleSupport F c := by
      by_contra hn
      rw [colourExponent_outside F c i hn] at he
      omega
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hm
    have hkj : k=j := Fin.ext (by rw [colourExponent_at F c hcPair i k hik] at he; omega)
    exact ⟨hkj ▸ hik,hz⟩

theorem mem_rightResidual_code (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (k : Fin 5) (i : PrimeIndex F) :
    i ∈ idealSupport (colourIdeals F) (rightResidual c d k) ↔
      colourExponent F c i=0 ∧ colourExponent F d i=k.val+1 := by
  rw [mem_rightResidual_support F hF c d hc hd hcPair k i,← colourExponent_zero_iff F c hcPair i]
  constructor
  · rintro ⟨hi,hz⟩
    exact ⟨hz,colourExponent_at F d hdPair i k hi⟩
  · rintro ⟨hz,he⟩
    have hm : i ∈ tupleSupport F d := by
      by_contra hn
      rw [colourExponent_outside F d i hn] at he
      omega
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hm
    have hjk : j=k := Fin.ext (by rw [colourExponent_at F d hdPair i j hij] at he; omega)
    exact ⟨hjk ▸ hij,hz⟩

/-- Free pivot and higher blocks, still on the ORIGINAL common prime
universe. Their residual-ideal interpretations are proved below. -/
def pivotLeftPrimes (F : Finset ColourTuple) (c d : ColourTuple) : Finset (PrimeIndex F) :=
  Finset.univ.filter (fun i => colourExponent F c i=1 ∧ colourExponent F d i=0)
def pivotRightPrimes (F : Finset ColourTuple) (c d : ColourTuple) : Finset (PrimeIndex F) :=
  Finset.univ.filter (fun i => colourExponent F c i=0 ∧ colourExponent F d i=1)
def higherLeftPrimes (F : Finset ColourTuple) (c d : ColourTuple) : Finset (PrimeIndex F) :=
  Finset.univ.filter (fun i => 2 ≤ colourExponent F c i ∧ colourExponent F d i=0)
def higherRightPrimes (F : Finset ColourTuple) (c d : ColourTuple) : Finset (PrimeIndex F) :=
  Finset.univ.filter (fun i => colourExponent F c i=0 ∧ 2 ≤ colourExponent F d i)
def sharedPrimitivePrimes (F : Finset ColourTuple) (c d : ColourTuple) : Finset (PrimeIndex F) :=
  Finset.univ.filter (fun i => 0 < colourExponent F c i ∧ 0 < colourExponent F d i ∧
    colourExponent F c i ≠ colourExponent F d i)

theorem pivotLeftPrimes_eq_residual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    pivotLeftPrimes F c d = idealSupport (colourIdeals F) (leftResidual c d 0) := by
  ext i
  simpa only [pivotLeftPrimes,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_zero,Nat.zero_add] using
    (mem_leftResidual_code F hF c d hc hd hcPair hdPair 0 i).symm

theorem pivotRightPrimes_eq_residual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    pivotRightPrimes F c d = idealSupport (colourIdeals F) (rightResidual c d 0) := by
  ext i
  simpa only [pivotRightPrimes,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_zero,Nat.zero_add] using
    (mem_rightResidual_code F hF c d hc hd hcPair hdPair 0 i).symm

theorem primitivePrimes_partition (F : Finset ColourTuple) (c d : ColourTuple) :
    primitivePrimes F c d = pivotLeftPrimes F c d ∪ (pivotRightPrimes F c d ∪
      (higherLeftPrimes F c d ∪ (higherRightPrimes F c d ∪ sharedPrimitivePrimes F c d))) := by
  ext i
  simp only [primitivePrimes,pivotLeftPrimes,pivotRightPrimes,higherLeftPrimes,higherRightPrimes,
    sharedPrimitivePrimes,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  omega

section CommonGauss
variable {ι : Type*} [DecidableEq ι]
variable (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
variable (hg : ∀ i,lambda ∉ Ideal.span {p i})

/-- Product CRT separation on a finite active set INSIDE a fixed prime
universe. The unary blocks therefore already have an index universe fixed
before pairing; unused primes do not enter the Gauss coefficient. -/
theorem finite_gauss_pivot_swap
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hchar : ∀ i,ringChar (O⧸Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i,lambda^2 ∣ p i-1) (e cL cR : ι → ℕ)
    (A B CL CR T : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A (CL ∪ (CR ∪ T)))
    (hBC : Disjoint B (CL ∪ (CR ∪ T)))
    (hLR : Disjoint CL CR) (hLT : Disjoint CL T) (hRT : Disjoint CR T)
    (hA : ∀ i ∈ A,e i=1) (hB : ∀ i ∈ B,e i=5)
    (hCL : ∀ i ∈ CL,e i=cL i) (hCR : ∀ i ∈ CR,e i=6-cR i)
    (hcL : ∀ i ∈ CL,1 ≤ cL i) (hcR : ∀ i ∈ CR,2 ≤ cR i ∧ cR i < 6)
    (rA rB rCL rCR : EisensteinEPrimaryPhase.Coord)
    (hrA : residue (∏ i ∈ A,p i)=rA) (hrB : residue (∏ i ∈ B,p i)=rB)
    (hrCL : residue (∏ i ∈ CL,p i)=rCL) (hrCR : residue (∏ i ∈ CR,p i)=rCR) :
    varyingUnaryGauss p hp hg e (A ∪ (B ∪ (CL ∪ (CR ∪ T)))) =
      (varyingUnaryGauss p hp hg e A*crossBlock (crossSymbol p hg) e A CL*crossBlock (crossSymbol p hg) e A T)*
      (varyingUnaryGauss p hp hg e B*crossBlock (crossSymbol p hg) e B CR*crossBlock (crossSymbol p hg) e B T)*
      (varyingUnaryGauss p hp hg e (CL ∪ (CR ∪ T))*quadraticRayPair rA rB*
        quadraticRayPair rA rCR*quadraticRayPair rB rCL)*
      star (higherCrossPhase p hg A CR cR)*higherCrossPhase p hg B CL cL := by
  have hACR : Disjoint A CR := hAC.mono_right (by
    intro i hi; exact Finset.mem_union_right _ (Finset.mem_union_left _ hi))
  have hBCL : Disjoint B CL := hBC.mono_right Finset.subset_union_left
  change orderedBlock _ _ _ _ = _
  rw [orderedBlock_three _ _ _ A B (CL ∪ (CR ∪ T)) hAB hAC hBC,
    crossBlock_union_right _ _ A CL (CR ∪ T) (Finset.disjoint_union_right.mpr ⟨hLR,hLT⟩),
    crossBlock_union_right _ _ A CR T hRT,
    crossBlock_union_right _ _ B CL (CR ∪ T) (Finset.disjoint_union_right.mpr ⟨hLR,hLT⟩),
    crossBlock_union_right _ _ B CR T hRT,
    pivot_left_all_higher p hg hprimary e cR A CR hcR hA hCR,
    pivot_right_all_higher p hg hprimary e cL B CL hcL hB hCL,
    pivot_pivot_crossBlock p hg hprimary e A B hA hB,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hAB,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A CR hACR,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar B CL hBCL,hrA,hrB,hrCL,hrCR]
  unfold varyingUnaryGauss
  ring
end CommonGauss

def quotientExponentOnPool (F : Finset ColourTuple) (c d : ColourTuple) (i : PrimeIndex F) : ℕ :=
  quotientExponent (colourExponent F c i) (colourExponent F d i)

def gaussBlockOnPool (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (S : Finset (PrimeIndex F)) : ℂ :=
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  varyingUnaryGauss (poolPrimary (colourIdeals F))
    (poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF))
    (quotientExponentOnPool F c d) S

def crossBlockOnPool (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (S T : Finset (PrimeIndex F)) : ℂ :=
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  crossBlock (crossSymbol (poolPrimary (colourIdeals F))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)))
    (quotientExponentOnPool F c d) S T

def higherPhaseOnPool (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (S T : Finset (PrimeIndex F)) (colour : PrimeIndex F → ℕ) : ℂ :=
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  higherCrossPhase (poolPrimary (colourIdeals F))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) S T colour

def blockRay (F : Finset ColourTuple) (S : Finset (PrimeIndex F)) : EisensteinEPrimaryPhase.Coord :=
  residue (∏ i ∈ S,poolPrimary (colourIdeals F) i)

/-- The actual pair-dependent primitive Gauss coefficient, rewritten as a
finite product on the same universe fixed from the original row family. -/
theorem primitiveGauss_eq_common_block (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    primitiveGauss F hF c d = gaussBlockOnPool F hF c d (primitivePrimes F c d) := by
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  exact FirstPassCubeLabels.canonicalProductGauss_eq_gaussBlock
    (poolPrimary (colourIdeals F))
    (poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_coprime (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF))
    (primitivePrimes F c d) (quotientExponentOnPool F c d)
    (fun i hi => (quotientExponent_range (colourExponent_range F c hcPair i)
      (colourExponent_range F d hdPair i) (Finset.mem_filter.mp hi).2).1.ne')

/-- Exact actual mixed Γ factorization. All five primitive colour states,
including exponent three in shared off-diagonal cells, remain literal.
Only free colour-one ideals occur in the two final cross phases. -/
theorem actual_primitive_gauss_factor (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    let A := pivotLeftPrimes F c d
    let B := pivotRightPrimes F c d
    let CL := higherLeftPrimes F c d
    let CR := higherRightPrimes F c d
    let T := sharedPrimitivePrimes F c d
    primitiveGauss F hF c d =
      (gaussBlockOnPool F hF c d A*crossBlockOnPool F hF c d A CL*crossBlockOnPool F hF c d A T)*
      (gaussBlockOnPool F hF c d B*crossBlockOnPool F hF c d B CR*crossBlockOnPool F hF c d B T)*
      (gaussBlockOnPool F hF c d (CL ∪ (CR ∪ T))*quadraticRayPair (blockRay F A) (blockRay F B)*
        quadraticRayPair (blockRay F A) (blockRay F CR)*quadraticRayPair (blockRay F B) (blockRay F CL))*
      star (higherPhaseOnPool F hF A CR (colourExponent F d))*
        higherPhaseOnPool F hF B CL (colourExponent F c) := by
  dsimp only
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  rw [primitiveGauss_eq_common_block F hF c d hcPair hdPair,primitivePrimes_partition]
  apply finite_gauss_pivot_swap
    (poolPrimary (colourIdeals F))
    (poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_coprime (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_odd (colourIdeals F) (colourIdeals_admissible F hF))
    (fun i => (primaryPrime_spec i.val
      (poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF) i)).2.2.2)
    (quotientExponentOnPool F c d) (colourExponent F c) (colourExponent F d)
    (pivotLeftPrimes F c d) (pivotRightPrimes F c d)
    (higherLeftPrimes F c d) (higherRightPrimes F c d) (sharedPrimitivePrimes F c d)
  all_goals first
    | (apply Finset.disjoint_left.mpr
       intro i hi hj
       simp only [pivotLeftPrimes,pivotRightPrimes,higherLeftPrimes,higherRightPrimes,
         sharedPrimitivePrimes,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
       omega)
    | (intro i hi
       have hl := colourExponent_range F c hcPair i
       have hr := colourExponent_range F d hdPair i
       simp only [pivotLeftPrimes,pivotRightPrimes,higherLeftPrimes,higherRightPrimes,
         sharedPrimitivePrimes,Finset.mem_filter,Finset.mem_univ,true_and] at hi
       try simp only [quotientExponentOnPool,quotientExponent]
       omega)
    | rfl

theorem colourExponent_eq_iff (F : Finset ColourTuple) (c : ColourTuple)
    (hpair : Pairwise (fun j k => IsCoprime (c j) (c k))) (i : PrimeIndex F) (j : Fin 5) :
    colourExponent F c i=j.val+1 ↔ i ∈ idealSupport (colourIdeals F) (c j) := by
  constructor
  · intro he
    have hm : i ∈ tupleSupport F c := by
      by_contra hn
      rw [colourExponent_outside F c i hn] at he
      omega
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hm
    have hkj : k=j := Fin.ext (by rw [colourExponent_at F c hpair i k hik] at he; omega)
    exact hkj ▸ hik
  · exact colourExponent_at F c hpair i j

theorem mem_table_cell_code (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F) (j k : Fin 5) :
    i ∈ idealSupport (colourIdeals F) (table c d j k) ↔
      colourExponent F c i=j.val+1 ∧ colourExponent F d i=k.val+1 := by
  change i ∈ idealSupport (colourIdeals F) (gcd (c j) (d k)) ↔ _
  rw [mem_support_gcd F _ _ (hF c hc j).1 (hF d hd k).1 i,
    colourExponent_eq_iff F c hcPair i j,colourExponent_eq_iff F d hdPair i k]

def higherPrimes (F : Finset ColourTuple) (v : HigherTuple) : Finset (PrimeIndex F) :=
  Finset.univ.biUnion (fun j => idealSupport (colourIdeals F) (v j))

theorem higherLeftPrimes_eq_residual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    higherLeftPrimes F c d = higherPrimes F (higherTuple (leftResidual c d)) := by
  ext i
  simp only [higherLeftPrimes,higherPrimes,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_biUnion,higherTuple]
  constructor
  · rintro ⟨hl,hr⟩
    have hm : i ∈ tupleSupport F c := by
      by_contra hn
      rw [colourExponent_outside F c i hn] at hl
      omega
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hm
    have hj0 : 0 < j.val := by rw [colourExponent_at F c hcPair i j hij] at hl; omega
    let k : Fin 4 := ⟨j.val-1,by omega⟩
    have hkj : k.succ=j := Fin.ext (by dsimp [k]; omega)
    refine ⟨k,?_⟩
    rw [hkj,mem_leftResidual_code F hF c d hc hd hcPair hdPair]
    exact ⟨colourExponent_at F c hcPair i j hij,hr⟩
  · rintro ⟨k,hk⟩
    obtain ⟨hl,hr⟩ := (mem_leftResidual_code F hF c d hc hd hcPair hdPair k.succ i).mp hk
    simp only [Fin.val_succ] at hl
    exact ⟨by omega,hr⟩

theorem higherRightPrimes_eq_residual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    higherRightPrimes F c d = higherPrimes F (higherTuple (rightResidual c d)) := by
  ext i
  simp only [higherRightPrimes,higherPrimes,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_biUnion,higherTuple]
  constructor
  · rintro ⟨hl,hr⟩
    have hm : i ∈ tupleSupport F d := by
      by_contra hn
      rw [colourExponent_outside F d i hn] at hr
      omega
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hm
    have hk0 : 0 < k.val := by rw [colourExponent_at F d hdPair i k hik] at hr; omega
    let j : Fin 4 := ⟨k.val-1,by omega⟩
    have hjk : j.succ=k := Fin.ext (by dsimp [j]; omega)
    refine ⟨j,?_⟩
    rw [hjk,mem_rightResidual_code F hF c d hc hd hcPair hdPair]
    exact ⟨hl,colourExponent_at F d hdPair i k hik⟩
  · rintro ⟨j,hj⟩
    obtain ⟨hl,hr⟩ := (mem_rightResidual_code F hF c d hc hd hcPair hdPair j.succ i).mp hj
    simp only [Fin.val_succ] at hr
    exact ⟨hl,by omega⟩

def offDiagonalPrimes (F : Finset ColourTuple) (g : SharedTable) : Finset (PrimeIndex F) :=
  Finset.univ.biUnion (fun q : Fin 5 × Fin 5 =>
    if q.1=q.2 then ∅ else idealSupport (colourIdeals F) (g q.1 q.2))

theorem sharedPrimitivePrimes_eq_table (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    sharedPrimitivePrimes F c d = offDiagonalPrimes F (table c d) := by
  ext i
  simp only [sharedPrimitivePrimes,Finset.mem_filter,Finset.mem_univ,true_and,
    offDiagonalPrimes,Finset.mem_biUnion]
  constructor
  · rintro ⟨hl,hr,hne⟩
    have hci : i ∈ tupleSupport F c := by
      by_contra hn
      rw [colourExponent_outside F c i hn] at hl
      omega
    have hdi : i ∈ tupleSupport F d := by
      by_contra hn
      rw [colourExponent_outside F d i hn] at hr
      omega
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hci
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hdi
    have hjk : j ≠ k := by
      intro he
      rw [colourExponent_at F c hcPair i j hij,colourExponent_at F d hdPair i k hik,he] at hne
      exact hne rfl
    refine ⟨(j,k),?_⟩
    simp only [hjk,ite_false]
    exact (mem_table_cell_code F hF c d hc hd hcPair hdPair i j k).mpr
      ⟨colourExponent_at F c hcPair i j hij,colourExponent_at F d hdPair i k hik⟩
  · rintro ⟨⟨j,k⟩,hi⟩
    by_cases hjk : j=k
    · simpa [hjk] using hi
    · simp only [hjk,ite_false] at hi
      obtain ⟨hl,hr⟩ := (mem_table_cell_code F hF c d hc hd hcPair hdPair i j k).mp hi
      have hn : j.val ≠ k.val := fun he => hjk (Fin.ext he)
      omega

/-- Table exponents are defined from the fixed table alone, before either
free residual row or ordinary Fourier source is chosen. -/
def tableColourCode (F : Finset ColourTuple) (g : SharedTable)
    (colour : Fin 5 × Fin 5 → ℕ) (i : PrimeIndex F) : ℕ :=
  ∑ q : Fin 5 × Fin 5, if i ∈ idealSupport (colourIdeals F) (g q.1 q.2) then colour q else 0

def tableExponent (F : Finset ColourTuple) (g : SharedTable) (i : PrimeIndex F) : ℕ :=
  quotientExponent (tableColourCode F g (fun q => q.1.val+1) i)
    (tableColourCode F g (fun q => q.2.val+1) i)

theorem tableColourCode_at (F : Finset ColourTuple) (g : SharedTable)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (colour : Fin 5 × Fin 5 → ℕ) (i : PrimeIndex F) (q : Fin 5 × Fin 5)
    (hi : i ∈ idealSupport (colourIdeals F) (g q.1 q.2)) : tableColourCode F g colour i=colour q := by
  unfold tableColourCode
  rw [Finset.sum_eq_single q]
  · exact ite_eq_left hi
  · intro r hr hrq
    apply ite_eq_right
    intro hir
    exact Finset.disjoint_left.mp
      (idealSupport_disjoint_of_coprime (colourIdeals F) _ _ (hgp hrq.symm)) hi hir
  · simp

theorem tableExponent_eq_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F)
    (hi : i ∈ sharedPrimitivePrimes F c d) :
    tableExponent F (table c d) i=quotientExponentOnPool F c d i := by
  rw [sharedPrimitivePrimes_eq_table F hF c d hc hd hcPair hdPair] at hi
  obtain ⟨⟨j,k⟩,hq,hij⟩ := Finset.mem_biUnion.mp hi
  by_cases hjk : j=k
  · simpa [hjk] using hij
  · simp only [hjk,ite_false] at hij
    obtain ⟨hl,hr⟩ := (mem_table_cell_code F hF c d hc hd hcPair hdPair i j k).mp hij
    unfold tableExponent quotientExponentOnPool
    rw [tableColourCode_at F _ (table_pairwise hcPair hdPair) _ i (j,k) hij,
      tableColourCode_at F _ (table_pairwise hcPair hdPair) _ i (j,k) hij,hl,hr]

theorem tupleSupport_leftResidual_code (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F) :
    i ∈ tupleSupport F (leftResidual c d) ↔
      0 < colourExponent F c i ∧ colourExponent F d i=0 := by
  constructor
  · intro hi
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨hl,hr⟩ := (mem_leftResidual_code F hF c d hc hd hcPair hdPair j i).mp hij
    exact ⟨by omega,hr⟩
  · rintro ⟨hl,hr⟩
    have hm : i ∈ tupleSupport F c := by
      by_contra hn
      rw [colourExponent_outside F c i hn] at hl
      omega
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,
      (mem_leftResidual_code F hF c d hc hd hcPair hdPair j i).mpr
        ⟨colourExponent_at F c hcPair i j hij,hr⟩⟩

theorem tupleSupport_rightResidual_code (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F) :
    i ∈ tupleSupport F (rightResidual c d) ↔
      colourExponent F c i=0 ∧ 0 < colourExponent F d i := by
  constructor
  · intro hi
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨hl,hr⟩ := (mem_rightResidual_code F hF c d hc hd hcPair hdPair k i).mp hik
    exact ⟨hl,by omega⟩
  · rintro ⟨hl,hr⟩
    have hm : i ∈ tupleSupport F d := by
      by_contra hn
      rw [colourExponent_outside F d i hn] at hr
      omega
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,
      (mem_rightResidual_code F hF c d hc hd hcPair hdPair k i).mpr
        ⟨hl,colourExponent_at F d hdPair i k hik⟩⟩

theorem colourExponent_leftResidual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F)
    (hi : i ∈ tupleSupport F (leftResidual c d)) :
    colourExponent F (leftResidual c d) i=colourExponent F c i := by
  obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
  rw [colourExponent_at F _ (leftResidual_pairwise hcPair hdPair) i j hij]
  exact ((mem_leftResidual_code F hF c d hc hd hcPair hdPair j i).mp hij).1.symm

theorem colourExponent_rightResidual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F)
    (hi : i ∈ tupleSupport F (rightResidual c d)) :
    colourExponent F (rightResidual c d) i=colourExponent F d i := by
  obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
  rw [colourExponent_at F _ (rightResidual_pairwise hcPair hdPair) i j hij]
  exact ((mem_rightResidual_code F hF c d hc hd hcPair hdPair j i).mp hij).2.symm

/-- These exponent arrays use ONLY their own residual tuple and the fixed
shared table. They are formed before the opposite free pivot is summed. -/
def leftUnaryExponent (F : Finset ColourTuple) (g : SharedTable) (a : ColourTuple) (i : PrimeIndex F) : ℕ :=
  if i ∈ tupleSupport F a then colourExponent F a i else tableExponent F g i
def rightUnaryExponent (F : Finset ColourTuple) (g : SharedTable) (b : ColourTuple) (i : PrimeIndex F) : ℕ :=
  if i ∈ tupleSupport F b then 6-colourExponent F b i else tableExponent F g i

theorem leftUnaryExponent_eq_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F)
    (hi : i ∈ pivotLeftPrimes F c d ∪ (higherLeftPrimes F c d ∪ sharedPrimitivePrimes F c d)) :
    leftUnaryExponent F (table c d) (leftResidual c d) i=quotientExponentOnPool F c d i := by
  unfold leftUnaryExponent
  by_cases ha : i ∈ tupleSupport F (leftResidual c d)
  · rw [ite_eq_left ha,colourExponent_leftResidual F hF c d hc hd hcPair hdPair i ha]
    obtain ⟨hl,hr⟩ := (tupleSupport_leftResidual_code F hF c d hc hd hcPair hdPair i).mp ha
    have hrange := colourExponent_range F c hcPair i
    unfold quotientExponentOnPool quotientExponent
    omega
  · rw [ite_eq_right ha]
    apply tableExponent_eq_actual F hF c d hc hd hcPair hdPair i
    simp only [Finset.mem_union,pivotLeftPrimes,higherLeftPrimes,Finset.mem_filter,
      Finset.mem_univ,true_and] at hi
    have hn := (tupleSupport_leftResidual_code F hF c d hc hd hcPair hdPair i).not.mp ha
    rcases hi with hi | hi | hi
    · exact (hn ⟨by omega,hi.2⟩).elim
    · exact (hn ⟨by omega,hi.2⟩).elim
    · exact hi

theorem rightUnaryExponent_eq_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F)
    (hi : i ∈ pivotRightPrimes F c d ∪ (higherRightPrimes F c d ∪ sharedPrimitivePrimes F c d)) :
    rightUnaryExponent F (table c d) (rightResidual c d) i=quotientExponentOnPool F c d i := by
  unfold rightUnaryExponent
  by_cases hb : i ∈ tupleSupport F (rightResidual c d)
  · rw [ite_eq_left hb,colourExponent_rightResidual F hF c d hc hd hcPair hdPair i hb]
    obtain ⟨hl,hr⟩ := (tupleSupport_rightResidual_code F hF c d hc hd hcPair hdPair i).mp hb
    have hrange := colourExponent_range F d hdPair i
    unfold quotientExponentOnPool quotientExponent
    omega
  · rw [ite_eq_right hb]
    apply tableExponent_eq_actual F hF c d hc hd hcPair hdPair i
    simp only [Finset.mem_union,pivotRightPrimes,higherRightPrimes,Finset.mem_filter,
      Finset.mem_univ,true_and] at hi
    have hn := (tupleSupport_rightResidual_code F hF c d hc hd hcPair hdPair i).not.mp hb
    rcases hi with hi | hi | hi
    · exact (hn ⟨hi.1,by omega⟩).elim
    · exact (hn ⟨hi.1,by omega⟩).elim
    · exact hi

def higherAsTuple (v : HigherTuple) : ColourTuple := Fin.cons 1 v

theorem higherAsTuple_support (F : Finset ColourTuple) (v : HigherTuple) :
    tupleSupport F (higherAsTuple v)=higherPrimes F v := by
  ext i
  simp [tupleSupport,higherPrimes,higherAsTuple,Fin.exists_fin_succ,idealSupport,← Ideal.one_eq_top]

theorem colourExponent_eq_higher (F : Finset ColourTuple) (a : ColourTuple) (i : PrimeIndex F)
    (hi : i ∉ idealSupport (colourIdeals F) (a 0)) :
    colourExponent F a i=colourExponent F (higherAsTuple (higherTuple a)) i := by
  unfold colourExponent
  conv_lhs => rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [higherAsTuple,Fin.cons_zero,Fin.cons_succ,higherTuple]
  have h1 : i ∉ idealSupport (colourIdeals F) 1 := by simp [idealSupport,← Ideal.one_eq_top]
  rw [ite_eq_right hi,ite_eq_right h1]

def higherPrimitiveExponent (F : Finset ColourTuple) (g : SharedTable)
    (v w : HigherTuple) (i : PrimeIndex F) : ℕ :=
  if i ∈ higherPrimes F v then colourExponent F (higherAsTuple v) i else
    if i ∈ higherPrimes F w then 6-colourExponent F (higherAsTuple w) i else tableExponent F g i

theorem higherPrimitiveExponent_eq_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F)
    (hi : i ∈ higherLeftPrimes F c d ∪ (higherRightPrimes F c d ∪ sharedPrimitivePrimes F c d)) :
    higherPrimitiveExponent F (table c d) (higherTuple (leftResidual c d))
      (higherTuple (rightResidual c d)) i=quotientExponentOnPool F c d i := by
  have hpL := pivotLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair
  have hpR := pivotRightPrimes_eq_residual F hF c d hc hd hcPair hdPair
  have hhL := higherLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair
  have hhR := higherRightPrimes_eq_residual F hF c d hc hd hcPair hdPair
  unfold higherPrimitiveExponent
  rw [← hhL,← hhR]
  rcases Finset.mem_union.mp hi with hl | hr
  · rw [ite_eq_left hl]
    have hcode := (Finset.mem_filter.mp hl).2
    have hs : i ∈ tupleSupport F (leftResidual c d) :=
      (tupleSupport_leftResidual_code F hF c d hc hd hcPair hdPair i).mpr ⟨by omega,hcode.2⟩
    have hn : i ∉ idealSupport (colourIdeals F) (leftResidual c d 0) := by
      rw [← hpL]
      simp only [pivotLeftPrimes,Finset.mem_filter,Finset.mem_univ,true_and]
      omega
    rw [← colourExponent_eq_higher F _ i hn,colourExponent_leftResidual F hF c d hc hd hcPair hdPair i hs]
    have hlrange := colourExponent_range F c hcPair i
    unfold quotientExponentOnPool quotientExponent
    omega
  · rcases Finset.mem_union.mp hr with hr | ht
    · have hcode := (Finset.mem_filter.mp hr).2
      have hnL : i ∉ higherLeftPrimes F c d := by
        simp only [higherLeftPrimes,Finset.mem_filter,Finset.mem_univ,true_and]
        omega
      rw [ite_eq_right hnL,ite_eq_left hr]
      have hs : i ∈ tupleSupport F (rightResidual c d) :=
        (tupleSupport_rightResidual_code F hF c d hc hd hcPair hdPair i).mpr ⟨hcode.1,by omega⟩
      have hn : i ∉ idealSupport (colourIdeals F) (rightResidual c d 0) := by
        rw [← hpR]
        simp only [pivotRightPrimes,Finset.mem_filter,Finset.mem_univ,true_and]
        omega
      rw [← colourExponent_eq_higher F _ i hn,colourExponent_rightResidual F hF c d hc hd hcPair hdPair i hs]
      have hrrange := colourExponent_range F d hdPair i
      unfold quotientExponentOnPool quotientExponent
      omega
    · have hcode := (Finset.mem_filter.mp ht).2
      have hnL : i ∉ higherLeftPrimes F c d := by
        simp only [higherLeftPrimes,Finset.mem_filter,Finset.mem_univ,true_and]
        omega
      have hnR : i ∉ higherRightPrimes F c d := by
        simp only [higherRightPrimes,Finset.mem_filter,Finset.mem_univ,true_and]
        omega
      rw [ite_eq_right hnL,ite_eq_right hnR]
      exact tableExponent_eq_actual F hF c d hc hd hcPair hdPair i ht

section ExponentCongruence
variable {ι : Type*} [DecidableEq ι]
variable (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
variable (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem unaryGauss_congr_on (e e' : ι → ℕ) (S : Finset ι) (he : ∀ i ∈ S,e i=e' i) :
    varyingUnaryGauss p hp hg e S=varyingUnaryGauss p hp hg e' S := by
  unfold varyingUnaryGauss orderedBlock
  apply Finset.prod_congr rfl
  intro i hi
  simp_rw [he i hi]

theorem crossBlock_congr_on (e e' : ι → ℕ) (S T : Finset ι)
    (heS : ∀ i ∈ S,e i=e' i) (heT : ∀ i ∈ T,e i=e' i) :
    crossBlock (crossSymbol p hg) e S T=crossBlock (crossSymbol p hg) e' S T := by
  unfold crossBlock
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  rw [heS i hi,heT k hk]

theorem higherPhase_congr_on (S T : Finset ι) (colour colour' : ι → ℕ)
    (he : ∀ i ∈ T,colour i=colour' i) :
    higherCrossPhase p hg S T colour=higherCrossPhase p hg S T colour' := by
  unfold higherCrossPhase
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  rw [he k hk]
end ExponentCongruence

def gaussWithExponent (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (e : PrimeIndex F → ℕ) (S : Finset (PrimeIndex F)) : ℂ :=
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  varyingUnaryGauss (poolPrimary (colourIdeals F))
    (poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) e S

def crossWithExponent (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (e : PrimeIndex F → ℕ) (S T : Finset (PrimeIndex F)) : ℂ :=
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  crossBlock (crossSymbol (poolPrimary (colourIdeals F))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF))) e S T

def leftUnaryFactor (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (g : SharedTable) (a : ColourTuple) : ℂ :=
  let e := leftUnaryExponent F g a
  let A := idealSupport (colourIdeals F) (a 0)
  let CL := higherPrimes F (higherTuple a)
  let T := offDiagonalPrimes F g
  gaussWithExponent F hF e A*crossWithExponent F hF e A CL*crossWithExponent F hF e A T

def rightUnaryFactor (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (g : SharedTable) (b : ColourTuple) : ℂ :=
  let e := rightUnaryExponent F g b
  let B := idealSupport (colourIdeals F) (b 0)
  let CR := higherPrimes F (higherTuple b)
  let T := offDiagonalPrimes F g
  gaussWithExponent F hF e B*crossWithExponent F hF e B CR*crossWithExponent F hF e B T

def higherGaussFactor (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (g : SharedTable) (v w : HigherTuple) (rA rB : EisensteinEPrimaryPhase.Coord) : ℂ :=
  let CL := higherPrimes F v
  let CR := higherPrimes F w
  let T := offDiagonalPrimes F g
  gaussWithExponent F hF (higherPrimitiveExponent F g v w) (CL ∪ (CR ∪ T))*
    quadraticRayPair rA rB*quadraticRayPair rA (blockRay F CR)*quadraticRayPair rB (blockRay F CL)

/-- The entire left unary Γ factor is chosen from the fixed table and its
own residual tuple BEFORE the right free pivot is summed. -/
theorem leftUnaryFactor_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    leftUnaryFactor F hF (table c d) (leftResidual c d) =
      gaussBlockOnPool F hF c d (pivotLeftPrimes F c d)*
        crossBlockOnPool F hF c d (pivotLeftPrimes F c d) (higherLeftPrimes F c d)*
        crossBlockOnPool F hF c d (pivotLeftPrimes F c d) (sharedPrimitivePrimes F c d) := by
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  unfold leftUnaryFactor
  dsimp only
  rw [← pivotLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair,
    ← higherLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair,
    ← sharedPrimitivePrimes_eq_table F hF c d hc hd hcPair hdPair]
  have he := leftUnaryExponent_eq_actual F hF c d hc hd hcPair hdPair
  have hA (i : PrimeIndex F) (hi : i ∈ pivotLeftPrimes F c d) :=
    he i (Finset.mem_union_left _ hi)
  have hCL (i : PrimeIndex F) (hi : i ∈ higherLeftPrimes F c d) :=
    he i (Finset.mem_union_right _ (Finset.mem_union_left _ hi))
  have hT (i : PrimeIndex F) (hi : i ∈ sharedPrimitivePrimes F c d) :=
    he i (Finset.mem_union_right _ (Finset.mem_union_right _ hi))
  have h1 := unaryGauss_congr_on (poolPrimary (colourIdeals F))
    (poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) _ _ _ hA
  have h2 := crossBlock_congr_on (poolPrimary (colourIdeals F))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) _ _ _ _ hA hCL
  have h3 := crossBlock_congr_on (poolPrimary (colourIdeals F))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) _ _ _ _ hA hT
  exact congrArg₂ (·*·) (congrArg₂ (·*·) h1 h2) h3

theorem rightUnaryFactor_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    rightUnaryFactor F hF (table c d) (rightResidual c d) =
      gaussBlockOnPool F hF c d (pivotRightPrimes F c d)*
        crossBlockOnPool F hF c d (pivotRightPrimes F c d) (higherRightPrimes F c d)*
        crossBlockOnPool F hF c d (pivotRightPrimes F c d) (sharedPrimitivePrimes F c d) := by
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  unfold rightUnaryFactor
  dsimp only
  rw [← pivotRightPrimes_eq_residual F hF c d hc hd hcPair hdPair,
    ← higherRightPrimes_eq_residual F hF c d hc hd hcPair hdPair,
    ← sharedPrimitivePrimes_eq_table F hF c d hc hd hcPair hdPair]
  have he := rightUnaryExponent_eq_actual F hF c d hc hd hcPair hdPair
  have hB (i : PrimeIndex F) (hi : i ∈ pivotRightPrimes F c d) :=
    he i (Finset.mem_union_left _ hi)
  have hCR (i : PrimeIndex F) (hi : i ∈ higherRightPrimes F c d) :=
    he i (Finset.mem_union_right _ (Finset.mem_union_left _ hi))
  have hT (i : PrimeIndex F) (hi : i ∈ sharedPrimitivePrimes F c d) :=
    he i (Finset.mem_union_right _ (Finset.mem_union_right _ hi))
  have h1 := unaryGauss_congr_on (poolPrimary (colourIdeals F))
    (poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) _ _ _ hB
  have h2 := crossBlock_congr_on (poolPrimary (colourIdeals F))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) _ _ _ _ hB hCR
  have h3 := crossBlock_congr_on (poolPrimary (colourIdeals F))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) _ _ _ _ hB hT
  exact congrArg₂ (·*·) (congrArg₂ (·*·) h1 h2) h3

theorem higherGaussFactor_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (rA rB : EisensteinEPrimaryPhase.Coord) :
    higherGaussFactor F hF (table c d) (higherTuple (leftResidual c d))
      (higherTuple (rightResidual c d)) rA rB =
      gaussBlockOnPool F hF c d (higherLeftPrimes F c d ∪ (higherRightPrimes F c d ∪ sharedPrimitivePrimes F c d))*
        quadraticRayPair rA rB*quadraticRayPair rA (blockRay F (higherRightPrimes F c d))*
        quadraticRayPair rB (blockRay F (higherLeftPrimes F c d)) := by
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  unfold higherGaussFactor
  dsimp only
  rw [← higherLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair,
    ← higherRightPrimes_eq_residual F hF c d hc hd hcPair hdPair,
    ← sharedPrimitivePrimes_eq_table F hF c d hc hd hcPair hdPair]
  have he := higherPrimitiveExponent_eq_actual F hF c d hc hd hcPair hdPair
  have hh := unaryGauss_congr_on (poolPrimary (colourIdeals F))
    (poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) _ _ _ he
  exact congrArg (fun x => x*quadraticRayPair rA rB*
    quadraticRayPair rA (blockRay F (higherRightPrimes F c d))*
    quadraticRayPair rB (blockRay F (higherLeftPrimes F c d))) hh

theorem leftHigherColour_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F)
    (hi : i ∈ higherLeftPrimes F c d) :
    colourExponent F c i=colourExponent F (higherAsTuple (higherTuple (leftResidual c d))) i := by
  have hcode := (Finset.mem_filter.mp hi).2
  have hs : i ∈ tupleSupport F (leftResidual c d) :=
    (tupleSupport_leftResidual_code F hF c d hc hd hcPair hdPair i).mpr ⟨by omega,hcode.2⟩
  have hn : i ∉ idealSupport (colourIdeals F) (leftResidual c d 0) := by
    rw [← pivotLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair]
    simp only [pivotLeftPrimes,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  rw [← colourExponent_leftResidual F hF c d hc hd hcPair hdPair i hs,
    colourExponent_eq_higher F _ i hn]

theorem rightHigherColour_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (i : PrimeIndex F)
    (hi : i ∈ higherRightPrimes F c d) :
    colourExponent F d i=colourExponent F (higherAsTuple (higherTuple (rightResidual c d))) i := by
  have hcode := (Finset.mem_filter.mp hi).2
  have hs : i ∈ tupleSupport F (rightResidual c d) :=
    (tupleSupport_rightResidual_code F hF c d hc hd hcPair hdPair i).mpr ⟨hcode.1,by omega⟩
  have hn : i ∉ idealSupport (colourIdeals F) (rightResidual c d 0) := by
    rw [← pivotRightPrimes_eq_residual F hF c d hc hd hcPair hdPair]
    simp only [pivotRightPrimes,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  rw [← colourExponent_rightResidual F hF c d hc hd hcPair hdPair i hs,
    colourExponent_eq_higher F _ i hn]

/-- Actual Γ now has the precise BEFORE-PAIRING dependency of the swap:
one own left coefficient, one own right coefficient, one higher-only kernel
after fixing pivot rays, and two literal higher-cross modulations. -/
theorem actual_primitive_gauss_independent (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    let a := leftResidual c d
    let b := rightResidual c d
    let A := idealSupport (colourIdeals F) (a 0)
    let B := idealSupport (colourIdeals F) (b 0)
    let v := higherTuple a
    let w := higherTuple b
    primitiveGauss F hF c d =
      leftUnaryFactor F hF (table c d) a*rightUnaryFactor F hF (table c d) b*
      higherGaussFactor F hF (table c d) v w (blockRay F A) (blockRay F B)*
      star (higherPhaseOnPool F hF A (higherPrimes F w) (colourExponent F (higherAsTuple w)))*
        higherPhaseOnPool F hF B (higherPrimes F v) (colourExponent F (higherAsTuple v)) := by
  dsimp only
  rw [actual_primitive_gauss_factor F hF c d hcPair hdPair,
    ← leftUnaryFactor_actual F hF c d hc hd hcPair hdPair,
    ← rightUnaryFactor_actual F hF c d hc hd hcPair hdPair,
    ← higherGaussFactor_actual F hF c d hc hd hcPair hdPair]
  have hphaseL : higherPhaseOnPool F hF (pivotLeftPrimes F c d) (higherRightPrimes F c d)
      (colourExponent F d)=higherPhaseOnPool F hF (pivotLeftPrimes F c d) (higherRightPrimes F c d)
        (colourExponent F (higherAsTuple (higherTuple (rightResidual c d)))) := by
    letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
    exact higherPhase_congr_on (poolPrimary (colourIdeals F))
      (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) _ _ _ _
      (rightHigherColour_actual F hF c d hc hd hcPair hdPair)
  have hphaseR : higherPhaseOnPool F hF (pivotRightPrimes F c d) (higherLeftPrimes F c d)
      (colourExponent F c)=higherPhaseOnPool F hF (pivotRightPrimes F c d) (higherLeftPrimes F c d)
        (colourExponent F (higherAsTuple (higherTuple (leftResidual c d)))) := by
    letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
    exact higherPhase_congr_on (poolPrimary (colourIdeals F))
      (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) _ _ _ _
      (leftHigherColour_actual F hF c d hc hd hcPair hdPair)
  rw [hphaseL,hphaseR,pivotLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair,
    pivotRightPrimes_eq_residual F hF c d hc hd hcPair hdPair,
    higherLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair,
    higherRightPrimes_eq_residual F hF c d hc hd hcPair hdPair]

/-- Divisor ideals use the same original prime pool; forming a gcd residual
does not require enlarging it after the opposite row has been selected. -/
theorem support_product_of_dvd_colour (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c : ColourTuple) (hc : c ∈ F) (j : Fin 5)
    (I : Ideal O) (hI : Squarefree I) (hdiv : I ∣ c j) :
    (∏ i ∈ idealSupport (colourIdeals F) I,i.val)=I := by
  have himage : (idealSupport (colourIdeals F) I).image Subtype.val=
      (UniqueFactorizationMonoid.normalizedFactors I).toFinset := by
    ext P
    simp only [Finset.mem_image,Multiset.mem_toFinset]
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact (mem_idealSupport_iff _ _ p).mp hp
    · intro hP
      have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
      have hPdiv := (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP).trans hdiv
      have hPmem : P ∈ UniqueFactorizationMonoid.normalizedFactors (c j) :=
        (Ideal.mem_normalizedFactors_iff (hF c hc j).1).mpr
          ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hPdiv⟩
      let p : PrimeIndex F := ⟨P,mem_primePool_iff.mpr ⟨c j,colour_mem hc j,hPmem⟩⟩
      exact ⟨p,(mem_idealSupport_iff _ _ p).mpr hP,rfl⟩
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI
  calc
    _ = ∏ P ∈ (idealSupport (colourIdeals F) I).image Subtype.val,P := by
      rw [Finset.prod_image]
      exact fun a ha b hb h => Subtype.val_injective h
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,P := by rw [himage]
    _ = (UniqueFactorizationMonoid.normalizedFactors I).prod := by
      change ((UniqueFactorizationMonoid.normalizedFactors I).toFinset.val.map id).prod=_
      rw [Multiset.map_id,Multiset.toFinset_val,Multiset.dedup_eq_self.mpr hnodup]
    _ = I := Ideal.prod_normalizedFactors_eq_self hI.ne_zero

theorem primary_product_of_dvd_colour (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c : ColourTuple) (hc : c ∈ F) (j : Fin 5)
    (I : Ideal O) (hI : Squarefree I) (hdiv : I ∣ c j) :
    (∏ i ∈ idealSupport (colourIdeals F) I,poolPrimary (colourIdeals F) i)=primaryGenerator I := by
  calc
    _ = ∏ i ∈ idealSupport (colourIdeals F) I,primaryGenerator i.val :=
      Finset.prod_congr rfl (fun i hi => primaryPrime_eq_primaryGenerator i.val)
    _ = primaryGenerator (∏ i ∈ idealSupport (colourIdeals F) I,i.val) := by
      change (∏ i ∈ idealSupport (colourIdeals F) I,primaryGeneratorHom i.val)=
        primaryGeneratorHom (∏ i ∈ idealSupport (colourIdeals F) I,i.val)
      rw [map_prod]
    _ = primaryGenerator I := congrArg _ (support_product_of_dvd_colour F hF c hc j I hI hdiv)

theorem primitiveRow_eq_common_feature (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (n : O) :
    primitiveRow F hF c d n=featureBlock (fun i : PrimeIndex F => i.val)
      (poolGood (colourIdeals F) (colourIdeals_admissible F hF))
      (quotientExponentOnPool F c d) (primitivePrimes F c d) n := by
  rw [primitiveRow_eq]
  unfold finiteSexticRow
  change (∏ i : primitivePrimes F c d,
    (canonicalSextic i.val.val (poolGood (colourIdeals F) (colourIdeals_admissible F hF) i.val)^
      quotientExponentOnPool F c d i.val) (Ideal.Quotient.mk i.val.val n))=_
  have he (i : primitivePrimes F c d) :
      (canonicalSextic i.val.val (poolGood (colourIdeals F) (colourIdeals_admissible F hF) i.val)^
        quotientExponentOnPool F c d i.val) (Ideal.Quotient.mk i.val.val n)=
      (canonicalSextic i.val.val (poolGood (colourIdeals F) (colourIdeals_admissible F hF) i.val)
        (Ideal.Quotient.mk i.val.val n))^quotientExponentOnPool F c d i.val :=
    MulChar.pow_apply' _ (primitiveExponent_range F c d hcPair hdPair i).1.ne' _
  simp_rw [he]
  exact Finset.prod_coe_sort (primitivePrimes F c d) (fun i : PrimeIndex F =>
    ((canonicalSextic i.val (poolGood (colourIdeals F) (colourIdeals_admissible F hF) i)
      (Ideal.Quotient.mk i.val n) : ℂ))^quotientExponentOnPool F c d i)

def higherFeature (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (g : SharedTable) (v w : HigherTuple) (n : O) : ℂ :=
  featureBlock (fun i : PrimeIndex F => i.val)
    (poolGood (colourIdeals F) (colourIdeals_admissible F hF)) (higherPrimitiveExponent F g v w)
    (higherPrimes F v ∪ (higherPrimes F w ∪ offDiagonalPrimes F g)) n

/-- Actual primitive row splits into its two literal free squarefree pivots
and ONE higher-only feature. Every shared primitive exponent is retained. -/
theorem primitiveRow_pivot_higher (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (n : O) :
    primitiveRow F hF c d n=primitivePair (leftResidual c d 0) (rightResidual c d 0) n*
      higherFeature F hF (table c d) (higherTuple (leftResidual c d)) (higherTuple (rightResidual c d)) n := by
  let A := pivotLeftPrimes F c d
  let B := pivotRightPrimes F c d
  let C := higherLeftPrimes F c d ∪ (higherRightPrimes F c d ∪ sharedPrimitivePrimes F c d)
  let good := poolGood (colourIdeals F) (colourIdeals_admissible F hF)
  let e := quotientExponentOnPool F c d
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hl := (Finset.mem_filter.mp hi).2
    have hr := (Finset.mem_filter.mp hj).2
    omega
  have hAC : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [A,C,pivotLeftPrimes,higherLeftPrimes,higherRightPrimes,sharedPrimitivePrimes,
      Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
    omega
  have hBC : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [B,C,pivotRightPrimes,higherLeftPrimes,higherRightPrimes,sharedPrimitivePrimes,
      Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
    omega
  have hA : featureBlock (fun i : PrimeIndex F => i.val) good e A n=idealRowHom n (leftResidual c d 0) := by
    rw [featureBlock_eq_idealRowHom]
    congr 1
    have he (i : PrimeIndex F) (hi : i ∈ A) : e i=1 := by
      have hi := (Finset.mem_filter.mp hi).2
      simp only [e,quotientExponentOnPool,quotientExponent]
      omega
    simp_rw [Finset.prod_congr rfl (fun i hi => congrArg (fun k => i.val^k) (he i hi))]
    simp only [pow_one]
    dsimp only [A]
    rw [pivotLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair]
    exact support_product_of_dvd_colour F hF c hc 0 _
      (admissible_of_dvd (hF c hc 0) (leftResidual_dvd hdPair 0)).2.1 (leftResidual_dvd hdPair 0)
  have hB : featureBlock (fun i : PrimeIndex F => i.val) good e B n=star (idealRowHom n (rightResidual c d 0)) := by
    have hprod : (∏ i ∈ B,i.val)=rightResidual c d 0 := by
      dsimp only [B]
      rw [pivotRightPrimes_eq_residual F hF c d hc hd hcPair hdPair]
      exact support_product_of_dvd_colour F hF d hd 0 _
        (admissible_of_dvd (hF d hd 0) (rightResidual_dvd hcPair 0)).2.1 (rightResidual_dvd hcPair 0)
    rw [← hprod,map_prod,star_prod]
    unfold featureBlock
    apply Finset.prod_congr rfl
    intro i hi
    have hi := (Finset.mem_filter.mp hi).2
    have he : e i=5 := by simp only [e,quotientExponentOnPool,quotientExponent]; omega
    rw [he,idealRowHom_prime n i.val (good i)]
    simpa [quotientExponent] using (local_natural_quotient i.val (good i) 0 1
      (by decide) (by decide) (by decide) n).symm
  have hC : featureBlock (fun i : PrimeIndex F => i.val) good e C n=
      higherFeature F hF (table c d) (higherTuple (leftResidual c d)) (higherTuple (rightResidual c d)) n := by
    unfold higherFeature
    rw [← higherLeftPrimes_eq_residual F hF c d hc hd hcPair hdPair,
      ← higherRightPrimes_eq_residual F hF c d hc hd hcPair hdPair,
      ← sharedPrimitivePrimes_eq_table F hF c d hc hd hcPair hdPair]
    unfold featureBlock
    apply Finset.prod_congr rfl
    intro i hi
    rw [higherPrimitiveExponent_eq_actual F hF c d hc hd hcPair hdPair i hi]
  rw [primitiveRow_eq_common_feature F hF c d hcPair hdPair n,primitivePrimes_partition]
  change featureBlock (fun i : PrimeIndex F => i.val) good e (A ∪ (B ∪ C)) n=_
  unfold featureBlock
  rw [Finset.prod_union (Finset.disjoint_union_right.mpr ⟨hAB,hAC⟩),Finset.prod_union hBC]
  change featureBlock _ good e A n*(featureBlock _ good e B n*featureBlock _ good e C n)=_
  rw [hA,hB,hC]
  simp only [primitivePair,mul_assoc]

def higherFrequencyWeight (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (g : SharedTable) (v w : HigherTuple) (q b : O) (H : Ideal O) : ℂ :=
  higherFeature F hF g v w q*star (higherFeature F hF g v w (b*primaryGenerator H))

/-- The actual retained source divisor and bad-output multiplier survive in
the two own coefficients and the common higher weight. The ordinary source
is still H, never the ramified product b*H. -/
theorem actual_dual_frequency_factor (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (H : Ideal O) (hH : Supported H) (q b : O) (rL rR : EisensteinEPrimaryPhase.Coord)
    (hrL : residue (primaryGenerator (leftResidual c d 0))=rL)
    (hrR : residue (primaryGenerator (rightResidual c d 0))=rR) :
    let a := leftResidual c d
    let a' := rightResidual c d
    primitiveRow F hF c d q*star (primitiveRow F hF c d (b*primaryGenerator H)) =
      (idealRowHom q (a 0)*star (idealRowHom b (a 0)))*
      (star (idealRowHom q (a' 0))*idealRowHom b (a' 0))*
      (higherFrequencyWeight F hF (table c d) (higherTuple a) (higherTuple a') q b H*
        frozenReciprocityWeight rL rR H)*
      star (idealRowHom (primaryGenerator (a 0)) H)*idealRowHom (primaryGenerator (a' 0)) H := by
  dsimp only
  have hL := admissible_of_dvd (hF c hc 0) (leftResidual_dvd hdPair 0)
  have hR := admissible_of_dvd (hF d hd 0) (rightResidual_dvd hcPair 0)
  rw [primitiveRow_pivot_higher F hF c d hc hd hcPair hdPair q,
    primitiveRow_pivot_higher F hF c d hc hd hcPair hdPair (b*primaryGenerator H),star_mul,
    primitivePair_frozen_frequency_fixed_rays _ _ H (admissible_supported hL) (admissible_supported hR)
      hH rL rR hrL hrR b]
  unfold primitivePair higherFrequencyWeight
  ring

theorem blockRay_leftResidual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    blockRay F (idealSupport (colourIdeals F) (leftResidual c d 0))=
      residue (primaryGenerator (leftResidual c d 0)) := by
  unfold blockRay
  rw [primary_product_of_dvd_colour F hF c hc 0 _
    (admissible_of_dvd (hF c hc 0) (leftResidual_dvd hdPair 0)).2.1 (leftResidual_dvd hdPair 0)]

theorem blockRay_rightResidual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    blockRay F (idealSupport (colourIdeals F) (rightResidual c d 0))=
      residue (primaryGenerator (rightResidual c d 0)) := by
  unfold blockRay
  rw [primary_product_of_dvd_colour F hF d hd 0 _
    (admissible_of_dvd (hF d hd 0) (rightResidual_dvd hcPair 0)).2.1 (rightResidual_dvd hcPair 0)]

/-- Every literal good puncture subset belongs to the original table's
diagonal divisor set. This is the actual label used by the mass incidence
estimate, not an abstract pool cardinality. -/
theorem goodPuncture_divides_diagonal (F : Finset ColourTuple) (g : SharedTable)
    (E : Finset (PrimeIndex F)) (hE : E ⊆ diagonalPrimes F g) :
    (∏ i ∈ E,i.val) ∣ NaturalTupleIdentity.diagonalProduct g := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))
  · intro i hi
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp (hE hi)
    exact (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      ((mem_idealSupport_iff _ _ i).mp hij)).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

def goodPunctureSupport (F : Finset ColourTuple) (E : Finset (SourceMaskIndex F)) : Finset (PrimeIndex F) :=
  Finset.univ.filter (fun i => Sum.inr i ∈ E)

theorem actual_goodPuncture_divides_diagonal (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (E : Finset (SourceMaskIndex F)) (hE : E ∈ (sourceMaskSupport F c d).powerset) :
    (∏ i ∈ goodPunctureSupport F E,i.val) ∣ NaturalTupleIdentity.diagonalProduct (table c d) := by
  apply goodPuncture_divides_diagonal
  intro i hi
  have hmem := Finset.mem_powerset.mp hE ((Finset.mem_filter.mp hi).2)
  rw [sourceMaskSupport_eq_table F hF c d hc hd hcPair hdPair] at hmem
  simpa [tableSourceMask] using hmem

end
end Qrh.JointDetector.NaturalPairPackets

#print axioms Qrh.JointDetector.NaturalPairPackets.pair_character_actual

#print axioms Qrh.JointDetector.NaturalPairPackets.sourceMaskPrime_injective
#print axioms Qrh.JointDetector.NaturalPairPackets.sourceMask_factor

#print axioms Qrh.JointDetector.NaturalPairPackets.pair_character_primitive_mask

#print axioms Qrh.JointDetector.NaturalPairPackets.actual_pair_integrand

#print axioms Qrh.JointDetector.NaturalPairPackets.actual_pair_poisson
#print axioms Qrh.JointDetector.NaturalPairPackets.supported_pair_packet_eq

#print axioms Qrh.JointDetector.NaturalPairPackets.sourceMaskSupport_eq_table
#print axioms Qrh.JointDetector.NaturalPairPackets.actual_primitive_gauss_independent
#print axioms Qrh.JointDetector.NaturalPairPackets.primitiveRow_pivot_higher
#print axioms Qrh.JointDetector.NaturalPairPackets.actual_dual_frequency_factor
#print axioms Qrh.JointDetector.NaturalPairPackets.actual_goodPuncture_divides_diagonal
