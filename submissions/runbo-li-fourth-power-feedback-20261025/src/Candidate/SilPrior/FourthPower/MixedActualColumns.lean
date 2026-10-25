/- Copyright (c) 2026 Sil. Apache-2.0.
The actual ordinary pair and injective annular prime slots, packed as one
common tuple before a variable character is chosen. Ordinary punctures,
the fifth-free restriction and all natural slot zeros are retained.
-/
import Candidate.SilPrior.FourthPower.MixedFirstZero
import Candidate.SilPrior.FourthPower.MixedSecondZero
import Candidate.SilPrior.FourthPower.PrincipalMarked
import Candidate.SilPrior.FourthPower.ReferenceNaturalMarkedFactor

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedActualColumns
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelRestrictedState KernelLabelledSlots KernelRowExpansion KernelRowProfiles
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelPunctureRows
open ReferenceConvolution ReferenceCoefficients
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def extend {τ : Type*} (x y : τ) (z : ι → τ) : Option (Option ι) → τ
  | none => x
  | some none => y
  | some (some i) => z i

theorem prod_extend {τ : Type*} [CommMonoid τ] (x y : τ) (z : ι → τ) :
    (∏ j, extend x y z j) = x*y*∏ i, z i := by
  simp only [Fintype.prod_option,extend,mul_assoc]

def pack (S : Finset PrimeIdeal) (x : (ι → S) × IdealPair) : Option (Option ι) → Id :=
  extend x.2.1 x.2.2 (fun i => (x.1 i).val.val)

omit [Fintype ι] in
theorem pack_injective (S : Finset PrimeIdeal) : Function.Injective (pack (ι := ι) S) := by
  intro x y he
  apply Prod.ext
  · funext i
    exact Subtype.ext (Subtype.ext (congrFun he (some (some i))))
  · exact Prod.ext (congrFun he none) (congrFun he (some none))

theorem pack_product (S : Finset PrimeIdeal) (x : (ι → S) × IdealPair) :
    product (pack S x) = x.2.1*x.2.2*KernelWholeColumns.markedProduct (fun i => (x.1 i).val) :=
  prod_extend _ _ _

def admissible (S H : Finset PrimeIdeal) (pool : ι → Finset Id)
    (x : (ι → S) × IdealPair) : Prop :=
  Function.Injective x.1 ∧ (∀ i, (x.1 i).val.val ∈ pool i) ∧
    Restricted S (augmented S H (marked S x.1)) x.2.1 x.2.2

def entries (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (D : Finset IdealPair) :
    Finset ((ι → S) × IdealPair) := (Finset.univ ×ˢ D).filter (admissible S H pool)

def tuples (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (D : Finset IdealPair) :
    Finset (Option (Option ι) → Id) := (entries S H pool D).image (pack S)

theorem tuples_supported (S H : Finset PrimeIdeal) (pool : ι → Finset Id)
    (D : Finset IdealPair) (hD : ∀ n ∈ D, Supported n.1 ∧ Supported n.2)
    (hp : ∀ i I, I ∈ pool i → Supported I) :
    ∀ v ∈ tuples S H pool D, Supported (product v) := by
  intro v hv
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
  have hd := hD x.2 (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
  have ha := (Finset.mem_filter.mp hx).2
  apply ReferenceProductEnergy.supported_product
  intro j
  cases j with
  | none => exact hd.1
  | some j =>
    cases j with
    | none => exact hd.2
    | some i => exact hp i _ (ha.2.1 i)

theorem tuples_fifth_free (S H : Finset PrimeIdeal) (pool : ι → Finset Id)
    (D : Finset IdealPair) (hD : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0) :
    ∀ v ∈ tuples S H pool D, SexticSieve.PowerFree 5 (product v) := by
  intro v hv
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
  have hd := hD x.2 (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
  have ha := (Finset.mem_filter.mp hx).2
  rw [pack_product]
  exact KernelWholeColumns.labelled_restriction_whole S x.1 ha.1 hd.1 hd.2
    ((augmented_restriction S H (marked S x.1) x.2.1 x.2.2).mp ha.2.2).1

def ordinary (W : ℝ → ℂ) (X : ℝ) (I : Id) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹*W ((Ideal.absNorm I : ℝ)/X)

def slotCoefficient (β : ι → Id → ℂ) (P : ι → ℝ) (i : ι) (I : Id) : ℂ :=
  (Real.sqrt (P i) : ℂ)⁻¹*β i I

def vector (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (v : Option (Option ι) → Id) : ℂ :=
  ∏ j, extend (ordinary W₁ X₁) (ordinary W₂ X₂) (slotCoefficient β P) j (v j)

theorem vector_pack (S : Finset PrimeIdeal) (x : (ι → S) × IdealPair)
    (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    vector β P W₁ W₂ X₁ X₂ (pack S x) =
      ordinary W₁ X₁ x.2.1*ordinary W₂ X₂ x.2.2*
        ∏ i, slotCoefficient β P i (x.1 i).val.val := by
  simp only [vector,Fintype.prod_option,pack,extend,mul_assoc]

theorem ordinary_bound (W : ℝ → ℂ) (X b B : ℝ) (hX : 0 < X) (hb : 0 ≤ b)
    (hB : 0 ≤ B) (I : Id) (hI : I ≠ 0) (hcap : (Ideal.absNorm I : ℝ) ≤ b*X)
    (hW : ‖W ((Ideal.absNorm I : ℝ)/X)‖ ≤ B) :
    ‖ordinary W X I‖ ≤ (Real.sqrt b*B)/Real.sqrt (Ideal.absNorm I : ℝ) := by
  simpa only [ordinary,phaseCoefficient,norm_mul,FourierBridge.logPhase_norm,mul_one]
    using phase_coefficient_bound W X 0 b B hX hb hB I hI hcap hW

def lengthCap (b X₁ X₂ : ℝ) (P : ι → ℝ) : ℝ := (b*X₁)*(b*X₂)*∏ i, 2*P i
def amplitude (b B₁ B₂ : ℝ) (M : ι → ℝ) : ℝ :=
  (Real.sqrt b*B₁)*(Real.sqrt b*B₂)*∏ i, Real.sqrt 2*M i

theorem actual_bounds (S H : Finset PrimeIdeal) (pool : ι → Finset Id)
    (D : Finset IdealPair) (β : ι → Id → ℂ) (P M : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ b B₁ B₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hb : 0 ≤ b) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hD : ∀ n ∈ D, Supported n.1 ∧ Supported n.2 ∧
      (Ideal.absNorm n.1 : ℝ) ≤ b*X₁ ∧ (Ideal.absNorm n.2 : ℝ) ≤ b*X₂)
    (hP : ∀ i, 0 < P i) (hM : ∀ i, 0 ≤ M i)
    (hp : ∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i)
    (hβ : ∀ i I, I ∈ pool i → ‖β i I‖ ≤ M i)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂) :
    ∀ v ∈ tuples S H pool D,
      Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ lengthCap b X₁ X₂ P ∧
      ‖vector β P W₁ W₂ X₁ X₂ v‖ ≤ amplitude b B₁ B₂ M/Real.sqrt (Ideal.absNorm (product v) : ℝ) := by
  intro v hv
  have hs := tuples_supported S H pool D (fun n hn => ⟨(hD n hn).1,(hD n hn).2.1⟩)
    (fun i I hi => (hp i I hi).1) v hv
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
  have hd := hD x.2 (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
  have ha := (Finset.mem_filter.mp hx).2
  refine ⟨hs,?_,?_⟩
  · have hc := product_length_bound (pack S x) (extend (b*X₁) (b*X₂) (fun i => 2*P i)) (by
      intro j
      cases j with
      | none => exact hd.2.2.1
      | some j =>
        cases j with
        | none => exact hd.2.2.2
        | some i => exact (hp i _ (ha.2.1 i)).2)
    simpa only [prod_extend,lengthCap] using hc
  · have hc := product_coefficient_bound
      (extend (ordinary W₁ X₁) (ordinary W₂ X₂) (slotCoefficient β P))
      (extend (Real.sqrt b*B₁) (Real.sqrt b*B₂) (fun i => Real.sqrt 2*M i)) (by
        intro j
        cases j with
        | none => exact mul_nonneg (Real.sqrt_nonneg _) hB₁
        | some j =>
          cases j with
          | none => exact mul_nonneg (Real.sqrt_nonneg _) hB₂
          | some i => exact mul_nonneg (Real.sqrt_nonneg _) (hM i)) (pack S x) (by
        intro j
        cases j with
        | none => exact ordinary_bound W₁ X₁ b B₁ hX₁ hb hB₁ _ hd.1.1 hd.2.2.1 (hW₁ _)
        | some j =>
          cases j with
          | none => exact ordinary_bound W₂ X₂ b B₂ hX₂ hb hB₂ _ hd.2.1.1 hd.2.2.2 (hW₂ _)
          | some i =>
            exact ordinary_bound (fun _ => β i (x.1 i).val.val) (P i) 2 (M i) (hP i)
              (by norm_num) (hM i) _ (hp i _ (ha.2.1 i)).1.1
              (hp i _ (ha.2.1 i)).2 (hβ i _ (ha.2.1 i)))
    simpa only [prod_extend,amplitude,vector] using hc

theorem ordinary_pair (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 ≤ X₁) (n : IdealPair) :
    ordinary W₁ X₁ n.1*ordinary W₂ X₂ n.2 =
      (Real.sqrt (X₁*X₂) : ℂ)⁻¹*pairProfile W₁ W₂ X₁ X₂ n := by
  rw [Real.sqrt_mul hX₁,Complex.ofReal_mul,mul_inv_rev]
  unfold ordinary pairProfile
  ring

theorem natural_product (χ : Character) (S : Finset PrimeIdeal) (pool : ι → Finset Id)
    (β : ι → Id → ℂ) (P : ι → ℝ) (slot : ι → S)
    (hp : ∀ i, (slot i).val.val ∈ pool i) :
    (∏ i, naturalCoefficients χ S pool β P i (slot i)) =
      (∏ i, slotCoefficient β P i (slot i).val.val)*
        idealCoeff χ (KernelWholeColumns.markedProduct (fun i => (slot i).val)) := by
  calc
    _ = ∏ i, slotCoefficient β P i (slot i).val.val*idealCoeff χ (slot i).val.val := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [naturalCoefficients,slotTerm,hp i,ite_true,slotCoefficient]
      ring
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [KernelWholeColumns.markedProduct,map_prod]

theorem packed_term (χ : Character) (S : Finset PrimeIdeal) (pool : ι → Finset Id)
    (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 ≤ X₁) (slot : ι → S) (n : IdealPair)
    (hp : ∀ i, (slot i).val.val ∈ pool i) :
    vector β P W₁ W₂ X₁ X₂ (pack S (slot,n))*idealCoeff χ (product (pack S (slot,n))) =
      ((Real.sqrt (X₁*X₂) : ℂ)⁻¹*(pairCharacter χ n*pairProfile W₁ W₂ X₁ X₂ n))*
        ∏ i, naturalCoefficients χ S pool β P i (slot i) := by
  rw [vector_pack,pack_product,map_mul,natural_product χ S pool β P slot hp,
    ordinary_pair W₁ W₂ X₁ X₂ hX₁]
  unfold pairCharacter
  ring

/-- Exact identity before taking any norm, for every character with the
same tuple vector. It includes the original annular square roots. -/
theorem actual_row_identity (χ : Character) (S H : Finset PrimeIdeal)
    (pool : ι → Finset Id) (D : Finset IdealPair) (β : ι → Id → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 ≤ X₁) :
    (∑ v ∈ tuples S H pool D, vector β P W₁ W₂ X₁ X₂ v*idealCoeff χ (product v)) =
      weightedSum (naturalCoefficients χ S pool β P)
        (fun slot => normalizedRow χ D (restrictedValue S (augmented S H (marked S slot)))
          W₁ W₂ X₁ X₂) := by
  rw [tuples,Finset.sum_image (fun x _ y _ he => pack_injective S he),
    entries,Finset.sum_filter,Finset.sum_product]
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro slot _
  by_cases hi : Function.Injective slot
  · by_cases hp : ∀ i, (slot i).val.val ∈ pool i
    · simp only [admissible,hi,hp,implies_true,true_and,ite_true]
      rw [normalizedRow,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hr : Restricted S (augmented S H (marked S slot)) n.1 n.2
      · rw [ite_eq_left hr,restrictedValue,ite_eq_left hr,one_mul]
        exact packed_term χ S pool β P W₁ W₂ X₁ X₂ hX₁ slot n hp
      · simp only [hr,ite_false,restrictedValue,zero_mul,mul_zero]
    · have hz : (∏ i, naturalCoefficients χ S pool β P i (slot i))=0 := by
        obtain ⟨i,hi⟩ := not_forall.mp hp
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [naturalCoefficients,slotTerm,hi])
      simp only [admissible,hi,hp,true_and,false_and,ite_false,ite_true,
        Finset.sum_const_zero,hz,mul_zero]
  · simp only [admissible,hi,false_and,ite_false,Finset.sum_const_zero]

/-- The coefficients are constructed independently of the physical row. -/
theorem grouped_row_identity (χ : Character) (S H : Finset PrimeIdeal)
    (pool : ι → Finset Id) (D : Finset IdealPair) (β : ι → Id → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 ≤ X₁) :
    (∑ I ∈ columns (tuples S H pool D),
      coefficient (tuples S H pool D) (vector β P W₁ W₂ X₁ X₂) I*idealCoeff χ I) =
      weightedSum (naturalCoefficients χ S pool β P)
        (fun slot => normalizedRow χ D (restrictedValue S (augmented S H (marked S slot)))
          W₁ W₂ X₁ X₂) := by
  rw [← row_identity]
  exact actual_row_identity χ S H pool D β P W₁ W₂ X₁ X₂ hX₁

end
end Candidate.SilPrior.FourthPower.MixedActualColumns
