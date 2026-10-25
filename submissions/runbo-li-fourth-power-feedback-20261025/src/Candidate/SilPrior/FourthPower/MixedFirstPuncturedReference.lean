/- Copyright (c) 2026 Sil. Apache-2.0.
Actual finite seed-one rectangles, with the whole puncture moved into
ordinary holes and canonical marked zeros. The original character is
unchanged.
-/
import Candidate.SilPrior.FourthPower.MixedFirstSeededSource
import Candidate.SilPrior.FourthPower.MixedFirstReferenceChoice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstPuncturedReference
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRectangle CenteredMomentRectangle CenteredMomentUncenteredTerminal
open CenteredMomentLattice
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowProfiles
open KernelRowExpansion KernelRowPools KernelLabelledSlots KernelPunctureRows
open MixedCommonRestriction MixedCommonCoefficient MixedTupleRows MixedCompletedRows
open MixedCenteredEnergy MixedLiveNormalization MixedCanonicalSource
open MixedFirstSeededSource MixedFirstReferenceChoice ReferencePrimeEnclosure
open ReferenceFactors ReferenceHeckeProducts CenteredMomentScaleSupremum
open CenteredMomentTwist MixedPrincipalPair MixedPrincipalHeights
open MixedPrincipalAllocations MixedPrincipalWindow MixedOriginalSecondZero
open MixedFirstRebase MixedLiteralAllocation MixedRestrictedDictionary
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι]

def tupleSum (χ : Character) (S H : Finset PrimeIdeal) (R : Id)
    (pool : ι → Finset Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (A B : Finset Id) : ℂ :=
  ∑ v ∈ Fintype.piFinset (pools pool A B), tupleWeight (punctureProduct S H) v *
    uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1 v *
      idealCoeff χ (finiteTupleProduct v)

/-- The literal uncentered rectangle at its actual scales. -/
def rectangleRow (χ : Character) (S H : Finset PrimeIdeal) (R : Id)
    (pool : ι → Finset Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  normalization (X₁*X₂) P * tupleSum χ S H R pool ν Wslot P W₁ W₂ X₁ X₂
    (idealBall (b*X₁)) (idealBall (b*X₂))

private theorem product_plain (v : Tuple ι) :
    finiteTupleProduct v = (v (Sum.inr 0)*v (Sum.inr 1)) * ∏i,v (Sum.inl i) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two]
  ring

/-- The whole ordinary-pair support is supplied by the actual supported
column and the two enclosure bounds, rather than assumed on all tuples. -/
theorem rectangle_pair_support (χ : Character) (S : Finset PrimeIdeal)
    (pool : ι → Finset Id) (b X₁ X₂ : ℝ)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I, Supported I →
      ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues S)
    (v : Tuple ι)
    (hv : v ∈ Fintype.piFinset (pools pool (idealBall (b*X₁)) (idealBall (b*X₂))))
    (hχ : idealCoeff χ (finiteTupleProduct v) ≠ 0) :
    v (Sum.inr 0)*v (Sum.inr 1) ≠ 0 ∧
      primeSupport (v (Sum.inr 0)*v (Sum.inr 1)) ⊆ primeValues S := by
  have hs : Supported (finiteTupleProduct v) := by
    by_contra hn
    exact hχ (hoff _ hn)
  rw [product_plain] at hs
  have hp := (supported_mul_iff _ _).mp hs |>.1
  have hparts := (supported_mul_iff _ _).mp hp
  have h₁ : v (Sum.inr 0) ∈ idealBall (b*X₁) := Fintype.mem_piFinset.mp hv (Sum.inr 0)
  have h₂ : v (Sum.inr 1) ∈ idealBall (b*X₂) := Fintype.mem_piFinset.mp hv (Sum.inr 1)
  refine ⟨hp.1,?_⟩
  intro Q hQ
  have hprime : Prime Q := primeSupport_prime hQ
  have hdiv : Q ∣ v (Sum.inr 0)*v (Sum.inr 1) :=
    (CenteredMomentNaturalPrimitive.prime_mem_support_iff _ Q hp.1 hprime).mp hQ
  rcases hprime.dvd_mul.mp hdiv with hd | hd
  · exact henclose _ hparts.1 (Or.inl ((mem_idealBall _ _).mp h₁).2)
      ((CenteredMomentNaturalPrimitive.prime_mem_support_iff _ Q hparts.1.1 hprime).mpr hd)
  · exact henclose _ hparts.2 (Or.inr ((mem_idealBall _ _).mp h₂).2)
      ((CenteredMomentNaturalPrimitive.prime_mem_support_iff _ Q hparts.2.1 hprime).mpr hd)

theorem uncentered_punctured_tuple (S H : Finset PrimeIdeal) (R : Id) (hR : R ≠ 0)
    (ν : ι → Character) (R₀ : ι → Finset Id) (t : ℝ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (hW₀ : W₁ 0 = 0) (X₁ X₂ : ℝ) (v : Tuple ι)
    (hp : ∀ i, Prime (v (Sum.inl i)))
    (hv : v (Sum.inr 0)*v (Sum.inr 1) ≠ 0)
    (hS : primeSupport (v (Sum.inr 0)*v (Sum.inr 1)) ⊆ primeValues S) :
    tupleWeight (punctureProduct S H) v *
      uncenteredProfileCoefficient R (slotCoefficient ν R₀ t) Wslot P W₁ W₂
        X₁ X₂ 1 1 1 v =
      tupleWeight (punctureProduct S (enlargedHoles S H R)) v *
        uncenteredProfileCoefficient 1
          (slotCoefficient ν (fun i => R₀ i ∪ primeSupport R) t)
          Wslot P W₁ W₂ X₁ X₂ 1 1 1 v := by
  have he := canonical_punctured_tuple S H R hR ν R₀ t Wslot P W₁ W₂
    X₁ X₂ 0 0 1 1 1 v hp hv hS
  simpa only [profileCoefficient,uncenteredProfileCoefficient,idealRectangle,
    div_zero,hW₀,zero_mul,sub_zero] using he

theorem rectangle_mask_sum (χ : Character) (S H : Finset PrimeIdeal) (R : Id) (hR : R ≠ 0)
    (pool : ι → Finset Id) (hp : ∀ i I, I ∈ pool i → Prime I)
    (ν : ι → Character) (R₀ : ι → Finset Id) (t : ℝ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (hW₀ : W₁ 0 = 0) (b X₁ X₂ : ℝ)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I, Supported I →
      ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) → primeSupport I ⊆ primeValues S) :
    tupleSum χ S H R pool (slotCoefficient ν R₀ t) Wslot P W₁ W₂ X₁ X₂
        (idealBall (b*X₁)) (idealBall (b*X₂)) =
      tupleSum χ S (enlargedHoles S H R) 1 pool
        (slotCoefficient ν (fun i => R₀ i ∪ primeSupport R) t) Wslot P W₁ W₂ X₁ X₂
        (idealBall (b*X₁)) (idealBall (b*X₂)) := by
  unfold tupleSum
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hχ : idealCoeff χ (finiteTupleProduct v) = 0
  · simp only [hχ,mul_zero]
  · obtain ⟨hn,hs⟩ := rectangle_pair_support χ S pool b X₁ X₂ hoff henclose v hv hχ
    rw [uncentered_punctured_tuple S H R hR ν R₀ t Wslot P W₁ W₂ hW₀ X₁ X₂ v
      (fun i => hp i _ (Fintype.mem_piFinset.mp hv (Sum.inl i))) hn hs]

private theorem uncentered_centralization (pool : ι → Finset Id)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (v : Tuple ι)
    (hv : ∀ i, v (Sum.inl i) ∈ pool i) :
    normalization (X₁*X₂) P *
      uncenteredProfileCoefficient 1 ν Wslot P W₁ W₂ X₁ X₂ 1 1 1 v =
      rectangleCoefficient pool (fun i I => ν i I*Wslot i (I.absNorm/P i)) P W₁ W₂ X₁ X₂ v := by
  have he : (∏ i,slotWeight pool (fun j I => ν j I*Wslot j (I.absNorm/P j)) P i (v (Sum.inl i))) =
      (∏ i,(Real.sqrt (P i) : ℂ)⁻¹) *
        ∏ i,ν i (v (Sum.inl i))*Wslot i ((v (Sum.inl i)).absNorm/P i) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [slotWeight,hv i,ite_true]
  unfold normalization uncenteredProfileCoefficient rectangleCoefficient pairProfile
  rw [he]
  simp only [isCoprime_one_right,one_dvd,ite_true,one_mul,mul_one]
  ring

private theorem rectangle_pool_completion (χ : Character) (S H : Finset PrimeIdeal)
    (pool : ι → Finset Id) (hpool : ∀ i, pool i ⊆ primeValues S)
    (A B : Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    (∑ v ∈ Fintype.piFinset (pools pool A B),tupleWeight (punctureProduct S H) v *
      rectangleCoefficient pool β P W₁ W₂ X₁ X₂ v * idealCoeff χ (finiteTupleProduct v)) =
      ∑ v ∈ Fintype.piFinset (pools (fun _ : ι => primeValues S) A B),
        tupleWeight (punctureProduct S H) v * rectangleCoefficient pool β P W₁ W₂ X₁ X₂ v *
          idealCoeff χ (finiteTupleProduct v) := by
  have hsub : Fintype.piFinset (pools pool A B) ⊆
      Fintype.piFinset (pools (fun _ : ι => primeValues S) A B) := by
    intro v hv
    apply Fintype.mem_piFinset.mpr
    intro j
    cases j with
    | inl i => exact hpool i (Fintype.mem_piFinset.mp hv (Sum.inl i))
    | inr i => exact Fintype.mem_piFinset.mp hv (Sum.inr i)
  apply Finset.sum_subset hsub
  intro v hv hn
  by_contra hne
  have hc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2
  have hp : (∏i,slotWeight pool β P i (v (Sum.inl i))) ≠ 0 :=
    (mul_ne_zero_iff.mp hc).2
  apply hn
  apply Fintype.mem_piFinset.mpr
  intro j
  cases j with
  | inl i =>
      by_contra hi
      change v (Sum.inl i) ∉ pool i at hi
      exact (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i))
        (by simp only [slotWeight,hi,ite_false])
  | inr i => exact Fintype.mem_piFinset.mp hv (Sum.inr i)

/-- Complete exact source-to-reference dictionary. Missing supported or
marked terms are justified by their zeros before taking squared norms. -/
theorem rectangle_row_eq (χ : Character) (S H : Finset PrimeIdeal) (R : Id) (hR : R ≠ 0)
    (pool : ι → Finset Id) (hpool : ∀ i, pool i ⊆ primeValues S)
    (hp : ∀ i I, I ∈ pool i → Prime I)
    (ν : ι → Character) (R₀ : ι → Finset Id) (t : ℝ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (hW₀ : W₁ 0 = 0) (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Iic b) (hs₂ : Function.support W₂ ⊆ Iic b)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I, Supported I →
      ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) → primeSupport I ⊆ primeValues S) :
    rectangleRow χ S H R pool (slotCoefficient ν R₀ t) Wslot P W₁ W₂ b X₁ X₂ =
      puncturedRow χ S (enlargedHoles S H R) pool
        (fun i I => slotCoefficient ν (fun j => R₀ j ∪ primeSupport R) t i I *
          Wslot i (I.absNorm/P i)) P W₁ W₂ b X₁ X₂ := by
  unfold rectangleRow
  rw [rectangle_mask_sum χ S H R hR pool hp ν R₀ t Wslot P W₁ W₂ hW₀ b X₁ X₂ hoff henclose]
  unfold tupleSum
  rw [Finset.mul_sum]
  have hterm (v : Tuple ι)
      (hv : v ∈ Fintype.piFinset (pools pool (idealBall (b*X₁)) (idealBall (b*X₂)))) :
      normalization (X₁*X₂) P * (tupleWeight (punctureProduct S (enlargedHoles S H R)) v *
        uncenteredProfileCoefficient 1 (slotCoefficient ν (fun j => R₀ j ∪ primeSupport R) t)
          Wslot P W₁ W₂ X₁ X₂ 1 1 1 v * idealCoeff χ (finiteTupleProduct v)) =
        tupleWeight (punctureProduct S (enlargedHoles S H R)) v *
          rectangleCoefficient pool (fun i I => slotCoefficient ν
            (fun j => R₀ j ∪ primeSupport R) t i I*Wslot i (I.absNorm/P i)) P W₁ W₂ X₁ X₂ v *
          idealCoeff χ (finiteTupleProduct v) := by
    have he := uncentered_centralization pool
      (slotCoefficient ν (fun j => R₀ j ∪ primeSupport R) t) Wslot P W₁ W₂ X₁ X₂ v
      (fun i => Fintype.mem_piFinset.mp hv (Sum.inl i))
    calc
      _ = tupleWeight (punctureProduct S (enlargedHoles S H R)) v *
          (normalization (X₁*X₂) P * uncenteredProfileCoefficient 1
            (slotCoefficient ν (fun j => R₀ j ∪ primeSupport R) t)
            Wslot P W₁ W₂ X₁ X₂ 1 1 1 v) * idealCoeff χ (finiteTupleProduct v) := by ring
      _ = _ := by rw [he]
  rw [Finset.sum_congr rfl hterm]
  rw [rectangle_pool_completion χ S (enlargedHoles S H R) pool hpool,
    normalized_character_sum]
  unfold puncturedRow
  apply congrArg (weightedSum _)
  funext slot
  exact normalized_row_complete χ S (rectangle b X₁ X₂) _ W₁ W₂ b X₁ X₂
    hX₁ hX₂ hs₁ hs₂ (fun _ h => h) hoff henclose

/-- Ordinary zero extension on the actual union support. Both coordinates
remain present; only terms with a zero ordinary profile are removed. -/
theorem tuple_sum_complete (χ : Character) (S H : Finset PrimeIdeal) (R : Id)
    (pool : ι → Finset Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (A B : Finset Id)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Iic b) (hs₂ : Function.support W₂ ⊆ Iic b)
    (hA : idealBall (b*X₁) ⊆ A) (hB : idealBall (b*X₂) ⊆ B)
    (hAz : ∀ I ∈ A, I ≠ 0) (hBz : ∀ I ∈ B, I ≠ 0) :
    tupleSum χ S H R pool ν Wslot P W₁ W₂ X₁ X₂ A B =
      tupleSum χ S H R pool ν Wslot P W₁ W₂ X₁ X₂
        (idealBall (b*X₁)) (idealBall (b*X₂)) := by
  have hsub : Fintype.piFinset (pools pool (idealBall (b*X₁)) (idealBall (b*X₂))) ⊆
      Fintype.piFinset (pools pool A B) := by
    intro v hv
    apply Fintype.mem_piFinset.mpr
    intro j
    cases j with
    | inl i => exact Fintype.mem_piFinset.mp hv (Sum.inl i)
    | inr j =>
        fin_cases j
        · exact hA (Fintype.mem_piFinset.mp hv (Sum.inr 0))
        · exact hB (Fintype.mem_piFinset.mp hv (Sum.inr 1))
  unfold tupleSum
  symm
  apply Finset.sum_subset hsub
  intro v hv hn
  by_contra hne
  have hc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2
  have hw : W₁ ((v (Sum.inr 0)).absNorm/X₁)*
      W₂ ((v (Sum.inr 1)).absNorm/X₂) ≠ 0 := by
    unfold uncenteredProfileCoefficient at hc
    simp only [one_mul] at hc
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc).1).2
  have hw₁ := (mul_ne_zero_iff.mp hw).1
  have hw₂ := (mul_ne_zero_iff.mp hw).2
  apply hn
  apply Fintype.mem_piFinset.mpr
  intro j
  cases j with
  | inl i => exact Fintype.mem_piFinset.mp hv (Sum.inl i)
  | inr j =>
      fin_cases j
      · exact (mem_idealBall _ _).mpr
          ⟨hAz _ (Fintype.mem_piFinset.mp hv (Sum.inr 0)),
            (div_le_iff₀ hX₁).mp (hs₁ hw₁)⟩
      · exact (mem_idealBall _ _).mpr
          ⟨hBz _ (Fintype.mem_piFinset.mp hv (Sum.inr 1)),
            (div_le_iff₀ hX₂).mp (hs₂ hw₂)⟩

private theorem unit_tuple_pools {a b : ℝ} (s : Source ι a b) (hd : s.d = (1,1)) :
    tuplePools s = pools s.pool (plainSupportPool b s.X₁ s.Y₁)
      (plainSupportPool b s.X₂ s.Y₂) := by
  unfold MixedPrincipalAllocations.tuplePools sourcePools
  simp only [hd,Prod.fst,Prod.snd,residual_plain_pool,map_one,Nat.cast_one,div_one]

/-- Actual source centering after the ordinary prefixes have been rebased.
The two rectangles have their literal X and Y scales. Thus using a new Y
requires the explicit reference Source constructor; enclosure alone does
not change Y. The entire original character and both heights are retained. -/
theorem weighted_row_centering {a b : ℝ} (s : Source ι a b) (ha : 0 < a)
    (hd : s.d = (1,1)) (χ : Character) :
    rectangleRow χ s.S s.H s.R s.pool s.ν s.Wslot s.P
      (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
      (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂) b s.X₁ s.X₂ =
      weightedRow s ha 1 (idealCoeff χ) +
        rectangleRow χ s.S s.H s.R s.pool s.ν s.Wslot s.P
          (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
          (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂) b s.Y₁ s.Y₂ := by
  let V₁ : ℝ → ℂ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
  let V₂ : ℝ → ℂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
  have hV₁ : Function.support V₁ ⊆ Iic b :=
    fun x hx => (s.hs₁ (normPowerProfile_support _ _ _ _ _ _ _ hx)).2
  have hV₂ : Function.support V₂ ⊆ Iic b :=
    fun x hx => (s.hs₂ (normPowerProfile_support _ _ _ _ _ _ _ hx)).2
  have hpz (X Y : ℝ) : ∀ I ∈ plainSupportPool b X Y, I ≠ 0 := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI | hI
    · exact ((mem_idealBall _ _).mp hI).1
    · exact ((mem_idealBall _ _).mp hI).1
  have hx := tuple_sum_complete χ s.S s.H s.R s.pool s.ν s.Wslot s.P V₁ V₂
    b s.X₁ s.X₂ (plainSupportPool b s.X₁ s.Y₁) (plainSupportPool b s.X₂ s.Y₂)
    (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂) hV₁ hV₂
    (Finset.subset_union_left) (Finset.subset_union_left) (hpz _ _) (hpz _ _)
  have hy := tuple_sum_complete χ s.S s.H s.R s.pool s.ν s.Wslot s.P V₁ V₂
    b s.Y₁ s.Y₂ (plainSupportPool b s.X₁ s.Y₁) (plainSupportPool b s.X₂ s.Y₂)
    (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂) hV₁ hV₂
    (Finset.subset_union_right) (Finset.subset_union_right) (hpz _ _) (hpz _ _)
  have hrow := raw_row_tuples s ha 1 (idealCoeff χ).toMonoidHom
  have htuples := unit_tuple_pools s hd
  have hnorm : normalization (s.Y₁*s.Y₂) s.P = normalization (s.X₁*s.X₂) s.P := by
    rw [s.hpY,s.hpX]
  change normalization (s.X₁*s.X₂) s.P *
      tupleSum χ s.S s.H s.R s.pool s.ν s.Wslot s.P V₁ V₂ s.X₁ s.X₂
        (idealBall (b*s.X₁)) (idealBall (b*s.X₂)) = _
  rw [← hx]
  change _ = normalization (s.X₁*s.X₂) s.P * rawRow s ha 1 (idealCoeff χ).toMonoidHom +
    normalization (s.Y₁*s.Y₂) s.P * tupleSum χ s.S s.H s.R s.pool s.ν s.Wslot s.P
      V₁ V₂ s.Y₁ s.Y₂ (idealBall (b*s.Y₁)) (idealBall (b*s.Y₂))
  rw [hnorm,← hy,hrow]
  simp only [originalTuple,hd,Prod.fst,Prod.snd,htuples]
  rw [← mul_add]
  apply congrArg (normalization (s.X₁*s.X₂) s.P * ·)
  exact finite_centering
    (Fintype.piFinset (pools s.pool (plainSupportPool b s.X₁ s.Y₁)
      (plainSupportPool b s.X₂ s.Y₂))) (punctureProduct s.S s.H) s.R s.ν s.Wslot s.P
    V₁ V₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 1 (idealCoeff χ)

/-- The uncentered comparison rectangle vanishes at its actual subunit
first length. No claim that this length is at least one is required. -/
theorem comparison_rectangle_zero (χ : Character) (S H : Finset PrimeIdeal) (R : Id)
    (pool : ι → Finset Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (a b Y₂ : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Icc a b) :
    rectangleRow χ S H R pool ν Wslot P W₁ W₂ b (comparisonScale b) Y₂ = 0 := by
  unfold rectangleRow tupleSum
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro v hv
  simp only [uncenteredProfileCoefficient,
    comparison_first_zero W₁ a b ha hs₁ 1 (v (Sum.inr 0)) one_ne_zero,
    zero_mul,mul_zero]

/-- The genuine Source built with the comparison reference carries
exactly the uncentered actual row, including both ordinary heights. -/
theorem weighted_row_uncentered {a b : ℝ} (s : Source ι a b) (ha : 0 < a)
    (hd : s.d = (1,1)) (hY : s.Y₁ = comparisonScale b) (χ : Character) :
    weightedRow s ha 1 (idealCoeff χ) =
      rectangleRow χ s.S s.H s.R s.pool s.ν s.Wslot s.P
        (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
        (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂) b s.X₁ s.X₂ := by
  have h := weighted_row_centering s ha hd χ
  rw [hY,comparison_rectangle_zero χ s.S s.H s.R s.pool s.ν s.Wslot s.P
    _ _ a b s.Y₂ ha
    ((normPowerProfile_support _ _ _ _ _ _ _).trans s.hs₁),add_zero] at h
  exact h.symm

/-- The short/reference estimate now applies to the original finite
rectangle. Union holes are supplied internally, and the conductor and
nonprincipal hypothesis refer to the SAME original characters. -/
theorem short_actual_reference (ε L K a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
    ∃ n : ℕ, ∀ Wlong : ℝ → ℂ,
      Function.support Wlong ⊆ Icc a b → ContDiff ℝ ∞ Wlong →
      ∃ C : ℝ, 0 < C ∧ ∀ Z R P s d l δ : ℝ,
      1 ≤ Z → 0 ≤ R → 0 ≤ s → 0 ≤ d → 0 ≤ l → 0 ≤ δ → P+2*s+4*d < R →
      R+(l+(R+d)/2+s+2*δ) ≤ L →
      l+(R+d)/2+s+2*δ ≤ (4/5)*R → R+d+2*l-P+s+2*δ ≤ R/2 →
      (b+4)*b*(2:ℝ)^Fintype.card ι ≤ Z^δ → xi/2 ≤ δ →
      ∀ (η : Character) (m D₀ : O) (rows : Finset O) (χ : rows → Character),
      (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D₀ I*idealRowHom x.val I) →
      (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ i, (χ i).residue ≠ 1) →
      ∀ (U X₁ X₂ Height t₁ t₂ : ℝ) (Wshort : ℝ → ℂ) (B : ℝ),
      1 ≤ U → U ≤ Z^K → U ≤ Z^(R+d) → 0 < X₁ → 0 < X₂ → X₁*X₂ = Z^P → X₁ ≤ Z^l →
      0 ≤ Height → ‖t₂‖ ≤ Height → (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ U) →
      0 ≤ B → Function.support Wshort ⊆ Icc a b → ContDiff ℝ ∞ Wshort →
      (∀ (j : Fin 2) (x : ℝ), ‖scaleTest Wshort j x‖ ≤ B) →
      ∀ (S H : Finset PrimeIdeal) (Rmask F : Id), Rmask ≠ 0 → F ≠ 0 →
      ((F*Rmask).absNorm : ℝ) ≤ Z^K → (∀ Q ∈ H, Q.val ∣ F) →
      (∀ Q ∈ S, Supported Q.val ∧ (Q.val.absNorm : ℝ) ≤ Z^K) →
      (∀ I, Supported I → ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues S) →
      ∀ (pool : ι → Finset Id) (ν : ι → Character) (R₀ : ι → Finset Id)
        (t : ℝ) (Wslot : ι → ℝ → ℂ) (scales : ι → ℝ),
      (∀ i, pool i ⊆ primeValues S) → (∀ i I, I ∈ pool i → Prime I) →
      (∀ i, 0 < scales i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (I.absNorm : ℝ) ≤ 2*scales i) →
      (∀ i I, I ∈ pool i → ‖slotCoefficient ν R₀ t i I*Wslot i (I.absNorm/scales i)‖ ≤ Bf) →
      (∀ i Q, Q ∈ H → Q.val ∈ R₀ i) →
      (∏ i, 2*scales i) ≤ Z^L → b*X₁*(∏ i, 2*scales i) ≤ Z^L →
      (∏ i, scales i) ≤ Z^s →
      (∑ i : rows, ‖rectangleRow (χ i) S H Rmask pool (slotCoefficient ν R₀ t)
        Wslot scales (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) b X₁ X₂‖^2) ≤
        C*(1+Height)^(2*n)*Z^(R+ε)*B^2 := by
  obtain ⟨n,hn⟩ := short_punctured_reference (ι := ι) ε L K a b xi Bf
    hε hL hK ha hb hxi hBf
  refine ⟨n,?_⟩
  intro Wlong hlong hsmooth
  obtain ⟨C,hC,hbound⟩ := hn Wlong hlong hsmooth
  refine ⟨C,hC,?_⟩
  intro Z R P s d l δ hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m D₀ rows χ hon hoff hrows hnonprincipal
    U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hUsharp hX₁ hX₂ hprod hshort
    hHeight ht₂ hmod hB hWs hWsm htest S H Rmask F hRmask hF hFcap hH hS henclose
    pool ν R₀ t Wslot scales hpool hprime hP hp hβ hHR hVcap hvolume hVsharp
  have hnewH : ∀ Q ∈ enlargedHoles S H Rmask, Q.val ∣ F*Rmask := by
    intro Q hQ
    rcases (Finset.mem_filter.mp hQ).2 with hQ | hQ
    · exact (hH Q hQ).trans (dvd_mul_right F Rmask)
    · exact hQ.trans (dvd_mul_left Rmask F)
  have hnewHR : ∀ i Q, Q ∈ enlargedHoles S H Rmask → Q.val ∈ R₀ i ∪ primeSupport Rmask := by
    intro i Q hQ
    rcases (Finset.mem_filter.mp hQ).2 with hQ | hQ
    · exact Finset.mem_union_left _ (hHR i Q hQ)
    · exact Finset.mem_union_right _
        ((CenteredMomentNaturalPrimitive.prime_mem_support_iff Rmask Q.val hRmask Q.property).mpr hQ)
  have hnewβ : ∀ i I, I ∈ pool i →
      ‖slotCoefficient ν (fun j => R₀ j ∪ primeSupport Rmask) t i I *
        Wslot i (I.absNorm/scales i)‖ ≤ Bf := by
    intro i I hI
    have he := punctured_canonical_slot Rmask hRmask ν R₀ t i (⟨I,hprime i I hI⟩ : PrimeIdeal)
    rw [← he]
    unfold puncturedSlot
    split_ifs
    · exact hβ i I hI
    · simp only [zero_mul,norm_zero]
      exact zero_le_one.trans hBf
  have hh := hbound Z R P s d l δ hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m D₀ rows χ hon hoff hrows hnonprincipal
    U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hUsharp hX₁ hX₂ hprod hshort
    hHeight ht₂ hmod hB hWs hWsm htest S (enlargedHoles S H Rmask) (F*Rmask)
    (mul_ne_zero hF hRmask) hFcap hnewH hS henclose
    pool ν (fun i => R₀ i ∪ primeSupport Rmask) t Wslot scales hP hp hnewβ hnewHR
    hVcap hvolume hVsharp
  have hw₀ : Wshort 0 = 0 := by
    by_contra hn
    have hz := (hWs hn).1
    linarith
  have hphase₀ : phaseProfile Wshort t₁ 0 = 0 := by
    simp only [phaseProfile,hw₀,zero_mul]
  have hphase₁ : Function.support (phaseProfile Wshort t₁) ⊆ Iic b :=
    fun x hx => (hWs (phaseProfile_support Wshort t₁ hx)).2
  have hphase₂ : Function.support (phaseProfile Wlong t₂) ⊆ Iic b :=
    fun x hx => (hlong (phaseProfile_support Wlong t₂ hx)).2
  calc
    _ = ∑ i : rows, ‖puncturedRow (χ i) S (enlargedHoles S H Rmask) pool
        (fun j I => slotCoefficient ν (fun k => R₀ k ∪ primeSupport Rmask) t j I *
          Wslot j (I.absNorm/scales j)) scales
        (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) b X₁ X₂‖^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [rectangle_row_eq (χ i) S H Rmask hRmask pool hpool hprime ν R₀ t Wslot scales
        (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) hphase₀ b X₁ X₂ hX₁ hX₂
        hphase₁ hphase₂ (hoff i) henclose]
    _ ≤ _ := hh

end
end Candidate.SilPrior.FourthPower.MixedFirstPuncturedReference
