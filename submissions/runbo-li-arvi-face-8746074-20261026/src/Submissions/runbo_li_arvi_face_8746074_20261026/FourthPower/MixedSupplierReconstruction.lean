/- Copyright (c) 2026 Sil. Apache-2.0.
Exact finite regrouping, full supplier partition and selected split of
the original Gauss row. Product deltas are removed only by finite fibers.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedSupplierKernel
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedSupplierReconstruction
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRectangle CenteredMomentRectangle CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentLiveDomain
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSourceLiveColumn
open CenteredMomentRemainingBox
open CenteredMomentHeckeColumnWindow Record12518109GainDeletion
open MixedHeightEnergy MixedLiteralAllocation MixedCommonRestriction MixedCommonCoefficient
open MixedCommonAllocation MixedTupleRows MixedSupplierPartition MixedSupplierSplit
open MixedSupplierKernel MixedRestrictedDictionary KernelAssignmentReindex
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The kernel sees the actual product, after the finite-column fiber sum
has been evaluated. The multiplier F can contain the whole Gauss row. -/
def productKernel (pool : α→Finset Id) (A B : Finset Id) (H R seed : Id)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (F : Id→ℂ)
    (p : α→markedUniverse pool) : ℂ :=
  ∑ n∈A×ˢB,
    ordinaryKernel H R seed (finiteTupleProduct (MixedTupleRows.pack (values pool p) n))
      W₁ W₂ X₁ X₂ Y₁ Y₂ d (values pool p) n *
      F (finiteTupleProduct (MixedTupleRows.pack (values pool p) n))

theorem tuple_profile_weighted (pool : α→Finset Id) (A B : Finset Id)
    (H R seed : Id) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (F : Id→ℂ) :
    (∑ v∈Fintype.piFinset (pools pool A B),tupleWeight H v*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed v*
      F (finiteTupleProduct v)) =
      weightedSum (slotAmplitude pool ν Wslot P)
        (productKernel pool A B H R seed W₁ W₂ X₁ X₂ Y₁ Y₂ d F) := by
  rw [split_tuple_sum,pi_sum_zeroextend]
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro p hp
  have hi : Function.Injective (values pool p) ↔ Function.Injective p := by
    constructor
    · intro h i j he
      exact h (congrArg Subtype.val he)
    · intro h i j he
      exact h (Subtype.ext he)
  by_cases hpool : ∀ i,(p i).val∈pool i
  · rw [if_pos hpool]
    have hamp : (∏ i,slotAmplitude pool ν Wslot P i (p i)) =
        ∏ i,ν i ((p i).val)*Wslot i (((p i).val.absNorm:ℝ)/P i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [slotAmplitude,if_pos (hpool i)]
    have hpack (n : Id×Id) :
        tupleWeight H (MixedTupleRows.pack (values pool p) n)*
          profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed
            (MixedTupleRows.pack (values pool p) n) =
          if Function.Injective p then
            ordinaryKernel H R seed (finiteTupleProduct (MixedTupleRows.pack (values pool p) n))
              W₁ W₂ X₁ X₂ Y₁ Y₂ d (values pool p) n *
              ∏ i,ν i ((p i).val)*Wslot i (((p i).val.absNorm:ℝ)/P i)
          else 0 := by
      simpa only [if_pos rfl,ite_true,hi,values] using
        packed_coefficient H R seed (finiteTupleProduct (MixedTupleRows.pack (values pool p) n))
          ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d (values pool p) n
    simp_rw [hpack]
    rw [hamp]
    by_cases hinj : Function.Injective p
    · simp only [hinj,ite_true,productKernel,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    · simp only [hinj,ite_false,zero_mul,Finset.sum_const_zero]
  · rw [if_neg hpool]
    push_neg at hpool
    obtain ⟨i,hi⟩ := hpool
    have hz : (∏ j,slotAmplitude pool ν Wslot P j (p j))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [slotAmplitude,hi])
    simp only [hz,mul_zero,ite_self]

/-- The exact grouped coefficient is used on the left; finite_column_sum
evaluates its product delta before the selected split is performed. -/
theorem finite_profile_multiplier (pool : α→Finset Id) (A B : Finset Id)
    (H R seed : Id) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (F : Id→ℂ) :
    (∑ I∈finiteColumns (Fintype.piFinset (pools pool A B)),
      finiteColumnCoefficient (Fintype.piFinset (pools pool A B))
        (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ d.1 d.2 seed v) I*F I) =
      weightedSum (slotAmplitude pool ν Wslot P)
        (productKernel pool A B H R seed W₁ W₂ X₁ X₂ Y₁ Y₂ d F) := by
  rw [finite_column_sum]
  exact tuple_profile_weighted pool A B H R seed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d F

/-- All suppliers are partitioned, then their actual values are fixed,
then selected live values are fixed. remainingSum keeps every cross-hole.
The remaining kernel is the exact reconstructed original kernel. -/
def supplierExpansion (u : Id) (J : (L : Finset α)→Finset {i // i∉Lᶜ})
    (pool : α→Finset Id) (A B : Finset Id) (H R seed : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (F : Id→ℂ) : ℂ :=
  ∑ L : Finset α,
    let a := slotAmplitude pool (supplierCharacters u L ν) Wslot P
    let K := productKernel pool A B H R seed W₁ W₂ X₁ X₂ Y₁ Y₂ d F
    ∑ t : ↥(Lᶜ)→markedUniverse pool,if Function.Injective t then
      (∏ i : ↥(Lᶜ),a i.val (t i))*
        ∑ s : J L→markedUniverse pool,if Function.Injective s then
          (∏ j : J L,frozenLiveAmplitude Lᶜ a t j.val (s j))*
            remainingSum (J L) (frozenLiveAmplitude Lᶜ a t) s (fun r=>
              K (joinAssignments (fun i=>i∈Lᶜ) t
                (joinAssignments (fun j=>j∈J L) s r))) else 0
      else 0

set_option maxHeartbeats 800000 in
theorem tuple_supplier_expansion (u : Id) (J : (L : Finset α)→Finset {i // i∉Lᶜ})
    (pool : α→Finset Id) (A B : Finset Id) (H R seed : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (F : Id→ℂ) :
    (∑ v∈Fintype.piFinset (pools pool A B),tupleWeight H v*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed v*
      F (finiteTupleProduct v)) =
      supplierExpansion u J pool A B H R seed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d F := by
  simp_rw [weighted_tuple_partition u H R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed]
  rw [Finset.sum_comm]
  unfold supplierExpansion
  apply Finset.sum_congr rfl
  intro L hL
  rw [tuple_profile_weighted]
  have he := split_two_levels Lᶜ (J L)
    (slotAmplitude pool (supplierCharacters u L ν) Wslot P)
    (productKernel pool A B H R seed W₁ W₂ X₁ X₂ Y₁ Y₂ d F)
  apply he.trans
  dsimp only
  apply Finset.sum_congr (by ext; simp)
  intro t ht
  by_cases htinj : Function.Injective t
  · simp only [htinj,ite_true]
    apply congrArg (fun z : ℂ=>(∏i : ↥(Lᶜ),
      slotAmplitude pool (supplierCharacters u L ν) Wslot P i.val (t i))*z)
    apply Finset.sum_congr (by ext; simp)
    intro s hs
    by_cases hsinj : Function.Injective s <;> simp only [hsinj,ite_true,ite_false]
  · simp only [htinj,ite_false]

theorem original_column_supplier_expansion
    (u : Id) (J : (L : Finset α)→Finset {i // i∉Lᶜ})
    (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (F : Id→ℂ) :
    (∑ I∈finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂)),
      originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I*F I) =
      supplierExpansion u J pool
        (residualPool d.1 hd.1 (plainSupportPool b X₁ Y₁))
        (residualPool d.2 hd.2 (plainSupportPool b X₂ Y₂))
        (punctureProduct S H) R seed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d F := by
  unfold originalColumn
  rw [finite_column_sum]
  exact tuple_supplier_expansion u J pool _ _ (punctureProduct S H) R seed
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d F

/-- Unsupported columns are removed only because their actual primary
Gauss row is zero. No support or restriction of a nonzero row is lost. -/
theorem supported_gauss_sum (Q : Finset Id) (c : Id→ℂ) (k : O) :
    (∑ I∈supportedColumns Q,c I*primaryGaussRow I k)=
      ∑ I∈Q,c I*primaryGaussRow I k := by
  rw [supportedColumns,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hs : Supported I
  · simp only [hs,ite_true]
  · simp only [primaryGaussRow,hs,ite_false,dite_false,mul_zero]

theorem source_gauss_sum (Q : Finset Id) (c : Id→ℂ) (k : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q=>c I) k =
      ∑ I∈Q,c I*primaryGaussRow I k := by
  rw [source_gaussPolynomial,supported_gauss_sum]

/-- Concrete Gauss specialization of original_column_supplier_expansion.
At a fixed Fourier variable w, use t+2*pi*(w-theta) here. Thus neither
the old norm window nor a selected-product cutoff is hidden in c. -/
theorem original_gauss_supplier_expansion
    (u : Id) (J : (L : Finset α)→Finset {i // i∉Lᶜ})
    (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) (τ : Character) (t : ℝ) (k : O) :
    let Q := finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q=>
        originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I*
          heightCoeff τ t I) k =
      supplierExpansion u J pool
        (residualPool d.1 hd.1 (plainSupportPool b X₁ Y₁))
        (residualPool d.2 hd.2 (plainSupportPool b X₂ Y₂))
        (punctureProduct S H) R seed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d
        (fun I=>heightCoeff τ t I*primaryGaussRow I k) := by
  dsimp only
  rw [source_gauss_sum _ (fun I=>
    originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I*
      heightCoeff τ t I) k]
  simp only [mul_assoc]
  exact original_column_supplier_expansion u J S H pool d hd R seed ν Wslot P W₁ W₂
    b X₁ X₂ Y₁ Y₂ (fun I=>heightCoeff τ t I*primaryGaussRow I k)

/-- Repacking arbitrary actual tuple pools is an equality of functions,
including both independent ordinary pools. -/
theorem pools_eta (T : (α⊕Fin 2)→Finset Id) :
    pools (fun i=>T (Sum.inl i)) (T (Sum.inr 0)) (T (Sum.inr 1))=T := by
  funext j
  cases j with
  | inl i=>rfl
  | inr j=>fin_cases j <;> rfl

/-- The residual artificial mask is incorporated into the ORIGINAL seed
slot. It is not deleted, even when this divisor has suppliers in the live
marked slots. The complete supplier partition subsequently handles it. -/
theorem profile_seed_mask (H R seed : Id) (ν : α→Id→ℂ)
    (Wslot : α→ℝ→ℂ) (P : α→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (v : Tuple α) :
    (if seed∣finiteTupleProduct v then tupleWeight H v*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v else 0) =
      tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed v := by
  unfold profileCoefficient
  by_cases hs : seed∣finiteTupleProduct v <;>
    simp only [hs,ite_true,ite_false,one_dvd,mul_one,mul_zero]

/-- Applies directly to every genuine common-allocation liveBox/liveProfile:
take T=remainingSets, R=R_original*G, and the exact enlarged ordinary
prefixes. Their possibly shifted ordinary pools are kept verbatim. -/
theorem masked_tuple_supplier_expansion (T : (α⊕Fin 2)→Finset Id)
    (seed : Id) (J : (L : Finset α)→Finset {i // i∉Lᶜ}) (H R : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (F : Id→ℂ) :
    (∑ v∈Fintype.piFinset T,
      (if seed∣finiteTupleProduct v then tupleWeight H v*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v else 0)*
        F (finiteTupleProduct v)) =
      supplierExpansion seed J (fun i=>T (Sum.inl i))
        (T (Sum.inr 0)) (T (Sum.inr 1)) H R seed ν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d F := by
  simp_rw [profile_seed_mask]
  have h := tuple_supplier_expansion seed J (fun i=>T (Sum.inl i))
    (T (Sum.inr 0)) (T (Sum.inr 1)) H R seed ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ d F
  rwa [pools_eta] at h

/-- The precise supported first-child domain from MixedFirstWindow.
Its coprimality filter is moved into the scalar, without changing the row. -/
theorem first_gauss_sum (C G : Id) (hG : Supported G) (Q : Finset Id)
    (c : Id→ℂ) (k : O) :
    gaussPolynomial Finset.univ
      (CenteredMomentFirstPhysicalSource.element C G hG.1 Q)
      (CenteredMomentFirstPhysicalSource.element_supported C G hG.1 Q)
      (fun I : CenteredMomentFirstPhysicalSource.columns C G hG.1 Q=>c I) k =
      ∑ I∈residualPool G hG.1 Q,
        (if IsCoprime C I then c I else 0)*primaryGaussRow I k := by
  have he : gaussPolynomial Finset.univ
      (CenteredMomentFirstPhysicalSource.element C G hG.1 Q)
      (CenteredMomentFirstPhysicalSource.element_supported C G hG.1 Q)
      (fun I : CenteredMomentFirstPhysicalSource.columns C G hG.1 Q=>c I) k =
      ∑ I∈CenteredMomentFirstPhysicalSource.columns C G hG.1 Q,
        c I*primaryGaussRow I k := by
    unfold gaussPolynomial
    rw [←Finset.sum_coe_sort (CenteredMomentFirstPhysicalSource.columns C G hG.1 Q)
      (fun I=>c I*primaryGaussRow I k)]
    apply Finset.sum_congr rfl
    intro I hI
    rw [primaryGaussRow,dif_pos (CenteredMomentFirstPhysicalSource.column_supported C G hG.1 Q I)]
    rfl
  rw [he,CenteredMomentFirstPhysicalSource.columns,
    ←supported_residualPool G hG Q,Finset.sum_filter]
  calc
    _ = ∑ I∈supportedColumns (residualPool G hG.1 Q),
        (if IsCoprime C I then c I else 0)*primaryGaussRow I k := by
      apply Finset.sum_congr rfl
      intro I hI
      split_ifs <;> simp only [zero_mul]
    _ = _ := supported_gauss_sum _ _ k

/-- At every Fourier height, the ACTUAL first-child Gauss polynomial is
regrouped over genuine common allocations and their original live tuples.
The original seed|G is retained as an explicit genuine-common condition;
the new artificial divisor L is left on the residual tuple product.
Use masked_tuple_supplier_expansion on each resulting live summand. -/
theorem first_gauss_common_tuples (H : Id) (T : (α⊕Fin 2)→Finset Id)
    (hT : ∀j,∀I∈T j,I≠0) (hp : ∀i,∀I∈T (Sum.inl i),Prime I)
    (C G R seed L : Id) (hC : Supported C) (hG : Supported G)
    (hCG : primeSupport C=primeSupport G) (hseed : seed∣G)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (τ : Character) (t : ℝ) (k : O) :
    let Q := finiteColumns (Fintype.piFinset T)
    let β := finiteColumnCoefficient (Fintype.piFinset T)
      (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed v)
    gaussPolynomial Finset.univ
      (CenteredMomentFirstPhysicalSource.element C G hG.1 Q)
      (CenteredMomentFirstPhysicalSource.element_supported C G hG.1 Q)
      (fun I : CenteredMomentFirstPhysicalSource.columns C G hG.1 Q=>
        (if L∣I.val then β (G*I) else 0)*heightCoeff τ t I) k =
      ∑ B : actualAllocations T G,
        (frozenWeight H B.val*frozenCoefficient B.val G R ν Wslot P)*
          ∑ v∈liveBox T B.val
              (allocation_data T G B.val (Finset.mem_filter.mp B.property).1).1,
            (if L∣finiteTupleProduct v then tupleWeight H v*
              liveProfile B.val G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v else 0)*
              (heightCoeff τ t (finiteTupleProduct v)*primaryGaussRow (finiteTupleProduct v) k) := by
  dsimp only
  rw [first_gauss_sum C G hG (finiteColumns (Fintype.piFinset T))
    (fun I=>(if L∣I then finiteColumnCoefficient (Fintype.piFinset T)
      (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d.1 d.2 seed v) (G*I) else 0)*heightCoeff τ t I) k]
  have hmask (I : Id) :
      (if IsCoprime C I then
        (if L∣I then finiteColumnCoefficient (Fintype.piFinset T)
          (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
            X₁ X₂ Y₁ Y₂ d.1 d.2 seed v) (G*I) else 0)*heightCoeff τ t I
        else 0)*primaryGaussRow I k =
      (if IsCoprime G I ∧ L∣I then finiteColumnCoefficient (Fintype.piFinset T)
        (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ d.1 d.2 seed v) (G*I) else 0)*
          (heightCoeff τ t I*primaryGaussRow I k) := by
    by_cases hI : Supported I
    · have hc : IsCoprime C I ↔ IsCoprime G I := by
        have hsupport : IdealMobiusDivisorSum.primeSupport C=
            IdealMobiusDivisorSum.primeSupport G := hCG
        rw [←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC.1 hI.1,
          ←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hG.1 hI.1,hsupport]
      by_cases hg : IsCoprime G I <;> by_cases hl : L∣I <;>
        simp only [hc,hg,hl,true_and,false_and,and_false,ite_true,ite_false,
          mul_zero,zero_mul,mul_assoc]
    · simp only [primaryGaussRow,dif_neg hI,mul_zero]
  simp_rw [hmask]
  have he := common_masked_column_sum H T hT hp G R seed L hG.1 hseed ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 (fun I=>heightCoeff τ t I*primaryGaussRow I k)
  apply he.trans
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun x : ℂ=>(frozenWeight H B.val*frozenCoefficient B.val G R ν Wslot P)*x)
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> simp only [zero_mul]

/-- The alphabet is the union of actual pools, not an arbitrary ideal
set. Every one of its values is prime under the source's pool condition. -/
theorem alphabet_prime (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (q : markedUniverse pool) : Prime q.val := by
  obtain ⟨i,hi,hq⟩ := Finset.mem_biUnion.mp q.property
  exact hp i q.val hq

theorem alphabet_coprime_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (p : ι→markedUniverse pool) (q : κ→markedUniverse pool) :
    IsCoprime (∏ i,(p i).val) (∏ j,(q j).val) ↔ ∀i j,p i≠q j := by
  have h := prime_cross_iff
    (fun i=>⟨(p i).val,alphabet_prime pool hp (p i)⟩)
    (fun j=>⟨(q j).val,alphabet_prime pool hp (q j)⟩)
  constructor
  · intro hc i j he
    exact (h.mp hc i j) (Subtype.ext (congrArg (fun z : markedUniverse pool=>z.val) he))
  · intro hc
    apply h.mpr
    intro i j he
    apply hc i j
    exact Subtype.ext (congrArg (fun z : PrimeIdeal=>z.val) he)

theorem frozen_product_mask {ι : Type*} [Fintype ι]
    (pool : α→Finset Id) (T : Finset α)
    (a : α→markedUniverse pool→ℂ) (t : T→markedUniverse pool)
    (v : ι→{i // i∉T}) (y : ι→markedUniverse pool) :
    (∏j,frozenLiveAmplitude T a t (v j) (y j))=
      if ∀i : T,∀j,t i≠y j then ∏j,a (v j).val (y j) else 0 := by
  by_cases h : ∀i : T,∀j,t i≠y j
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro j hj
    exact if_pos (fun i=>h i j)
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    obtain ⟨j,hj⟩ := not_forall.mp hi
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact if_neg (fun hall=>hj (hall i))

/-- Exact pointwise collapse of ALL cross-holes in the nested split.
The residual slot product on the right is independent of selected s.
Its selected dependence consists solely of crossGate, which is handled
by ordinary_kernel_at_product and then literal_row_eq.
No nonzero-coefficient or separation premise is required. -/
theorem selected_holes (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (T : Finset α) (J : Finset {i // i∉T})
    (a : α→markedUniverse pool→ℂ) (t : T→markedUniverse pool)
    (s : J→markedUniverse pool) (r : {j : {i // i∉T} // j∉J}→markedUniverse pool)
    (g : ℂ) :
    (∏ j : J,frozenLiveAmplitude T a t j.val (s j))*
      (if Function.Injective r ∧ (∀j k,s j≠r k) then
        g*∏ k : {j : {i // i∉T} // j∉J},frozenLiveAmplitude T a t k.val (r k)
      else 0) =
    (∏ j : J,a j.val.val (s j))*
      (if Function.Injective r then
        (if crossGate (∏i : T,(t i).val) (∏j : J,(s j).val)
          (∏k : {j : {i // i∉T} // j∉J},(r k).val) then (1:ℂ) else 0)*g*
          ∏ k : {j : {i // i∉T} // j∉J},a k.val.val (r k)
      else 0) := by
  rw [frozen_product_mask pool T a t (fun j : J=>j.val) s,
      frozen_product_mask pool T a t (fun k : {j : {i // i∉T} // j∉J}=>k.val) r]
  simp only [crossGate,alphabet_coprime_iff pool hp]
  split_ifs <;> simp_all <;> ring

theorem slot_supplier_nonzero (pool : α→Finset Id) (u : Id) (L : Finset α)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (i : α) (q : markedUniverse pool)
    (hq : slotAmplitude pool (supplierCharacters u L ν) Wslot P i q≠0) :
    i∈L ↔ ¬q.val∣u := by
  apply supplier_character_nonzero u L ν i q.val
  intro hz
  exact hq (by simp only [slotAmplitude,hz,zero_mul,ite_self])

/-- The two structural conditions needed by the kernel are derived from
the ACTUAL nonzero frozen and selected slot products. No arbitrary
factorization u=f*seed or coprimality premise is inserted into the row. -/
theorem actual_suppliers_seed (pool : α→Finset Id)
    (hp : ∀i,∀I∈pool i,Prime I) (u : Id) (L : Finset α)
    (J : Finset {i // i∉Lᶜ}) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (t : ↥(Lᶜ)→markedUniverse pool) (s : J→markedUniverse pool)
    (ht : Function.Injective t)
    (hft : (∏ i : ↥(Lᶜ),slotAmplitude pool (supplierCharacters u L ν) Wslot P i.val (t i))≠0)
    (hsel : (∏ j : J,frozenLiveAmplitude Lᶜ
      (slotAmplitude pool (supplierCharacters u L ν) Wslot P) t j.val (s j))≠0) :
    ∃seed : Id,u=(∏ i : ↥(Lᶜ),(t i).val)*seed ∧
      IsCoprime seed (∏ j : J,(s j).val) := by
  let pt : ↥(Lᶜ)→PrimeIdeal := fun i=>⟨(t i).val,alphabet_prime pool hp (t i)⟩
  have hpt : Function.Injective pt := by
    intro i j he
    exact ht (Subtype.ext (congrArg (fun z : PrimeIdeal=>z.val) he))
  have hdiv : (∏ i : ↥(Lᶜ),(t i).val)∣u := by
    apply suppliers_product_dvd pt hpt u
    intro i
    have hi := slot_supplier_nonzero pool u L ν Wslot P i.val (t i)
      ((Finset.prod_ne_zero_iff.mp hft) i (Finset.mem_univ i))
    by_contra hn
    have hmem : i.val∈L := hi.mpr hn
    exact (Finset.mem_compl.mp i.property) hmem
  have hcop : IsCoprime u (∏ j : J,(s j).val) := by
    apply IsCoprime.prod_right
    intro j hj
    have hjn : frozenLiveAmplitude Lᶜ
        (slotAmplitude pool (supplierCharacters u L ν) Wslot P) t j.val (s j)≠0 :=
      (Finset.prod_ne_zero_iff.mp hsel) j (Finset.mem_univ j)
    have hslot : slotAmplitude pool (supplierCharacters u L ν) Wslot P
        j.val.val (s j)≠0 := by
      intro hz
      exact hjn (by simp only [frozenLiveAmplitude,hz,ite_self])
    have hjL : j.val.val∈L := by simpa using j.val.property
    have hnd := (slot_supplier_nonzero pool u L ν Wslot P j.val.val (s j) hslot).mp hjL
    exact ((prime_coprime ⟨(s j).val,alphabet_prime pool hp (s j)⟩ u).mpr hnd).symm
  obtain ⟨seed,hseed⟩ := hdiv
  refine ⟨seed,hseed,hcop.of_isCoprime_of_dvd_left ?_⟩
  rw [hseed]
  exact dvd_mul_left seed (∏ i : ↥(Lᶜ),(t i).val)

end
end Candidate.FourthPower.MixedSupplierReconstruction
