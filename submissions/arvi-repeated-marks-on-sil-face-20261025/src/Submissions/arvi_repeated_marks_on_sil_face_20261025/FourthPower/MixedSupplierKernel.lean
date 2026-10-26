/- Copyright (c) 2026 Sil. Apache-2.0.
Exact masks and fixed-supplier Gauss separation. 
The fixed supplier f remains in the residual character coefficient.
Only D, never f*D, is passed to the fourth-power transfer.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSupplierSplit
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSelectedCommon
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSourceEnergy

set_option autoImplicit false
namespace Candidate.FourthPower.MixedSupplierKernel
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentFirstColumns
open CenteredMomentFixedRay RayFourExpansion HeckeFamily
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSourceRectangle CenteredMomentRectangle
open CenteredMomentAddedZeroUniform
open QRH.Record1252270103KernelMass IdealMobiusDivisorSum
open MixedCommonRestriction MixedTupleRows MixedSupplierSplit MixedSelectedCommon
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- On actual prime assignments, cross-distinctness is exactly product
coprimality. This supplies crossGate from the reindexer's retained holes. -/
theorem prime_cross_iff {α β : Type*} [Fintype α] [Fintype β]
    (p : α→PrimeIdeal) (q : β→PrimeIdeal) :
    IsCoprime (∏ i,(p i).val) (∏ j,(q j).val) ↔ ∀ i j,p i≠q j := by
  simp only [IsCoprime.prod_left_iff,IsCoprime.prod_right_iff,
    Finset.mem_univ,forall_const]
  constructor
  · intro h i j he
    have hn := (prime_coprime (p i) (q j).val).mp (h j i)
    apply hn
    rw [he]
  · intro h j i
    apply (prime_coprime (p i) (q j).val).mpr
    intro hd
    exact h i j (Subtype.ext ((prime_dvd_prime_iff_eq
      (p i).property (q j).property).mp hd))

/-- Every frozen supplier really divides u; injectivity makes their
product divide u. Thus u=f*seed is obtainable, not an extra assumption. -/
theorem suppliers_product_dvd {α : Type*} [Fintype α]
    (p : α→PrimeIdeal) (hinj : Function.Injective p) (u : Id)
    (hd : ∀ i,(p i).val∣u) : (∏ i,(p i).val)∣u := by
  apply Fintype.prod_dvd_of_coprime _ hd
  intro i j hij
  apply (prime_coprime (p i) (p j).val).mpr
  intro hdiv
  exact hij (hinj (Subtype.ext ((prime_dvd_prime_iff_eq
    (p i).property (p j).property).mp hdiv)))

/-- All three cross-holes between frozen, selected and residual marked
products. Within-block injectivity remains in the weighted assignments. -/
def crossGate (f D M : Id) : Prop :=
  IsCoprime f D ∧ IsCoprime f M ∧ IsCoprime D M

def selectedGate (R f D : Id) : Prop := IsCoprime f D ∧ IsCoprime D R

/-- This predicate has NO selected-product argument. The original
fifth-free ordinary restriction, both old punctures and seed survive. -/
def commonGate (H R f seed M A B : Id) : Prop :=
  IsCoprime f M ∧ restriction H (f*M) A B ∧
    IsCoprime (f*(A*B*M)) R ∧ seed ∣ A*B*M

theorem common_gate_coprime (H R f seed M A B : Id)
    (h : commonGate H R f seed M A B) : IsCoprime f (A*B*M) := by
  simp only [commonGate,restriction,IsCoprime.mul_left_iff,
    IsCoprime.mul_right_iff] at h ⊢
  tauto

/-- All masks separate exactly. The residual seed is not discarded.
Its coprimality with D is supplied by the complete supplier partition. -/
theorem full_gate_split (H R f seed D M A B : Id) (hf : f≠0)
    (hseed : IsCoprime seed D) :
    (crossGate f D M ∧ restriction H (f*D*M) A B ∧
      IsCoprime (f*D*(A*B*M)) R ∧ f*seed ∣ f*D*(A*B*M)) ↔
      selectedGate R f D ∧ commonGate H R f seed M A B ∧
        IsCoprime D (A*B*M) := by
  rw [surviving_seed_iff f seed D (A*B*M) hf hseed]
  simp only [crossGate,selectedGate,commonGate,restriction,
    IsCoprime.mul_left_iff,IsCoprime.mul_right_iff]
  tauto

/-- Literal original scalar after expanding the product f*D*M.
No norm, absolute value or relaxation of restrictions occurs here. -/
def originalKernel (H R f seed D M A B : Id) (rectangle : ℂ) : ℂ :=
  (if crossGate f D M then 1 else 0) *
    restrictionWeight H (f*D*M) A B *
    (if IsCoprime (f*D*(A*B*M)) R then 1 else 0) * rectangle *
    (if f*seed ∣ f*D*(A*B*M) then 1 else 0)

def commonKernel (H R f seed M A B : Id) (rectangle : ℂ) : ℂ :=
  if commonGate H R f seed M A B then rectangle else 0

theorem original_kernel_split (H R f seed D M A B : Id) (hf : f≠0)
    (hseed : IsCoprime seed D) (rectangle : ℂ) :
    originalKernel H R f seed D M A B rectangle =
      (if selectedGate R f D then 1 else 0) *
        commonKernel H R f seed M A B rectangle *
        (if IsCoprime D (A*B*M) then 1 else 0) := by
  have hg := full_gate_split H R f seed D M A B hf hseed
  unfold originalKernel commonKernel restrictionWeight
  split_ifs <;> simp_all only [zero_mul,mul_zero,one_mul,mul_one] <;> tauto

/-- Connection to the actual kernel constructed by the supplier reindexing.
It is evaluated at its ACTUAL tuple product. A fixed-I column delta must
first be regrouped in the finite column-to-Gauss sum; it cannot be dropped.
The hypothesis hp is the exact joinAssignments product identity. -/
theorem ordinary_kernel_at_product {α : Type*} [Fintype α]
    (H R f seed D M : Id) (hf : f≠0) (hseed : IsCoprime seed D)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (p : α→Id) (n : Id×Id) (hp : (∏ i,p i)=f*D*M) :
    (if crossGate f D M then (1:ℂ) else 0) *
      ordinaryKernel H R (f*seed) (finiteTupleProduct (MixedTupleRows.pack p n))
        W₁ W₂ X₁ X₂ Y₁ Y₂ d p n =
      (if selectedGate R f D then 1 else 0) *
        commonKernel H R f seed M n.1 n.2
          (idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (d.1*n.1) (d.2*n.2)) *
        (if IsCoprime D (n.1*n.2*M) then 1 else 0) := by
  have hprod : finiteTupleProduct (MixedTupleRows.pack p n)=f*D*(n.1*n.2*M) := by
    rw [MixedTupleRows.pack_product,hp]
    ring
  rw [← original_kernel_split H R f seed D M n.1 n.2 hf hseed]
  simp only [ordinaryKernel,ite_true,hp,hprod,originalKernel]
  ring

/-- Fixed-f twist belongs to the common vector; there is no D argument.
The Hecke height and residual ray remain literal factors. -/
def fixedCommonCoefficient {ι : Type*} (n : ι→Id) (B : ι→ℂ)
    (f : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (v : ι) : ℂ :=
  B v * heightCoeff τ t (n v) *
    (idealRowHom (primaryGenerator f) (n v))^2 *
    rayCharacter ξ (primaryGenerator (n v))

/-- Exact CRT/ray separation WITH f, but before fourth-power transfer.
Both masks in IsCoprime(f*D,n) are retained, including the fixed f hole. -/
theorem fixed_product_rays (f D n : Id) (hf : Supported f)
    (hD : Supported D) (hn : Supported n) (k : O) :
    (if IsCoprime (f*D) n then
      idealGauss ((f*D)*n)
        ((supported_mul_iff (f*D) n).mpr
          ⟨(supported_mul_iff f D).mpr ⟨hf,hD⟩,hn⟩) k else 0) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff firstPhaseTable χ ξ *
          rayCharacter χ (primaryGenerator (f*D)) *
          rayCharacter ξ (primaryGenerator n) *
          ((idealRowHom (primaryGenerator f) n)^2 *
            (idealRowHom (primaryGenerator D) n)^2) *
          idealGauss (f*D) ((supported_mul_iff f D).mpr ⟨hf,hD⟩) k *
          idealGauss n hn k := by
  let hfD : Supported (f*D) := (supported_mul_iff f D).mpr ⟨hf,hD⟩
  have hcop : IsCoprime (primaryGenerator (f*D)) (primaryGenerator n) ↔
      IsCoprime (f*D) n := by
    rw [←Ideal.isCoprime_span_singleton_iff,
      primary_span_supported (f*D) hfD,primary_span_supported n hn]
  have he := masked_product_rays (primaryGenerator (f*D)) (primaryGenerator n)
    (primary_supported (f*D) hfD) (primary_supported n hn)
    (primaryGenerator_spec (f*D) (supported_primaryGenerator_ne_zero (f*D) hfD)).2
    (primaryGenerator_spec n (supported_primaryGenerator_ne_zero n hn)).2 k
  simp only [hcop,primary_span_supported n hn] at he
  have hmul : (idealRowHom (primaryGenerator (f*D)) n)^2 =
      (idealRowHom (primaryGenerator f) n)^2 *
        (idealRowHom (primaryGenerator D) n)^2 := by
    rw [primaryGenerator_mul,idealRowHom_argument_mul,mul_pow]
  rw [hmul] at he
  simpa only [idealGauss,primaryGenerator_mul] using he

/-- The selected-frequency dilation is D^4. In particular no f^4 is
introduced. The fixed-f twist was split multiplicatively beforehand. -/
theorem fixed_supplier_row_fourth {ι : Type*} (V : Finset ι)
    (n : ι→Id) (hn : ∀ v,Supported (n v)) (A : ℂ) (B : ι→ℂ)
    (f D : Id) (hf : Supported f) (hD : Supported D)
    (τ : Character) (t : ℝ)
    (hfree : ∀ v∈V, B v≠0 → SexticSieve.PowerFree 5 (n v)) (k : O) :
    (∑ v∈V, A*B v*heightCoeff τ t ((f*D)*n v) *
      (if IsCoprime (f*D) (n v) then
        idealGauss ((f*D)*n v)
          ((supported_mul_iff (f*D) (n v)).mpr
            ⟨(supported_mul_iff f D).mpr ⟨hf,hD⟩,hn v⟩) k else 0)) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff firstPhaseTable χ ξ *
          (A*heightCoeff τ t (f*D)*rayCharacter χ (primaryGenerator (f*D))*
            idealGauss (f*D) ((supported_mul_iff f D).mpr ⟨hf,hD⟩) k) *
          gaussPolynomial V (fun v=>primaryGenerator (n v))
            (fun v=>primary_supported (n v) (hn v))
            (fixedCommonCoefficient n B f τ t ξ) ((primaryGenerator D)^4*k) := by
  have hfour (ξ : RayCharacter) := MixedPhysicalTransfer.sparse_fourth_power V
    (fun v=>primaryGenerator (n v)) (fun v=>primary_supported (n v) (hn v))
    (fixedCommonCoefficient n B f τ t ξ)
    (by
      intro v hv hb
      apply KernelWholeColumns.element_fifth_free
      rw [primary_span_supported (n v) (hn v)]
      apply hfree v hv
      intro hz
      exact hb (by simp only [fixedCommonCoefficient,hz,zero_mul]))
    (primaryGenerator D) k
  have hrow (v : ι) := fixed_product_rays f D (n v) hf hD (hn v) k
  simp_rw [hfour]
  simp_rw [hrow, heightCoeff_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  apply Finset.sum_congr rfl
  intro v hv
  simp only [fixedCommonCoefficient,idealGauss,primary_span_supported (n v) (hn v)]
  ring

/-- Actual ordinary+remaining-slot coefficient, common over the selected
assignments. slotRest is the exact residual slot product from split_two_levels;
this definition does not postulate any factorization of the original kernel. -/
def residualCoefficient {ι : Type*} (H R f seed : Id)
    (M A B : ι→Id) (slotRest : ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (v : ι) : ℂ :=
  slotRest v * commonKernel H R f seed (M v) (A v) (B v)
    (idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (d.1*A v) (d.2*B v))

/-- Fifth-freeness for the actual residual marked+ordinary product comes
from the retained restriction, with no character or phase assumption. -/
theorem common_gate_fifth_free {α : Type*} [Fintype α]
    (H R f seed A B : Id) (p : α→PrimeIdeal) (hinj : Function.Injective p)
    (hA : A≠0) (hB : B≠0)
    (h : commonGate H R f seed (∏ i,(p i).val) A B) :
    SexticSieve.PowerFree 5 (A*B*∏ i,(p i).val) := by
  apply KernelWholeColumns.restricted_whole_fifth_free p hinj hA hB h.2.1.1
  intro i
  apply (prime_coprime (p i) (A*B)).mp
  have hm : IsCoprime (∏ j,(p j).val) (A*B) :=
    ((IsCoprime.mul_left_iff.mp h.2.1.2).2).of_isCoprime_of_dvd_left
      (dvd_mul_left (∏ j,(p j).val) f)
  exact hm.of_isCoprime_of_dvd_left
    (Finset.dvd_prod_of_mem (fun j=>(p j).val) (Finset.mem_univ i))

/-- For this explicit vector, the moving-only hole equals the full CRT
hole. Equality uses its literal old restrictions, not cancellation. -/
theorem residual_mask_eq {ι : Type*} (H R f seed D : Id)
    (M A B : ι→Id) (slotRest : ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) (v : ι) (g : ℂ) :
    residualCoefficient H R f seed M A B slotRest W₁ W₂ X₁ X₂ Y₁ Y₂ d v *
      (if IsCoprime D (A v*B v*M v) then g else 0) =
    residualCoefficient H R f seed M A B slotRest W₁ W₂ X₁ X₂ Y₁ Y₂ d v *
      (if IsCoprime (f*D) (A v*B v*M v) then g else 0) := by
  by_cases h : commonGate H R f seed (M v) (A v) (B v)
  · have hc := common_gate_coprime H R f seed (M v) (A v) (B v) h
    rw [IsCoprime.mul_left_iff]
    simp only [hc,true_and]
  · simp only [residualCoefficient,commonKernel,if_neg h,mul_zero,zero_mul]

/-- The original reconstructed ordinary kernel and literal residual slot
product give the very row consumed by fixed_supplier_row_fourth. This is
an exact identity, not an assumed common-coefficient factorization.
The fixed selected slot product is As; its expression was already supplied
by split_two_levels. No selected assignment occurs in c. -/
theorem literal_row_eq {ι : Type*} (V : Finset ι) (H R f seed D : Id)
    (hf : Supported f) (hD : Supported D) (hf0 : f≠0)
    (hseed : IsCoprime seed D) (M A B : ι→Id)
    (hn : ∀ v,Supported (A v*B v*M v)) (As : ℂ) (slotRest : ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (τ : Character) (t : ℝ) (k : O) :
    let c := residualCoefficient H R f seed M A B slotRest W₁ W₂ X₁ X₂ Y₁ Y₂ d
    (∑ v∈V, As*slotRest v*
      originalKernel H R f seed D (M v) (A v) (B v)
        (idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (d.1*A v) (d.2*B v)) *
      heightCoeff τ t ((f*D)*(A v*B v*M v)) *
      idealGauss ((f*D)*(A v*B v*M v))
        ((supported_mul_iff (f*D) (A v*B v*M v)).mpr
          ⟨(supported_mul_iff f D).mpr ⟨hf,hD⟩,hn v⟩) k) =
    ∑ v∈V, ((if selectedGate R f D then (1:ℂ) else 0)*As)*c v*
      heightCoeff τ t ((f*D)*(A v*B v*M v)) *
      (if IsCoprime (f*D) (A v*B v*M v) then
        idealGauss ((f*D)*(A v*B v*M v))
          ((supported_mul_iff (f*D) (A v*B v*M v)).mpr
            ⟨(supported_mul_iff f D).mpr ⟨hf,hD⟩,hn v⟩) k else 0) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [original_kernel_split H R f seed D (M v) (A v) (B v) hf0 hseed]
  by_cases h : commonGate H R f seed (M v) (A v) (B v)
  · have hc := common_gate_coprime H R f seed (M v) (A v) (B v) h
    simp only [residualCoefficient,commonKernel,if_pos h,
      IsCoprime.mul_left_iff,hc,true_and]
    split_ifs <;> ring
  · simp only [residualCoefficient,commonKernel,if_neg h,mul_zero,zero_mul]

end
end Candidate.FourthPower.MixedSupplierKernel
