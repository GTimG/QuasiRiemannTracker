/- Copyright (c) 2026 Sil. Apache-2.0.
Actual frozen-supplier family to one common residual vector, with only
the selected product raised to the fourth power.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedSupplierReconstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedSupplierFourthRow
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss RayFourExpansion CenteredMomentFixedRay CenteredMomentFirstColumns
open ConcretePrimeRowBridge
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRectangle CenteredMomentRectangle
open CenteredMomentAddedZeroUniform
open QRH.Record1252270103KernelMass Record12518109GainDeletion
open MixedCommonRestriction MixedTupleRows MixedSupplierPartition MixedSupplierSplit
open MixedSupplierKernel MixedSupplierReconstruction KernelAssignmentReindex
open MixedSelectedCommon (idealGauss primary_supported)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Raw original tuple data after genuine common extraction and Fourier
separation. No common-coefficient factorization or estimate is a field. -/
structure Data (α : Type*) [Fintype α] where
  pool : α→Finset Id
  prime : ∀i,∀I∈pool i,Prime I
  A : Finset Id
  B : Finset Id
  H : Id
  R : Id
  u : Id
  ν : α→Id→ℂ
  Wslot : α→ℝ→ℂ
  P : α→ℝ
  W₁ : ℝ→ℂ
  W₂ : ℝ→ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  d : Id×Id
  L : Finset α
  J : Finset {i // i∉Lᶜ}

variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

abbrev Alphabet (q : Data α) := markedUniverse q.pool
abbrev Frozen (q : Data α) := ↥(q.Lᶜ)→Alphabet q
abbrev Selected (q : Data α) := q.J→Alphabet q
abbrev Rest (q : Data α) := {j : {i // i∉q.Lᶜ} // j∉q.J}→Alphabet q
abbrev Residual (q : Data α) := Rest q × (q.A×ˢq.B)

def amplitude (q : Data α) : α→Alphabet q→ℂ :=
  slotAmplitude q.pool (supplierCharacters q.u q.L q.ν) q.Wslot q.P
def frozenProduct (q : Data α) (x : Frozen q) : Id := ∏i,(x i).val
def selectedProduct (q : Data α) (y : Selected q) : Id := ∏j,(y j).val
def restProduct (q : Data α) (r : Rest q) : Id := ∏j,(r j).val
def frozenWeight (q : Data α) (x : Frozen q) : ℂ := ∏i,amplitude q i.val (x i)
def selectedWeight (q : Data α) (y : Selected q) : ℂ := ∏j,amplitude q j.val.val (y j)
def restWeight (q : Data α) (v : Residual q) : ℂ :=
  if Function.Injective v.1 then ∏j,amplitude q j.val.val (v.1 j) else 0
def residualColumn (q : Data α) (v : Residual q) : Id :=
  v.2.val.1*v.2.val.2*restProduct q v.1

/-- Fixed before every selected assignment. Unsupported n has primary
Gauss row zero, and is the only support removed from this index set. -/
def keptResidual (q : Data α) : Finset (Residual q) :=
  Finset.univ.filter (fun v=>Supported (residualColumn q v))

theorem kept_supported (q : Data α) (v : keptResidual q) :
    Supported (residualColumn q v.val) := (Finset.mem_filter.mp v.property).2

def baseCoefficient (q : Data α) (x : Frozen q) (seed : Id) (v : Residual q) : ℂ :=
  residualCoefficient q.H q.R (frozenProduct q x) seed
    (fun w=>restProduct q w.1) (fun w=>w.2.val.1) (fun w=>w.2.val.2)
    (restWeight q) q.W₁ q.W₂ q.X₁ q.X₂ q.Y₁ q.Y₂ q.d v

/-- This vector contains neither selected assignment nor selected product.
The fixed-f character, Hecke height and residual reciprocity ray remain. -/
def commonVector (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (ξ : RayCharacter) (v : keptResidual q) : ℂ :=
  fixedCommonCoefficient (fun w : keptResidual q=>residualColumn q w.val)
    (fun w=>baseCoefficient q x seed w.val) (frozenProduct q x) τ t ξ v

/-- Exactly one selected summand of supplierExpansion, before any masks
are moved or any unsupported columns are omitted. -/
def selectedRow (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (t : ℝ) (k : O) : ℂ :=
  (∏j,frozenLiveAmplitude q.Lᶜ (amplitude q) x j.val (y j))*
    remainingSum q.J (frozenLiveAmplitude q.Lᶜ (amplitude q) x) y (fun r=>
      productKernel q.pool q.A q.B q.H q.R q.u q.W₁ q.W₂ q.X₁ q.X₂ q.Y₁ q.Y₂ q.d
        (fun I=>heightCoeff τ t I*primaryGaussRow I k)
        (joinAssignments (fun i=>i∈q.Lᶜ) x
          (joinAssignments (fun j=>j∈q.J) y r)))

def originalFamily (q : Data α) (x : Frozen q) (τ : Character) (t : ℝ) (k : O) : ℂ :=
  ∑y : Selected q,if Function.Injective y then selectedRow q x y τ t k else 0

theorem frozen_nonzero (q : Data α) (x : Frozen q) : frozenProduct q x≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (alphabet_prime q.pool q.prime (x i)).ne_zero

theorem frozen_divides (q : Data α) (x : Frozen q) (hx : Function.Injective x)
    (hw : frozenWeight q x≠0) : frozenProduct q x∣q.u := by
  let p : ↥(q.Lᶜ)→PrimeIdeal := fun i=>⟨(x i).val,alphabet_prime q.pool q.prime (x i)⟩
  apply suppliers_product_dvd p
    (fun i j he=>hx (Subtype.ext (congrArg (fun z : PrimeIdeal=>z.val) he))) q.u
  intro i
  have hi := slot_supplier_nonzero q.pool q.u q.L q.ν q.Wslot q.P i.val (x i)
    ((Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i))
  by_contra hn
  exact (Finset.mem_compl.mp i.property) (hi.mpr hn)

theorem selected_seed_coprime (q : Data α) (x : Frozen q) (seed : Id)
    (hseed : q.u=frozenProduct q x*seed) (y : Selected q)
    (hy : selectedWeight q y≠0) : IsCoprime seed (selectedProduct q y) := by
  have hu : IsCoprime q.u (selectedProduct q y) := by
    apply IsCoprime.prod_right
    intro j hj
    have hjL : j.val.val∈q.L := by simpa using j.val.property
    have hjn := (Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j)
    have hn := (slot_supplier_nonzero q.pool q.u q.L q.ν q.Wslot q.P j.val.val (y j) hjn).mp hjL
    exact ((prime_coprime ⟨(y j).val,alphabet_prime q.pool q.prime (y j)⟩ q.u).mpr hn).symm
  apply hu.of_isCoprime_of_dvd_left
  rw [hseed]
  exact dvd_mul_left seed (frozenProduct q x)

theorem base_fifth_free (q : Data α) (x : Frozen q) (seed : Id) (v : keptResidual q)
    (hv : baseCoefficient q x seed v.val≠0) :
    SexticSieve.PowerFree 5 (residualColumn q v.val) := by
  have hw : restWeight q v.val≠0 := (mul_ne_zero_iff.mp hv).1
  have hr : Function.Injective v.val.1 := by
    by_contra h
    exact hw (by simp only [restWeight,if_neg h])
  have hc : commonGate q.H q.R (frozenProduct q x) seed
      (restProduct q v.val.1) v.val.2.val.1 v.val.2.val.2 := by
    by_contra h
    exact hv (by simp only [baseCoefficient,residualCoefficient,commonKernel,if_neg h,mul_zero])
  have hn := (kept_supported q v).1
  have hAB : v.val.2.val.1*v.val.2.val.2≠0 := left_ne_zero_of_mul hn
  let p : {j : {i // i∉q.Lᶜ} // j∉q.J}→PrimeIdeal := fun j=>
    ⟨(v.val.1 j).val,alphabet_prime q.pool q.prime (v.val.1 j)⟩
  exact common_gate_fifth_free q.H q.R (frozenProduct q x) seed
    v.val.2.val.1 v.val.2.val.2 p
    (fun i j he=>hr (Subtype.ext (congrArg (fun z : PrimeIdeal=>z.val) he)))
    (left_ne_zero_of_mul hAB) (right_ne_zero_of_mul hAB) hc

theorem primary_product_zero (f D n : Id)
    (h : ¬Supported f ∨ ¬Supported D ∨ ¬Supported n) (k : O) :
    primaryGaussRow ((f*D)*n) k=0 := by
  have hn : ¬Supported ((f*D)*n) := by
    simp only [supported_mul_iff] at h ⊢
    tauto
  simp only [primaryGaussRow,dif_neg hn]

set_option maxHeartbeats 800000 in
/-- Reindex the ordinary pair together with the residual marked tuple.
The result still has the exact primary Gauss row and all original masks. -/
theorem selected_row_literal (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (hseed : q.u=frozenProduct q x*seed)
    (τ : Character) (t : ℝ) (k : O) :
    selectedRow q x y τ t k =
      ∑ v : Residual q,selectedWeight q y*restWeight q v*
        originalKernel q.H q.R (frozenProduct q x) seed (selectedProduct q y)
          (restProduct q v.1) v.2.val.1 v.2.val.2
          (idealRectangle q.W₁ q.W₂ q.X₁ q.X₂ q.Y₁ q.Y₂
            (q.d.1*v.2.val.1) (q.d.2*v.2.val.2)) *
        heightCoeff τ t ((frozenProduct q x*selectedProduct q y)*residualColumn q v)*
        primaryGaussRow ((frozenProduct q x*selectedProduct q y)*residualColumn q v) k := by
  unfold selectedRow remainingSum
  rw [Finset.mul_sum,Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext; simp)
  intro r hr
  have hholes := MixedSupplierReconstruction.selected_holes q.pool q.prime q.Lᶜ q.J
    (amplitude q) x y r
    (productKernel q.pool q.A q.B q.H q.R q.u q.W₁ q.W₂ q.X₁ q.X₂ q.Y₁ q.Y₂ q.d
      (fun I=>heightCoeff τ t I*primaryGaussRow I k)
      (joinAssignments (fun i=>i∈q.Lᶜ) x
        (joinAssignments (fun j=>j∈q.J) y r)))
  refine Eq.trans ?_ (hholes.trans ?_)
  · apply congrArg (fun z : ℂ=>
      (∏j,frozenLiveAmplitude q.Lᶜ (amplitude q) x j.val (y j))*z)
    split_ifs
    · apply congrArg (fun z : ℂ=>
        productKernel q.pool q.A q.B q.H q.R q.u q.W₁ q.W₂ q.X₁ q.X₂ q.Y₁ q.Y₂ q.d
          (fun I=>heightCoeff τ t I*primaryGaussRow I k)
          (joinAssignments (fun i=>i∈q.Lᶜ) x
            (joinAssignments (fun j=>j∈q.J) y r))*z)
      apply Finset.prod_congr (by ext; simp)
      intro j hj
      rfl
    · rfl
  unfold productKernel
  rw [←Finset.sum_coe_sort (q.A×ˢq.B)]
  by_cases hinj : Function.Injective r
  · simp only [hinj,ite_true,Finset.mul_sum,Finset.sum_mul,restWeight,selectedWeight]
    apply Finset.sum_congr (by ext; simp)
    intro n hn
    have hprod := packed_two_level_product q.pool q.Lᶜ q.J x y r n.val
    have hmark : (∏i,(values q.pool (joinAssignments (fun i=>i∈q.Lᶜ) x
        (joinAssignments (fun j=>j∈q.J) y r))) i)=
        frozenProduct q x*selectedProduct q y*restProduct q r := by
      have he := packed_two_level_product q.pool q.Lᶜ q.J x y r (1,1)
      simpa only [MixedTupleRows.pack_product,one_mul,mul_one,
        frozenProduct,selectedProduct,restProduct] using he
    simp only [ordinaryKernel,if_pos rfl,ite_true,hprod,hmark,hseed,originalKernel,
      frozenProduct,selectedProduct,restProduct,residualColumn]
    ring
  · simp only [hinj,ite_false,restWeight,mul_zero,zero_mul,Finset.sum_const_zero]

/-- A zero selected slot product gives zero before restriction or Gauss
separation. The whole selected assignment remains in the finite family. -/
theorem selected_row_zero (q : Data α) (x : Frozen q) (y : Selected q)
    (hy : selectedWeight q y=0) (τ : Character) (t : ℝ) (k : O) :
    selectedRow q x y τ t k=0 := by
  have hz : (∏j,frozenLiveAmplitude q.Lᶜ (amplitude q) x j.val (y j))=0 := by
    rw [frozen_product_mask q.pool q.Lᶜ (amplitude q) x (fun j : q.J=>j.val) y]
    change (if _ then selectedWeight q y else 0)=0
    simp only [hy,ite_self]
  simp only [selectedRow,hz,zero_mul]

theorem primary_supported_eq (I : Id) (hI : Supported I) (k : O) :
    primaryGaussRow I k=idealGauss I hI k := by
  rw [primaryGaussRow,dif_pos hI]
  rfl

def selectedScalar (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (t : ℝ) (k : O) (χ : RayCharacter) : ℂ :=
  ((if selectedGate q.R (frozenProduct q x) (selectedProduct q y) then 1 else 0)*
    selectedWeight q y)*heightCoeff τ t (frozenProduct q x*selectedProduct q y)*
    rayCharacter χ (primaryGenerator (frozenProduct q x*selectedProduct q y))*
    primaryGaussRow (frozenProduct q x*selectedProduct q y) k

/-- Exact completion onto one supported residual domain, independent of
selected y. Every discarded term has a zero actual primary Gauss row. -/
theorem selected_supported_row (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (hseed : q.u=frozenProduct q x*seed)
    (hf : Supported (frozenProduct q x)) (hD : Supported (selectedProduct q y))
    (hy : selectedWeight q y≠0) (τ : Character) (t : ℝ) (k : O) :
    selectedRow q x y τ t k =
      ∑ v : keptResidual q,
        ((if selectedGate q.R (frozenProduct q x) (selectedProduct q y) then 1 else 0)*
          selectedWeight q y)*baseCoefficient q x seed v.val*
        heightCoeff τ t ((frozenProduct q x*selectedProduct q y)*residualColumn q v.val)*
        (if IsCoprime (frozenProduct q x*selectedProduct q y) (residualColumn q v.val) then
          idealGauss ((frozenProduct q x*selectedProduct q y)*residualColumn q v.val)
            ((supported_mul_iff _ _).mpr
              ⟨(supported_mul_iff _ _).mpr ⟨hf,hD⟩,kept_supported q v⟩) k else 0) := by
  rw [selected_row_literal q x y seed hseed τ t k]
  let F : Residual q→ℂ := fun v=>selectedWeight q y*restWeight q v*
    originalKernel q.H q.R (frozenProduct q x) seed (selectedProduct q y)
      (restProduct q v.1) v.2.val.1 v.2.val.2
      (idealRectangle q.W₁ q.W₂ q.X₁ q.X₂ q.Y₁ q.Y₂ (q.d.1*v.2.val.1) (q.d.2*v.2.val.2))*
    heightCoeff τ t ((frozenProduct q x*selectedProduct q y)*residualColumn q v)*
    primaryGaussRow ((frozenProduct q x*selectedProduct q y)*residualColumn q v) k
  have hcut : (∑v : Residual q,F v)=∑v : keptResidual q,F v.val := by
    rw [Finset.sum_coe_sort,keptResidual,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hs : Supported (residualColumn q v)
    · simp only [hs,ite_true]
    · have hz := primary_product_zero (frozenProduct q x) (selectedProduct q y)
        (residualColumn q v) (Or.inr (Or.inr hs)) k
      simp only [hs,ite_false,F,hz,mul_zero]
  change (∑v : Residual q,F v)=_
  rw [hcut]
  have hgauss (v : keptResidual q) :
      primaryGaussRow ((frozenProduct q x*selectedProduct q y)*residualColumn q v.val) k =
      idealGauss ((frozenProduct q x*selectedProduct q y)*residualColumn q v.val)
        ((supported_mul_iff _ _).mpr
          ⟨(supported_mul_iff _ _).mpr ⟨hf,hD⟩,kept_supported q v⟩) k :=
    primary_supported_eq _ _ k
  simp only [F,hgauss]
  exact literal_row_eq Finset.univ q.H q.R (frozenProduct q x) seed (selectedProduct q y)
    hf hD (frozen_nonzero q x) (selected_seed_coprime q x seed hseed y hy)
    (fun v : keptResidual q=>restProduct q v.val.1)
    (fun v=>v.val.2.val.1) (fun v=>v.val.2.val.2) (kept_supported q)
    (selectedWeight q y) (fun v=>restWeight q v.val) q.W₁ q.W₂
    q.X₁ q.X₂ q.Y₁ q.Y₂ q.d τ t k

/-- Pointwise selected-row identity, including zero/unsupported cases.
Fifth-freeness is discharged by base_fifth_free from actual source masks. -/
theorem selected_fourth (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (hseed : q.u=frozenProduct q x*seed)
    (τ : Character) (t : ℝ) (k : O) :
    selectedRow q x y τ t k =
      ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
        selectedScalar q x y τ t k χ*
        gaussPolynomial Finset.univ
          (fun v : keptResidual q=>primaryGenerator (residualColumn q v.val))
          (fun v=>primary_supported _ (kept_supported q v))
          (commonVector q x seed τ t ξ) ((primaryGenerator (selectedProduct q y))^4*k) := by
  by_cases hf : Supported (frozenProduct q x)
  · by_cases hD : Supported (selectedProduct q y)
    · by_cases hy : selectedWeight q y=0
      · rw [selected_row_zero q x y hy τ t k]
        simp only [selectedScalar,hy,mul_zero,zero_mul,Finset.sum_const_zero]
      · rw [selected_supported_row q x y seed hseed hf hD hy τ t k]
        have he := fixed_supplier_row_fourth Finset.univ
          (fun v : keptResidual q=>residualColumn q v.val) (kept_supported q)
          ((if selectedGate q.R (frozenProduct q x) (selectedProduct q y) then 1 else 0)*
            selectedWeight q y) (fun v=>baseCoefficient q x seed v.val)
          (frozenProduct q x) (selectedProduct q y) hf hD τ t
          (fun v hv hb=>base_fifth_free q x seed v hb) k
        have hscalar (χ : RayCharacter) : selectedScalar q x y τ t k χ=
            (((if selectedGate q.R (frozenProduct q x) (selectedProduct q y) then 1 else 0)*
              selectedWeight q y)*heightCoeff τ t (frozenProduct q x*selectedProduct q y)*
              rayCharacter χ (primaryGenerator (frozenProduct q x*selectedProduct q y))*
              idealGauss (frozenProduct q x*selectedProduct q y)
                ((supported_mul_iff _ _).mpr ⟨hf,hD⟩) k) := by
          unfold selectedScalar
          rw [primary_supported_eq _ ((supported_mul_iff _ _).mpr ⟨hf,hD⟩)]
        refine Eq.trans ?_ (he.trans ?_)
        · apply Finset.sum_congr (by ext; simp)
          intro v hv
          rfl
        · apply Finset.sum_congr (by ext; simp)
          intro χ hχ
          apply Finset.sum_congr (by ext; simp)
          intro ξ hξ
          rw [←hscalar χ]
          apply congrArg (fun z : ℂ=>pairCoeff firstPhaseTable χ ξ*
            selectedScalar q x y τ t k χ*z)
          unfold gaussPolynomial
          apply Finset.sum_congr (by ext; simp)
          intro v hv
          rfl
    · have hz (n : Id) := primary_product_zero (frozenProduct q x) (selectedProduct q y)
        n (Or.inr (Or.inl hD)) k
      have hfn : ¬Supported (frozenProduct q x*selectedProduct q y) := by
        rw [supported_mul_iff]
        tauto
      have hscalar (χ : RayCharacter) : selectedScalar q x y τ t k χ=0 := by
        simp only [selectedScalar,primaryGaussRow,dif_neg hfn,mul_zero]
      rw [selected_row_literal q x y seed hseed τ t k]
      simp_rw [hz]
      simp only [hscalar,mul_zero,Finset.sum_const_zero,zero_mul]
  · have hz (n : Id) := primary_product_zero (frozenProduct q x) (selectedProduct q y)
      n (Or.inl hf) k
    have hfn : ¬Supported (frozenProduct q x*selectedProduct q y) := by
      rw [supported_mul_iff]
      tauto
    have hscalar (χ : RayCharacter) : selectedScalar q x y τ t k χ=0 := by
      simp only [selectedScalar,primaryGaussRow,dif_neg hfn,mul_zero]
    rw [selected_row_literal q x y seed hseed τ t k]
    simp_rw [hz]
    simp only [hscalar,mul_zero,Finset.sum_const_zero,zero_mul]

/-- Whole family: for fixed genuine supplier values x there exists ONE
residual seed and ONE vector per reciprocity ray, common to ALL selected
assignments y. No assumed coefficient factorization, analytic bound or
fifth-free premise occurs in the conclusion's hypotheses. -/
theorem actual_family_fourth (q : Data α) (x : Frozen q)
    (hx : Function.Injective x) (hw : frozenWeight q x≠0)
    (τ : Character) (t : ℝ) (k : O) :
    ∃seed : Id,q.u=frozenProduct q x*seed ∧
      originalFamily q x τ t k =
        ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
          ∑y : Selected q,if Function.Injective y then
            selectedScalar q x y τ t k χ*
              gaussPolynomial Finset.univ
                (fun v : keptResidual q=>primaryGenerator (residualColumn q v.val))
                (fun v=>primary_supported _ (kept_supported q v))
                (commonVector q x seed τ t ξ) ((primaryGenerator (selectedProduct q y))^4*k)
          else 0 := by
  obtain ⟨seed,hseed⟩ := frozen_divides q x hx hw
  refine ⟨seed,hseed,?_⟩
  unfold originalFamily
  have hrow (y : Selected q) := selected_fourth q x y seed hseed τ t k
  simp_rw [hrow]
  have hif (y : Selected q) :
      (if Function.Injective y then
        ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
          selectedScalar q x y τ t k χ*
          gaussPolynomial Finset.univ
            (fun v : keptResidual q=>primaryGenerator (residualColumn q v.val))
            (fun v=>primary_supported _ (kept_supported q v))
            (commonVector q x seed τ t ξ) ((primaryGenerator (selectedProduct q y))^4*k)
        else 0) =
      ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
        (if Function.Injective y then selectedScalar q x y τ t k χ*
          gaussPolynomial Finset.univ
            (fun v : keptResidual q=>primaryGenerator (residualColumn q v.val))
            (fun v=>primary_supported _ (kept_supported q v))
            (commonVector q x seed τ t ξ) ((primaryGenerator (selectedProduct q y))^4*k)
          else 0) := by
    by_cases hy : Function.Injective y
    · simp only [hy,ite_true,mul_assoc]
    · simp only [hy,ite_false,mul_zero,Finset.sum_const_zero]
  simp_rw [hif]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [Finset.mul_sum]

def fourthFamily (q : Data α) (x : Frozen q) (seed : Id)
    (τ : Character) (t : ℝ) (k : O) : ℂ :=
  ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
    ∑y : Selected q,if Function.Injective y then selectedScalar q x y τ t k χ*
      gaussPolynomial Finset.univ
        (fun v : keptResidual q=>primaryGenerator (residualColumn q v.val))
        (fun v=>primary_supported _ (kept_supported q v))
        (commonVector q x seed τ t ξ) ((primaryGenerator (selectedProduct q y))^4*k)
    else 0

/-- Includes the ACTUAL frozen scalar and its zero case. Thus every
injective frozen branch of supplierExpansion is covered, with all outer
weights preserved; no normalized or absolute-value coefficient replaces it. -/
theorem weighted_family_fourth (q : Data α) (x : Frozen q)
    (hx : Function.Injective x) (τ : Character) (t : ℝ) (k : O) :
    ∃seed : Id,(frozenWeight q x≠0 → q.u=frozenProduct q x*seed) ∧
      frozenWeight q x*originalFamily q x τ t k =
        frozenWeight q x*fourthFamily q x seed τ t k := by
  by_cases hw : frozenWeight q x=0
  · exact ⟨1,by simp only [hw,ne_eq,not_true_eq_false,false_implies],by rw [hw];ring⟩
  · obtain ⟨seed,hseed,he⟩ := actual_family_fourth q x hx hw τ t k
    exact ⟨seed,fun _=>hseed,congrArg (fun z : ℂ=>frozenWeight q x*z) he⟩

/-- Entire branch of the complete supplier partition, including all
frozen assignments and their zero/noninjective cases. A seed can depend
on frozen x, while the residual vector remains common over selected y. -/
theorem partition_branch_fourth (q : Data α) (τ : Character) (t : ℝ) (k : O) :
    ∃seeds : Frozen q→Id,
      (∀x,Function.Injective x→frozenWeight q x≠0→q.u=frozenProduct q x*seeds x) ∧
      (∑x : Frozen q,if Function.Injective x then
        frozenWeight q x*originalFamily q x τ t k else 0) =
      ∑x : Frozen q,if Function.Injective x then
        frozenWeight q x*fourthFamily q x (seeds x) τ t k else 0 := by
  have hchoose (x : Frozen q) : ∃seed : Id,
      (Function.Injective x→frozenWeight q x≠0→q.u=frozenProduct q x*seed) ∧
      (if Function.Injective x then frozenWeight q x*originalFamily q x τ t k else 0)=
      (if Function.Injective x then frozenWeight q x*fourthFamily q x seed τ t k else 0) := by
    by_cases hx : Function.Injective x
    · obtain ⟨seed,hs,he⟩ := weighted_family_fourth q x hx τ t k
      exact ⟨seed,fun _=>hs,by simpa only [hx,ite_true] using he⟩
    · exact ⟨1,fun hh=>False.elim (hx hh),by simp only [hx,ite_false]⟩
  choose seeds hs using hchoose
  refine ⟨seeds,fun x=> (hs x).1,?_⟩
  apply Finset.sum_congr rfl
  intro x hx
  exact (hs x).2

end
end Candidate.FourthPower.MixedSupplierFourthRow
