/- Copyright (c) 2026 Sil. Apache-2.0.
Exact common-vector/source interfaces. 
The cubic character has a linear fixed-supplier conductor. Supplier
holes are removed ONLY after genuine extraction makes them redundant.
-/
import Candidate.FourthPower.MixedSupplierPositive
import Candidate.FourthPower.ReferenceCubicCharacter
import Candidate.FourthPower.MixedCommonEnergy
import Candidate.FourthPower.MixedLiveRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedSupplierSource
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentLiveDomain
open CenteredMomentFixedRay RayFourExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentChildRows CenteredMomentSecondChildProfile
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
open QRH.Record1252270103KernelMass
open MixedSupplierKernel MixedSupplierPartition MixedSupplierSplit MixedSupplierFourthRow
open MixedSupplierPositive MixedCommonEnergy MixedCommonRestriction MixedCommonCoefficient
open MixedCommonAllocation MixedSupplierReconstruction MixedTupleRows
open CenteredMomentSourceRectangle CenteredMomentRectangle
open MixedSelectedCommon (primary_supported)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The fixed f hole is a whole-column puncture R*f. No seed mask is lost. -/
theorem common_gate_original (H R f seed M A B : Id) :
    commonGate H R f seed M A B ↔
      IsCoprime f R ∧ restriction H M A B ∧
        IsCoprime (A*B*M) (R*f) ∧ seed∣A*B*M := by
  simp only [commonGate,restriction,IsCoprime.mul_left_iff,IsCoprime.mul_right_iff]
  have ha : IsCoprime A f ↔ IsCoprime f A := ⟨IsCoprime.symm,IsCoprime.symm⟩
  have hb : IsCoprime B f ↔ IsCoprime f B := ⟨IsCoprime.symm,IsCoprime.symm⟩
  have hm : IsCoprime M f ↔ IsCoprime f M := ⟨IsCoprime.symm,IsCoprime.symm⟩
  simp only [ha,hb,hm]
  tauto

theorem common_kernel_original (H R f seed M A B : Id) (rectangle : ℂ) :
    commonKernel H R f seed M A B rectangle=
      (if IsCoprime f R then (1:ℂ) else 0)*restrictionWeight H M A B*
        (if IsCoprime (A*B*M) (R*f) then 1 else 0)*rectangle*
        (if seed∣A*B*M then 1 else 0) := by
  rw [commonKernel,common_gate_original]
  unfold restrictionWeight
  split_ifs <;> simp_all only [zero_mul,mul_zero,one_mul,mul_one] <;> tauto

/-- Construct the fixed cubic-and-ray character before choosing height,
column, selected assignment, or frequency. Its modulus is linear in N(f).
In particular we do not use a row presentation with parameter f^2. -/
theorem common_height_character (τ : Character) (f : Id) (hf : Supported f)
    (ξ : RayCharacter) :
    ∃ψ : Character,
      ψ.modulus.absNorm ≤ τ.modulus.absNorm*
        (ReferenceCubicCharacter.conductorConstant*f.absNorm)*
        (Ideal.span {(12:O)}).absNorm ∧
      ∀I : Id,Supported I → ∀t : ℝ,
        heightCoeff ψ t I=heightCoeff τ t I*
          (idealRowHom (primaryGenerator f) I)^2*rayCharacter ξ (primaryGenerator I) := by
  obtain ⟨r⟩ := ReferenceCubicCharacter.data_exists (primaryGenerator f)
    (supported_primaryGenerator_ne_zero f hf)
  let ψ := childCharacter (τ.product r.character) ξ
  refine ⟨ψ,?_,?_⟩
  · have hr : r.character.modulus.absNorm≤
        ReferenceCubicCharacter.conductorConstant*f.absNorm := by
      simpa only [primary_span_supported f hf] using r.modulus_bound
    have h₁ := ReferenceCubicCharacter.product_modulus_bound τ r.character
    have h₂ := ReferenceCubicCharacter.product_modulus_bound
      (τ.product r.character) (primaryRayCharacter ξ)
    apply h₂.trans
    rw [primaryRayCharacter_modulus]
    exact Nat.mul_le_mul_right _
      (h₁.trans (Nat.mul_le_mul_left _ hr))
  · intro I hI t
    change idealCoeff (childCharacter (τ.product r.character) ξ) I*
      (I.absNorm:ℂ)^(Complex.I*t)=_
    rw [child_ideal_primary _ ξ I hI,idealCoeff_product,r.on_supported I hI]
    unfold heightCoeff
    ring

abbrev RestIndex (q : MixedSupplierFourthRow.Data α) :=
  {j : {i // i∉q.Lᶜ} // j∉q.J}

def residualTuple (q : MixedSupplierFourthRow.Data α) (v : Residual q) :
    Tuple (RestIndex q) := MixedTupleRows.pack (fun j=>(v.1 j).val) v.2.val

def restCharacters (q : MixedSupplierFourthRow.Data α) (j : RestIndex q) (I : Id) : ℂ :=
  if I∈q.pool j.val.val then supplierCharacters q.u q.L q.ν j.val.val I else 0

def residualProfile (q : MixedSupplierFourthRow.Data α) (x : Frozen q) (seed : Id) :
    Tuple (RestIndex q)→ℂ := fun v=>tupleWeight q.H v*
      profileCoefficient (q.R*frozenProduct q x) (restCharacters q)
        (fun j=>q.Wslot j.val.val) (fun j=>q.P j.val.val) q.W₁ q.W₂
        q.X₁ q.X₂ q.Y₁ q.Y₂ q.d.1 q.d.2 seed v

theorem residual_tuple_product (q : MixedSupplierFourthRow.Data α) (v : Residual q) :
    finiteTupleProduct (residualTuple q v)=residualColumn q v :=
  MixedTupleRows.pack_product _ _

theorem residual_tuple_injective (q : MixedSupplierFourthRow.Data α) :
    Function.Injective (residualTuple q) := by
  intro v w he
  apply Prod.ext
  · funext j
    exact Subtype.ext (congrFun he (Sum.inl j))
  · apply Subtype.ext
    apply Prod.ext
    · exact congrFun he (Sum.inr 0)
    · exact congrFun he (Sum.inr 1)

/-- This generic lemma expands only the ordinary kernel, on an arbitrary
plain finite index type. It never unfolds a Data-dependent tuple profile. -/
theorem common_kernel_packed (H R f seed : Id)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (p : α→Id) (n : Id×Id) :
    commonKernel H R f seed (∏i,p i) n.1 n.2
      (idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (d.1*n.1) (d.2*n.2))=
      (if IsCoprime f R then (1:ℂ) else 0)*
        ordinaryKernel H (R*f) seed (finiteTupleProduct (MixedTupleRows.pack p n))
          W₁ W₂ X₁ X₂ Y₁ Y₂ d p n := by
  rw [common_kernel_original]
  unfold ordinaryKernel
  rw [if_pos rfl,MixedTupleRows.pack_product]
  ring

theorem base_coefficient_profile (q : MixedSupplierFourthRow.Data α)
    (x : Frozen q) (seed : Id) (v : Residual q) :
    baseCoefficient q x seed v=
      (if IsCoprime (frozenProduct q x) q.R then (1:ℂ) else 0)*
        residualProfile q x seed (residualTuple q v) := by
  let p : RestIndex q→Id := fun j=>(v.1 j).val
  let K : ℂ := ordinaryKernel q.H (q.R*frozenProduct q x) seed
    (finiteTupleProduct (MixedTupleRows.pack p v.2.val)) q.W₁ q.W₂
    q.X₁ q.X₂ q.Y₁ q.Y₂ q.d p v.2.val
  let a : ℂ := ∏j : RestIndex q,amplitude q j.val.val (v.1 j)
  let c : ℂ := if IsCoprime (frozenProduct q x) q.R then 1 else 0
  have hi : Function.Injective p↔Function.Injective v.1 := by
    constructor
    · intro h i j hij
      exact h (congrArg Subtype.val hij)
    · intro h i j hij
      exact h (Subtype.ext hij)
  have hprod : (∏j : RestIndex q,restCharacters q j (p j)*
      q.Wslot j.val.val (((p j).absNorm:ℝ)/q.P j.val.val))=a := by
    apply Finset.prod_congr rfl
    intro j hj
    dsimp only [p,restCharacters,amplitude,slotAmplitude]
    split_ifs <;> simp only [zero_mul]
  have hprofile : residualProfile q x seed (residualTuple q v)=
      if Function.Injective v.1 then K*a else 0 := by
    have he := packed_coefficient q.H (q.R*frozenProduct q x) seed
      (finiteTupleProduct (MixedTupleRows.pack p v.2.val)) (restCharacters q)
      (fun j : RestIndex q=>q.Wslot j.val.val) (fun j=>q.P j.val.val)
      q.W₁ q.W₂ q.X₁ q.X₂ q.Y₁ q.Y₂ q.d p v.2.val
    rw [ite_eq_left rfl] at he
    simp only [hi,hprod] at he
    exact he
  have hkernel : commonKernel q.H q.R (frozenProduct q x) seed
      (restProduct q v.1) v.2.val.1 v.2.val.2
      (idealRectangle q.W₁ q.W₂ q.X₁ q.X₂ q.Y₁ q.Y₂
        (q.d.1*v.2.val.1) (q.d.2*v.2.val.2))=c*K :=
    common_kernel_packed q.H q.R (frozenProduct q x) seed q.W₁ q.W₂
      q.X₁ q.X₂ q.Y₁ q.Y₂ q.d p v.2.val
  change (if Function.Injective v.1 then a else 0)*_=c*_
  rw [hkernel,hprofile]
  by_cases hinj : Function.Injective v.1
  · simp only [hinj,ite_true]
    ring
  · simp only [hinj,ite_false,zero_mul,mul_zero]


/-- A finite column pool and actual fiber sum for this residual vector. -/
def commonColumns (q : MixedSupplierFourthRow.Data α) : Finset Id :=
  Finset.univ.image (residualColumn q)

def commonColumn (q : MixedSupplierFourthRow.Data α) (x : Frozen q) (seed I : Id) : ℂ :=
  ∑v∈Finset.univ.filter (fun v : Residual q=>residualColumn q v=I),
    baseCoefficient q x seed v

def commonTuples (q : MixedSupplierFourthRow.Data α) : Finset (Tuple (RestIndex q)) :=
  Finset.univ.image (residualTuple q)

theorem common_columns_tuple (q : MixedSupplierFourthRow.Data α) :
    finiteColumns (commonTuples q)=commonColumns q := by
  unfold finiteColumns commonTuples commonColumns
  rw [Finset.image_image]
  apply congrArg (fun F : Residual q→Id=>Finset.univ.image F)
  funext v
  exact residual_tuple_product q v

/-- The grouped coefficient is literally the standard tuple-weighted
profile, with the residual seed and the R*f puncture. The finite alphabet
contains zero-extended marked pools; restCharacters keeps those zeroes. -/
theorem common_column_profile (q : MixedSupplierFourthRow.Data α)
    (x : Frozen q) (seed I : Id) :
    commonColumn q x seed I=
      (if IsCoprime (frozenProduct q x) q.R then (1:ℂ) else 0)*
        finiteColumnCoefficient (commonTuples q) (residualProfile q x seed) I := by
  unfold commonColumn finiteColumnCoefficient commonTuples
  rw [Finset.sum_filter,Finset.sum_filter,
    Finset.sum_image (fun a ha b hb he=>residual_tuple_injective q he),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [residual_tuple_product]
  by_cases h : residualColumn q v=I
  · simp only [h,ite_true]
    exact base_coefficient_profile q x seed v
  · simp only [h,ite_false,mul_zero]

theorem common_column_sum (q : MixedSupplierFourthRow.Data α)
    (x : Frozen q) (seed : Id) (F : Id→ℂ) :
    (∑I∈commonColumns q,commonColumn q x seed I*F I)=
      ∑v : Residual q,baseCoefficient q x seed v*F (residualColumn q v) := by
  calc
    _=∑I∈commonColumns q,∑v∈Finset.univ.filter
        (fun v : Residual q=>residualColumn q v=I),
        baseCoefficient q x seed v*F (residualColumn q v) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [commonColumn,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _=_ := Finset.sum_fiberwise_of_maps_to
      (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

/-- Exact actual-column identity for the common polynomial. The entire
fixed f remains in ψ, with the linear conductor bound; the independent
frequency k is never multiplied by f^4. No energy bound is assumed. -/
theorem common_polynomial_source (q : MixedSupplierFourthRow.Data α)
    (x : Frozen q) (seed : Id) (τ : Character)
    (hf : Supported (frozenProduct q x)) (ξ : RayCharacter) :
    ∃ψ : Character,
      ψ.modulus.absNorm ≤ τ.modulus.absNorm*
        (ReferenceCubicCharacter.conductorConstant*(frozenProduct q x).absNorm)*
        (Ideal.span {(12:O)}).absNorm ∧
      ∀t : ℝ,∀k : O,commonPolynomial q x seed τ t ξ k=
        gaussPolynomial Finset.univ (sourceGenerator (commonColumns q))
          (sourceGenerator_supported (commonColumns q))
          (fun I : supportedColumns (commonColumns q)=>commonColumn q x seed I*
            heightCoeff ψ t I) k := by
  obtain ⟨ψ,hψ,hheight⟩ := common_height_character τ (frozenProduct q x) hf ξ
  refine ⟨ψ,hψ,?_⟩
  intro t k
  rw [source_gauss_sum (commonColumns q) (fun I=>commonColumn q x seed I*heightCoeff ψ t I) k]
  have hgroup := common_column_sum q x seed (fun I=>heightCoeff ψ t I*primaryGaussRow I k)
  simp only [←mul_assoc] at hgroup
  rw [hgroup]
  have hactual : commonPolynomial q x seed τ t ξ k=
      ∑v : keptResidual q,baseCoefficient q x seed v.val*
        heightCoeff ψ t (residualColumn q v.val)*primaryGaussRow (residualColumn q v.val) k := by
    unfold commonPolynomial gaussPolynomial
    apply Finset.sum_congr rfl
    intro v hv
    rw [primary_supported_eq _ (kept_supported q v),hheight _ (kept_supported q v) t]
    unfold commonVector fixedCommonCoefficient MixedSelectedCommon.idealGauss
    ring
  rw [hactual]
  rw [Finset.sum_coe_sort (keptResidual q) (fun v : Residual q=>
    baseCoefficient q x seed v*heightCoeff ψ t (residualColumn q v)*primaryGaussRow (residualColumn q v) k)]
  rw [keptResidual,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hs : Supported (residualColumn q v)
  · simp only [hs,ite_true]
  · simp only [primaryGaussRow,hs,ite_false,dite_false,mul_zero]

/-- The raw residual polynomial uses exactly the ordinary volume times
the surviving slot volumes. No second normalization of its slots occurs. -/
theorem common_normalization (q : MixedSupplierFourthRow.Data α)
    (x : Frozen q) (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (k : O)
    (hT : 0<q.X₁*q.X₂) (hP : ∀j : RestIndex q,0<q.P j.val.val) :
    ‖MixedLiveNormalization.normalization (q.X₁*q.X₂)
        (fun j : RestIndex q=>q.P j.val.val)*commonPolynomial q x seed τ t ξ k‖^2=
      ‖commonPolynomial q x seed τ t ξ k‖^2/
        ((q.X₁*q.X₂)*∏j : RestIndex q,q.P j.val.val) := by
  rw [norm_mul,mul_pow,MixedLiveNormalization.normalization_sq _ hT _ hP]
  ring

/-- Every remaining marked slot avoids u. This predicate is NOT a
fixed-cardinality hole set and its cardinality is never bounded here. -/
def avoid (u : Id) (ν : α→Id→ℂ) (i : α) (I : Id) : ℂ :=
  if I∣u then 0 else ν i I

theorem actual_remaining_character (q : MixedSupplierFourthRow.Data α)
    (j : {j : {i // i∉q.Lᶜ} // j∉q.J}) (I : Id) :
    supplierCharacters q.u q.L q.ν j.val.val I=avoid q.u q.ν j.val.val I := by
  have hj : j.val.val∈q.L := by simpa using j.val.property
  simp only [supplierCharacters,KernelHoleCompletion.mixed,hj,ite_true,
    KernelHoleCompletion.good,avoid]

/-- A prime marked slot divides the tuple product. Thus, if u divides
the existing whole-column puncture, its supplier hole is already zero. -/
theorem profile_avoid (R u seed : Id) (hu : u∣R)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id)
    (v : Tuple α) (hp : ∀i,Prime (v (Sum.inl i))) :
    profileCoefficient R (avoid u ν) Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v=
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v := by
  by_cases hc : IsCoprime (finiteTupleProduct v) R
  · have hslot (i : α) : avoid u ν i (v (Sum.inl i))=ν i (v (Sum.inl i)) := by
      apply if_neg
      intro hd
      have hdprod : v (Sum.inl i)∣finiteTupleProduct v :=
        Finset.dvd_prod_of_mem v (Finset.mem_univ (Sum.inl i))
      have hcop := hc.of_isCoprime_of_dvd_left hdprod
      exact (prime_coprime ⟨v (Sum.inl i),hp i⟩ R).mp hcop (hd.trans hu)
    unfold profileCoefficient
    simp_rw [hslot]
  · simp only [profileCoefficient,hc,ite_false,mul_zero,zero_mul]

/-- Supplier masks on a genuine frozen allocation stay as a scalar. -/
def frozenAvoid (u : Id) (B : Tuple α) : ℂ :=
  ∏i∈Finset.univ.filter (fun i=>B (Sum.inl i)≠1),
    if B (Sum.inl i)∣u then 0 else 1

theorem frozen_coefficient_avoid (u : Id) (B : Tuple α) (G R : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ) :
    frozenCoefficient B G R (avoid u ν) Wslot P=
      frozenAvoid u B*frozenCoefficient B G R ν Wslot P := by
  have he (i : α) : avoid u ν i (B (Sum.inl i))*
      Wslot i ((B (Sum.inl i)).absNorm/P i)=
      (if B (Sum.inl i)∣u then (0:ℂ) else 1)*
        (ν i (B (Sum.inl i))*Wslot i ((B (Sum.inl i)).absNorm/P i)) := by
    unfold avoid
    split_ifs <;> ring
  unfold frozenCoefficient frozenAvoid
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  ring

theorem frozen_avoid_norm (u : Id) (B : Tuple α) : ‖frozenAvoid u B‖≤1 := by
  rw [frozenAvoid,norm_prod]
  calc
    _ ≤ ∏i∈Finset.univ.filter (fun i=>B (Sum.inl i)≠1),(1:ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
      intro i hi
      split_ifs <;> norm_num
    _ = 1 := by simp

theorem live_profile_avoid (u G R : Id) (hu : u∣R*G)
    (B : Tuple α) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id)
    (v : Tuple (liveIndices B)) (hp : ∀i,Prime (v (Sum.inl i))) :
    liveProfile B G R (avoid u ν) Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v=
      liveProfile B G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v := by
  exact profile_avoid (R*G) u 1 hu (fun i : liveIndices B=>ν i.val)
    (fun i=>Wslot i.val) (fun i=>P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) v hp

/-- The actual u=f*seed and seed|G imply the exact live-hole condition,
using the whole puncture (R*f)*G, with no radical/cardinality relaxation. -/
theorem supplier_dvd_puncture (R f seed u G : Id)
    (hu : u=f*seed) (hseed : seed∣G) : u∣(R*f)*G := by
  rw [hu,mul_assoc]
  exact (mul_dvd_mul_left f hseed).trans (dvd_mul_left (f*G) R)

/-- Concrete restricted common-column replacement. All frozen supplier
masks remain visible. The live row is the existing unmasked canonical
coefficient, and its old tupleWeight, divisor masks and profile survive. -/
theorem extracted_avoiding_column (H : Id) (S : (α⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (u G R seed I : Id) (hG : G≠0) (hI : I≠0) (hseed : seed∣G) (hu : u∣R*G)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    (if IsCoprime G I then finiteColumnCoefficient (Fintype.piFinset S)
      (fun v=>tupleWeight H v*profileCoefficient R (avoid u ν) Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ seed v) (G*I) else 0)=
      ∑B : actualAllocations S G,
        frozenAvoid u B.val*((MixedCommonCoefficient.frozenWeight H B.val*
          frozenCoefficient B.val G R ν Wslot P)*
          finiteColumnCoefficient
            (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1)
            (fun v=>tupleWeight H v*liveProfile B.val G R ν Wslot P W₁ W₂
              X₁ X₂ Y₁ Y₂ B₁ B₂ v) I) := by
  rw [punctured_restricted_column H S hS hp G R seed I hG hI hseed]
  apply Finset.sum_congr rfl
  intro B hB
  rw [frozen_coefficient_avoid]
  have hcol : finiteColumnCoefficient
      (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1)
      (fun v=>tupleWeight H v*liveProfile B.val G R (avoid u ν) Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ v) I=
      finiteColumnCoefficient
      (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1)
      (fun v=>tupleWeight H v*liveProfile B.val G R ν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ v) I := by
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only
    rw [live_profile_avoid u G R hu]
    intro i
    have hv' := (Finset.mem_filter.mp hv).1
    rw [MixedLiveRows.live_box] at hv'
    exact hp i.val _ (Fintype.mem_piFinset.mp hv' (Sum.inl i))
  rw [hcol]
  ring

end
end Candidate.FourthPower.MixedSupplierSource
