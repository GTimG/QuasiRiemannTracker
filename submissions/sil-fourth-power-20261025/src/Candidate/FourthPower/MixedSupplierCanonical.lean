/- Copyright (c) 2026 Sil. Apache-2.0.
Exact zero-extension completion of the supplier residual coefficient.

-/
import Candidate.FourthPower.MixedSupplierSource
import Candidate.FourthPower.MixedAllocationCost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedSupplierCanonical
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CompletedGauss CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentLiveDomain CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
open CenteredMomentOriginalRadialComparison
open CenteredMomentSourceRectangle
open CenteredMomentHeckeColumnWindow
open QRH.Record1252270103KernelMass
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierSplit MixedSupplierPartition
open MixedCommonCoefficient MixedCommonRestriction MixedTupleRows MixedHeightEnergy
open MixedLiteralAllocation MixedLiveNormalization MixedRestrictedDictionary MixedDivisorMask
open MixedOriginalSource MixedAllocationCost
open MixedCommonSource
open MixedSupplierPositive MixedSupplierReconstruction
open CenteredMomentFixedRay RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The existing supplier alphabet is a literal finite product box.
It contains the true remaining pools, whose extra points carry zeroes. -/
theorem common_tuples_box (q : MixedSupplierFourthRow.Data α) :
    commonTuples q=Fintype.piFinset
      (pools (fun _ : RestIndex q=>markedUniverse q.pool) q.A q.B) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro j
    cases j with
    | inl i=>exact (w.1 i).property
    | inr j=>
      fin_cases j
      · exact (Finset.mem_product.mp w.2.property).1
      · exact (Finset.mem_product.mp w.2.property).2
  · intro hv
    have hp (j : RestIndex q) : v (Sum.inl j)∈markedUniverse q.pool :=
      Fintype.mem_piFinset.mp hv (Sum.inl j)
    have hA : v (Sum.inr 0)∈q.A := Fintype.mem_piFinset.mp hv (Sum.inr 0)
    have hB : v (Sum.inr 1)∈q.B := Fintype.mem_piFinset.mp hv (Sum.inr 1)
    let w : Residual q := (fun j=>⟨v (Sum.inl j),hp j⟩,
      ⟨(v (Sum.inr 0),v (Sum.inr 1)),Finset.mem_product.mpr ⟨hA,hB⟩⟩)
    apply Finset.mem_image.mpr
    refine ⟨w,Finset.mem_univ _,?_⟩
    funext j
    cases j with
    | inl i=>rfl
    | inr j=>fin_cases j <;> rfl

/-- An invalid slot has a zero factor in the ORIGINAL coefficient. -/
theorem profile_zeroextend (pool : α→Finset Id) (R seed : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) (v : Tuple α) :
    profileCoefficient R (fun i I=>if I∈pool i then ν i I else 0)
      Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v=
      if ∀i,v (Sum.inl i)∈pool i then
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v else 0 := by
  by_cases h : ∀i,v (Sum.inl i)∈pool i
  · simp only [profileCoefficient,h,implies_true,ite_true]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    have hz : (∏j,(if v (Sum.inl j)∈pool j then ν j (v (Sum.inl j)) else 0)*
        Wslot j ((v (Sum.inl j)).absNorm/P j))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi,zero_mul])
    simp only [profileCoefficient,hz,zero_mul]

theorem completed_pool_filter (pool : α→Finset Id) (V A B : Finset Id)
    (hp : ∀i,pool i⊆V) :
    (Fintype.piFinset (pools (fun _=>V) A B)).filter
      (fun v=>∀i,v (Sum.inl i)∈pool i)=Fintype.piFinset (pools pool A B) := by
  ext v
  simp only [Finset.mem_filter,Fintype.mem_piFinset]
  constructor
  · rintro ⟨h,hm⟩ j
    cases j with
    | inl i=>exact hm i
    | inr j=>exact h (Sum.inr j)
  · intro h
    refine ⟨?_,fun i=>h (Sum.inl i)⟩
    intro j
    cases j with
    | inl i=>exact hp i (h (Sum.inl i))
    | inr j=>exact h (Sum.inr j)

/-- Finite-column zero-extension, before any squared norm is taken.
All tuple restrictions and the exact column delta stay in the sum. -/
theorem finite_column_zeroextend (pool : α→Finset Id) (V A B : Finset Id)
    (hp : ∀i,pool i⊆V) (H R seed I : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    finiteColumnCoefficient (Fintype.piFinset (pools (fun _=>V) A B))
      (fun v=>tupleWeight H v*profileCoefficient R
        (fun i I=>if I∈pool i then ν i I else 0) Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ seed v) I=
      finiteColumnCoefficient (Fintype.piFinset (pools pool A B))
        (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ B₁ B₂ seed v) I := by
  rw [←completed_pool_filter pool V A B hp]
  unfold finiteColumnCoefficient
  rw [Finset.filter_filter]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  rw [profile_zeroextend]
  by_cases hm : ∀i,v (Sum.inl i)∈pool i <;>
    by_cases hd : finiteTupleProduct v=I <;>
      simp only [hm,hd,implies_true,and_true,and_false,ite_true,ite_false,mul_zero]

/-- The actual grouped residual coefficient now has exactly its original
finite slot pools, with only the real supplier holes left in nu. -/
theorem common_column_pool (q : MixedSupplierFourthRow.Data α)
    (x : Frozen q) (seed I : Id) :
    commonColumn q x seed I=
      (if IsCoprime (frozenProduct q x) q.R then (1:ℂ) else 0)*
        finiteColumnCoefficient (Fintype.piFinset
          (pools (fun j : RestIndex q=>q.pool j.val.val) q.A q.B))
          (fun v=>tupleWeight q.H v*profileCoefficient (q.R*frozenProduct q x)
            (fun j : RestIndex q=>avoid q.u q.ν j.val.val)
            (fun j=>q.Wslot j.val.val) (fun j=>q.P j.val.val) q.W₁ q.W₂
            q.X₁ q.X₂ q.Y₁ q.Y₂ q.d.1 q.d.2 seed v) I := by
  rw [common_column_profile,common_tuples_box]
  apply congrArg (fun z : ℂ=>(if IsCoprime (frozenProduct q x) q.R then 1 else 0)*z)
  unfold residualProfile restCharacters
  simp_rw [actual_remaining_character]
  exact finite_column_zeroextend _ (markedUniverse q.pool) q.A q.B
    (fun j I hI=>mem_markedUniverse q.pool j.val.val I hI) q.H
    (q.R*frozenProduct q x) seed I _ _ _ q.W₁ q.W₂
    q.X₁ q.X₂ q.Y₁ q.Y₂ q.d.1 q.d.2

/-- Direct originalColumn interface. The three equalities are geometric
source data, supplied by sourcePools or source_live_box; no coefficient
equality, support relaxation, or energy estimate is a premise. -/
theorem common_column_original (q : MixedSupplierFourthRow.Data α)
    (x : Frozen q) (seed I : Id) (S H : Finset PrimeIdeal)
    (hd : q.d.1≠0 ∧ q.d.2≠0) (b : ℝ)
    (hH : q.H=punctureProduct S H)
    (hA : q.A=residualPool q.d.1 hd.1 (plainSupportPool b q.X₁ q.Y₁))
    (hB : q.B=residualPool q.d.2 hd.2 (plainSupportPool b q.X₂ q.Y₂)) :
    commonColumn q x seed I=
      (if IsCoprime (frozenProduct q x) q.R then (1:ℂ) else 0)*
        originalColumn S H (fun j : RestIndex q=>q.pool j.val.val) q.d hd
          (q.R*frozenProduct q x) seed (fun j : RestIndex q=>avoid q.u q.ν j.val.val)
          (fun j=>q.Wslot j.val.val) (fun j=>q.P j.val.val) q.W₁ q.W₂
          b q.X₁ q.X₂ q.Y₁ q.Y₂ I := by
  rw [common_column_pool,hH,hA,hB]
  rfl

theorem remaining_columns_subset (q : MixedSupplierFourthRow.Data α) :
    finiteColumns (Fintype.piFinset
      (pools (fun j : RestIndex q=>q.pool j.val.val) q.A q.B))⊆commonColumns q := by
  rw [←common_columns_tuple,common_tuples_box]
  intro I hI
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hI
  refine Finset.mem_image.mpr ⟨v,Fintype.mem_piFinset.mpr ?_,he⟩
  intro j
  cases j with
  | inl i=>exact mem_markedUniverse q.pool i.val.val _ (Fintype.mem_piFinset.mp hv (Sum.inl i))
  | inr i=>exact Fintype.mem_piFinset.mp hv (Sum.inr i)

/-- The common polynomial itself, now on canonical sourcePools and the
literal originalColumn coefficient. There is no enlarged pool or zero
extension remaining on the right. Fixed f stays in the outer character. -/
theorem common_polynomial_original (q : MixedSupplierFourthRow.Data α)
    (x : Frozen q) (seed : Id) (τ : Character)
    (hf : Supported (frozenProduct q x)) (ξ : RayCharacter)
    (S H : Finset PrimeIdeal) (hd : q.d.1≠0 ∧ q.d.2≠0) (b : ℝ)
    (hH : q.H=punctureProduct S H)
    (hA : q.A=residualPool q.d.1 hd.1 (plainSupportPool b q.X₁ q.Y₁))
    (hB : q.B=residualPool q.d.2 hd.2 (plainSupportPool b q.X₂ q.Y₂)) :
    ∃ψ : Character,
      ψ.modulus.absNorm≤τ.modulus.absNorm*
        (ReferenceCubicCharacter.conductorConstant*(frozenProduct q x).absNorm)*
        (Ideal.span {(12:O)}).absNorm ∧
      let Q := finiteColumns (Fintype.piFinset (sourcePools
        (fun j : RestIndex q=>q.pool j.val.val) q.d hd b q.X₁ q.X₂ q.Y₁ q.Y₂))
      let β := originalColumn S H (fun j : RestIndex q=>q.pool j.val.val) q.d hd
        (q.R*frozenProduct q x) seed (fun j : RestIndex q=>avoid q.u q.ν j.val.val)
        (fun j=>q.Wslot j.val.val) (fun j=>q.P j.val.val) q.W₁ q.W₂
        b q.X₁ q.X₂ q.Y₁ q.Y₂
      ∀t : ℝ,∀k : O,commonPolynomial q x seed τ t ξ k=
        (if IsCoprime (frozenProduct q x) q.R then (1:ℂ) else 0)*
          gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
            (fun I : supportedColumns Q=>β I*heightCoeff ψ t I) k := by
  obtain ⟨ψ,hψ,he⟩ := common_polynomial_source q x seed τ hf ξ
  refine ⟨ψ,hψ,?_⟩
  dsimp only
  let Q := finiteColumns (Fintype.piFinset (sourcePools
    (fun j : RestIndex q=>q.pool j.val.val) q.d hd b q.X₁ q.X₂ q.Y₁ q.Y₂))
  let β := originalColumn S H (fun j : RestIndex q=>q.pool j.val.val) q.d hd
    (q.R*frozenProduct q x) seed (fun j : RestIndex q=>avoid q.u q.ν j.val.val)
    (fun j=>q.Wslot j.val.val) (fun j=>q.P j.val.val) q.W₁ q.W₂ b q.X₁ q.X₂ q.Y₁ q.Y₂
  have hsub : Q⊆commonColumns q := by
    simpa only [Q,sourcePools,hA,hB] using remaining_columns_subset q
  have hmem (I : Id) (hn : β I≠0) : I∈Q := finite_column_mem _ _ I hn
  have hid (I : Id) : commonColumn q x seed I=
      (if IsCoprime (frozenProduct q x) q.R then (1:ℂ) else 0)*β I :=
    common_column_original q x seed I S H hd b hH hA hB
  intro t k
  rw [he t k,
    source_gauss_sum (commonColumns q) (fun I=>commonColumn q x seed I*heightCoeff ψ t I) k,
    source_gauss_sum Q (fun I=>β I*heightCoeff ψ t I) k]
  simp_rw [hid]
  rw [Finset.mul_sum]
  have hsum : (∑I∈Q,β I*heightCoeff ψ t I*primaryGaussRow I k)=
      ∑I∈commonColumns q,β I*heightCoeff ψ t I*primaryGaussRow I k := by
    apply Finset.sum_subset hsub
    intro I hI hnot
    have hz : β I=0 := by
      by_contra hn
      exact hnot (hmem I hn)
    simp only [hz,zero_mul]
  simp only [mul_assoc] at hsum ⊢
  rw [←Finset.mul_sum,←hsum]
  simp only [Finset.mul_sum,mul_assoc]

/-- Exact canonical source box after the preceding genuine extraction:
ordinary prefixes multiply, remaining prime pools do not change. -/
theorem canonical_live_box (pool : α→Finset Id) (d : Id×Id)
    (hd : d.1≠0 ∧ d.2≠0) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (B : Tuple α) (hB : ∀j,B j≠0) :
    liveBox (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) B hB=
      Fintype.piFinset (sourcePools (fun i : liveIndices B=>pool i.val)
        (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))
        ⟨mul_ne_zero hd.1 (hB _),mul_ne_zero hd.2 (hB _)⟩ b X₁ X₂ Y₁ Y₂) :=
  MixedLiveRows.source_live_box pool d hd (plainSupportPool b X₁ Y₁)
    (plainSupportPool b X₂ Y₂) B hB

theorem masked_live_avoid (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0)
    (u G R D : Id) (hu : u∣R*G) (ν : α→Id→ℂ)
    (Wslot : α→ℝ→ℂ) (P : α→ℝ) (W₁ W₂ : ℝ→ℂ)
    (b X₁ X₂ Y₁ Y₂ : ℝ) :
    maskedLiveSum χ S H pool d hd B hB G R D (avoid u ν) Wslot P W₁ W₂
      b X₁ X₂ Y₁ Y₂=
    maskedLiveSum χ S H pool d hd B hB G R D ν Wslot P W₁ W₂
      b X₁ X₂ Y₁ Y₂ := by
  unfold maskedLiveSum
  apply Finset.sum_congr rfl
  intro v hv
  have he := live_profile_avoid u G R hu B ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v
    (by
      intro i
      rw [MixedLiveRows.live_box] at hv
      exact hp i.val _ (Fintype.mem_piFinset.mp hv (Sum.inl i)))
  rw [he]

/-- Actual common-allocation row, exactly the expression to which the
checked uniform_common_masked_source theorem applies. -/
def commonRow (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R D : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (B : actualAllocations (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) G) : ℂ :=
  normalization (X₁*X₂) P*(frozenCoefficient B.val G R ν Wslot P*
    maskedLiveSum χ S H pool d hd B.val
      (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1 G R D
      ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂)

/-- No original-row mask is dropped. Supplier masks become a fixed
phase outside each actual canonical common row. -/
theorem original_avoiding_row (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (u G R seed D : Id)
    (hG : G≠0) (hseed : seed∣G) (hu : u∣R*G)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    originalMaskedRow χ S H pool d hd G R seed D hG (avoid u ν)
      Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      ∑B : actualAllocations (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) G,
        (frozenAvoid u B.val*MixedCommonCoefficient.frozenWeight (punctureProduct S H) B.val)*
          commonRow χ S H pool d hd G R D ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ B := by
  rw [original_masked_row_eq χ S H pool hp d hd G R seed D hG hseed]
  unfold commonMaskedRow
  apply Finset.sum_congr rfl
  intro B hB
  rw [frozen_coefficient_avoid,masked_live_avoid χ S H pool hp d hd B.val
    (allocation_data _ G B.val (Finset.mem_filter.mp B.property).1).1 u G R D hu]
  unfold commonRow
  ring

/-- Explicit positive transfer for these actual rows. The right side
contains their actual energies, not a new hypothesis asserting a bound.
Their existing canonical estimate can therefore be applied separately. -/
theorem original_avoiding_energy (χ : O→Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (u G R seed D : Id)
    (hG : G≠0) (hseed : seed∣G) (hu : u∣R*G)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0<K)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) :
    radialEnergy (fun z=>originalMaskedRow (χ z) S H pool d hd G R seed D hG
      (avoid u ν) Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂) keep Φ K≤
      ((actualAllocations (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) G).card:ℝ)*
        ∑B : actualAllocations (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) G,
          radialEnergy (fun z=>commonRow (χ z) S H pool d hd G R D ν Wslot P W₁ W₂
            b X₁ X₂ Y₁ Y₂ B) keep Φ K := by
  let T := sourcePools pool d hd b X₁ X₂ Y₁ Y₂
  let phase := fun (B : actualAllocations T G)(_ : O)=>
    frozenAvoid u B.val*MixedCommonCoefficient.frozenWeight (punctureProduct S H) B.val
  let f := fun (B : actualAllocations T G)(z : O)=>
    commonRow (χ z) S H pool d hd G R D ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ B
  have hphase : ∀B z,keep z→‖phase B z‖≤1 := by
    intro B z hz
    dsimp only [phase]
    rw [norm_mul]
    have hw : ‖MixedCommonCoefficient.frozenWeight (punctureProduct S H) B.val‖≤1 := by
      unfold MixedCommonCoefficient.frozenWeight
      split_ifs <;> norm_num
    simpa only [one_mul] using mul_le_mul (frozen_avoid_norm u B.val) hw
      (norm_nonneg _) zero_le_one
  have he := radial_phase_family phase f (fun B=>radialEnergy (f B) keep Φ K)
    keep Φ K radial hK hs hΦ hphase (fun _=>le_rfl)
  simp only [Fintype.card_coe] at he
  have hid : (fun z=>originalMaskedRow (χ z) S H pool d hd G R seed D hG
      (avoid u ν) Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂)=fun z=>∑B,phase B z*f B z := by
    funext z
    exact original_avoiding_row (χ z) S H pool hp d hd u G R seed D hG hseed hu
      ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂
  rw [hid]
  exact he

end
end Candidate.FourthPower.MixedSupplierCanonical
