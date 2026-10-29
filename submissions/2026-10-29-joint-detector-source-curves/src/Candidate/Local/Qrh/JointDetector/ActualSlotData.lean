/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.NaturalCount
import Candidate.Local.Qrh.JointDetector.WholeWordAmplification
import Candidate.Local.Qrh.JointDetector.SelectedSlotData

/-! Literal original-slot data. The natural sixth root stays in a common
coprime mask; neither bad natural zeros nor the original prime pools change. -/
namespace Qrh.JointDetector.ActualSlotData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators ContDiff
open Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentPrimeSlot CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentNaturalRowSource CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- This constant is chosen from the fixed profile before any slot scale,
character, height, anchor, state or sixth root is supplied. -/
theorem uniform_annular_bound (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ (χ : Character) (P σ v : ℝ) (I : Ideal O),
      0 < P → σ ∈ Icc (33/50:ℝ) (33/50) →
      ‖idealCoeff χ I*HeckePrimeAnnular.annularWeight W P σ v I‖ ≤ B := by
  obtain ⟨B,hB,hprof⟩ := HeckePrimeAnnular.fixed_profile_norm_bound W hW
    1 2 (33/50) (33/50) (by norm_num)
  refine ⟨B,hB,?_⟩
  intro χ P σ v I hP hσ
  apply (show ‖idealCoeff χ I*HeckePrimeAnnular.annularWeight W P σ v I‖ ≤
      ‖HeckePrimeAnnular.annularWeight W P σ v I‖ from by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)).trans
  by_cases hz : W ((I.absNorm:ℝ)/P)=0
  · simpa [HeckePrimeAnnular.annularWeight,hz] using hB.le
  · have hy := hWs hz
    rw [HeckePrimeAnnular.annularWeight,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < (I.absNorm:ℝ)/P by linarith [hy.1])]
    simpa only [Complex.neg_re,HeckeDyadic.shift_re] using hprof σ hσ _ hy

/-- Actual prime-pool support, including nonzero source ideals. -/
theorem primePool_bounds (rayM : Ideal O) (H : Subgroup (O⧸rayM)ˣ)
    (P : ℝ) (hP : 0 < P) (I : Ideal O) (hI : I ∈ primePool rayM H 2 P) :
    I ≠ 0 ∧ (Ideal.absNorm I:ℝ) ≤ 2*P := by
  have hi := Finset.mem_filter.mp hI
  refine ⟨hi.2.1.ne_zero,?_⟩
  have hn := (mem_idealsUpTo.mp hi.1).2
  exact (Nat.cast_le.mpr hn).trans (by
    simpa only [max_eq_right (by norm_num : (1:ℝ) ≤ 2)] using
      (Nat.floor_le (show 0 ≤ max (1:ℝ) 2*P by positivity)))

/-- The common sixth-root mask, applied to the literal original coefficient. -/
def coefficient (η χ : Character) (m : O) (root : NonzeroIdeal)
    (W : ℝ → ℂ) (P σ v t : ℝ) (I : Ideal O) : ℂ :=
  WholeWordAmplification.normalizedSlotCoefficient η m 1
    (fun I => (if IsCoprime I root.val then (1:ℂ) else 0)*
      (idealCoeff χ I*HeckePrimeAnnular.annularWeight W P σ v I)) t P I

/-- The mass constant does not depend on the root or any live slot data. -/
theorem coefficient_mass (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (rayM : Ideal O) (H : Subgroup (O⧸rayM)ˣ)
      (η χ : Character) (m : O) (root : NonzeroIdeal) (P σ v t : ℝ),
      1 ≤ P → σ ∈ Icc (33/50:ℝ) (33/50) →
      (∑ I ∈ primePool rayM H 2 P, ‖coefficient η χ m root W P σ v t I‖^2) ≤ C := by
  obtain ⟨B,hB,hbound⟩ := uniform_annular_bound W hW hWs
  refine ⟨max 1 (256*B^2),le_max_left _ _,?_⟩
  intro rayM H η χ m root P σ v t hP hσ
  have hp : 0 < P := zero_lt_one.trans_le hP
  apply (WholeWordAmplification.normalizedSlotCoefficient_mass η m 1
    (primePool rayM H 2 P)
    (fun I => (if IsCoprime I root.val then (1:ℂ) else 0)*
      (idealCoeff χ I*HeckePrimeAnnular.annularWeight W P σ v I)) t P 2 B hp
    (by linarith) (fun I hI => (primePool_bounds rayM H P hp I hI).1)
    (fun I hI => (primePool_bounds rayM H P hp I hI).2) ?_).trans
    (by convert le_max_right (1:ℝ) (256*B^2) using 1 <;> ring)
  intro I _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (NaturalCount.sixth_root_mask_norm_le_one root I)).trans
    (hbound χ P σ v I hp hσ)

/-- Exact ordinary-source polynomial at the free core, with every natural
root and bad-prime zero still present in the original normalized slot. -/
theorem polynomial_eq {Z bΦ : ℝ} (st : NaturalState Z 0 bΦ)
    (χ : Character) (root : NonzeroIdeal) (u : FreeRow)
    (rayM : Ideal O) (H : Subgroup (O⧸rayM)ˣ)
    (W : ℝ → ℂ) (P σ v t : ℝ) :
    (∑ I ∈ primePool rayM H 2 P,
      coefficient st.character χ st.mask root W P σ v t I*idealRowHom u.val I) =
    normalizedSlot st.character st.mask 1 (rowMap (u,root)) (primePool rayM H 2 P)
      (fun I => idealCoeff χ I*HeckePrimeAnnular.annularWeight W P σ v I) t P := by
  have hm := NaturalCount.naturalState_mask_divisibility st
  rw [show rowMap (u,root)=u.val*(idealGenerator root.val)^6 from rfl,
    NaturalCount.normalizedSlot_sixth_root st.character st.mask 1 u.val hm.1 hm.2]
  exact (WholeWordAmplification.normalizedSlot_polynomial _ _ _ _ _ _ _ _).symm

section Padding
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Extend the live dictionary by a prescribed inactive value. -/
def extend {β : Type*} (T : Finset α) (b : β) (f : T → β) (k : α) : β :=
  if h : k ∈ T then f ⟨k,h⟩ else b

def pad (T : Finset α) (w E : T → ℝ) (S : T → Finset (Ideal O))
    (c : T → Ideal O → ℂ) : SelectedSlotData (Fintype.card α) where
  width i := extend T 0 w ((Fintype.equivFin α).symm i)
  energy i := extend T 0 E ((Fintype.equivFin α).symm i)
  sources i := extend T {1} S ((Fintype.equivFin α).symm i)
  coefficient i := extend T (fun I => if I=1 then (1:ℂ) else 0) c ((Fintype.equivFin α).symm i)

theorem sum_extend (T : Finset α) (f : T → ℝ) :
    (∑ i : Fin (Fintype.card α), extend T 0 f ((Fintype.equivFin α).symm i)) = ∑ k, f k := by
  calc
    _ = ∑ k : α, extend T 0 f k := (Fintype.equivFin α).symm.sum_comp _
    _ = ∑ k ∈ T, extend T 0 f k := (Finset.sum_subset (Finset.subset_univ T)
      (fun k _ hk => by simp [extend,hk])).symm
    _ = ∑ k : T, extend T 0 f k.val := Finset.sum_subtype T (fun _ => Iff.rfl) _
    _ = _ := by apply Finset.sum_congr rfl; intro k _; simp [extend,k.property]

theorem prod_extend {β : Type*} [CommMonoid β] (T : Finset α) (f : T → β) :
    (∏ i : Fin (Fintype.card α), extend T 1 f ((Fintype.equivFin α).symm i)) = ∏ k, f k := by
  calc
    _ = ∏ k : α, extend T 1 f k := (Fintype.equivFin α).symm.prod_comp _
    _ = ∏ k ∈ T, extend T 1 f k := (Finset.prod_subset (Finset.subset_univ T)
      (fun k _ hk => by simp [extend,hk])).symm
    _ = ∏ k : T, extend T 1 f k.val := Finset.prod_subtype T (fun _ => Iff.rfl) _
    _ = _ := by apply Finset.prod_congr rfl; intro k _; simp [extend,k.property]

theorem pad_width (T : Finset α) (w E : T → ℝ) (S : T → Finset (Ideal O))
    (c : T → Ideal O → ℂ) : ∑ i, (pad T w E S c).width i = ∑ k, w k :=
  sum_extend T w

theorem pad_energy (T : Finset α) (w E : T → ℝ) (S : T → Finset (Ideal O))
    (c : T → Ideal O → ℂ) : ∑ i, (pad T w E S c).energy i = ∑ k, E k :=
  sum_extend T E

theorem pad_polynomial (T : Finset α) (w E : T → ℝ) (S : T → Finset (Ideal O))
    (c : T → Ideal O → ℂ) (i : Fin (Fintype.card α)) (z : O) :
    (pad T w E S c).polynomial i z =
      extend T 1 (fun k => ∑ I ∈ S k,c k I*idealRowHom z I) ((Fintype.equivFin α).symm i) := by
  by_cases h : (Fintype.equivFin α).symm i ∈ T
  · simp [pad,SelectedSlotData.polynomial,extend,h]
  · simp [pad,SelectedSlotData.polynomial,extend,h]
    simpa only [Ideal.one_eq_top] using (map_one (idealRowHom z))

theorem pad_bounded (T : Finset α) (w E : T → ℝ) (S : T → Finset (Ideal O))
    (c : T → Ideal O → ℂ) (Z mesh C : ℝ) (hZ : 1 < Z) (hm : 0 ≤ mesh) (hC : 1 ≤ C)
    (hw : ∀ k,0 ≤ w k) (hwm : ∀ k,w k ≤ mesh)
    (hzero : ∀ k,∀ I ∈ S k,I ≠ 0)
    (hN : ∀ k,∀ I ∈ S k,(Ideal.absNorm I:ℝ) ≤ 2*Z^(w k))
    (hc : ∀ k,(∑ I ∈ S k,‖c k I‖^2) ≤ C) :
    (pad T w E S c).Bounded Z mesh C := by
  constructor
  · intro i
    by_cases hi : (Fintype.equivFin α).symm i ∈ T
    · simpa [pad,extend,hi] using hw ⟨_,hi⟩
    · simp [pad,extend,hi]
  · intro i
    by_cases hi : (Fintype.equivFin α).symm i ∈ T
    · simpa [pad,extend,hi] using hwm ⟨_,hi⟩
    · simpa [pad,extend,hi] using hm
  · intro i I hI
    by_cases hi : (Fintype.equivFin α).symm i ∈ T
    · exact hzero ⟨_,hi⟩ I (by simpa [pad,extend,hi] using hI)
    · have : I=1 := by simpa [pad,extend,hi] using hI
      simp [this]
  · intro i I hI
    by_cases hi : (Fintype.equivFin α).symm i ∈ T
    · simpa [pad,extend,hi] using hN ⟨_,hi⟩ I (by simpa [pad,extend,hi] using hI)
    · have : I=1 := by simpa [pad,extend,hi] using hI
      simp [pad,extend,hi,this]
  · intro i
    by_cases hi : (Fintype.equivFin α).symm i ∈ T
    · simpa [pad,extend,hi] using hc ⟨_,hi⟩
    · simpa [pad,extend,hi] using hC

end Padding

section Original
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
variable {Z bΦ : ℝ} (st : NaturalState Z 0 bΦ) (η₀ : Character)
variable (W : ℝ → ℂ) (T : Finset α) (θ : T → RayQuotient.Characters rayM H)
variable (w σ v E : T → ℝ) (t : ℝ) (root : NonzeroIdeal)

/-- The ambient index count is the ORIGINAL dictionary size, even when only
T is live. Inactive entries have zero width/energy and the unit polynomial. -/
def data : SelectedSlotData (Fintype.card α) :=
  pad T w E (fun k => primePool rayM H 2 (Z^(w k)))
    (fun k => coefficient st.character (relativeCharacter rayM H hH η₀ (θ k))
      st.mask root W (Z^(w k)) (σ k) (v k) t)

theorem data_width : ∑ i,(data rayM H hH st η₀ W T θ w σ v E t root).width i = ∑ k,w k :=
  pad_width _ _ _ _ _

theorem data_energy : ∑ i,(data rayM H hH st η₀ W T θ w σ v E t root).energy i = ∑ k,E k :=
  pad_energy _ _ _ _ _

theorem data_polynomial (u : FreeRow) (i : Fin (Fintype.card α)) :
    (data rayM H hH st η₀ W T θ w σ v E t root).polynomial i u.val =
      extend T 1 (fun k => normalizedSlot st.character st.mask 1 (rowMap (u,root))
        (primePool rayM H 2 (Z^(w k)))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I) t (Z^(w k)))
        ((Fintype.equivFin α).symm i) := by
  rw [data,pad_polynomial]
  unfold extend
  split_ifs with hi
  · exact polynomial_eq st _ root u rayM H W _ _ _ _
  · rfl


/-- Active original indices carry exactly their original width and energy. -/
theorem data_active (k : T) :
    (data rayM H hH st η₀ W T θ w σ v E t root).width ((Fintype.equivFin α) k.val)=w k ∧
    (data rayM H hH st η₀ W T θ w σ v E t root).energy ((Fintype.equivFin α) k.val)=E k ∧
    (data rayM H hH st η₀ W T θ w σ v E t root).sources ((Fintype.equivFin α) k.val)=
      primePool rayM H 2 (Z^(w k)) := by
  simp [data,pad,extend,k.property]

/-- Inactive dictionary entries are the unit ideal with its unit coefficient. -/
theorem data_inactive (k : α) (hk : k ∉ T) :
    (data rayM H hH st η₀ W T θ w σ v E t root).width ((Fintype.equivFin α) k)=0 ∧
    (data rayM H hH st η₀ W T θ w σ v E t root).energy ((Fintype.equivFin α) k)=0 ∧
    (data rayM H hH st η₀ W T θ w σ v E t root).sources ((Fintype.equivFin α) k)={1} ∧
    (data rayM H hH st η₀ W T θ w σ v E t root).coefficient ((Fintype.equivFin α) k)=
      (fun I => if I=1 then (1:ℂ) else 0) := by
  simp [data,pad,extend,hk]

theorem data_polynomial_active (u : FreeRow) (k : T) :
    (data rayM H hH st η₀ W T θ w σ v E t root).polynomial ((Fintype.equivFin α) k.val) u.val =
      normalizedSlot st.character st.mask 1 (rowMap (u,root)) (primePool rayM H 2 (Z^(w k)))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I) t (Z^(w k)) := by
  rw [data_polynomial]
  simp [extend,k.property]

theorem data_polynomial_inactive (u : FreeRow) (k : α) (hk : k ∉ T) :
    (data rayM H hH st η₀ W T θ w σ v E t root).polynomial ((Fintype.equivFin α) k) u.val=1 := by
  rw [data_polynomial]
  simp [extend,hk]

theorem data_product (u : FreeRow) :
    ‖∏ i,(data rayM H hH st η₀ W T θ w σ v E t root).polynomial i u.val‖^2 =
      RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root)) := by
  simp_rw [data_polynomial]
  rw [prod_extend,norm_prod]
  exact Finset.prod_pow _ _ _ |>.symm


/-- The equivalent product of individual squared responses, as used by the
amplitude histogram. -/
theorem data_mass (u : FreeRow) :
    (∏ i,‖(data rayM H hH st η₀ W T θ w σ v E t root).polynomial i u.val‖^2) =
      RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root)) := by
  simpa only [norm_prod,Finset.prod_pow] using
    data_product rayM H hH st η₀ W T θ w σ v E t root u

end Original

/-- The sole factory constant is chosen from W, before even the original
finite dictionary. All state, anchor, sixth-root and height data are uniform. -/
theorem data_bounded (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : Type) [Fintype α] [DecidableEq α]
      (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
      (hH : RayOrthogonality.globalUnits rayM ≤ H) (Z bΦ : ℝ)
      (st : NaturalState Z 0 bΦ) (η₀ : Character) (T : Finset α)
      (θ : T → RayQuotient.Characters rayM H) (w σ v E : T → ℝ) (t : ℝ)
      (root : NonzeroIdeal) (mesh : ℝ),
      1 < Z → 0 ≤ mesh → (∀ k,0 ≤ w k) → (∀ k,w k ≤ mesh) →
      (∀ k,σ k ∈ Icc (33/50:ℝ) (33/50)) →
      (data rayM H hH st η₀ W T θ w σ v E t root).Bounded Z mesh C := by
  obtain ⟨C,hC,hmass⟩ := coefficient_mass W hW hWs
  refine ⟨C,hC,?_⟩
  intro α _ _ rayM _ H hH Z bΦ st η₀ T θ w σ v E t root mesh hZ hm hw hwm hσ
  apply pad_bounded T w E _ _ Z mesh C hZ hm hC hw hwm
  · intro k I hI
    exact (primePool_bounds rayM H (Z^(w k)) (Real.rpow_pos_of_pos (by linarith) _) I hI).1
  · intro k I hI
    exact (primePool_bounds rayM H (Z^(w k)) (Real.rpow_pos_of_pos (by linarith) _) I hI).2
  · intro k
    exact hmass rayM H st.character (relativeCharacter rayM H hH η₀ (θ k)) st.mask root
      (Z^(w k)) (σ k) (v k) t (Real.one_le_rpow hZ.le (hw k)) (hσ k)

end
end Qrh.JointDetector.ActualSlotData

#print axioms Qrh.JointDetector.ActualSlotData.coefficient_mass
#print axioms Qrh.JointDetector.ActualSlotData.polynomial_eq

#print axioms Qrh.JointDetector.ActualSlotData.data_bounded
#print axioms Qrh.JointDetector.ActualSlotData.data_product
