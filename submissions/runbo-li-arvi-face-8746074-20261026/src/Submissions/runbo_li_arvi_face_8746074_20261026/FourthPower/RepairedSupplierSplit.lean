/- Copyright (c) 2026 Sil. Apache-2.0.
Shared EXACT finite large/small supplier boundary for both lanes. The full
supplier Cauchy count is used on both branches; no extra branchwise Cauchy.
No analytical branch estimate is asserted by this mechanism.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedRawSupplier
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedFirstRawSides
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstLiveEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSupplierSplit
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy
open CenteredMomentSmoothedWindowEnergy
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedInnerExceptionalBlock MixedFirstLiveSource MixedOriginalSecondZero MixedCommonCoefficient MixedCommonRestriction
open OuterFreshSource
open RepairedRawSupplier RepairedFirstRawSides
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (priority := 2000) {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def supplierTerm (s : Source ι a b) (ha : 0 < a) (u : Id)
    (J : (L : Finset ι) → Finset {i // i ∉ Lᶜ}) (p : SupplierIndex s ha u J)
    (τ : Character) (v : ℝ) (k : O) : ℂ :=
  MixedSupplierFourthRow.frozenWeight (supplierData s ha u p.1 (J p.1)) p.2.val *
    originalFamily (supplierData s ha u p.1 (J p.1)) p.2.val τ v k

def finiteSupplierEnergy (s : Source ι a b) (ha : 0 < a) (u : Id)
    (J : (L : Finset ι) → Finset {i // i ∉ Lᶜ}) (p : SupplierIndex s ha u J)
    (τ : Character) (v K : ℝ) (rows : Finset O) : ℝ :=
  ∑ k ∈ rows, (ballProfile (‖eisEmbedding k‖^2/K)).re * ‖supplierTerm s ha u J p τ v k‖^2

/-- Predicate true selects the large branch; its complement selects small.
The Cauchy cardinality is that of the WHOLE supplier family in both cases. -/
def supplierBranch (s : Source ι a b) (ha : 0 < a) (u : Id)
    (J : (L : Finset ι) → Finset {i // i ∉ Lᶜ}) (large : Finset ι → Prop)
    (τ : Character) (v K : ℝ) (rows : Finset O) : ℝ :=
  (Fintype.card (SupplierIndex s ha u J) : ℝ) *
    ∑ p : SupplierIndex s ha u J, if large p.1 then finiteSupplierEnergy s ha u J p τ v K rows else 0

theorem supplierBranch_nonneg (s : Source ι a b) (ha : 0 < a) (u : Id)
    (J : (L : Finset ι) → Finset {i // i ∉ Lᶜ}) (large : Finset ι → Prop)
    (τ : Character) (v K : ℝ) (rows : Finset O) : 0 ≤ supplierBranch s ha u J large τ v K rows := by
  unfold supplierBranch
  apply mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg ?_)
  intro p hp
  split_ifs
  · exact Finset.sum_nonneg (fun k _ => mul_nonneg (ballProfile_nonneg _) (sq_nonneg _))
  · exact le_rfl

theorem active_supplier_sum (s : Source ι a b) (ha : 0 < a) (u : Id)
    (J : (L : Finset ι) → Finset {i // i ∉ Lᶜ}) (τ : Character) (v : ℝ) (k : O) :
    gaussPolynomial Finset.univ (sourceGenerator (sourceColumns s))
      (sourceGenerator_supported (sourceColumns s))
      (fun I : supportedColumns (sourceColumns s) => sourceCoefficient s ha u I * heightCoeff τ v I) k =
      ∑ p : SupplierIndex s ha u J, supplierTerm s ha u J p τ v k := by
  rw [source_supplier_expansion s ha u J τ v k, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro L hL
  simp only [supplierTerm]
  rw [Finset.sum_coe_sort (activeFrozen (supplierData s ha u L (J L)))
    (fun x : Frozen (supplierData s ha u L (J L)) =>
      MixedSupplierFourthRow.frozenWeight (supplierData s ha u L (J L)) x *
        originalFamily (supplierData s ha u L (J L)) x τ v k)]
  simp only [activeFrozen, Finset.sum_filter, supplierTerm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hi : Function.Injective x
  · by_cases hw : MixedSupplierFourthRow.frozenWeight (supplierData s ha u L (J L)) x = 0
    · simp only [hi, hw, zero_mul, ne_eq, not_true_eq_false, and_false, ite_false, ite_true]
    · simp only [hi, hw, ne_eq, not_false_eq_true, and_self, ite_true]
  · simp only [hi, false_and, ite_false]

theorem finite_source_split (s : Source ι a b) (ha : 0 < a) (u : Id)
    (J : (L : Finset ι) → Finset {i // i ∉ Lᶜ}) (large : Finset ι → Prop)
    (τ : Character) (v K : ℝ) (rows : Finset O) :
    (∑ k ∈ rows, (ballProfile (‖eisEmbedding k‖^2/K)).re *
      ‖gaussPolynomial Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s) => sourceCoefficient s ha u I * heightCoeff τ v I) k‖^2) ≤
      supplierBranch s ha u J large τ v K rows + supplierBranch s ha u J (fun L => ¬large L) τ v K rows := by
  have hpoint (k : O) := CubicEisenstein.norm_sum_sq_le_card Finset.univ
    (fun p : SupplierIndex s ha u J => supplierTerm s ha u J p τ v k)
  have hbound := Finset.sum_le_sum (fun k (_ : k ∈ rows) =>
    mul_le_mul_of_nonneg_left (hpoint k) (ballProfile_nonneg (‖eisEmbedding k‖^2/K)))
  simp only [← active_supplier_sum, Finset.card_univ] at hbound
  apply hbound.trans_eq
  unfold supplierBranch finiteSupplierEnergy
  rw [← mul_add, ← Finset.sum_add_distrib]
  have hsplit (p : SupplierIndex s ha u J) :
      (if large p.1 then ∑ k ∈ rows, (ballProfile (‖eisEmbedding k‖^2/K)).re * ‖supplierTerm s ha u J p τ v k‖^2 else 0) +
      (if ¬large p.1 then ∑ k ∈ rows, (ballProfile (‖eisEmbedding k‖^2/K)).re * ‖supplierTerm s ha u J p τ v k‖^2 else 0) =
      ∑ k ∈ rows, (ballProfile (‖eisEmbedding k‖^2/K)).re * ‖supplierTerm s ha u J p τ v k‖^2 := by
    by_cases h : large p.1 <;> simp only [h, not_true_eq_false, not_false_eq_true, ite_true, ite_false, zero_add, add_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : large p.1
  all_goals
    simp only [h, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
      zero_add, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

def firstScalar (root : Source ι a b) (G : Id) (B : actualAllocations (tuplePools root) G) : ℂ :=
  MixedCommonCoefficient.frozenWeight (punctureProduct root.S root.H) B.val *
    frozenCoefficient B.val G root.R root.ν root.Wslot root.P

/-- Exact shared boundary for Raw and Small. It includes the first genuine
allocation Cauchy, its actual frozen coefficient, and the full supplier count.
The predicate distinguishes branches but does not change either count. -/
def firstBranch (root : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure root)
    (G u : Id)
    (J : (B : actualAllocations (tuplePools root) G) → (L : Finset (liveIndices B.val)) → Finset {i // i ∉ Lᶜ})
    (large : (B : actualAllocations (tuplePools root) G) → Finset (liveIndices B.val) → Prop)
    (τ : Character) (v K : ℝ) (rows : Finset O) : ℝ :=
  ((actualAllocations (tuplePools root) G).card : ℝ) *
    ∑ B : actualAllocations (tuplePools root) G, ‖firstScalar root G B‖^2 *
      supplierBranch (allocatedLiveSource root hb cover G B) ha u (J B) (large B) τ v K rows

/-- The raw original common-side finite energy splits into precisely the
two shared contributions. No analytical side estimate is used. -/
theorem finite_common_split (root : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure root)
    (opposite G : Id) (hOpp : Supported opposite) (hG : Supported G)
    (hSame : CompletedGauss.primeSupport opposite = CompletedGauss.primeSupport G) (u : Id)
    (J : (B : actualAllocations (tuplePools root) G) → (L : Finset (liveIndices B.val)) → Finset {i // i ∉ Lᶜ})
    (large : (B : actualAllocations (tuplePools root) G) → Finset (liveIndices B.val) → Prop)
    (τ : Character) (v K : ℝ) (rows : Finset O) :
    (∑ k ∈ rows, (ballProfile (‖eisEmbedding k‖^2/K)).re *
      ‖gaussPolynomial Finset.univ (element opposite G hG.1 (sourceColumns root))
        (element_supported opposite G hG.1 (sourceColumns root))
        (fun I : columns opposite G hG.1 (sourceColumns root) => originalResidual root ha 1 G u I * heightCoeff τ v I) k‖^2) ≤
      firstBranch root ha hb cover G u J large τ v K rows +
      firstBranch root ha hb cover G u J (fun B L => ¬large B L) τ v K rows := by
  let w := fun B : actualAllocations (tuplePools root) G => firstScalar root G B
  let f := fun (B : actualAllocations (tuplePools root) G) (k : O) =>
    gaussPolynomial Finset.univ (sourceGenerator (sourceColumns (allocatedLiveSource root hb cover G B)))
      (sourceGenerator_supported (sourceColumns (allocatedLiveSource root hb cover G B)))
      (fun I : supportedColumns (sourceColumns (allocatedLiveSource root hb cover G B)) =>
        sourceCoefficient (allocatedLiveSource root hb cover G B) ha u I * heightCoeff τ v I) k
  have hp (k : O) :
      ‖gaussPolynomial Finset.univ (element opposite G hG.1 (sourceColumns root))
        (element_supported opposite G hG.1 (sourceColumns root))
        (fun I : columns opposite G hG.1 (sourceColumns root) => originalResidual root ha 1 G u I * heightCoeff τ v I) k‖^2 ≤
      ((actualAllocations (tuplePools root) G).card : ℝ) *
        ∑ B : actualAllocations (tuplePools root) G, ‖w B‖^2 * ‖f B k‖^2 := by
    rw [first_gauss_live_sources root ha hb cover opposite G 1 u hOpp hG hSame (one_dvd _) τ v k]
    simpa only [w, f, firstScalar, Finset.card_univ, Fintype.card_coe, norm_mul, mul_pow] using
      CubicEisenstein.norm_sum_sq_le_card Finset.univ (fun B : actualAllocations (tuplePools root) G => w B * f B k)
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ rows) =>
    mul_le_mul_of_nonneg_left (hp k) (ballProfile_nonneg (‖eisEmbedding k‖^2/K)))
  apply hs.trans
  have hsource (B : actualAllocations (tuplePools root) G) :=
    finite_source_split (allocatedLiveSource root hb cover G B) ha u (J B) (large B) τ v K rows
  calc
    _ = ((actualAllocations (tuplePools root) G).card : ℝ) *
        ∑ B : actualAllocations (tuplePools root) G, ‖w B‖^2 *
          ∑ k ∈ rows, (ballProfile (‖eisEmbedding k‖^2/K)).re * ‖f B k‖^2 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ((actualAllocations (tuplePools root) G).card : ℝ) *
        ∑ B : actualAllocations (tuplePools root) G, ‖w B‖^2 *
          (supplierBranch (allocatedLiveSource root hb cover G B) ha u (J B) (large B) τ v K rows +
           supplierBranch (allocatedLiveSource root hb cover G B) ha u (J B) (fun L => ¬large B L) τ v K rows) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _ => mul_le_mul_of_nonneg_left (hsource B) (sq_nonneg _))) (Nat.cast_nonneg _)
    _ = _ := by simp only [firstBranch, Finset.mul_sum, Finset.sum_add_distrib, mul_add, w] <;> rfl

/-- Conversion from actual uniform finite branch bounds to the exact
infinite raw side in RootAssembly. The two supplies remain explicit. -/
theorem raw_energy_of_branch_bounds (root : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure root)
    (opposite G : Id) (hOpp : Supported opposite) (hG : Supported G)
    (hSame : CompletedGauss.primeSupport opposite = CompletedGauss.primeSupport G) (u : Id)
    (J : (B : actualAllocations (tuplePools root) G) → (L : Finset (liveIndices B.val)) → Finset {i // i ∉ Lᶜ})
    (large : (B : actualAllocations (tuplePools root) G) → Finset (liveIndices B.val) → Prop)
    (τ : Character) (v K BL BS : ℝ) (hK : 0 < K)
    (hLarge : ∀ rows : Finset O, firstBranch root ha hb cover G u J large τ v K rows ≤ BL)
    (hSmall : ∀ rows : Finset O, firstBranch root ha hb cover G u J (fun B L => ¬large B L) τ v K rows ≤ BS) :
    rawEnergy root ha opposite G hG u τ v K ≤ BL+BS := by
  have hs := gaussEnergy_hasSum_re Finset.univ (element opposite G hG.1 (sourceColumns root))
    (element_supported opposite G hG.1 (sourceColumns root))
    (fun I : columns opposite G hG.1 (sourceColumns root) => originalResidual root ha 1 G u I * heightCoeff τ v I)
    ballProfile K hK
  unfold rawEnergy
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun k => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))
  intro rows
  have he := (finite_common_split root ha hb cover opposite G hOpp hG hSame u J large τ v K rows).trans
    (add_le_add (hLarge rows) (hSmall rows))
  simpa only [mul_comm] using he

end
end Candidate.FourthPower.RepairedSupplierSplit
