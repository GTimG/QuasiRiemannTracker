/- Copyright (c) 2026 Sil. Apache-2.0.
Exact seed allocation into rebased seed-one sources. The full extracted
support F remains in R*F, independently of the product of the frozen tuple.
Reference replacement constructs its finite enclosure, rather than asking
for an enclosure at the newly chosen lengths.
-/
import Candidate.Feedback.FourthPower.MixedFirstLiveSource
import Candidate.Feedback.FourthPower.MixedFirstRebase
import Candidate.Feedback.FourthPower.MixedCanonicalSource
import Candidate.Feedback.FourthPower.MixedOriginalCoprimality
import Candidate.Feedback.FourthPower.MixedFirstPhysicalApplication
import Candidate.Feedback.FourthPower.MixedFirstReferenceChoice
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedFirstSeededSource
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentSourceRectangle CenteredMomentFirstSectors CenteredMomentLiveDomain
open CenteredMomentDivisorAllocation CenteredMomentDivisorEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentCommonRawScale
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedOriginalSecondZero
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedFixedSupport MixedArtificialRestriction MixedFirstLiveSource MixedFirstRebase
open MixedLiveRows MixedTupleRows MixedCompletedRows MixedCanonicalSource
open MixedLiveNormalization MixedInnerExceptionalBlock
open ReferencePrimeEnclosure NativeFiniteHoles
open ConcretePrimeRowBridge CenteredMomentHeckeExpansion CenteredMomentSourceRow
open CenteredMomentSecondHeightFamily CenteredMomentSourceRectangleMask
open CenteredMomentLattice MixedHeightEnergy
open MixedRestrictedDictionary MixedCommonAllocation
open MixedFirstPhysicalApplication MixedFirstReferenceChoice
open CenteredMomentFirstTailAggregate CanonicalRowCompletion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Unlike a genuine common allocation, the product here need not equal F.
The existing Source record therefore stores the actual product of B. -/
def frozenSource (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (F : Id) (B : boundedLabels (tuplePools s) F) : Source ι a b :=
  { s with
    B := B.val
    hB := (allocation_data (tuplePools s) F B.val (Finset.mem_filter.mp B.property).1).1
    G := finiteTupleProduct B.val
    hprod := rfl
    henclose := by
      let hB := (allocation_data (tuplePools s) F B.val (Finset.mem_filter.mp B.property).1).1
      have hpre (d e : Id) (hd : d ≠ 0) (he : e ≠ 0) (U : ℝ) (hU : 0 ≤ U) :
          U / (d*e).absNorm ≤ U / d.absNorm := by
        simp only [map_mul,Nat.cast_mul]
        apply div_le_div_of_nonneg_left hU (zero_lt_one.trans_le (ideal_norm_one_le hd))
        exact le_mul_of_one_le_right (Nat.cast_nonneg _) (ideal_norm_one_le he)
      intro I hI hlen
      apply cover I hI
      rcases hlen with hlen | hlen
      · exact Or.inl (hlen.trans (mul_le_mul_of_nonneg_left
          (hpre s.d.1 (B.val (Sum.inr 0)) s.hd.1 (hB _) s.U₁
            ((s.hL.trans_le s.hX₁).trans_le s.hXU₁).le) hb))
      · exact Or.inr (hlen.trans (mul_le_mul_of_nonneg_left
          (hpre s.d.2 (B.val (Sum.inr 1)) s.hd.2 (hB _) s.U₂
            ((s.hL.trans_le s.hX₂).trans_le s.hXU₂).le) hb)) }

/-- The actual fixed-support live source. Updating R is essential:
the checked artificial expansion punctures at F, not merely product B. -/
def seededLiveSource (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (F : Id) (hF : F ≠ 0) (B : boundedLabels (tuplePools s) F) :
    Source (liveIndices B.val) a b :=
  { liveSource (frozenSource s hb cover F B) with
    R := s.R*F
    hR := mul_ne_zero s.hR hF }

def seededRebasedSource (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (F : Id) (hF : F ≠ 0) (B : boundedLabels (tuplePools s) F) :=
  rebase (seededLiveSource s hb cover F hF B)

theorem seeded_rebased_data (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (F : Id) (hF : F ≠ 0) (B : boundedLabels (tuplePools s) F) :
    let r := seededRebasedSource s hb cover F hF B
    r.d = (1,1) ∧ r.B = (fun _ => 1) ∧ r.G = 1 ∧ r.R = s.R*F ∧
      r.X₁ = s.X₁ / (s.d.1*B.val (Sum.inr 0)).absNorm ∧
      r.X₂ = s.X₂ / (s.d.2*B.val (Sum.inr 1)).absNorm := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem seeded_rebased_volume (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (F : Id) (hF : F ≠ 0) (B : boundedLabels (tuplePools s) F) :
    sourceVolume (seededRebasedSource s hb cover F hF B) =
      sourceVolume s / (pairNorm s.d * rawReduction B.val s.P) := by
  let hB := (allocation_data (tuplePools s) F B.val (Finset.mem_filter.mp B.property).1).1
  have hraw := raw_scale_identity B.val hB ((s.X₁*s.X₂)/pairNorm s.d) s.P
  have hr := (rawReduction_pos B.val hB s.P (fun i => zero_lt_one.trans_le (s.hP i))).ne'
  rw [seededRebasedSource,rebase_volume]
  change ((s.X₁*s.X₂)*∏i : liveIndices B.val,s.P i.val) /
    pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) = _
  rw [extracted_pair_norm]
  calc
    _ = remainingRaw B.val ((s.X₁*s.X₂)/pairNorm s.d) s.P := by
      unfold remainingRaw
      ring
    _ = (((s.X₁*s.X₂)/pairNorm s.d)*∏i,s.P i)/rawReduction B.val s.P :=
      (eq_div_iff hr).mpr hraw
    _ = _ := by unfold sourceVolume;ring

/-- Exactly the scalar paid by ReferenceChoice.seed_frozen_cost_with_prefix.
The old normalization and original prefix denominator each occur once. -/
theorem seeded_normalization (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (F : Id) (hF : F ≠ 0) (B : boundedLabels (tuplePools s) F) (c : ℂ) (E : ℝ) :
    ‖c‖^2 * E / sourceVolume s =
      (‖c‖^2 / rawReduction B.val s.P) *
        (E / sourceVolume (seededRebasedSource s hb cover F hF B)) / pairNorm s.d := by
  rw [seeded_rebased_volume]
  have hr := (rawReduction_pos B.val
    (allocation_data (tuplePools s) F B.val (Finset.mem_filter.mp B.property).1).1
    s.P (fun i => zero_lt_one.trans_le (s.hP i))).ne'
  field_simp [(sourceVolume_pos s).ne',(pairNorm_pos s.hd.1 s.hd.2).ne',hr] <;> ring

theorem seeded_live_box (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (F : Id) (hF : F ≠ 0) (B : boundedLabels (tuplePools s) F) :
    Fintype.piFinset (tuplePools (seededLiveSource s hb cover F hF B)) =
      liveBox (tuplePools s) B.val
        (allocation_data (tuplePools s) F B.val (Finset.mem_filter.mp B.property).1).1 := by
  exact live_source_box (frozenSource s hb cover F B)

/-- Literal seed-one coefficient, with the original tuple weight,
full fixed-support puncture, two ordinary heights, and all live slots. -/
theorem seeded_live_coefficient (s : Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : OriginalEnclosure s) (F : Id) (hF : F ≠ 0)
    (B : boundedLabels (tuplePools s) F) (I : Id) :
    sourceCoefficient (seededLiveSource s hb cover F hF B) ha 1 I =
      finiteColumnCoefficient
        (liveBox (tuplePools s) B.val
          (allocation_data (tuplePools s) F B.val (Finset.mem_filter.mp B.property).1).1)
        (fun v => tupleWeight (punctureProduct s.S s.H) v *
          liveProfile B.val F s.R s.ν s.Wslot s.P
            (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
            (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
            s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 v) I := by
  change finiteColumnCoefficient
    (Fintype.piFinset (tuplePools (seededLiveSource s hb cover F hF B)))
    (fun v => tupleWeight (punctureProduct s.S s.H) v *
      liveProfile B.val F s.R s.ν s.Wslot s.P
        (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
        (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
        s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 v) I = _
  rw [seeded_live_box]

def rawRow (s : Source ι a b) (ha : 0 < a) (seed : Id) (ψ : Id →* ℂ) : ℂ :=
  ∑ I ∈ sourceColumns s, sourceCoefficient s ha seed I * ψ I

theorem raw_row_tuples (s : Source ι a b) (ha : 0 < a) (seed : Id) (ψ : Id →* ℂ) :
    rawRow s ha seed ψ =
      ∑ v ∈ Fintype.piFinset (tuplePools s), originalTuple s ha seed v * ψ (finiteTupleProduct v) := by
  exact finite_column_sum (Fintype.piFinset (tuplePools s)) (originalTuple s ha seed) ψ

theorem seeded_raw_row (s : Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : OriginalEnclosure s) (F : Id) (hF : F ≠ 0)
    (B : boundedLabels (tuplePools s) F) (ψ : Id →* ℂ) :
    rawRow (seededRebasedSource s hb cover F hF B) ha 1 ψ =
      ∑ v ∈ liveBox (tuplePools s) B.val
        (allocation_data (tuplePools s) F B.val (Finset.mem_filter.mp B.property).1).1,
        tupleWeight (punctureProduct s.S s.H) v *
          liveProfile B.val F s.R s.ν s.Wslot s.P
            (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
            (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
            s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 v * ψ (finiteTupleProduct v) := by
  unfold seededRebasedSource rawRow
  rw [rebase_columns,rebase_coefficient]
  simp_rw [seeded_live_coefficient]
  change (∑ I ∈ finiteColumns
    (Fintype.piFinset (tuplePools (seededLiveSource s hb cover F hF B))), _) = _
  rw [seeded_live_box]
  exact finite_column_sum _ _ ψ

def frozenScalar (s : Source ι a b) (D F : Id)
    (A : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (B : boundedLabels (tuplePools s) F) (ψ : Id →* ℂ) : ℂ :=
  frozenWeight (punctureProduct s.S s.H) B.val *
    allocationTerm D Finset.univ B.val A *
    frozenCoefficient B.val (finiteTupleProduct B.val) s.R s.ν s.Wslot s.P *
    ψ (finiteTupleProduct B.val)

/-- A complete actual artificial allocation now ends in constructed
seed-one, prefix-one Sources. No common-vector premise is introduced. -/
theorem allocated_raw_row (s : Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : OriginalEnclosure s) (D F : Id) (hF : F ≠ 0) (hDF : D ∣ F)
    (A : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (ψ : Id →* ℂ) :
    (∑ v ∈ Fintype.piFinset (tuplePools s), tupleWeight (punctureProduct s.S s.H) v *
      allocationTerm D Finset.univ v A *
      profileCoefficient s.R s.ν s.Wslot s.P
        (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
        (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
        s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 1 v * ψ (finiteTupleProduct v)) =
      ∑ B : boundedLabels (tuplePools s) F,
        frozenScalar s D F A B ψ * rawRow (seededRebasedSource s hb cover F hF B) ha 1 ψ := by
  simp_rw [seeded_raw_row]
  exact allocated_restricted_character_sum (punctureProduct s.S s.H) (tuplePools s)
    (source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂)
    (fun i I hI => s.hp i I hI) D F s.R hF hDF A ψ s.ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2

/-- The whole squarefree seed is removed by its exact signed allocation,
not by replacing a restricted norm by an unrestricted norm. -/
theorem seeded_raw_decomposition (s : Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : OriginalEnclosure s) (D : Id) (hD : Squarefree D)
    (ψ : Id →* ℂ) :
    rawRow s ha D ψ =
      ∑ A : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
        ∑ B : boundedLabels (tuplePools s) D,
          frozenScalar s D D A B ψ *
            rawRow (seededRebasedSource s hb cover D hD.ne_zero B) ha 1 ψ := by
  rw [raw_row_tuples]
  have he := finite_mask_regroup D hD (Finset.univ : Finset (ι ⊕ Fin 2))
    (Fintype.piFinset (tuplePools s)) id
    (fun (_ : Unit) v => originalTuple s ha 1 v * ψ (finiteTupleProduct v)) ()
  have hmask : (∑ v ∈ Fintype.piFinset (tuplePools s),
      originalTuple s ha D v * ψ (finiteTupleProduct v)) =
      ∑ v ∈ Fintype.piFinset (tuplePools s),
        if D ∣ finiteTupleProduct v then originalTuple s ha 1 v * ψ (finiteTupleProduct v) else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    change (tupleWeight _ v * profileCoefficient _ _ _ _ _ _ _ _ _ _ _ _ D v) * _ = _
    rw [← MixedSupplierReconstruction.profile_seed_mask]
    by_cases hDv : D ∣ finiteTupleProduct v <;>
      simp only [hDv,ite_true,ite_false,originalTuple,zero_mul,mul_zero]
  rw [hmask]
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro A hA
  have halloc := allocated_raw_row s ha hb cover D D hD.ne_zero (dvd_refl D) A ψ
  refine Eq.trans ?_ halloc
  unfold allocatedPolynomial
  apply Finset.sum_congr rfl
  intro v hv
  dsimp only [id_eq,originalTuple]
  ring

/- Reference re-enclosure. The old active puncture is frozen before
enlarging S, so previously inactive members of H never become active. -/
def activeHoles (s : Source ι a b) : Finset PrimeIdeal := s.S.filter (fun Q => Q ∈ s.H)

def referenceCap (s : Source ι a b) (Y₁ Y₂ : ℝ) : ℝ :=
  b * max (max s.X₁ Y₁) (max s.X₂ Y₂)

def referencePrimes (s : Source ι a b) (Y₁ Y₂ : ℝ) : Finset PrimeIdeal :=
  s.S ∪ enclosure (referenceCap s Y₁ Y₂)

theorem reference_puncture (s : Source ι a b) (Y₁ Y₂ : ℝ) :
    punctureProduct (referencePrimes s Y₁ Y₂) (activeHoles s) = punctureProduct s.S s.H := by
  unfold punctureProduct
  congr 1
  ext Q
  simp only [referencePrimes,activeHoles,Finset.mem_filter,Finset.mem_union]
  tauto

/-- Actual Source at the selected reference pair. The support enclosure
is constructed from its lengths; there is no new enclosure hypothesis. -/
def referenceSource (s : Source ι a b) (hb : 0 ≤ b) (Y₁ Y₂ L : ℝ)
    (hL : 0 < L) (hX₁ : L ≤ s.X₁) (hX₂ : L ≤ s.X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂) (hprod : Y₁*Y₂ = s.T) : Source ι a b :=
  { s with
    S := referencePrimes s Y₁ Y₂
    H := activeHoles s
    Y₁ := Y₁
    Y₂ := Y₂
    U₁ := max s.X₁ Y₁
    U₂ := max s.X₂ Y₂
    L := L
    hL := hL
    hX₁ := hX₁
    hX₂ := hX₂
    hY₁ := hY₁
    hY₂ := hY₂
    hXU₁ := le_max_left _ _
    hXU₂ := le_max_left _ _
    hYU₁ := le_max_right _ _
    hYU₂ := le_max_right _ _
    hpY := hprod
    hpool := fun i I hI => Finset.mem_image.mpr (by
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp (s.hpool i hI)
      exact ⟨Q,Finset.mem_union_left _ hQ,rfl⟩)
    hS := fun Q hQ => (Finset.mem_union.mp hQ).elim (s.hS Q)
      (fun hQ => (enclosure_bound _ Q hQ).1)
    hH := fun Q hQ => s.hH Q (Finset.mem_filter.mp hQ).2
    henclose := by
      intro I hI hlen
      have hm₁ : 0 ≤ max s.X₁ Y₁ := (hL.trans_le hX₁).le.trans (le_max_left _ _)
      have hm₂ : 0 ≤ max s.X₂ Y₂ := (hL.trans_le hX₂).le.trans (le_max_left _ _)
      have hd₁ := ideal_norm_one_le (mul_ne_zero s.hd.1 (s.hB (Sum.inr 0)))
      have hd₂ := ideal_norm_one_le (mul_ne_zero s.hd.2 (s.hB (Sum.inr 1)))
      have hcap : (I.absNorm : ℝ) ≤ referenceCap s Y₁ Y₂ := by
        rcases hlen with hlen | hlen
        · exact hlen.trans (mul_le_mul_of_nonneg_left
            ((div_le_self hm₁ hd₁).trans (le_max_left _ _)) hb)
        · exact hlen.trans (mul_le_mul_of_nonneg_left
            ((div_le_self hm₂ hd₂).trans (le_max_right _ _)) hb)
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp (support_enclosed _ I hI hcap hP)
      exact Finset.mem_image.mpr ⟨Q,Finset.mem_union_right _ hQ,rfl⟩ }

theorem reference_original_enclosure (s : Source ι a b) (hb : 0 ≤ b) (Y₁ Y₂ L : ℝ)
    (hL : 0 < L) (hX₁ : L ≤ s.X₁) (hX₂ : L ≤ s.X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂) (hprod : Y₁*Y₂ = s.T) :
    OriginalEnclosure (referenceSource s hb Y₁ Y₂ L hL hX₁ hX₂ hY₁ hY₂ hprod) := by
  intro I hI hlen
  have hm₁ : 0 ≤ max s.X₁ Y₁ := (hL.trans_le hX₁).le.trans (le_max_left _ _)
  have hm₂ : 0 ≤ max s.X₂ Y₂ := (hL.trans_le hX₂).le.trans (le_max_left _ _)
  have hcap : (I.absNorm : ℝ) ≤ referenceCap s Y₁ Y₂ := by
    rcases hlen with hlen | hlen
    · exact hlen.trans (mul_le_mul_of_nonneg_left
        ((div_le_self hm₁ (ideal_norm_one_le s.hd.1)).trans (le_max_left _ _)) hb)
    · exact hlen.trans (mul_le_mul_of_nonneg_left
        ((div_le_self hm₂ (ideal_norm_one_le s.hd.2)).trans (le_max_right _ _)) hb)
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp (support_enclosed _ I hI hcap hP)
  exact Finset.mem_image.mpr ⟨Q,Finset.mem_union_right _ hQ,rfl⟩

/-- A single coarse bound, chosen before B and the branch, controls all
new enclosure primes. It suffices to bound the actual four lengths. -/
theorem reference_primes_bound (s : Source ι a b) (hb : 0 ≤ b) (Y₁ Y₂ C : ℝ)
    (hS : ∀ Q ∈ s.S, (Q.val.absNorm : ℝ) ≤ C)
    (h₁ : b*s.X₁ ≤ C) (h₂ : b*s.X₂ ≤ C)
    (hy₁ : b*Y₁ ≤ C) (hy₂ : b*Y₂ ≤ C) :
    ∀ Q ∈ referencePrimes s Y₁ Y₂, (Q.val.absNorm : ℝ) ≤ C := by
  intro Q hQ
  rcases Finset.mem_union.mp hQ with hQ | hQ
  · exact hS Q hQ
  · apply (enclosure_bound _ Q hQ).2.trans
    dsimp only [referenceCap]
    simp only [mul_max_of_nonneg _ _ hb]
    exact max_le (max_le h₁ hy₁) (max_le h₂ hy₂)

private theorem enclosed_of_bound (C : ℝ) (Q : PrimeIdeal)
    (hQ : Supported Q.val) (hC : (Q.val.absNorm : ℝ) ≤ C) : Q ∈ enclosure C := by
  have hv : Q.val ∈ primeValues (enclosure C) := by
    rw [enclosure_values]
    exact Finset.mem_filter.mpr ⟨(mem_idealBall _ _).mpr ⟨Q.property.ne_zero,hC⟩,
      Q.property,hQ⟩
  obtain ⟨P,hP,hPQ⟩ := Finset.mem_image.mp hv
  exact Subtype.val_injective hPQ ▸ hP

/-- The enclosure can be chosen before the branch and allocation. Its
only extra inputs are the four literal numerical length bounds and the
old prime bound; no analytical or coefficient-domination premise occurs. -/
def canonicalReferenceSource (s : Source ι a b) (hb : 0 ≤ b) (Y₁ Y₂ L : ℝ)
    (hL : 0 < L) (hX₁ : L ≤ s.X₁) (hX₂ : L ≤ s.X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂) (hprod : Y₁*Y₂ = s.T)
    (C : ℝ) (hS : ∀ Q ∈ s.S, (Q.val.absNorm : ℝ) ≤ C)
    (h₁ : b*s.X₁ ≤ C) (h₂ : b*s.X₂ ≤ C)
    (hy₁ : b*Y₁ ≤ C) (hy₂ : b*Y₂ ≤ C) : Source ι a b := by
  let r := referenceSource s hb Y₁ Y₂ L hL hX₁ hX₂ hY₁ hY₂ hprod
  have hsub : r.S ⊆ enclosure C := by
    intro Q hQ
    exact enclosed_of_bound C Q (r.hS Q hQ)
      (reference_primes_bound s hb Y₁ Y₂ C hS h₁ h₂ hy₁ hy₂ Q hQ)
  exact { r with
    S := enclosure C
    hpool := fun i I hI => by
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp (r.hpool i hI)
      exact Finset.mem_image.mpr ⟨Q,hsub hQ,rfl⟩
    hS := fun Q hQ => (enclosure_bound C Q hQ).1
    henclose := by
      intro I hI hlen P hP
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp (r.henclose I hI hlen hP)
      exact Finset.mem_image.mpr ⟨Q,hsub hQ,rfl⟩ }

/-- Changing the enclosure does not change a single finite column:
its active ordinary punctures were frozen before the enlargement. -/
theorem canonical_reference_coefficient (s : Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (Y₁ Y₂ L : ℝ)
    (hL : 0 < L) (hX₁ : L ≤ s.X₁) (hX₂ : L ≤ s.X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂) (hprod : Y₁*Y₂ = s.T)
    (C : ℝ) (hS : ∀ Q ∈ s.S, (Q.val.absNorm : ℝ) ≤ C)
    (h₁ : b*s.X₁ ≤ C) (h₂ : b*s.X₂ ≤ C)
    (hy₁ : b*Y₁ ≤ C) (hy₂ : b*Y₂ ≤ C) (seed : Id) :
    sourceCoefficient
        (canonicalReferenceSource s hb Y₁ Y₂ L hL hX₁ hX₂ hY₁ hY₂ hprod C hS h₁ h₂ hy₁ hy₂) ha seed =
      sourceCoefficient (referenceSource s hb Y₁ Y₂ L hL hX₁ hX₂ hY₁ hY₂ hprod) ha seed := by
  have hsub : activeHoles s ⊆ enclosure C := by
    intro Q hQ
    exact enclosed_of_bound C Q (s.hS Q (Finset.mem_filter.mp hQ).1)
      (hS Q (Finset.mem_filter.mp hQ).1)
  have he : punctureProduct (enclosure C) (activeHoles s) = punctureProduct s.S s.H := by
    unfold punctureProduct
    congr 1
    ext Q
    simp only [Finset.mem_filter,activeHoles]
    exact ⟨fun h => h.2,fun h => ⟨hsub (Finset.mem_filter.mpr h),h⟩⟩
  change MixedHeightEnergy.originalColumn (enclosure C) (activeHoles s) s.pool s.d s.hd s.R seed
    s.ν s.Wslot s.P _ _ b s.X₁ s.X₂ Y₁ Y₂ =
      MixedHeightEnergy.originalColumn (referencePrimes s Y₁ Y₂) (activeHoles s)
        s.pool s.d s.hd s.R seed s.ν s.Wslot s.P _ _ b s.X₁ s.X₂ Y₁ Y₂
  unfold MixedHeightEnergy.originalColumn
  rw [he,reference_puncture]
  rfl

/- Canonical puncture dictionary, before any norm. Only marked prime
coefficients are deleted; the remaining ordinary mask is displayed. In
particular the ambient character and its modulus are not changed. -/
def puncturedSlot (R : Id) (ν : ι → Id → ℂ) (i : ι) (I : Id) : ℂ :=
  if IsCoprime I R then ν i I else 0

theorem punctured_slot_norm (R : Id) (ν : ι → Id → ℂ)
    (hν : ∀ i I, ‖ν i I‖ ≤ 1) (i : ι) (I : Id) :
    ‖puncturedSlot R ν i I‖ ≤ 1 := by
  unfold puncturedSlot
  split_ifs
  · exact hν i I
  · simp only [norm_zero,zero_le_one]

/-- On the actual marked prime pools this is precisely canonical hole
deletion by the UNION of the previous holes and the full new support.
It makes no cardinality assertion about that support. -/
theorem punctured_canonical_slot (R : Id) (hR : R ≠ 0) (ν : ι → Character)
    (R₀ : ι → Finset Id) (t : ℝ) (i : ι) (Q : PrimeIdeal) :
    puncturedSlot R (slotCoefficient ν R₀ t) i Q.val =
      slotCoefficient ν (fun j => R₀ j ∪ QRH.Record1252270103KernelMass.primeSupport R) t i Q.val := by
  have hc : IsCoprime Q.val R ↔
      Q.val ∉ QRH.Record1252270103KernelMass.primeSupport R := by
    rw [prime_coprime]
    exact not_congr (CenteredMomentNaturalPrimitive.prime_mem_support_iff R Q.val hR Q.property).symm
  by_cases hr : Q.val ∈ R₀ i <;>
    by_cases hp : Q.val ∈ QRH.Record1252270103KernelMass.primeSupport R <;>
    simp only [puncturedSlot,hc,slotCoefficient,heightCoefficient,holeCoefficient,
      Finset.mem_union,hr,hp,or_true,true_or,or_false,false_or,
      not_true_eq_false,not_false_eq_true,ite_true,ite_false,zero_mul]

theorem punctured_canonical_zero (R : Id) (hR : R ≠ 0) (ν : ι → Character)
    (R₀ : ι → Finset Id) (t : ℝ) (H : Finset PrimeIdeal)
    (hHR : ∀ i Q, Q ∈ H → Q.val ∈ R₀ i) (i : ι) (Q : PrimeIdeal)
    (hQ : Q ∈ H ∨ Q.val ∣ R) :
    puncturedSlot R (slotCoefficient ν R₀ t) i Q.val = 0 := by
  rw [punctured_canonical_slot R hR]
  have hm : Q.val ∈ R₀ i ∪ QRH.Record1252270103KernelMass.primeSupport R := by
    rcases hQ with hQ | hQ
    · exact Finset.mem_union_left _ (hHR i Q hQ)
    · exact Finset.mem_union_right _
        ((CenteredMomentNaturalPrimitive.prime_mem_support_iff R Q.val hR Q.property).mpr hQ)
  simp only [slotCoefficient,heightCoefficient,holeCoefficient,hm,ite_true,zero_mul]

/-- Full-mask separation is coefficient equality, not an estimate.
The fifth-free/injective tuple weight may multiply both sides unchanged. -/
theorem profile_puncture_split (R : Id) (ν : ι → Id → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (d₁ d₂ seed : Id) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d₁ d₂ seed v =
      (if IsCoprime (v (Sum.inr 0)*v (Sum.inr 1)) R then (1 : ℂ) else 0) *
        profileCoefficient 1 (puncturedSlot R ν) Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ d₁ d₂ seed v := by
  have hc : IsCoprime (finiteTupleProduct v) R ↔
      IsCoprime (v (Sum.inr 0)*v (Sum.inr 1)) R ∧
        ∀ i, IsCoprime (v (Sum.inl i)) R := by
    simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,
      IsCoprime.mul_left_iff,IsCoprime.prod_left_iff,Finset.mem_univ,forall_const]
    tauto
  by_cases ho : IsCoprime (v (Sum.inr 0)*v (Sum.inr 1)) R
  · by_cases hm : ∀ i, IsCoprime (v (Sum.inl i)) R
    · have hprod : (∏ i, puncturedSlot R ν i (v (Sum.inl i)) *
          Wslot i ((v (Sum.inl i)).absNorm / P i)) =
          ∏ i, ν i (v (Sum.inl i)) * Wslot i ((v (Sum.inl i)).absNorm / P i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [puncturedSlot,hm i,ite_true]
      simp only [profileCoefficient,hc,ho,hm,implies_true,and_self,ite_true,
        isCoprime_one_right,hprod,one_mul,mul_one]
    · obtain ⟨i,hi⟩ := not_forall.mp hm
      have hprod : (∏ j, puncturedSlot R ν j (v (Sum.inl j)) *
          Wslot j ((v (Sum.inl j)).absNorm / P j)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp only [puncturedSlot,hi,ite_false,zero_mul]
      simp only [profileCoefficient,hc,ho,hm,true_and,ite_true,ite_false,
        isCoprime_one_right,hprod,zero_mul,mul_zero]
  · simp only [profileCoefficient,hc,ho,false_and,ite_false,zero_mul,mul_zero]

def enlargedHoles (S H : Finset PrimeIdeal) (R : Id) : Finset PrimeIdeal :=
  S.filter (fun Q => Q ∈ H ∨ Q.val ∣ R)

/-- Prime factors outside the actual enclosure are irrelevant only
because the supported ordinary column has its whole support inside S. -/
theorem enclosed_puncture_coprime (S H : Finset PrimeIdeal) (R I : Id)
    (hR : R ≠ 0) (hI : I ≠ 0)
    (hS : QRH.Record1252270103KernelMass.primeSupport I ⊆ primeValues S) :
    IsCoprime (punctureProduct S (enlargedHoles S H R)) I ↔
      IsCoprime (punctureProduct S H) I ∧ IsCoprime R I := by
  have hc (T : Finset PrimeIdeal) : IsCoprime (punctureProduct S T) I ↔
      ∀ Q ∈ S, Q ∈ T → ¬Q.val ∣ I := by
    simp only [punctureProduct,IsCoprime.prod_left_iff,Finset.mem_filter,prime_coprime]
    tauto
  rw [hc,hc]
  constructor
  · intro h
    refine ⟨fun Q hQ hH => h Q hQ (Finset.mem_filter.mpr ⟨hQ,Or.inl hH⟩),?_⟩
    apply IsCoprime.symm
    apply (CenteredMomentNaturalPrimitive.coprime_support_iff I R hR).mpr
    intro P hP
    have hp : Prime P := primeSupport_prime hP
    have hPR : P ∣ R :=
      (CenteredMomentNaturalPrimitive.prime_mem_support_iff R P hR hp).mp hP
    by_cases hd : P ∣ I
    · have hPI := (CenteredMomentNaturalPrimitive.prime_mem_support_iff I P hI hp).mpr hd
      obtain ⟨Q,hQ,hQP⟩ := Finset.mem_image.mp (hS hPI)
      have hQR : Q.val ∣ R := hQP.symm ▸ hPR
      have hQI : Q.val ∣ I := hQP.symm ▸ hd
      exact False.elim (h Q hQ (Finset.mem_filter.mpr ⟨hQ,Or.inr hQR⟩) hQI)
    · exact ((prime_coprime (⟨P,hp⟩ : PrimeIdeal) I).mpr hd).symm
  · rintro ⟨hH,hRcop⟩ Q hQ hnew
    rcases (Finset.mem_filter.mp hnew).2 with hQH | hQR
    · exact hH Q hQ hQH
    · exact (prime_coprime Q I).mp (hRcop.of_isCoprime_of_dvd_left hQR)

theorem enlarged_tuple_weight (S H : Finset PrimeIdeal) (R : Id) (hR : R ≠ 0)
    (v : Tuple ι) (hv : v (Sum.inr 0)*v (Sum.inr 1) ≠ 0)
    (hS : QRH.Record1252270103KernelMass.primeSupport
      (v (Sum.inr 0)*v (Sum.inr 1)) ⊆ primeValues S) :
    tupleWeight (punctureProduct S (enlargedHoles S H R)) v =
      (if IsCoprime (v (Sum.inr 0)*v (Sum.inr 1)) R then (1 : ℂ) else 0) *
        tupleWeight (punctureProduct S H) v := by
  have he := enclosed_puncture_coprime S H R
    (v (Sum.inr 0)*v (Sum.inr 1)) hR hv hS
  have hs : IsCoprime R (v (Sum.inr 0)*v (Sum.inr 1)) ↔
      IsCoprime (v (Sum.inr 0)*v (Sum.inr 1)) R := isCoprime_comm
  unfold tupleWeight tupleRestriction restriction
  simp only [IsCoprime.mul_left_iff,he,hs]
  split_ifs <;> simp_all

/-- Final literal canonical puncture dictionary. It keeps the ambient
character entirely untouched: multiply either side by any character,
height, Fourier or ray factor. All ordinary restrictions remain inside
the same term; no norm monotonicity is invoked. -/
theorem canonical_punctured_tuple (S H : Finset PrimeIdeal) (R : Id) (hR : R ≠ 0)
    (ν : ι → Character) (R₀ : ι → Finset Id) (t : ℝ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (d₁ d₂ seed : Id) (v : Tuple ι)
    (hp : ∀ i, Prime (v (Sum.inl i)))
    (hv : v (Sum.inr 0)*v (Sum.inr 1) ≠ 0)
    (hS : QRH.Record1252270103KernelMass.primeSupport
      (v (Sum.inr 0)*v (Sum.inr 1)) ⊆ primeValues S) :
    tupleWeight (punctureProduct S H) v *
      profileCoefficient R (slotCoefficient ν R₀ t) Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ d₁ d₂ seed v =
      tupleWeight (punctureProduct S (enlargedHoles S H R)) v *
        profileCoefficient 1
          (slotCoefficient ν (fun i => R₀ i ∪ QRH.Record1252270103KernelMass.primeSupport R) t)
          Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d₁ d₂ seed v := by
  rw [profile_puncture_split,enlarged_tuple_weight S H R hR v hv hS]
  have hslot : (∏ i, puncturedSlot R (slotCoefficient ν R₀ t) i (v (Sum.inl i)) *
      Wslot i ((v (Sum.inl i)).absNorm / P i)) =
      ∏ i, slotCoefficient ν
        (fun j => R₀ j ∪ QRH.Record1252270103KernelMass.primeSupport R) t i (v (Sum.inl i)) *
        Wslot i ((v (Sum.inl i)).absNorm / P i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [punctured_canonical_slot R hR ν R₀ t i (⟨v (Sum.inl i),hp i⟩ : PrimeIdeal)]
  unfold profileCoefficient
  rw [hslot]
  ring

/- The physical first-energy presentation also uses Source.R in m.
This is harmless here for a proved reason: m occurs to the SIXTH power,
and its extra ideal factor is exactly a redundant coprimality mask. -/
theorem source_weight_mask (s : Source ι a b) (ha : 0 < a) (seed R : Id)
    (hR : R ∣ s.R) (η : Character) (A z : O) (t : ℝ) (I : Id) :
    sourceCoefficient s ha seed I * rowWeight η (fixedBadMask*idealGenerator R) A z t I =
      sourceCoefficient s ha seed I * rowWeight η fixedBadMask A z t I := by
  by_cases hc : sourceCoefficient s ha seed I = 0
  · simp only [hc,zero_mul]
  · have hm := MixedOriginalCoprimality.original_nonzero_masks
      s.S s.H s.pool s.d s.hd s.R seed s.ν s.Wslot s.P
      (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
      (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
      b s.X₁ s.X₂ s.Y₁ s.Y₂ I hc
    have hcop : IsCoprime I R := hm.1.of_isCoprime_of_dvd_right hR
    rw [← rowWeight_ideal_mask η fixedBadMask A z t
      (dvd_mul_right goodLambda (2 : O)) (dvd_mul_left (2 : O) goodLambda) R I]
    rw [if_pos hcop,one_mul]

/-- Even with an arbitrary selected twist or Fourier column multiplier,
the old and enlarged presentations give exactly the same first energy.
The original eta, A, height and frequency variable are all preserved. -/
theorem source_mask_energy (s : Source ι a b) (ha : 0 < a) (seed R : Id)
    (hR : R ∣ s.R) (η : Character) (A : O) (t : ℝ)
    (μ : Id → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η (fixedBadMask*idealGenerator R) A t (sourceColumns s)
        (fun I => sourceCoefficient s ha seed I*μ I) Φ K =
      finiteHeckeEnergy η fixedBadMask A t (sourceColumns s)
        (fun I => sourceCoefficient s ha seed I*μ I) Φ K := by
  have hrow (z : O) : (∑ I ∈ sourceColumns s,
        (sourceCoefficient s ha seed I*μ I)*rowWeight η (fixedBadMask*idealGenerator R) A z t I) =
      ∑ I ∈ sourceColumns s,
        (sourceCoefficient s ha seed I*μ I)*rowWeight η fixedBadMask A z t I := by
    apply Finset.sum_congr rfl
    intro I hI
    calc
      _ = (sourceCoefficient s ha seed I*rowWeight η (fixedBadMask*idealGenerator R) A z t I)*μ I := by ring
      _ = (sourceCoefficient s ha seed I*rowWeight η fixedBadMask A z t I)*μ I := by
        rw [source_weight_mask s ha seed R hR]
      _ = _ := by ring
  unfold finiteHeckeEnergy
  simp_rw [hrow]

theorem seeded_mask_energy (s : Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : OriginalEnclosure s) (F : Id) (hF : F ≠ 0)
    (B : boundedLabels (tuplePools s) F) (η : Character) (A : O) (t : ℝ)
    (μ : Id → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let r := seededRebasedSource s hb cover F hF B
    finiteHeckeEnergy η (fixedBadMask*idealGenerator r.R) A t (sourceColumns r)
        (fun I => sourceCoefficient r ha 1 I*μ I) Φ K =
      finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) A t (sourceColumns r)
        (fun I => sourceCoefficient r ha 1 I*μ I) Φ K := by
  dsimp only
  rw [source_mask_energy _ ha 1 _ (dvd_refl _)]
  exact (source_mask_energy _ ha 1 s.R (dvd_mul_right s.R F) η A t μ Φ K).symm

/-- The actual first physical row, including the selected cubic twist,
is a multiplicative ideal weight. Its original character and height are
not replaced in the seed allocation. -/
def selectedRowHom (η : Character) (m A z : O) (t : ℝ) (F : Id) : Id→*ℂ where
  toFun I := selectedTwist F I*rowWeight η m A z t I
  map_one' := by simp only [selectedTwist,map_one,one_pow,one_mul]
  map_mul' I J := by rw [selectedTwist_mul,map_mul];ring

theorem selected_row_hom_norm (η : Character) (m A z : O) (t : ℝ)
    (F I : Id) (hI : I≠0) : ‖selectedRowHom η m A z t F I‖≤1 := by
  change ‖selectedTwist F I*rowWeight η m A z t I‖≤1
  rw [norm_mul]
  exact (mul_le_mul (selectedTwist_norm F I) (rowWeight_norm_le_one η m A z t I hI)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- Literal decomposition of the actual selected physical row, before
any norm or Cauchy inequality. Frozen selected phases remain outside
their live row and are bounded only by the following scalar theorem. -/
theorem seeded_selected_row (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (D : Id) (hD : Squarefree D)
    (η : Character) (m A z : O) (t : ℝ) (F : Id) :
    (∑I∈sourceColumns s,selectedCoefficient s ha D F I*rowWeight η m A z t I)=
      ∑alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
        ∑B : boundedLabels (tuplePools s) D,
          frozenScalar s D D alloc B (selectedRowHom η m A z t F)*
            (∑I∈sourceColumns (seededRebasedSource s hb cover D hD.ne_zero B),
              selectedCoefficient (seededRebasedSource s hb cover D hD.ne_zero B) ha 1 F I*
                rowWeight η m A z t I) := by
  simpa only [rawRow,selectedRowHom,MonoidHom.coe_mk,OneHom.coe_mk,
    selectedCoefficient,mul_assoc] using
    seeded_raw_decomposition s ha hb cover D hD (selectedRowHom η m A z t F)

/-- The extra physical phase in the exact decomposition is paid,
including its selected twist, with the same full reciprocal seed norm
and precisely one original prefix denominator. -/
theorem selected_frozen_normalized_cost (s : Source ι a b)
    (D : Id) (hD : Squarefree D)
    (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (B : boundedLabels (tuplePools s) D)
    (η : Character) (m A z : O) (t : ℝ) (F : Id) :
    (‖frozenScalar s D D alloc B (selectedRowHom η m A z t F)‖^2/
      rawReduction B.val s.P)/pairNorm s.d≤
      (∏i,s.M i)^2*(2:ℝ)^Fintype.card ι/(pairNorm s.d*(D.absNorm:ℝ)) := by
  have hB := (allocation_data (tuplePools s) D B.val (Finset.mem_filter.mp B.property).1).1
  have hprod : finiteTupleProduct B.val≠0 := Finset.prod_ne_zero_iff.mpr (fun j _=>hB j)
  have hnorm : ‖frozenScalar s D D alloc B (selectedRowHom η m A z t F)‖≤
      ‖frozenWeight (punctureProduct s.S s.H) B.val*allocationTerm D Finset.univ B.val alloc*
        frozenCoefficient B.val (finiteTupleProduct B.val) s.R s.ν s.Wslot s.P‖ := by
    unfold frozenScalar
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (selected_row_hom_norm η m A z t F _ hprod)
  have hr := rawReduction_pos B.val hB s.P (fun i=>zero_lt_one.trans_le (s.hP i))
  exact (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hr.le)
    (pairNorm_pos s.hd.1 s.hd.2).le).trans
    (seed_frozen_cost_with_prefix (punctureProduct s.S s.H) s.R D hD alloc B.val hB s.d s.hd
      s.ν s.Wslot s.P s.M (fun i=>zero_lt_one.trans_le (s.hP i)) s.hν s.hWnorm s.hM s.hW)

end
end Candidate.Feedback.FourthPower.MixedFirstSeededSource
