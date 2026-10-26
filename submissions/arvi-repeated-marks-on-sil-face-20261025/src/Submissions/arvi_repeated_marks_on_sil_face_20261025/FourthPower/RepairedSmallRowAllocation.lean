/- Copyright (c) 2026 Sil. Apache-2.0.
Same-second-common allocation of the ORDINARY restricted row.  No new
Gauss/Poisson generation, no change of the original keep or normalization.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshSelectedWindow
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedNativeFloor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallRowAllocation
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentRowNorm CenteredMomentLattice CenteredMomentSourceRectangle
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentRestrictedDomain
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedCommonCoefficient
open MixedCommonEnergy MixedFirstLiveSource MixedFirstAvoidance MixedOriginalSource
open MixedLiveRows MixedCommonRestriction MixedLiteralAllocation
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def frozenScalar (s : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools s) G) : ℂ :=
  frozenWeight (punctureProduct s.S s.H) B.val *
    frozenCoefficient B.val G s.R s.ν s.Wslot s.P

def sectorEnergy (s : Source ι a b) (ha : 0<a) (G : Id) (hG : Supported G)
    (seed D : Id) (f : Id → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  sourceRestrictedEnergy keep (residualPool G hG.1 (sourceColumns s))
    (fun I => if IsCoprime G I ∧ D∣I then sourceCoefficient s ha seed (G*I) else 0)
    f Φ K

def liveEnergy (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (D : Id) (f : Id → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  sourceRestrictedEnergy keep (sourceColumns (allocatedLiveSource s hb cover G B))
    (sourceCoefficient (allocatedLiveSource s hb cover G B) ha D) f Φ K

theorem source_restricted_congr (S T : Finset Id) (c f : Id → ℂ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : ∀I,c I≠0 → (I∈S ↔ I∈T)) :
    sourceRestrictedEnergy keep S c f Φ K=sourceRestrictedEnergy keep T c f Φ K := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  by_cases hk : keep z
  · simp only [if_pos hk]
    have he : rowPolynomial Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*f I) z=
        rowPolynomial Finset.univ (sourceGenerator T)
          (fun I : supportedColumns T => c I*f I) z := by
      rw [source_rowPolynomial S (fun I => c I*f I) z,
        source_rowPolynomial T (fun I => c I*f I) z]
      simpa only [mul_assoc] using
        sum_same_support (supportedColumns S) (supportedColumns T) c
          (fun I => f I*CanonicalRowCompletion.idealRowHom z I)
          (fun I hI hn => Finset.mem_filter.mpr
            ⟨(h I hn).mp (Finset.mem_filter.mp hI).1,(Finset.mem_filter.mp hI).2⟩)
          (fun I hI hn => Finset.mem_filter.mpr
            ⟨(h I hn).mpr (Finset.mem_filter.mp hI).1,(Finset.mem_filter.mp hI).2⟩)
    rw [he]
  · simp only [if_neg hk]

/-- The artificial D mask remains on the residual ideal throughout. -/
theorem sector_coefficient (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G seed D I : Id) (hG : G≠0)
    (hI : I≠0) (hseed : seed∣G) :
    (if IsCoprime G I ∧ D∣I then sourceCoefficient s ha seed (G*I) else 0)=
      ∑B : actualAllocations (tuplePools s) G,
        frozenScalar s G B * sourceCoefficient (allocatedLiveSource s hb cover G B) ha D I := by
  have he := punctured_restricted_column (punctureProduct s.S s.H) (tuplePools s)
    (source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂)
    (fun i J hJ => s.hp i J hJ) G s.R seed I hG hI hseed s.ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2
  by_cases hD : D∣I
  · simp only [hD,and_true]
    apply he.trans
    apply Finset.sum_congr rfl
    intro B hB
    rw [show allocatedLiveSource s hb cover G B =
      liveSource (allocationSource s hb cover G B) from rfl,live_source_coefficient]
    simp only [if_pos hD,frozenScalar]
    rfl
  · simp only [hD,and_false,if_false]
    symm
    apply Finset.sum_eq_zero
    intro B hB
    rw [show allocatedLiveSource s hb cover G B =
      liveSource (allocationSource s hb cover G B) from rfl,live_source_coefficient]
    simp only [if_neg hD,mul_zero]

theorem live_support (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (hG : G≠0)
    (B : actualAllocations (tuplePools s) G) (D I : Id)
    (hn : sourceCoefficient (allocatedLiveSource s hb cover G B) ha D I≠0) :
    I∈residualPool G hG (sourceColumns s) ∧
      I∈sourceColumns (allocatedLiveSource s hb cover G B) := by
  have hmem : I∈sourceColumns (allocatedLiveSource s hb cover G B) :=
    finite_column_mem _ _ I hn
  rw [show allocatedLiveSource s hb cover G B =
    liveSource (allocationSource s hb cover G B) from rfl,live_source_coefficient] at hn
  split_ifs at hn with hD
  · have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
    have hs := masked_live_support (tuplePools s)
      (source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂)
      (fun i J hJ => s.hp i J hJ) B.val hB G s.R I
      (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
      s.ν s.Wslot s.P
      (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
      (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 (tupleWeight (punctureProduct s.S s.H)) hn
    exact ⟨(mem_residualPool G hG (sourceColumns s) I).mpr hs.1,hmem⟩
  · exact False.elim (hn rfl)

/-- Cauchy on the existing ORDINARY row, at its existing physical radius. -/
theorem sector_energy_le_allocations (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G seed D : Id) (hG : Supported G) (hseed : seed∣G)
    (f : Id → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    sectorEnergy s ha G hG seed D f keep Φ K ≤
      ((actualAllocations (tuplePools s) G).card:ℝ)*
        ∑B : actualAllocations (tuplePools s) G,
          ‖frozenScalar s G B‖^2 * liveEnergy s ha hb cover G B D f keep Φ K := by
  let Q := residualPool G hG.1 (sourceColumns s)
  let c := fun B : actualAllocations (tuplePools s) G => frozenScalar s G B
  let d := fun (B : actualAllocations (tuplePools s) G) (I : supportedColumns Q) =>
    sourceCoefficient (allocatedLiveSource s hb cover G B) ha D I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime G I.val ∧ D∣I.val then sourceCoefficient s ha seed (G*I.val) else 0)*f I.val=
        ∑B,c B*d B I := by
    rw [sector_coefficient s ha hb cover G seed D I.val hG.1
      (Finset.mem_filter.mp I.property).2.1 hseed,Finset.sum_mul]
    simp only [c,d,mul_assoc]
  have hc := smoothed_restricted_allocation keep Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) c d Φ K hK hΦ
  unfold sectorEnergy sourceRestrictedEnergy
  rw [funext he]
  apply hc.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ => ((actualAllocations (tuplePools s) G).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun x : ℝ => ‖c B‖^2*x)
  exact source_restricted_congr Q (sourceColumns (allocatedLiveSource s hb cover G B))
    (sourceCoefficient (allocatedLiveSource s hb cover G B) ha D) f keep Φ K
    (fun I hn => ⟨fun _ => (live_support s ha hb cover G hG.1 B D I hn).2,
      fun _ => (live_support s ha hb cover G hG.1 B D I hn).1⟩)

theorem live_energy_nonneg (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (D : Id) (f : Id → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤liveEnergy s ha hb cover G B D f keep Φ K := by
  unfold liveEnergy sourceRestrictedEnergy restrictedEnergy
  apply tsum_nonneg
  intro z
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (hΦ z)
  · exact le_rfl

/-- Only live coefficients are identified. The original avoided labels
and their actual frozen scalar remain on the left of the finite estimate. -/
theorem avoided_sector_energy_le (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (u G seed D : Id) (hG : Supported G)
    (hseed : seed∣G) (hu : u∣s.R*G) (f : Id → ℂ) (keep : O → Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    sectorEnergy (avoidSource s u) ha G hG seed D f keep Φ K ≤
      ((actualAllocations (tuplePools s) G).card:ℝ)*
        ∑B : actualAllocations (tuplePools s) G,
          ‖frozenScalar s G B‖^2 * liveEnergy s ha hb cover G B D f keep Φ K := by
  apply (sector_energy_le_allocations (avoidSource s u) ha hb cover G seed D hG hseed
    f keep Φ K hK hΦ).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B hB
  have he : liveEnergy (avoidSource s u) ha hb cover G B D f keep Φ K=
      liveEnergy s ha hb cover G B D f keep Φ K := by
    unfold liveEnergy
    rw [funext (allocated_coefficients s ha hb cover u G hu B D)]
    rfl
  rw [he]
  exact mul_le_mul_of_nonneg_right (frozen_weight_le s u G B)
    (live_energy_nonneg s ha hb cover G B D f keep Φ K hΦ)

end
end Candidate.FourthPower.RepairedSmallRowAllocation
