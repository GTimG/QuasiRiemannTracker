import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedFixedAmplitudeCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorHighBatchCount
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedAdaptiveCutoff

/- Original finite rows and moments at the retuned cutoff; moment bounds remain inputs. -/
set_option autoImplicit false

namespace BelowSevenEighthsTight.FiberExtension

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst RowCountExtension

theorem balanced_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ κ₀ capacity ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → 13/18≤κ₀ → κ₀≤3/4 → capacity=κ₀+2*Δ → capacity≤1 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff κ₀ (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        CapacityMoments (B.fiber bin j J K hne) capacity c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(rowEnvelope (1/(3*κ₀)) (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    FiberExtension.fixed_amplitude_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ κ₀ capacity ν C height q i hU ha hd hε hε' hΔ hk₀ hk₀u hk hku hν hC hh hf Label Slot _ B hne hq hmom
  have hδ : 0<2*a-1 := by linarith
  have hqb := FiberExtension.batch_mean_bounds B hne (by linarith) q hq
  have hx : 0≤q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := cutoff_bounds κ₀ (2*a-1) q hk₀ hk₀u hδ.le
  have hc' := hcount a ε (cutoff κ₀ (2*a-1) q) T allowance Δ κ₀ capacity ν C height q i
    hU ha hd hε hε' ht.1 ht.2 hΔ hk₀ hk₀u hk hku hν hC hh hf B hq hmom
  have he : max (shortExponent (1/(3*κ₀)) (2*a-1) (q/(2*a-1)) (cutoff κ₀ (2*a-1) q))
      (longExponent (2*a-1) (cutoff κ₀ (2*a-1) q)) =
      rowEnvelope (1/(3*κ₀)) (2*a-1) (1/2-q/(2*a-1)) := by
    rw [cutoff_eq_balanced κ₀ (2*a-1) q hδ hd hqb.1 hqb.2]
    exact FiberExtension.balanced_count_identity κ₀ (2*a-1) (q/(2*a-1)) hk₀ hk₀u hδ.le hd hx hx'
  rw [he] at hc'
  exact hc'

theorem high_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance κ₀ capacity C height q : ℝ) (i : ℕ),
      1<U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff κ₀ (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        CapacityMoments (B.fiber bin j J K hne) capacity c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorHighBatchCount.high_batch_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance κ₀ capacity C height q i hU ha ha' hε hε' hC hh hf
  rw [cutoff_eq_high κ₀ (2*a-1) q ha]
  exact hcount a ε T allowance ((capacity-3/4)/2) C height i hU ha.le ha' hε hε' hC hh hf

#print axioms balanced_adaptive_count_from_raw_moments
#print axioms high_adaptive_count_from_raw_moments

end

end BelowSevenEighthsTight.FiberExtension
