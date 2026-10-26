/- Copyright (c) 2026. Released under Apache 2.0. -/
import Candidate.Cycle63.Arithmetic.Bernstein.Endpoint
import Candidate.Cycle63.Arithmetic.Bernstein.Feedback
import Candidate.Cycle63.Physical.WitnessGeometry
import Candidate.Affine.Count

/-! Batch-level detector counts: the original count at the original cutoff,
and the region-aware count `countingR` at the region-aware cutoff `cutoffA`. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.DetectorAffineCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount Cycle25DetectorRawFiber

/-- The detector cutoff: the new cutoff on the affine region, else the original. -/
def cutoffA (δ p κ : ℝ) : ℝ :=
  if DetectorAffine.InRegion δ p ∧ Cycle63.Arithmetic.kappaStar ≤ κ then DetectorAffine.tN δ p
  else cutoff δ p κ

theorem rowCount_eq_countingR0 {κ δ p : ℝ} (hk : 7/10 ≤ κ) :
    rowCount δ p κ = Cycle63.Arithmetic.Bernstein.countingR0 κ δ p := by
  simp only [rowCount, Cycle63.Arithmetic.Bernstein.countingR0, V,
    Cycle63.Arithmetic.Bernstein.rowDen, Cycle63.Physical.coefficient_eq_old hk]

theorem cutoffA_bounds {δ p κ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 3/4)
    (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4) :
    1 ≤ cutoffA δ p κ ∧ cutoffA δ p κ ≤ 3/2 := by
  unfold cutoffA
  split_ifs with hreg
  · exact DetectorAffine.region_tN hreg.1
  · exact cutoff_bounds hδ hδ1 hp hp1 hk hk1

theorem balanced_both
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      (∀(a ε T allowance κplain ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(rowCount (2*a-1) (q/(2*a-1)) κplain+
          159*ε+εm+B.mesh+7*ν)) ∧
      (∀(a ε T allowance κplain ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/100000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/100 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoffA (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        AffineMarkedMoment (B.fiber bin j J K hne) C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Cycle63.Arithmetic.Bernstein.countingR κplain (2*a-1) (q/(2*a-1))+
          159*ε+εm+B.mesh+7*ν)) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    count_from_raw_moments_both M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  obtain ⟨hold,hnew⟩ := hcount
  constructor
  · intro a ε T allowance κplain ν C height q i hU ha hd hε hε' hk hk1 hν hC hh hf Label Slot _ B hne hq hmom
    have hδ : 0<2*a-1 := by linarith
    have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
    have hx : 0≤q/(2*a-1) := div_nonneg hqb.1 hδ.le
    have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
    have ht := cutoff_bounds hδ.le hd hx hx' hk hk1
    have he := max_at_cutoff hδ.le hd hx hx' hk hk1
    have hb := B.card_bound (fiberConstant C height K₀)
      (fun _=>rowCount (2*a-1) (q/(2*a-1)) κplain+159*ε+εm+B.mesh+7*ν)
      (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
        intro bin j J K hne'
        have hc' := hold a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance κplain ν C height i
          hU ha hd hε hε' ht.1 ht.2 hk hk1 hν hC hh hf
          (B.fiber bin j J K hne') (hmom bin j J K hne')
        rw [fiber_mean_eq B q hq bin j J K hne', he] at hc'
        exact hc')
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
  · intro a ε T allowance κplain ν C height q i hU ha hd hε hε' hk hk1 hν hν1 hC hh hf
      Label Slot _ B hne hq hmom haff
    have hδ : 0<2*a-1 := by linarith
    have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
    have hx : 0≤q/(2*a-1) := div_nonneg hqb.1 hδ.le
    have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
    have ht := cutoffA_bounds hδ.le hd hx hx' hk hk1
    by_cases hreg : DetectorAffine.InRegion (2*a-1) (q/(2*a-1)) ∧ Cycle63.Arithmetic.kappaStar ≤ κplain
    · have hcut : cutoffA (2*a-1) (q/(2*a-1)) κplain = DetectorAffine.tN (2*a-1) (q/(2*a-1)) :=
        if_pos hreg
      have hR : Cycle63.Arithmetic.Bernstein.countingR κplain (2*a-1) (q/(2*a-1)) =
          DetectorAffine.RNew (2*a-1) (q/(2*a-1)) := by
        unfold Cycle63.Arithmetic.Bernstein.countingR; rw [if_pos hreg]
      have hrN := DetectorAffine.region_rN hreg.1
      have hmN := DetectorAffine.region_mN hreg.1
      have htail := DetectorAffine.region_tail hreg.1 hk hk1
      have hmax := DetectorAffine.region_max hreg.1
      rw [← hcut] at hrN hmN htail hmax
      have hb := B.card_bound (fiberConstant C height K₀)
        (fun _=>Cycle63.Arithmetic.Bernstein.countingR κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
        (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
          intro bin j J K hne'
          have hmean := fiber_mean_eq B q hq bin j J K hne'
          have hc' := hnew a ε (cutoffA (2*a-1) (q/(2*a-1)) κplain) T allowance κplain ν C height i
            hU ha hd hε hε' ht.1 ht.2 hk hk1 hν hν1 hC hh hf
            (B.fiber bin j J K hne') (by rw [hmean]; exact hrN.1) (by rw [hmean]; exact hrN.2)
            (by rw [hmean]; exact hmN) (by rw [hmean]; exact htail)
            (hmom bin j J K hne') (haff bin j J K hne')
          rw [hmean, hmax, ← hR] at hc'
          exact hc')
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
    · have hcut : cutoffA (2*a-1) (q/(2*a-1)) κplain = cutoff (2*a-1) (q/(2*a-1)) κplain :=
        if_neg hreg
      have hR : Cycle63.Arithmetic.Bernstein.countingR κplain (2*a-1) (q/(2*a-1)) =
          rowCount (2*a-1) (q/(2*a-1)) κplain := by
        unfold Cycle63.Arithmetic.Bernstein.countingR; rw [if_neg hreg, rowCount_eq_countingR0 hk]
      have he := max_at_cutoff hδ.le hd hx hx' hk hk1
      rw [← hcut] at he
      have hb := B.card_bound (fiberConstant C height K₀)
        (fun _=>Cycle63.Arithmetic.Bernstein.countingR κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
        (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
          intro bin j J K hne'
          have hc' := hold a ε (cutoffA (2*a-1) (q/(2*a-1)) κplain) T allowance κplain ν C height i
            hU ha hd hε (by linarith) ht.1 ht.2 hk hk1 hν hC hh hf
            (B.fiber bin j J K hne') (hmom bin j J K hne')
          rw [fiber_mean_eq B q hq bin j J K hne', he, ← hR] at hc'
          exact hc')
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb

end SevenEighths.DetectorAffineCount
end
end OAI
