import Candidate.Target836.Detector836.AllCount
import Candidate.Target836.Detector836.Schedule

set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Detector836Count
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount Cycle25DetectorRawFiber

/-- Actual batch count with the new, accepted-low-density and old branches.
The analytic affine moment remains an explicit hypothesis on each actual fiber. -/
theorem balanced836
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance κplain ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/100000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/100 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε
          (Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        AffineMarkedMoment836 (B.fiber bin j J K hne) C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Detector836.count κplain (2*a-1) (q/(2*a-1))+
          159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    count_from_raw_moments_all836 M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  obtain ⟨hold,hnew,haccepted⟩ := hcount
  intro a ε T allowance κplain ν C height q i hU ha hd hε hε' hk hk1 hν hν1 hC hh hf
    Label Slot _ B hne hq hmom haff
  have hδ : 0<2*a-1 := by linarith
  have hqb := batch_mean_bounds B hne (by linarith) q hq
  have hx : 0≤q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := Detector836.cutoff_bounds hδ.le hd hx hx' hk hk1
  by_cases hn : Detector836.InRegion (2*a-1) (q/(2*a-1)) ∧ Detector836.kStar ≤ κplain
  · have hcut : Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain =
        Detector836.tN (2*a-1) (q/(2*a-1)) := if_pos hn
    have hR : Detector836.count κplain (2*a-1) (q/(2*a-1)) =
        Detector836.RNew (2*a-1) (q/(2*a-1)) := if_pos hn
    have hrN := Detector836.region_rN hn.1
    have hmN := Detector836.region_mN hn.1
    have htail := Detector836.region_tail hn.1 hk hk1
    have hmax := Detector836.region_max hn.1
    rw [←hcut] at hrN hmN htail hmax
    have hb := B.card_bound (fiberConstant C height K₀)
      (fun _=>Detector836.count κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
      (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
        intro bin j J K hne'
        have hmean := fiber_mean_eq B q hq bin j J K hne'
        have hb' := hnew a ε (Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain)
          T allowance κplain ν C height i hU ha hd hε hε' ht.1 ht.2 hk hk1 hν hν1 hC hh hf
          (B.fiber bin j J K hne') (by rw [hmean];exact hrN.1)
          (by rw [hmean];exact hrN.2) (by rw [hmean];exact hmN)
          (by rw [hmean];exact htail) (hmom bin j J K hne') (haff bin j J K hne')
        rw [hmean,hmax,←hR] at hb'
        exact hb')
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
  · by_cases haffregion : Detector836.InAcceptedRegion (2*a-1) (q/(2*a-1)) ∧ Detector836.kStar ≤ κplain
    · have hcut : Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain =
          DetectorAffine.tN (2*a-1) (q/(2*a-1)) := by
        unfold Detector836.cutoff;rw [if_neg hn,if_pos haffregion]
      have hR : Detector836.count κplain (2*a-1) (q/(2*a-1)) =
          DetectorAffine.RNew (2*a-1) (q/(2*a-1)) := by
        unfold Detector836.count;rw [if_neg hn,if_pos haffregion]
      have hsub := Detector836.accepted_region_subset haffregion.1
      have hrN := DetectorAffine.region_rN hsub
      have hmN := DetectorAffine.region_mN hsub
      have htail := DetectorAffine.region_tail hsub hk hk1
      have hmax := DetectorAffine.region_max hsub
      rw [←hcut] at hrN hmN htail hmax
      have hb := B.card_bound (fiberConstant C height K₀)
        (fun _=>Detector836.count κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
        (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
          intro bin j J K hne'
          have hmean := fiber_mean_eq B q hq bin j J K hne'
          have hb' := haccepted a ε (Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain)
            T allowance κplain ν C height i hU ha hd hε hε' ht.1 ht.2 hk hk1 hν hν1 hC hh hf
            (B.fiber bin j J K hne') (by rw [hmean];exact hrN.1)
            (by rw [hmean];exact hrN.2) (by rw [hmean];exact hmN)
            (by rw [hmean];exact htail) (hmom bin j J K hne') (haff bin j J K hne')
          rw [hmean,hmax,←hR] at hb'
          exact hb')
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
    · have hcut : Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain =
          cutoff (2*a-1) (q/(2*a-1)) κplain := by
        unfold Detector836.cutoff;rw [if_neg hn,if_neg haffregion]
      have hR : Detector836.count κplain (2*a-1) (q/(2*a-1)) =
          rowCount (2*a-1) (q/(2*a-1)) κplain := by
        unfold Detector836.count;rw [if_neg hn,if_neg haffregion]
        exact (DetectorAffineCount.rowCount_eq_countingR0 hk).symm
      have he := max_at_cutoff hδ.le hd hx hx' hk hk1
      rw [←hcut] at he
      have hb := B.card_bound (fiberConstant C height K₀)
        (fun _=>Detector836.count κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
        (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
          intro bin j J K hne'
          have hb' := hold a ε (Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain)
            T allowance κplain ν C height i hU ha hd hε (by linarith) ht.1 ht.2 hk hk1 hν hC hh hf
            (B.fiber bin j J K hne') (hmom bin j J K hne')
          rw [fiber_mean_eq B q hq bin j J K hne',he,←hR] at hb'
          exact hb')
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb

end SevenEighths.Detector836Count
end
end OAI

#print axioms OAI.SevenEighths.Detector836Count.balanced836
