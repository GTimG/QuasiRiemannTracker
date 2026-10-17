import Candidate.Target830.Physical.CountChoice
import Candidate.Target830.Physical.CountFromMoments
import Candidate.Affine.Balanced

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.Target830.Physical.DetectorCount
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
  HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
  HeckeDetectorFixedAmplitudeCount Cycle25DetectorRawFiber

/-- The finite count envelope is realized on the original batches. Its cutoff
is selected from the old crossing and the ten certified windows before the
actual batch is supplied. All five genuine affine moments remain explicit. -/
theorem balanced830
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
      7/10≤κplain → κplain≤kappa0 → 0<ν → ν≤1/100000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,∀P : Count.Plane,
        Count.lowerPlain P ≤ (B.fiber bin j J K hne).m →
        (B.fiber bin j J K hne).m ≤ Count.mHi →
        Count.AffineMarkedMoment (B.fiber bin j J K hne) P C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Count.count κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := count_from_raw_moments_finite
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  obtain ⟨hold,hnew⟩ := hcount
  intro a ε T allowance κplain ν C height q i hU ha hd hε hε' hk hk1 hν hν1 hC hh hf
    Label Slot _ B hne hq hmom haff
  have hδ : 0<2*a-1 := by linarith
  have hqb := batch_mean_bounds B hne (by linarith) q hq
  have hp : 0≤q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hp' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := cutoff_bounds hδ.le hd hp hp' hk hk1
  cases he : choice κplain (2*a-1) (q/(2*a-1)) with
  | none =>
    have hcut : cutoff (2*a-1) (q/(2*a-1)) κplain =
        Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) κplain := by simp [cutoff,he]
    have hR : Count.count κplain (2*a-1) (q/(2*a-1)) =
        rowCount (2*a-1) (q/(2*a-1)) κplain := by
      exact (choice_none he).trans (DetectorAffineCount.rowCount_eq_countingR0 hk).symm
    have hmax := max_at_cutoff hδ.le hd hp hp' hk (hk1.trans (by norm_num [kappa0]))
    rw [←hcut] at hmax
    have hb := B.card_bound (fiberConstant C height K₀)
      (fun _=>Count.count κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
      (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
        intro bin j J K hne'
        have hb' := hold a ε (cutoff (2*a-1) (q/(2*a-1)) κplain)
          T allowance κplain ν C height i hU ha hd hε (by linarith) ht.1 ht.2 hk
          (hk1.trans (by norm_num [kappa0])) hν hC hh hf (B.fiber bin j J K hne')
          (hmom bin j J K hne')
        rw [fiber_mean_eq B q hq bin j J K hne',hmax,←hR] at hb'
        exact hb')
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
  | some k =>
    have hs := choice_some he
    let P := (window k).plane
    have hgeom := CountArithmetic.admissible_geometry P (window_admissible k hs.1)
      hδ.le hp hk hk1
    have hcut : cutoff (2*a-1) (q/(2*a-1)) κplain=CountArithmetic.tN P (2*a-1) (q/(2*a-1)) := by
      simp [cutoff,he,P]
    have hmax := CountArithmetic.max_at_tN P
      (show CountArithmetic.JN P (2*a-1) (q/(2*a-1)) ≠ 0 from
        (window_admissible k hs.1).j.ne')
      (show CountArithmetic.DN P (q/(2*a-1)) ≠ 0 from
        (window_admissible k hs.1).denominator.ne')
    rw [CountArithmetic.RNew_formula,←hs.2,←hcut] at hmax
    rw [←hcut] at hgeom
    have hb := B.card_bound (fiberConstant C height K₀)
      (fun _=>Count.count κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
      (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
        intro bin j J K hne'
        have hmean := fiber_mean_eq B q hq bin j J K hne'
        have hb' := hnew P a ε (cutoff (2*a-1) (q/(2*a-1)) κplain)
          T allowance κplain ν C height i hU ha hd hε hε' ht.1 ht.2 hk hk1 hν hν1 hC hh hf
          (B.fiber bin j J K hne')
          (by rw [hmean];exact hgeom.2.2.1)
          (by rw [hmean];exact hgeom.2.2.2.1)
          (by rw [hmean];exact hgeom.2.2.2.2.1)
          (by rw [hmean];exact hgeom.2.2.2.2.2)
          (hmom bin j J K hne') (haff bin j J K hne' P)
        rw [hmean,hmax] at hb'
        exact hb')
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb

end OAI.SevenEighths.Target830.Physical.DetectorCount
end
#print axioms OAI.SevenEighths.Target830.Physical.DetectorCount.balanced830
