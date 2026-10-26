import Candidate.Target830.Physical.CountArithmetic
import Candidate.Cycle25.Assembly.Count.FromMoments
import Candidate.Cycle25.Assembly.Count.FixedAmplitude
import Candidate.Cycle25.Assembly.Count.Adaptive
import Candidate.Target830.Physical.CountChoice
import Candidate.Affine.Balanced
import Candidate.Target830.Physical.Data

/- Original module: Candidate.Target830.Physical.CountFromMoments. -/
section
/- Actual original detector fiber counts with one common inverse parameter pair
and the genuine finite affine family. Adapted accepted source; Apache-2.0. -/

namespace OAI.SevenEighths.Target830.Physical.DetectorCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber Cycle25DetectorBranchBudget
open Cycle25DetectorRawFiber Cycle25DetectorRowCount

/-- The Cycle25 fiber count and the affine fiber count, for one common choice
of inverse-moment parameters. The affine cutoff `tstar` is free; the four
region hypotheses are the admissibility conditions of the new crossing. -/
theorem count_from_raw_moments_finite
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      (∀ (a ε tstar T allowance κplain ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 7/10≤κplain → κplain≤3/4 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      Cycle25DetectorRawFiber.Moments F κplain c κ C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max (shortExponent (2*a-1) (F.q/(2*a-1)) κplain tstar) (longExponent (2*a-1) tstar)+
          159*ε+εm+F.mesh+7*ν)) ∧
      (∀ (P : Count.Plane) (a ε tstar T allowance κplain ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/100000 →
      1≤tstar → tstar≤3/2 → 7/10≤κplain → κplain≤kappa0 → 0<ν → ν≤1/100000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      23/37 ≤ CountArithmetic.rN P (F.q/(2*a-1)) tstar →
      CountArithmetic.rN P (F.q/(2*a-1)) tstar ≤ 1 →
      (Count.lowerPlain P)+1/100000 ≤ tstar-CountArithmetic.rN P (F.q/(2*a-1)) tstar →
      CountArithmetic.oldPlainExp (2*a-1) (F.q/(2*a-1)) κplain Count.mHi ≤
        CountArithmetic.shortNew P (2*a-1) (F.q/(2*a-1)) tstar →
      Cycle25DetectorRawFiber.Moments F κplain c κ C height εm →
      (Count.lowerPlain P ≤ F.m → F.m ≤ Count.mHi →
        Count.AffineMarkedMoment F P C height εm) →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max (CountArithmetic.shortNew P (2*a-1) (F.q/(2*a-1)) tstar)
            (CountArithmetic.longExp (2*a-1) tstar)+
          159*ε+εm+F.mesh+7*ν)) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  constructor
  · intro a ε tstar T allowance κplain ν C height i hU ha hδcap hε hεsmall ht ht' hk hk1 hν hC hh hf
      Label Slot F moments
    let δ := 2*a-1
    let x := F.q/δ
    have hδ : 0<δ := by dsimp [δ]; linarith
    have ha' : 1/2≤a := by linarith
    have hδ1 : δ≤1 := by dsimp [δ]; linarith
    obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
    have hx : 0≤x := div_nonneg hq0 hδ.le
    have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
    have hqx : δ*x=F.q := by dsimp [x]; field_simp
    have hgeom := F.lengths hU
    have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
    have hr2 : F.r≤2 := by linarith [hgeom.2.1]
    have hUp : 0<U := zero_lt_one.trans hU
    obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
    have promote (C' p q : ℝ) (hC' : C'≤fiberConstant C height K₀)
        (hb : (F.rows.card : ℝ)≤C'*U^p) (hpq : p≤q) :
        (F.rows.card : ℝ)≤fiberConstant C height K₀*U^q := by
      exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
    have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
      (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
      hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.original.inverse_raw
    have hI0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max 1 ((1+5*F.r)/6)-δ*F.r+commonLoss ε εm F.mesh ν) := by
      apply promote _ _ _ hconstI0 hi0
      exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
    have hp0 := F.plain_unmarked_count moments.original hU (by linarith) hC hh hf
    have hP0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(1-2*δ*F.m+commonLoss ε εm F.mesh ν) := by
      apply promote _ _ _ hconstP hp0
      exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
    have hI : 23/37≤F.r → F.r<1 → ν<(1-F.r)/2 →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(inverseExponent δ x F.r+commonLoss ε εm F.mesh ν) := by
      intro hr hr1 hv
      obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
      have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
      apply promote _ _ _ hconstI hb
      have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      rwa [hqx] at hl
    have hP : F.r≤crossing x κplain tstar → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(6*κplain)+commonLoss ε εm F.mesh ν) := by
      intro hr hm hv
      obtain ⟨hz,hz',hcap⟩ := plain_requested_capacity κplain x tstar F.r F.m ε ν hk hk1 hx hx' ht ht'
        hr hgeom.1 (by linarith) hν.le hv
      have hb := Cycle25DetectorRawFiber.plain_marked_count F moments hU ha' (by linarith) hC hh hf
        ((1-2*F.m)/(6*κplain)-ν) hz hz' hcap
      apply promote _ _ _ hconstP hb
      have hl := plain_marked_loss F.m δ x κplain ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      simpa only [hqx] using hl
    have hc' := count_bound_of_source_branches (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x κplain
      tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le (by dsimp [δ]; linarith) hx hx' hk hk1
      ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
    convert hc' using 1; congr 2
    unfold commonLoss
    ring
  · intro P a ε tstar T allowance κplain ν C height i hU ha hδcap hε hεsmall ht ht' hk hk1 hν hν1 hC hh hf
      Label Slot F hrN hrN1 hmN htail moments affine
    let δ := 2*a-1
    let x := F.q/δ
    have hδ : 0<δ := by dsimp [δ]; linarith
    have ha' : 1/2≤a := by linarith
    have hδ1 : δ≤1 := by dsimp [δ]; linarith
    obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
    have hx : 0≤x := div_nonneg hq0 hδ.le
    have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
    have hqx : δ*x=F.q := by dsimp [x]; field_simp
    have hgeom := F.lengths hU
    have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
    have hr2 : F.r≤2 := by linarith [hgeom.2.1]
    have hUp : 0<U := zero_lt_one.trans hU
    obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
    have promote (C' p q : ℝ) (hC' : C'≤fiberConstant C height K₀)
        (hb : (F.rows.card : ℝ)≤C'*U^p) (hpq : p≤q) :
        (F.rows.card : ℝ)≤fiberConstant C height K₀*U^q := by
      exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
    have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
      (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
      hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.original.inverse_raw
    have hI0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max 1 ((1+5*F.r)/6)-δ*F.r+commonLoss ε εm F.mesh ν) := by
      apply promote _ _ _ hconstI0 hi0
      exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
    have hp0 := F.plain_unmarked_count moments.original hU (by linarith) hC hh hf
    have hP0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(1-2*δ*F.m+commonLoss ε εm F.mesh ν) := by
      apply promote _ _ _ hconstP hp0
      exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
    have hI : 23/37≤F.r → F.r<1 → ν<(1-F.r)/2 →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(CountArithmetic.inverseExp δ x F.r+commonLoss ε εm F.mesh ν) := by
      intro hr hr1 hv
      obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
      have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
      apply promote _ _ _ hconstI hb
      have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      rw [hqx] at hl
      simpa only [CountArithmetic.inverseExp, inverseExponent] using hl
    have hA : (Count.lowerPlain P) ≤ F.m → F.m ≤ Count.mHi →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(CountArithmetic.affineExp P δ x F.m+2*(δ*x)*ν+commonLoss ε εm F.mesh ν) := by
      intro hm1 hm2
      have hb := Count.affine_marked_count_on_window F P moments (affine hm1 hm2) hU ha' hk hk1 hC hh hf hν.le (by linarith) hm1 hm2
      apply promote _ _ _ hconstP hb
      rw [← hqx]
      have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
      unfold CountArithmetic.affineExp commonLoss
      have e : 2*(δ*x)*((P.B-2*F.m)/P.lambda-ν) =
          2*(δ*x)*(P.B-2*F.m)/P.lambda-2*(δ*x)*ν := by ring
      rw [e]
      linarith
    have hP : Count.mHi ≤ F.m → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
        (F.rows.card : ℝ)≤fiberConstant C height K₀*
          U^(CountArithmetic.oldPlainExp δ x κplain F.m+commonLoss ε εm F.mesh ν) := by
      intro hm hm2 hv
      have hd : 0<6*κplain := by linarith only [hk]
      have hmHi : (847/2000:ℝ) ≤ F.m :=
        (show (847/2000:ℝ) ≤ Count.mHi by norm_num [Count.mHi,kappa0,widthLower]).trans hm
      have hc5 : (1-2*F.m)/(6*κplain) ≤ 5/42 := by
        rw [div_le_iff₀ hd]; linarith only [hmHi, hk]
      have hz : 0≤(1-2*F.m)/(6*κplain)-ν := by linarith only [hv]
      have hz' : (1-2*F.m)/(6*κplain)-ν≤7/37 := by linarith only [hc5, hν]
      have hκν : 0 ≤ 6*κplain*ν := mul_nonneg hd.le hν.le
      have hcap : 2*F.m+6*κplain*((1-2*F.m)/(6*κplain)-ν)≤1 := by
        rw [mul_sub,mul_div_cancel₀ _ hd.ne']
        linarith only [hκν]
      have hb := Cycle25DetectorRawFiber.plain_marked_count F moments hU ha'
        (by linarith only [hk]) hC hh hf ((1-2*F.m)/(6*κplain)-ν) hz hz' hcap
      apply promote _ _ _ hconstP hb
      have hl := plain_marked_loss F.m δ x κplain ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
      simpa only [hqx, CountArithmetic.oldPlainExp] using hl
    have hc' := CountArithmetic.affine_count_bound P (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x
      κplain tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le (by dsimp [δ]; linarith)
      hx hx' hk (hk1.trans (by norm_num [kappa0])) hν.le hε hgeom.1 hgeom.2.1 hrN hrN1 (by linarith) htail hI0 hP0 hI hA hP
    convert hc' using 1; congr 2
    unfold commonLoss
    ring


end
end OAI.SevenEighths.Target830.Physical.DetectorCount
#print axioms OAI.SevenEighths.Target830.Physical.DetectorCount.count_from_raw_moments_finite
end

/- Original module: Candidate.Target830.Physical.CountBalanced. -/
section

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
end

/- Original module: Candidate.Target830.Physical.CountParameters. -/
section

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.Target830.Physical.DetectorCount
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
  HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
  HeckeDetectorFixedAmplitudeCount Cycle25DetectorRawFiber

structure CountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  c : ℝ
  k : ℝ
  c_pos : 0<c
  c_one : c≤1
  k_pos : 0<k
  affine : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
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
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c k C height εm) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,∀P : Count.Plane,
        Count.lowerPlain P ≤ (B.fiber bin j J K hne).m →
        (B.fiber bin j J K hne).m ≤ Count.mHi →
        Count.AffineMarkedMoment (B.fiber bin j J K hne) P C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Count.count κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)

theorem exists_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) : Nonempty (CountParameters M H εm) := by
  obtain ⟨c,k,K,hc,hc1,hk,hK,hcount⟩ := balanced830 M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨c,k,hc,hc1,hk,⟨K,hK,hcount⟩⟩⟩

theorem fresh_count_parameters (D : DetectorData) (F : SourceData) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

end OAI.SevenEighths.Target830.Physical.DetectorCount
end
#print axioms OAI.SevenEighths.Target830.Physical.DetectorCount.exists_count_parameters
end
