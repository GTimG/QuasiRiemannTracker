import Candidate.Target836.Detector836.Count
import Candidate.Affine.Count

namespace OAI.SevenEighths.Cycle25DetectorRawFiber
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- On the literal positive-slot window, the new fixed line also supplies
the accepted PR60 affine moment. No extra analytic hypothesis is introduced. -/
theorem affine836_implies_accepted
    {F : Fiber M H Label Slot U a ε tstar T allowance i} {C height εm : ℝ}
    (h : AffineMarkedMoment836 F C height εm) : AffineMarkedMoment F C height εm := by
  intro selected hsel hmlo hmhi hwlo hwhi hcap j k hj s hs t ht
  apply h selected hsel hmlo hmhi hwlo hwhi _ j k hj s hs t ht
  have hdiff : 0 ≤ DetectorAffine.lam-Detector836.lam := by
    norm_num [DetectorAffine.lam,Detector836.lam]
  have hmass := mul_le_mul_of_nonneg_left hwlo hdiff
  norm_num [DetectorAffine.lam,Detector836.lam,DetectorAffine.Bc,Detector836.Bc] at *
  linarith
end
end OAI.SevenEighths.Cycle25DetectorRawFiber

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Detector836Count
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber Cycle25DetectorBranchBudget
open Cycle25DetectorRawFiber Cycle25DetectorRowCount

theorem count_from_raw_moments_all836
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
      (∀ (a ε tstar T allowance κplain ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/100000 →
      1≤tstar → tstar≤3/2 → 7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/100 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      23/37 ≤ Detector836.rN (F.q/(2*a-1)) tstar →
      Detector836.rN (F.q/(2*a-1)) tstar ≤ 1 →
      Detector836.mLo+1/100000 ≤ tstar-Detector836.rN (F.q/(2*a-1)) tstar →
      Detector836.oldPlainExp (2*a-1) (F.q/(2*a-1)) κplain Detector836.mHi ≤
        Detector836.shortNew (2*a-1) (F.q/(2*a-1)) tstar →
      Cycle25DetectorRawFiber.Moments F κplain c κ C height εm →
      AffineMarkedMoment836 F C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max (Detector836.shortNew (2*a-1) (F.q/(2*a-1)) tstar)
            (Detector836.longExp (2*a-1) tstar)+
          159*ε+εm+F.mesh+7*ν)) ∧
      (∀ (a ε tstar T allowance κplain ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤3/4 → 0≤ε → ε≤1/100000 →
      1≤tstar → tstar≤3/2 → 7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/100 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      23/37 ≤ DetectorAffine.rN (F.q/(2*a-1)) tstar →
      DetectorAffine.rN (F.q/(2*a-1)) tstar ≤ 1 →
      DetectorAffine.mLo+1/100000 ≤ tstar-DetectorAffine.rN (F.q/(2*a-1)) tstar →
      DetectorAffine.oldPlainExp (2*a-1) (F.q/(2*a-1)) κplain DetectorAffine.mHi ≤
        DetectorAffine.shortNew (2*a-1) (F.q/(2*a-1)) tstar →
      Cycle25DetectorRawFiber.Moments F κplain c κ C height εm →
      AffineMarkedMoment836 F C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max (DetectorAffine.shortNew (2*a-1) (F.q/(2*a-1)) tstar)
            (DetectorAffine.longExp (2*a-1) tstar)+
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
  · constructor
    · intro a ε tstar T allowance κplain ν C height i hU ha hδcap hε hεsmall ht ht' hk hk1 hν hν1 hC hh hf
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
            U^(Detector836.inverseExp δ x F.r+commonLoss ε εm F.mesh ν) := by
        intro hr hr1 hv
        obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
        have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
        apply promote _ _ _ hconstI hb
        have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
        rw [hqx] at hl
        simpa only [Detector836.inverseExp, inverseExponent] using hl
      have hA : Detector836.mLo ≤ F.m → F.m ≤ Detector836.mHi →
          (F.rows.card : ℝ)≤fiberConstant C height K₀*
            U^(Detector836.affineExp δ x F.m+2*(δ*x)*ν+commonLoss ε εm F.mesh ν) := by
        intro hm1 hm2
        have hb := affine_marked_count836 F moments affine hU ha' hk hk1 hC hh hf hν.le hν1 hm1 hm2
        apply promote _ _ _ hconstP hb
        rw [← hqx]
        have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
        unfold Detector836.affineExp commonLoss
        have e : 2*(δ*x)*((Detector836.Bc-2*F.m)/Detector836.lam-ν) =
            2*(δ*x)*(Detector836.Bc-2*F.m)/Detector836.lam-2*(δ*x)*ν := by ring
        rw [e]
        linarith
      have hP : Detector836.mHi ≤ F.m → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
          (F.rows.card : ℝ)≤fiberConstant C height K₀*
            U^(Detector836.oldPlainExp δ x κplain F.m+commonLoss ε εm F.mesh ν) := by
        intro hm hm2 hv
        have hd : 0<6*κplain := by linarith only [hk]
        have hmHi : (847/2000:ℝ) ≤ F.m := hm
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
        simpa only [hqx, Detector836.oldPlainExp] using hl
      have hc' := Detector836.affine_count_bound (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x
        κplain tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le (by dsimp [δ]; linarith)
        hx hx' hk hk1 hν.le hε hgeom.1 hgeom.2.1 hrN hrN1 (by linarith) htail hI0 hP0 hI hA hP
      convert hc' using 1; congr 2
      unfold commonLoss
      ring
    · intro a ε tstar T allowance κplain ν C height i hU ha hδcap hε hεsmall ht ht' hk hk1 hν hν1 hC hh hf
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
            U^(DetectorAffine.inverseExp δ x F.r+commonLoss ε εm F.mesh ν) := by
        intro hr hr1 hv
        obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
        have hb := F.inverse_marked_count moments.original hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
        apply promote _ _ _ hconstI hb
        have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
        rw [hqx] at hl
        simpa only [DetectorAffine.inverseExp, inverseExponent] using hl
      have hA : DetectorAffine.mLo ≤ F.m → F.m ≤ DetectorAffine.mHi →
          (F.rows.card : ℝ)≤fiberConstant C height K₀*
            U^(DetectorAffine.affineExp δ x F.m+2*(δ*x)*ν+commonLoss ε εm F.mesh ν) := by
        intro hm1 hm2
        have hb := affine_marked_count F moments (affine836_implies_accepted affine) hU ha' hk hk1 hC hh hf hν.le hν1 hm1 hm2
        apply promote _ _ _ hconstP hb
        rw [← hqx]
        have hm := mul_le_mul_of_nonneg_right hδ1 F.mesh_nonneg
        unfold DetectorAffine.affineExp commonLoss
        have e : 2*(δ*x)*((DetectorAffine.Bc-2*F.m)/DetectorAffine.lam-ν) =
            2*(δ*x)*(DetectorAffine.Bc-2*F.m)/DetectorAffine.lam-2*(δ*x)*ν := by ring
        rw [e]
        linarith
      have hP : DetectorAffine.mHi ≤ F.m → F.m<1/2 → ν<(1-2*F.m)/(6*κplain) →
          (F.rows.card : ℝ)≤fiberConstant C height K₀*
            U^(DetectorAffine.oldPlainExp δ x κplain F.m+commonLoss ε εm F.mesh ν) := by
        intro hm hm2 hv
        have hd : 0<6*κplain := by linarith only [hk]
        have hmHi : (847/2000:ℝ) ≤ F.m := hm
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
        simpa only [hqx, DetectorAffine.oldPlainExp] using hl
      have hc' := DetectorAffine.affine_count_bound (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x
        κplain tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le (by dsimp [δ]; linarith)
        hx hx' hk hk1 hν.le hε hgeom.1 hgeom.2.1 hrN hrN1 (by linarith) htail hI0 hP0 hI hA hP
      convert hc' using 1; congr 2
      unfold commonLoss
      ring

end SevenEighths.Detector836Count
end
end OAI

#print axioms OAI.SevenEighths.Cycle25DetectorRawFiber.affine836_implies_accepted
#print axioms OAI.SevenEighths.Detector836Count.count_from_raw_moments_all836
