import Candidate.Uneven.WarmupCover0
import Candidate.Uneven.WarmupCover1
import Candidate.Uneven.WarmupCover2
import Candidate.Uneven.WarmupCover3
import Candidate.Uneven.RowInterpolation
import Candidate.Uneven.MainCountConcrete
import Candidate.Uneven.MainCountIdentity
import Candidate.Uneven.MainCountMonotonicity

/- Original module: Candidate.Uneven.WarmupAllRows. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.WarmupRows

theorem full_rows {r : ℕ} (hr : r ≤ 3) {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    ∃ i : ℕ, i ≤ 7 ∧ available i d p ∧ row r i d p ≤ theta-reserve := by
  interval_cases r
  · exact full_row_0 hd hp
  · exact full_row_1 hd hp
  · exact full_row_2 hd hp
  · exact full_row_3 hd hp

def actualCapacity (r : ℕ) : ℝ :=
  if r ≤ 1 then min (rowHeight r) (2*y-rowHeight r)/(6*frozen_kappa)
  else min ((399999/10000000)*rowHeight r)
    ((2*y-(2-planeB 6)*rowHeight r)/planeLambda 6)

theorem row_capacity_eq_actual {r : ℕ} (hr : r ≤ 3) :
    rowCapacity r = actualCapacity r := by
  interval_cases r <;>
    norm_num [rowCapacity,actualCapacity,rowHeight,y,frozen_kappa,planeB,planeLambda,min_def]


end Sil.Uneven.WarmupRows
end

/- Original module: Candidate.Uneven.WarmupRowIntervals. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Full numerical row intervals, conditional only on the stated count bounds. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.WarmupRows

def rowConstant (d p : ℝ) : ℝ :=
  (1+d)/2+13*h/75-y/2-ell/2+ell*d*p

def scalarRow (z cap count d p : ℝ) : ℝ :=
  rowConstant d p-9*z/100-d*p*cap/2+3*z*count/4

def oldCapacity (z : ℝ) : ℝ := min z (2*y-z)/(6*frozen_kappa)
def newCapacity (z : ℝ) : ℝ :=
  min ((399999/10000000)*z)
    ((2*y-(2-(planeB 6))*z)/(planeLambda 6))

def CountBounds (count d p : ℝ) : Prop :=
  ∀ i : ℕ, i ≤ 7 → available i d p → count ≤ numerator i d p/denominator i d p

theorem scalar_row_eq (r i : ℕ) (d p : ℝ) :
    scalarRow (rowHeight r) (rowCapacity r)
      (numerator i d p/denominator i d p) d p = row r i d p := by
  unfold scalarRow rowConstant row base
  ring

theorem scalar_row_mono {z cap count count' d p : ℝ}
    (hz : 0 ≤ z) (hc : count ≤ count') :
    scalarRow z cap count d p ≤ scalarRow z cap count' d p := by
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3*z/4 by positivity)
  unfold scalarRow
  nlinarith only [hh]

theorem scalar_endpoints {r : ℕ} (hr : r ≤ 3) {d p count : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hc : CountBounds count d p) :
    scalarRow (rowHeight r) (rowCapacity r) count d p ≤ theta-reserve := by
  obtain ⟨i,hi,ha,hb⟩ := full_rows hr hd hp
  have hz : 0 ≤ rowHeight r := by interval_cases r <;> norm_num [rowHeight]
  have hm := scalar_row_mono (cap:=rowCapacity r) (d:=d) (p:=p) hz (hc i hi ha)
  rw [scalar_row_eq] at hm
  exact hm.trans hb

theorem old_row_formula (z count d p : ℝ) :
    scalarRow z (oldCapacity z) count d p =
      rowConstant d p+(-9/100+3*count/4)*z-
        (d*p/(12*frozen_kappa))*min (0+1*z) (2*y+(-1)*z) := by
  unfold scalarRow oldCapacity
  norm_num [frozen_kappa]
  ring

theorem new_row_formula (z count d p : ℝ) :
    scalarRow z (newCapacity z) count d p =
      rowConstant d p+(-9/100+3*count/4)*z-
        (d*p/2)*min (0+(399999/10000000)*z)
          (2*y/(planeLambda 6)+(-(2-(planeB 6))/(planeLambda 6))*z) := by
  have he : (2*y-(2-(planeB 6))*z)/(planeLambda 6) =
      2*y/(planeLambda 6)+(-(2-(planeB 6))/(planeLambda 6))*z := by ring
  unfold scalarRow newCapacity
  rw [he]
  simp only [zero_add]
  ring

theorem old_row_interval {z count d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1)
    (hc : CountBounds count d p) :
    scalarRow z (oldCapacity z) count d p ≤ theta-reserve := by
  have h0 := scalar_endpoints (r:=0) (by norm_num) hd hp hc
  have h1 := scalar_endpoints (r:=1) (by norm_num) hd hp hc
  have he0 : rowCapacity 0=oldCapacity (rowHeight 0) := by
    simpa only [actualCapacity,oldCapacity,show (0:ℕ) ≤ 1 by norm_num,if_pos] using
      row_capacity_eq_actual (r:=0) (by norm_num [planeLambda])
  have he1 : rowCapacity 1=oldCapacity (rowHeight 1) := by
    simpa only [actualCapacity,oldCapacity,show (1:ℕ) ≤ 1 by norm_num,if_pos] using
      row_capacity_eq_actual (r:=1) (by norm_num [planeLambda])
  rw [he0,old_row_formula] at h0
  rw [he1,old_row_formula] at h1
  rw [old_row_formula]
  apply RowInterpolation.min_capacity_between _ _ _ _ _ _ _ _ _ _ _ _ hz h0 h1
  exact div_nonneg (mul_nonneg hd.1 hp.1) (by norm_num [frozen_kappa])

theorem new_row_interval {z count d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3)
    (hc : CountBounds count d p) :
    scalarRow z (newCapacity z) count d p ≤ theta-reserve := by
  have h0 := scalar_endpoints (r:=2) (by norm_num) hd hp hc
  have h1 := scalar_endpoints (r:=3) (by norm_num) hd hp hc
  have he0 : rowCapacity 2=newCapacity (rowHeight 2) := by
    simpa only [actualCapacity,newCapacity,show ¬ (2:ℕ) ≤ 1 by norm_num,ite_false] using
      row_capacity_eq_actual (r:=2) (by norm_num [planeLambda])
  have he1 : rowCapacity 3=newCapacity (rowHeight 3) := by
    simpa only [actualCapacity,newCapacity,show ¬ (3:ℕ) ≤ 1 by norm_num,ite_false] using
      row_capacity_eq_actual (r:=3) (by norm_num [planeLambda])
  rw [he0,new_row_formula] at h0
  rw [he1,new_row_formula] at h1
  rw [new_row_formula]
  apply RowInterpolation.min_capacity_between _ _ _ _ _ _ _ _ _ _ _ _ hz h0 h1
  exact div_nonneg (mul_nonneg hd.1 hp.1) (by norm_num [planeLambda])

end Sil.Uneven.WarmupRows
end

/- Original module: Candidate.Uneven.WarmupActualCountBounds. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Sil.Uneven.WarmupRows
noncomputable section
open OAI.SevenEighths

theorem affine_numeric_identity {i : ℕ} (hi : i ≤ 7) {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    Target830.Count.affineR (planeLambda i) (planeB i) d p =
      numerator i d p/denominator i d p := by
  have hJ := (denominator_pos hi hd hp).ne'
  apply (eq_div_iff hJ).mpr
  have hJ' : Target830.Count.affineJ (planeLambda i) d p ≠ 0 := hJ
  convert Target830.Count.affine_count_mul (B:=planeB i) hJ' using 1 <;>
    dsimp [numerator,denominator,Target830.Count.affineN,Target830.Count.affineJ,
      Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineU,
      Target830.Count.affineC] <;> ring

/-- The actual finite count selector satisfies every bound used by the numerical
row certificates. No analytic source estimate is assumed in this algebraic bridge. -/
theorem actual_count_bounds {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    CountBounds (MainCount.count .warmup frozen_kappa d p) d p := by
  intro i hi ha
  rw [←affine_numeric_identity hi hd hp]
  rcases ha with hz | h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
  · subst i
    have hc := MainCount.count_le_old .warmup frozen_kappa d p
    rw [MainCount.old_count_affine (by norm_num [frozen_kappa]) hd hp] at hc
    convert hc using 1 <;> norm_num [planeLambda,planeB,frozen_kappa]
  · rcases h0 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window0.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window0 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window0,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h1 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window1.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window1 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window1,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h2 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window2.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window2 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window2,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h3 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window3.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window3 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window3,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h4 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window4.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window4 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window4,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h5 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window5.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window5 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window5,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h6 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window6.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window6 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window6,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h7 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window7.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window7 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window7,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h8 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window8.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window8 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window8,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h9 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window9.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .warmup frozen_kappa d p).trans
      (Target830.Count.count_le_window9 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window9,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h10 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window10 .warmup).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window10 .warmup (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window10,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h11 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window11 .warmup).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window11 .warmup (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window11,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h12 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window12 .warmup).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window12 .warmup (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window12,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h13 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window13 .warmup).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window13 .warmup (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window13,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h14 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window14 .warmup).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window14 .warmup (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window14,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]

theorem actual_old_row_interval {z d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1) :
    scalarRow z (oldCapacity z) (MainCount.count .warmup frozen_kappa d p) d p ≤
      theta-reserve :=
  old_row_interval hd hp hz (actual_count_bounds hd hp)

theorem actual_new_row_interval {z d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3) :
    scalarRow z (newCapacity z) (MainCount.count .warmup frozen_kappa d p) d p ≤
      theta-reserve :=
  new_row_interval hd hp hz (actual_count_bounds hd hp)

end
end Sil.Uneven.WarmupRows
end

/- Original module: Candidate.Uneven.WarmupCountIncumbent. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Sil.Uneven.WarmupRows
noncomputable section
open OAI.SevenEighths

def oldCapacityAt (κ z : ℝ) : ℝ := min z (2*y-z)/(6*κ)

theorem scalar_capacity_antitone {z cap cap' count d p : ℝ}
    (hd : 0 ≤ d) (hp : 0 ≤ p) (hc : cap ≤ cap') :
    scalarRow z cap' count d p ≤ scalarRow z cap count d p := by
  have hh := mul_le_mul_of_nonneg_left hc (mul_nonneg hd hp)
  unfold scalarRow
  linarith only [hh]

theorem old_row_at_incumbent {κ z d p : ℝ} (hk : 7/10 ≤ κ) (hkhi : κ ≤ frozen_kappa)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1) :
    scalarRow z (oldCapacityAt κ z) (MainCount.count .warmup κ d p) d p ≤ theta-reserve := by
  have hz0 : 0 ≤ z := (show (0:ℝ) ≤ rowHeight 0 by norm_num [rowHeight]).trans hz.1
  have htop : rowHeight 1 ≤ 2*y := by norm_num [rowHeight,y]
  have hm : 0 ≤ min z (2*y-z) := le_min hz0 (by linarith only [hz.2,htop])
  have hcap : oldCapacity z ≤ oldCapacityAt κ z := by
    exact div_le_div_of_nonneg_left hm (by linarith : 0 < 6*κ)
      (by linarith : 6*κ ≤ 6*frozen_kappa)
  have hc := MainCount.count_mono .warmup hk hkhi
    (show 0 ≤ d ∧ d ≤ 5/6 from ⟨hd.1,by linarith [hd.2]⟩) hp
  calc
    _ ≤ scalarRow z (oldCapacity z) (MainCount.count .warmup κ d p) d p :=
      scalar_capacity_antitone hd.1 hp.1 hcap
    _ ≤ scalarRow z (oldCapacity z) (MainCount.count .warmup frozen_kappa d p) d p :=
      scalar_row_mono hz0 hc
    _ ≤ _ := actual_old_row_interval hd hp hz

theorem new_row_at_incumbent {κ z d p : ℝ} (hk : 7/10 ≤ κ) (hkhi : κ ≤ frozen_kappa)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3) :
    scalarRow z (newCapacity z) (MainCount.count .warmup κ d p) d p ≤ theta-reserve := by
  have hz0 : 0 ≤ z := (show (0:ℝ) ≤ rowHeight 2 by norm_num [rowHeight]).trans hz.1
  have hc := MainCount.count_mono .warmup hk hkhi
    (show 0 ≤ d ∧ d ≤ 5/6 from ⟨hd.1,by linarith [hd.2]⟩) hp
  exact (scalar_row_mono hz0 hc).trans (actual_new_row_interval hd hp hz)

theorem old_supremum_deficit {beta z d p : ℝ} (hb : theta < beta)
    (hbhi : beta ≤ (frozen_kappa+1)/2)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1) :
    scalarRow z (oldCapacityAt (2*beta-1) z) (MainCount.count .warmup (2*beta-1) d p) d p-beta ≤
      -(reserve)-(beta-theta) := by
  have hk : 7/10 ≤ 2*beta-1 := by norm_num [theta] at hb; linarith only [hb]
  have hkhi : 2*beta-1 ≤ frozen_kappa := by linarith only [hbhi]
  have hh := old_row_at_incumbent hk hkhi hd hp hz
  linarith only [hh]

theorem new_supremum_deficit {beta z d p : ℝ} (hb : theta < beta)
    (hbhi : beta ≤ (frozen_kappa+1)/2)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3) :
    scalarRow z (newCapacity z) (MainCount.count .warmup (2*beta-1) d p) d p-beta ≤
      -(reserve)-(beta-theta) := by
  have hk : 7/10 ≤ 2*beta-1 := by norm_num [theta] at hb; linarith only [hb]
  have hkhi : 2*beta-1 ≤ frozen_kappa := by linarith only [hbhi]
  have hh := new_row_at_incumbent hk hkhi hd hp hz
  linarith only [hh]

end
end Sil.Uneven.WarmupRows
end
