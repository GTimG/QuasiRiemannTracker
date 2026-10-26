import Candidate.Uneven.MainCountConcrete
import Candidate.Uneven.MainCountIdentity
import Candidate.Uneven.RoundedRowIntervals
import Candidate.Uneven.MainCountMonotonicity
import Candidate.Uneven.EndpointStageParameters
import Candidate.Uneven.WarmupCountIncumbent

/- Original module: Candidate.Uneven.RoundedActualCountBounds. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Sil.Uneven.RoundedRows
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
    CountBounds (MainCount.count .final frozen_kappa d p) d p := by
  intro i hi ha
  rw [←affine_numeric_identity hi hd hp]
  rcases ha with hz | h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
  · subst i
    have hc := MainCount.count_le_old .final frozen_kappa d p
    rw [MainCount.old_count_affine (by norm_num [frozen_kappa]) hd hp] at hc
    convert hc using 1 <;> norm_num [planeLambda,planeB,frozen_kappa]
  · rcases h0 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window0.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window0 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window0,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h1 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window1.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window1 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window1,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h2 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window2.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window2 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window2,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h3 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window3.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window3 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window3,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h4 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window4.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window4 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window4,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h5 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window5.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window5 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window5,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h6 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window6.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window6 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window6,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h7 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window7.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window7 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window7,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h8 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window8.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window8 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window8,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h9 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window9.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window9 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window9,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h10 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window10 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window10 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window10,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h11 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window11 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window11 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window11,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h12 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window12 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window12 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window12,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h13 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window13 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window13 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window13,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h14 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window14 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window14 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window14,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]

theorem actual_old_row_interval {z d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1) :
    scalarRow z (oldCapacity z) (MainCount.count .final frozen_kappa d p) d p ≤
      theta-1/20000000000000 :=
  old_row_interval hd hp hz (actual_count_bounds hd hp)

theorem actual_new_row_interval {z d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3) :
    scalarRow z (newCapacity z) (MainCount.count .final frozen_kappa d p) d p ≤
      theta-1/20000000000000 :=
  new_row_interval hd hp hz (actual_count_bounds hd hp)

end
end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.RoundedCountIncumbent. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Sil.Uneven.RoundedRows
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
    scalarRow z (oldCapacityAt κ z) (MainCount.count .final κ d p) d p ≤ theta-1/20000000000000 := by
  have hz0 : 0 ≤ z := (show (0:ℝ) ≤ rowHeight 0 by norm_num [rowHeight]).trans hz.1
  have htop : rowHeight 1 ≤ 2*y := by norm_num [rowHeight,y]
  have hm : 0 ≤ min z (2*y-z) := le_min hz0 (by linarith only [hz.2,htop])
  have hcap : oldCapacity z ≤ oldCapacityAt κ z := by
    exact div_le_div_of_nonneg_left hm (by linarith : 0 < 6*κ)
      (by linarith : 6*κ ≤ 6*frozen_kappa)
  have hc := MainCount.count_mono .final hk hkhi
    (show 0 ≤ d ∧ d ≤ 5/6 from ⟨hd.1,by linarith [hd.2]⟩) hp
  calc
    _ ≤ scalarRow z (oldCapacity z) (MainCount.count .final κ d p) d p :=
      scalar_capacity_antitone hd.1 hp.1 hcap
    _ ≤ scalarRow z (oldCapacity z) (MainCount.count .final frozen_kappa d p) d p :=
      scalar_row_mono hz0 hc
    _ ≤ _ := actual_old_row_interval hd hp hz

theorem new_row_at_incumbent {κ z d p : ℝ} (hk : 7/10 ≤ κ) (hkhi : κ ≤ frozen_kappa)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3) :
    scalarRow z (newCapacity z) (MainCount.count .final κ d p) d p ≤ theta-1/20000000000000 := by
  have hz0 : 0 ≤ z := (show (0:ℝ) ≤ rowHeight 2 by norm_num [rowHeight]).trans hz.1
  have hc := MainCount.count_mono .final hk hkhi
    (show 0 ≤ d ∧ d ≤ 5/6 from ⟨hd.1,by linarith [hd.2]⟩) hp
  exact (scalar_row_mono hz0 hc).trans (actual_new_row_interval hd hp hz)

theorem old_supremum_deficit {beta z d p : ℝ} (hb : theta < beta)
    (hbhi : beta ≤ (frozen_kappa+1)/2)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1) :
    scalarRow z (oldCapacityAt (2*beta-1) z) (MainCount.count .final (2*beta-1) d p) d p-beta ≤
      -(1/20000000000000)-(beta-theta) := by
  have hk : 7/10 ≤ 2*beta-1 := by norm_num [theta] at hb; linarith only [hb]
  have hkhi : 2*beta-1 ≤ frozen_kappa := by linarith only [hbhi]
  have hh := old_row_at_incumbent hk hkhi hd hp hz
  linarith only [hh]

theorem new_supremum_deficit {beta z d p : ℝ} (hb : theta < beta)
    (hbhi : beta ≤ (frozen_kappa+1)/2)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3) :
    scalarRow z (newCapacity z) (MainCount.count .final (2*beta-1) d p) d p-beta ≤
      -(1/20000000000000)-(beta-theta) := by
  have hk : 7/10 ≤ 2*beta-1 := by norm_num [theta] at hb; linarith only [hb]
  have hkhi : 2*beta-1 ≤ frozen_kappa := by linarith only [hbhi]
  have hh := new_row_at_incumbent hk hkhi hd hp hz
  linarith only [hh]

end
end Sil.Uneven.RoundedRows
end

/- Original module: Candidate.Uneven.EndpointCountRows. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.UnevenEndpoint.Count
noncomputable section
variable [config : Configuration]

def count (κ d p : ℝ) : ℝ := MainCount.count config.stage κ d p
def d0 : ℝ := 1/200
def rowBase (d cap δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+d*(1/4-17/50)-δ*p*cap/2
def rowAt (κ d cap δ p : ℝ) : ℝ := rowBase d cap δ p+3*d*count κ δ p/4
def oldCapacityAt (κ d : ℝ) : ℝ := min d (2*y-d)/(6*κ)
def newCapacity (d : ℝ) : ℝ :=
  min (slotClip*d) ((2*y-(2-SourcePlane.A.B)*d)/SourcePlane.A.lambda)
def oldExponentAt (κ d δ p : ℝ) : ℝ := rowAt κ d (oldCapacityAt κ d) δ p
def newExponentAt (κ d δ p : ℝ) : ℝ := rowAt κ d (newCapacity d) δ p

theorem old_supremum_deficit {β d δ p : ℝ} (hb : theta < β)
    (hinc : β ≤ incumbent) (hd : d ∈ Set.Icc d0 dMinus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p-β ≤ -reserve-(β-theta) := by
  cases config with
  | mk stage =>
    cases stage
    · have hb' : Sil.Uneven.WarmupRows.theta < β := by simpa only [theta] using hb
      have hi' : β ≤ (Sil.Uneven.WarmupRows.frozen_kappa+1)/2 := by
        norm_num [incumbent,Sil.Uneven.WarmupRows.frozen_kappa] at hinc ⊢
        exact hinc
      have hd' : Sil.Uneven.WarmupRows.rowHeight 0 ≤ d ∧ d ≤ Sil.Uneven.WarmupRows.rowHeight 1 := by
        norm_num [Set.mem_Icc,d0,dMinus,dPlus,h,upperPadding,Sil.Uneven.WarmupRows.h,Sil.Uneven.WarmupRows.rowHeight] at hd ⊢
        constructor <;> linarith [hd.1,hd.2]
      have hh := Sil.Uneven.WarmupRows.old_supremum_deficit hb' hi' hδ hp hd'
      convert hh using 1 <;> norm_num [rowBase,rowAt,count,oldExponentAt,oldCapacityAt,h,ell,y,theta,slotClip,reserve,Sil.Uneven.WarmupRows.reserve,Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda,Sil.Uneven.WarmupRows.scalarRow,Sil.Uneven.WarmupRows.rowConstant,Sil.Uneven.WarmupRows.oldCapacityAt,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.WarmupRows.ell,Sil.Uneven.WarmupRows.y,SourcePlane.B,SourcePlane.lambda,SourcePlane.mainPlane,Sil.Uneven.MainSource.Plane.B,Sil.Uneven.MainSource.Plane.lambda] <;> ring_nf <;> simp

    · have hb' : Sil.Uneven.RoundedRows.theta < β := by simpa only [theta] using hb
      have hi' : β ≤ (Sil.Uneven.RoundedRows.frozen_kappa+1)/2 := by
        norm_num [incumbent,Sil.Uneven.RoundedRows.frozen_kappa] at hinc ⊢
        exact hinc
      have hd' : Sil.Uneven.RoundedRows.rowHeight 0 ≤ d ∧ d ≤ Sil.Uneven.RoundedRows.rowHeight 1 := by
        norm_num [Set.mem_Icc,d0,dMinus,dPlus,h,upperPadding,Sil.Uneven.RoundedRows.h,Sil.Uneven.RoundedRows.rowHeight] at hd ⊢
        constructor <;> linarith [hd.1,hd.2]
      have hh := Sil.Uneven.RoundedRows.old_supremum_deficit hb' hi' hδ hp hd'
      convert hh using 1 <;> norm_num [rowBase,rowAt,count,oldExponentAt,oldCapacityAt,h,ell,y,theta,slotClip,reserve,Sil.Uneven.RoundedRows.scalarRow,Sil.Uneven.RoundedRows.rowConstant,Sil.Uneven.RoundedRows.oldCapacityAt,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,Sil.Uneven.RoundedRows.ell,Sil.Uneven.RoundedRows.y,SourcePlane.B,SourcePlane.lambda,SourcePlane.mainPlane,Sil.Uneven.MainSource.Plane.B,Sil.Uneven.MainSource.Plane.lambda] <;> ring_nf <;> simp

theorem new_supremum_deficit {β d δ p : ℝ} (hb : theta < β)
    (hinc : β ≤ incumbent) (hd : d ∈ Set.Icc dMinus dPlus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt (2*β-1) d δ p-β ≤ -reserve-(β-theta) := by
  cases config with
  | mk stage =>
    cases stage
    · have hb' : Sil.Uneven.WarmupRows.theta < β := by simpa only [theta] using hb
      have hi' : β ≤ (Sil.Uneven.WarmupRows.frozen_kappa+1)/2 := by
        norm_num [incumbent,Sil.Uneven.WarmupRows.frozen_kappa] at hinc ⊢
        exact hinc
      have hd' : Sil.Uneven.WarmupRows.rowHeight 2 ≤ d ∧ d ≤ Sil.Uneven.WarmupRows.rowHeight 3 := by
        norm_num [Set.mem_Icc,d0,dMinus,dPlus,h,upperPadding,Sil.Uneven.WarmupRows.h,Sil.Uneven.WarmupRows.rowHeight] at hd ⊢
        constructor <;> linarith [hd.1,hd.2]
      have hh := Sil.Uneven.WarmupRows.new_supremum_deficit hb' hi' hδ hp hd'
      convert hh using 1 <;> norm_num [rowBase,rowAt,count,newExponentAt,newCapacity,h,ell,y,theta,slotClip,reserve,Sil.Uneven.WarmupRows.reserve,Sil.Uneven.WarmupRows.planeB,Sil.Uneven.WarmupRows.planeLambda,Sil.Uneven.WarmupRows.scalarRow,Sil.Uneven.WarmupRows.rowConstant,Sil.Uneven.WarmupRows.newCapacity,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.WarmupRows.ell,Sil.Uneven.WarmupRows.y,SourcePlane.B,SourcePlane.lambda,SourcePlane.mainPlane,Sil.Uneven.MainSource.Plane.B,Sil.Uneven.MainSource.Plane.lambda] <;> ring_nf <;> simp

    · have hb' : Sil.Uneven.RoundedRows.theta < β := by simpa only [theta] using hb
      have hi' : β ≤ (Sil.Uneven.RoundedRows.frozen_kappa+1)/2 := by
        norm_num [incumbent,Sil.Uneven.RoundedRows.frozen_kappa] at hinc ⊢
        exact hinc
      have hd' : Sil.Uneven.RoundedRows.rowHeight 2 ≤ d ∧ d ≤ Sil.Uneven.RoundedRows.rowHeight 3 := by
        norm_num [Set.mem_Icc,d0,dMinus,dPlus,h,upperPadding,Sil.Uneven.RoundedRows.h,Sil.Uneven.RoundedRows.rowHeight] at hd ⊢
        constructor <;> linarith [hd.1,hd.2]
      have hh := Sil.Uneven.RoundedRows.new_supremum_deficit hb' hi' hδ hp hd'
      convert hh using 1 <;> norm_num [rowBase,rowAt,count,newExponentAt,newCapacity,h,ell,y,theta,slotClip,reserve,Sil.Uneven.RoundedRows.scalarRow,Sil.Uneven.RoundedRows.rowConstant,Sil.Uneven.RoundedRows.newCapacity,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,Sil.Uneven.RoundedRows.ell,Sil.Uneven.RoundedRows.y,SourcePlane.B,SourcePlane.lambda,SourcePlane.mainPlane,Sil.Uneven.MainSource.Plane.B,Sil.Uneven.MainSource.Plane.lambda,Sil.Uneven.Critical.physicalB,Sil.Uneven.Critical.physicalLambda] <;> ring_nf <;> simp

end
end OAI.SevenEighths.UnevenEndpoint.Count
end
