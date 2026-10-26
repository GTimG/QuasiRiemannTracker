/- Repeated marks: fork of Collet's generic return module GenericFeedback (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Feedback algebra adapted from accepted PR63, Apache-2.0. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.Schedule
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return.GenericArithmetic
open QRH.Record1252270103Return
noncomputable section
open QRH.Record1252270103Return
variable [Geometry.Parameters] [Geometry.BoundsR] [CountScheme] [PhysicalSchedule]
open QRH.Record12518109Return (envelope_gap)
theorem new_feedback (bs : List Branch) {κ d δ p : ℝ} (hk : kappa ≤ κ)
    (hd : d ∈ Set.Icc 0 dp) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt bs κ d δ p-newExponent bs d δ p ≤ (κ-kappa)/50 := by
  have hg : 0 ≤ κ-kappa := sub_nonneg.mpr hk
  have hc := envelope_gap bs
    (show (7/10:ℝ) ≤ kappa by dsimp [kappa]; linarith [Geometry.BoundsR.theta_bounds.1]) hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1,hδ.2]) hp
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hcoef : 5*dp/288 ≤ (1:ℝ)/50 := by change 5*(Geometry.h+1/10000000000)/288 ≤ (1:ℝ)/50; linarith [Geometry.BoundsR.h_interval.2]
  have hp1 := mul_le_mul_of_nonneg_right hd.2 hg
  have hp2 := mul_le_mul_of_nonneg_right hcoef hg
  unfold newExponentAt newExponent rowAt
  nlinarith

theorem min_capacity_upper (d : ℝ) : min d (2*y-d) ≤ 1/2 := by
  have hy : y < (1:ℝ)/2 := Geometry.y_lt_half
  rcases le_total d y with hd | hd
  · have := min_le_left d (2*y-d)
    linarith
  · have := min_le_right d (2*y-d)
    linarith

theorem old_feedback (bs : List Branch) {κ d δ p : ℝ} (hk : kappa ≤ κ)
    (hd : d ∈ Set.Icc 0 dm) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt bs κ d δ p-oldExponent bs d δ p ≤ (κ-kappa)/8 := by
  have ha : (7/10:ℝ) ≤ kappa := by dsimp [kappa]; linarith [Geometry.BoundsR.theta_bounds.1]
  have hk7 := ha.trans hk
  have ha0 : 0 < kappa := by linarith
  have hk0 : 0 < κ := by linarith
  have hg : 0 ≤ κ-kappa := sub_nonneg.mpr hk
  have hc := envelope_gap bs ha hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1,hδ.2]) hp
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hd1 : d ≤ 1 := by exact hd.2.trans (PhysicalSchedule.dMinus_before_top.trans (RepeatedMarksReturn.Transport.Arithmetic.dPlus_lt_one.le))
  have hdp := mul_le_mul_of_nonneg_right hd1 hg
  have hprod : (7/10:ℝ)^2 ≤ κ*kappa := by
    rw [pow_two]
    exact mul_le_mul hk7 ha (by norm_num) hk0.le
  have hinvid : 1/kappa-1/κ=(κ-kappa)/(κ*kappa) := by field_simp
  have hinv : 1/kappa-1/κ ≤ (κ-kappa)/((7/10:ℝ)^2) := by
    rw [hinvid]
    exact div_le_div_of_nonneg_left hg (by norm_num) hprod
  have hmin0 : 0 ≤ min d (2*y-d) := by
    apply le_min hd.1
    have hh := PhysicalSchedule.switch_before_twoy
    linarith [hd.2]
  have hmin := min_capacity_upper d
  have hδp : δ*p ≤ 3/8 := by
    have := mul_le_mul hδ.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    linarith
  have hcoef0 : 0 ≤ δ*p*min d (2*y-d)/12 :=
    div_nonneg (mul_nonneg (mul_nonneg hδ.1 hp.1) hmin0) (by norm_num)
  have hcoef : δ*p*min d (2*y-d)/12 ≤ 1/64 := by
    have := mul_le_mul hδp hmin hmin0 (by norm_num : (0:ℝ) ≤ 3/8)
    linarith
  have hi : (δ*p*min d (2*y-d)/12)*(1/kappa-1/κ) ≤
      (1/64)*((κ-kappa)/((7/10:ℝ)^2)) := by
    calc
      _ ≤ (δ*p*min d (2*y-d)/12)*((κ-kappa)/((7/10:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hinv hcoef0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have he : oldExponentAt bs κ d δ p-oldExponent bs d δ p =
      (3*d/4)*(envelope bs κ δ p-envelope bs kappa δ p)+
      (δ*p*min d (2*y-d)/12)*(1/kappa-1/κ) := by
    unfold oldExponentAt oldExponent rowAt Ebase oldCapacityAt
    field_simp
    ring
  rw [he]
  ring_nf at hm hdp hi ⊢
  linarith only [hm,hdp,hi,hg]


theorem new_supremum_deficit (bs : List Branch) {β d δ p : ℝ}
    (hb : theta < β) (hd : d ∈ Set.Icc dm dp)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hbase : newExponent bs d δ p ≤ theta-rowFee) :
    newExponentAt bs (2*β-1) d δ p-β ≤ -rowFee-(24/25)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dp := by
    constructor
    · have hm := PhysicalSchedule.dMinus_lower; linarith [hd.1]
    · exact hd.2
  have hk : kappa ≤ 2*β-1 := by unfold kappa at *; linarith
  have hf := new_feedback bs hk hd' hδ hp
  unfold kappa at hf
  
  linarith

theorem old_supremum_deficit (bs : List Branch) {β d δ p : ℝ}
    (hb : theta < β) (hd : d ∈ Set.Icc d0 dm)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hbase : oldExponent bs d δ p ≤ theta-rowFee) :
    oldExponentAt bs (2*β-1) d δ p-β ≤ -rowFee-(3/4)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dm :=
    ⟨(show (0:ℝ) ≤ d0 by norm_num [d0]).trans hd.1,hd.2⟩
  have hk : kappa ≤ 2*β-1 := by unfold kappa at *; linarith
  have hf := old_feedback bs hk hd' hδ hp
  unfold kappa at hf
  
  linarith

theorem count_loss_reserve {d loss : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1)
    (hl : loss ≤ rowFee/4) :
    3*d*loss/4 ≤ rowFee/2 := by
  have h := mul_le_mul_of_nonneg_left hl hd
  have hfee : 0 < rowFee := by norm_num [rowFee]
  nlinarith

end
end QRH.RepeatedMarks.Return.GenericArithmetic
