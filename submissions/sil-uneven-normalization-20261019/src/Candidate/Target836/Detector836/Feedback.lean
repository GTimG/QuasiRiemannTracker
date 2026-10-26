/- Private target .874836 scalar continuation. The feedback algebra follows
   accepted Candidate/Cycle63/Arithmetic/Bernstein/Feedback.lean, Apache-2.0. -/
import Candidate.Target836.Detector836.Endpoint

set_option autoImplicit false
set_option maxHeartbeats 0
namespace Target836.EndpointArithmetic
noncomputable section
open Target836.Arithmetic

def oldCapacityAt (κ d : ℝ) : ℝ := min d (2*y-d)/(6*κ)
def newExponentAt (κ d δ p : ℝ) : ℝ := rowAt κ d (newCapacity d) δ p
def oldExponentAt (κ d δ p : ℝ) : ℝ := rowAt κ d (oldCapacityAt κ d) δ p

theorem newExponentAt_base (d δ p : ℝ) :
    newExponentAt kappaStar d δ p = newExponent d δ p := rfl
theorem oldExponentAt_base (d δ p : ℝ) :
    oldExponentAt kappaStar d δ p = oldExponent d δ p := rfl

theorem new_feedback {κ d δ p : ℝ} (hk : kappaStar ≤ κ)
    (hd : d ∈ Set.Icc 0 dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt κ d δ p-newExponent d δ p ≤ (κ-kappaStar)/50 := by
  have hgap : 0 ≤ κ-kappaStar := sub_nonneg.mpr hk
  have hrow := Detector836.count_gap
    (show Detector836.kStar ≤ kappaStar by rw [kappaStar_eq_detector]) hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1,hδ.2]) hp
  have hR := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hcoef : 5*dPlus/288 ≤ (1:ℝ)/50 := by norm_num [dPlus]
  have hdprod := mul_le_mul_of_nonneg_right hd.2 hgap
  have hco := mul_le_mul_of_nonneg_right hcoef hgap
  unfold newExponentAt newExponent rowAt
  nlinarith [hR,hdprod,hco]

theorem min_capacity_upper (d : ℝ) : min d (2*y-d) ≤ 1/2 := by
  rcases le_total d y with hd | hd
  · have hm := min_le_left d (2*y-d)
    linarith [y_lt_half]
  · have hm := min_le_right d (2*y-d)
    linarith [y_lt_half]

theorem old_feedback {κ d δ p : ℝ} (hk : kappaStar ≤ κ)
    (hd : d ∈ Set.Icc 0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt κ d δ p-oldExponent d δ p ≤ (κ-kappaStar)/8 := by
  have ha := kappaStar_mem.1
  have hk' := ha.trans hk
  have ha0 : 0 < kappaStar := by linarith
  have hk0 : 0 < κ := by linarith
  have hgap : 0 ≤ κ-kappaStar := sub_nonneg.mpr hk
  have hrow := Detector836.count_gap
    (show Detector836.kStar ≤ kappaStar by rw [kappaStar_eq_detector]) hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1,hδ.2]) hp
  have hR := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hd1 : d ≤ 1 := hd.2.trans dMinus_lt_h.le |>.trans (h_lt_dPlus.le.trans dPlus_lt_one.le)
  have hdprod := mul_le_mul_of_nonneg_right hd1 hgap
  have hprod : (7/10:ℝ)^2 ≤ κ*kappaStar := by
    rw [pow_two]
    exact mul_le_mul hk' ha (by norm_num) hk0.le
  have hinvid : 1/kappaStar-1/κ = (κ-kappaStar)/(κ*kappaStar) := by field_simp
  have hinv : 1/kappaStar-1/κ ≤ (κ-kappaStar)/((7/10:ℝ)^2) := by
    rw [hinvid]
    exact div_le_div_of_nonneg_left hgap (by norm_num) hprod
  have hmin0 : 0 ≤ min d (2*y-d) := by
    apply le_min hd.1
    have := hd.2
    norm_num [dMinus,y] at *
    linarith
  have hmin := min_capacity_upper d
  have hdpupper : δ*p ≤ 3/8 := by
    have hm := mul_le_mul hδ.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hm
    exact hm
  have hcoef : 0 ≤ δ*p*min d (2*y-d)/12 := by
    have hδ0 := hδ.1
    have hp0 := hp.1
    positivity
  have hcoefupper : δ*p*min d (2*y-d)/12 ≤ 1/64 := by
    have hm := mul_le_mul hdpupper hmin hmin0 (by norm_num : (0:ℝ) ≤ 3/8)
    linarith
  have hI : (δ*p*min d (2*y-d)/12)*(1/kappaStar-1/κ) ≤
      (1/64)*((κ-kappaStar)/((7/10:ℝ)^2)) := by
    calc
      _ ≤ (δ*p*min d (2*y-d)/12)*((κ-kappaStar)/((7/10:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hinv hcoef
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoefupper (by positivity)
  have hid : oldExponentAt κ d δ p-oldExponent d δ p =
      (3*d/4)*(Detector836.count κ δ p-Detector836.count kappaStar δ p)+
      (δ*p*min d (2*y-d)/12)*(1/kappaStar-1/κ) := by
    unfold oldExponentAt oldExponent rowAt rowBase oldCapacityAt oldCapacity
    field_simp
    ring
  rw [hid]
  ring_nf at hR hdprod hI ⊢
  linarith only [hR,hdprod,hI,hgap]

/-- Weak affine interval interpolation, retaining the complete endpoint reserve. -/
theorem affine_interval_le {f : ℝ → ℝ} {a b A S M d : ℝ}
    (hf : ∀ z, f z=A+z*S) (hd : d ∈ Set.Icc a b)
    (ha : f a ≤ M) (hb : f b ≤ M) : f d ≤ M := by
  simp only [hf] at ha hb ⊢
  rcases le_total 0 S with hS|hS
  · have hm := mul_le_mul_of_nonneg_right hd.2 hS
    linarith
  · have hm := mul_le_mul_of_nonpos_right hd.1 hS
    linarith

def rowCommon (δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p
def baseSlope (δ p : ℝ) : ℝ := 1/4-17/50+3*Detector836.count kappaStar δ p/4
def newSlope (δ p : ℝ) : ℝ := baseSlope δ p+δ*p*(2-B)/(2*lambda)

theorem newExponent_affine (d δ p : ℝ) :
    newExponent d δ p=rowCommon δ p-δ*p*y/lambda+d*newSlope δ p := by
  unfold newExponent rowAt rowBase rowCommon newSlope baseSlope newCapacity
  ring

theorem new_interval_bound {d δ p : ℝ}
    (hd : d ∈ Set.Icc dMinus dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : newExponent d δ p ≤ theta-reserve := by
  apply affine_interval_le (f:=fun z=>newExponent z δ p)
    (fun z=>newExponent_affine z δ p) hd
  · exact Target836.EndpointCertificates.new_junction_bound hδ hp
  · exact Target836.EndpointCertificates.top_bound hδ hp

theorem rowAt_capacity_antitone {κ d C₁ C₂ δ p : ℝ}
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hC : C₁ ≤ C₂) :
    rowAt κ d C₂ δ p ≤ rowAt κ d C₁ δ p := by
  have hm := mul_nonneg (mul_nonneg hδ hp) (sub_nonneg.mpr hC)
  unfold rowAt rowBase
  nlinarith

def oldLeftLine (d δ p : ℝ) : ℝ := rowAt kappaStar d (d/(6*kappaStar)) δ p
def oldRightLine (d δ p : ℝ) : ℝ := rowAt kappaStar d ((2*y-d)/(6*kappaStar)) δ p

theorem oldLeftLine_affine (d δ p : ℝ) :
    oldLeftLine d δ p=rowCommon δ p+d*(baseSlope δ p-δ*p/(12*kappaStar)) := by
  unfold oldLeftLine rowAt rowBase rowCommon baseSlope
  ring

theorem oldRightLine_affine (d δ p : ℝ) :
    oldRightLine d δ p=rowCommon δ p-δ*p*y/(6*kappaStar)+
      d*(baseSlope δ p+δ*p/(12*kappaStar)) := by
  unfold oldRightLine rowAt rowBase rowCommon baseSlope
  ring

theorem oldLeftLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldLeftLine d δ p ≤ oldExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_left d (2*y-d)) (by norm_num [kappaStar])

theorem oldRightLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldRightLine d δ p ≤ oldExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_right d (2*y-d)) (by norm_num [kappaStar])

theorem old_interval_of_endpoints {a b M d δ p : ℝ}
    (hd : d ∈ Set.Icc a b) (hδ : 0 ≤ δ) (hp : 0 ≤ p)
    (ha : oldExponent a δ p ≤ M) (hb : oldExponent b δ p ≤ M) :
    oldExponent d δ p ≤ M := by
  have hL : oldLeftLine d δ p ≤ M := by
    apply affine_interval_le (f:=fun z=>oldLeftLine z δ p)
      (fun z=>oldLeftLine_affine z δ p) hd
    · exact (oldLeftLine_le hδ hp).trans ha
    · exact (oldLeftLine_le hδ hp).trans hb
  have hR : oldRightLine d δ p ≤ M := by
    apply affine_interval_le (f:=fun z=>oldRightLine z δ p)
      (fun z=>oldRightLine_affine z δ p) hd
    · exact (oldRightLine_le hδ hp).trans ha
    · exact (oldRightLine_le hδ hp).trans hb
  rcases le_total d (2*y-d) with hmin|hmin
  · simpa only [oldExponent,oldCapacity,min_eq_left hmin,oldLeftLine] using hL
  · simpa only [oldExponent,oldCapacity,min_eq_right hmin,oldRightLine] using hR

theorem old_interval_bound {d δ p : ℝ}
    (hd : d ∈ Set.Icc d0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : oldExponent d δ p ≤ theta-reserve := by
  exact old_interval_of_endpoints hd hδ.1 hp.1
    (Target836.EndpointCertificates.old_lower_bound hδ hp)
    (Target836.EndpointCertificates.old_junction_bound hδ hp)

theorem supremum_kappa_mem {β : ℝ} (hβ : theta < β) (hβupper : β ≤ 7/8) :
    kappaStar ≤ 2*β-1 ∧ 2*β-1 ≤ 3/4 := by
  rw [kappaStar_eq]
  constructor <;> linarith

theorem new_supremum_deficit {β d δ p : ℝ} (hβ : theta < β)
    (hd : d ∈ Set.Icc dMinus dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt (2*β-1) d δ p-β ≤ -reserve-(24/25)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dPlus :=
    ⟨(by have := hd.1;norm_num [dMinus] at *;linarith),hd.2⟩
  have hk : kappaStar ≤ 2*β-1 := by rw [kappaStar_eq];linarith
  have hf := new_feedback hk hd' hδ hp
  rw [kappaStar_eq] at hf
  have hb := new_interval_bound hd hδ hp
  linarith

theorem old_supremum_deficit {β d δ p : ℝ} (hβ : theta < β)
    (hd : d ∈ Set.Icc d0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p-β ≤ -reserve-(3/4)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dMinus := ⟨d0_pos.le.trans hd.1,hd.2⟩
  have hk : kappaStar ≤ 2*β-1 := by rw [kappaStar_eq];linarith
  have hf := old_feedback hk hd' hδ hp
  rw [kappaStar_eq] at hf
  have hb := old_interval_bound hd hδ hp
  linarith

theorem new_supremum_saving {β d δ p : ℝ} (hβ : theta < β)
    (hd : d ∈ Set.Icc dMinus dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : newExponentAt (2*β-1) d δ p < β-reserve := by
  have := new_supremum_deficit hβ hd hδ hp
  linarith

theorem old_supremum_saving {β d δ p : ℝ} (hβ : theta < β)
    (hd : d ∈ Set.Icc d0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : oldExponentAt (2*β-1) d δ p < β-reserve := by
  have := old_supremum_deficit hβ hd hδ hp
  linarith

end
end Target836.EndpointArithmetic
#print axioms Target836.EndpointArithmetic.new_interval_bound
#print axioms Target836.EndpointArithmetic.old_interval_bound
#print axioms Target836.EndpointArithmetic.new_feedback
#print axioms Target836.EndpointArithmetic.old_feedback
#print axioms Target836.EndpointArithmetic.new_supremum_deficit
#print axioms Target836.EndpointArithmetic.old_supremum_deficit
#print axioms Target836.EndpointArithmetic.new_supremum_saving
#print axioms Target836.EndpointArithmetic.old_supremum_saving
