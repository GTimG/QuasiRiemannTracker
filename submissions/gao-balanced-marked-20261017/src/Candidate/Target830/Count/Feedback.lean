import Candidate.Target830.Count.Endpoint

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def newExponentAt (κ d δ p : ℝ) : ℝ := rowAt κ d (newCapacity d) δ p
def oldExponentAt (κ d δ p : ℝ) : ℝ := rowAt κ d (oldCapacityAt κ d) δ p

theorem new_feedback {κ d δ p : ℝ} (hk : kappaStar ≤ κ)
    (hd : d ∈ Set.Icc 0 dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt κ d δ p-newExponent d δ p ≤ (κ-kappaStar)/50 := by
  have hg : 0 ≤ κ-kappaStar := sub_nonneg.mpr hk
  have hc := count_gap
    (show (7/10:ℝ) ≤ kappaStar by norm_num [kappaStar,theta]) hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1,hδ.2]) hp
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hcoef : 5*dPlus/288 ≤ (1:ℝ)/50 := by norm_num [dPlus,h]
  have hp1 := mul_le_mul_of_nonneg_right hd.2 hg
  have hp2 := mul_le_mul_of_nonneg_right hcoef hg
  unfold newExponentAt newExponent rowAt
  nlinarith

theorem min_capacity_upper (d : ℝ) : min d (2*y-d) ≤ 1/2 := by
  have hy : y < (1:ℝ)/2 := by norm_num [y,h,ell,theta]
  rcases le_total d y with hd | hd
  · have := min_le_left d (2*y-d)
    linarith
  · have := min_le_right d (2*y-d)
    linarith

theorem old_feedback {κ d δ p : ℝ} (hk : kappaStar ≤ κ)
    (hd : d ∈ Set.Icc 0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt κ d δ p-oldExponent d δ p ≤ (κ-kappaStar)/8 := by
  have ha : (7/10:ℝ) ≤ kappaStar := by norm_num [kappaStar,theta]
  have hk7 := ha.trans hk
  have ha0 : 0 < kappaStar := by linarith
  have hk0 : 0 < κ := by linarith
  have hg : 0 ≤ κ-kappaStar := sub_nonneg.mpr hk
  have hc := count_gap ha hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1,hδ.2]) hp
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hd1 : d ≤ 1 := by have := hd.2;norm_num [dMinus,h] at *;linarith
  have hdp := mul_le_mul_of_nonneg_right hd1 hg
  have hprod : (7/10:ℝ)^2 ≤ κ*kappaStar := by
    rw [pow_two]
    exact mul_le_mul hk7 ha (by norm_num) hk0.le
  have hinvid : 1/kappaStar-1/κ=(κ-kappaStar)/(κ*kappaStar) := by field_simp
  have hinv : 1/kappaStar-1/κ ≤ (κ-kappaStar)/((7/10:ℝ)^2) := by
    rw [hinvid]
    exact div_le_div_of_nonneg_left hg (by norm_num) hprod
  have hmin0 : 0 ≤ min d (2*y-d) := by
    apply le_min hd.1
    have := hd.2
    norm_num [dMinus,y,h,ell,theta] at *
    linarith
  have hmin := min_capacity_upper d
  have hδp : δ*p ≤ 3/8 := by
    have := mul_le_mul hδ.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    linarith
  have hcoef0 : 0 ≤ δ*p*min d (2*y-d)/12 :=
    div_nonneg (mul_nonneg (mul_nonneg hδ.1 hp.1) hmin0) (by norm_num)
  have hcoef : δ*p*min d (2*y-d)/12 ≤ 1/64 := by
    have := mul_le_mul hδp hmin hmin0 (by norm_num : (0:ℝ) ≤ 3/8)
    linarith
  have hi : (δ*p*min d (2*y-d)/12)*(1/kappaStar-1/κ) ≤
      (1/64)*((κ-kappaStar)/((7/10:ℝ)^2)) := by
    calc
      _ ≤ (δ*p*min d (2*y-d)/12)*((κ-kappaStar)/((7/10:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hinv hcoef0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have he : oldExponentAt κ d δ p-oldExponent d δ p =
      (3*d/4)*(count κ δ p-count kappaStar δ p)+
      (δ*p*min d (2*y-d)/12)*(1/kappaStar-1/κ) := by
    unfold oldExponentAt oldExponent rowAt rowBase oldCapacityAt
    field_simp
    ring
  rw [he]
  ring_nf at hm hdp hi ⊢
  linarith only [hm,hdp,hi,hg]

theorem feedback_kappa_interval {β : ℝ} (hb : theta < β)
    (hbold : β ≤ 218709/250000) :
    kappaStar ≤ 2*β-1 ∧ 2*β-1 ≤ kappa0 := by
  norm_num [kappaStar,kappa0,theta] at *
  constructor <;> linarith

theorem new_supremum_deficit {β d δ p : ℝ} (hb : theta < β)
    (hd : d ∈ Set.Icc dMinus dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt (2*β-1) d δ p-β ≤ -reserve-(24/25)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dPlus := by
    constructor
    · have := hd.1;norm_num [dMinus,h] at *;linarith
    · exact hd.2
  have hk : kappaStar ≤ 2*β-1 := by unfold kappaStar;linarith
  have hf := new_feedback hk hd' hδ hp
  have he := new_interval_bound hd hδ hp
  unfold kappaStar at hf
  linarith

theorem old_supremum_deficit {β d δ p : ℝ} (hb : theta < β)
    (hd : d ∈ Set.Icc d0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p-β ≤ -reserve-(3/4)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dMinus :=
    ⟨(show (0:ℝ) ≤ d0 by norm_num [d0]).trans hd.1,hd.2⟩
  have hk : kappaStar ≤ 2*β-1 := by unfold kappaStar;linarith
  have hf := old_feedback hk hd' hδ hp
  have he := old_interval_bound hd hδ hp
  unfold kappaStar at hf
  linarith

def effectiveReserve : ℝ := 99/1000000000

theorem count_loss_reserve {d loss : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 1)
    (hl : loss ≤ 3/2500000000) :
    3*d*loss/4 ≤ reserve-effectiveReserve := by
  have h := mul_le_mul_of_nonneg_left hl hd
  norm_num [reserve,effectiveReserve] at *
  nlinarith

end
end OAI.SevenEighths.Target830.Count
#print axioms OAI.SevenEighths.Target830.Count.new_feedback
#print axioms OAI.SevenEighths.Target830.Count.old_feedback
#print axioms OAI.SevenEighths.Target830.Count.new_supremum_deficit
#print axioms OAI.SevenEighths.Target830.Count.old_supremum_deficit
#print axioms OAI.SevenEighths.Target830.Count.count_loss_reserve
