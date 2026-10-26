import Candidate.Target830.Count.Rows.OldLower
import Candidate.Target830.Count.Rows.OldHalf
import Candidate.Target830.Count.Rows.OldJunction
import Candidate.Target830.Count.Rows.NewJunction
import Candidate.Target830.Count.Rows.Top

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def oldExponent (d δ p : ℝ) : ℝ := rowAt kappaStar d (oldCapacityAt kappaStar d) δ p
def newExponent (d δ p : ℝ) : ℝ := rowAt kappaStar d (newCapacity d) δ p
def rowCommon (δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p
def rowSlope (δ p : ℝ) : ℝ := 1/4-17/50+3*count kappaStar δ p/4

theorem affine_interval_le {f : ℝ → ℝ} {a b A S M d : ℝ}
    (hf : ∀ z, f z=A+z*S) (hd : d ∈ Set.Icc a b)
    (ha : f a ≤ M) (hb : f b ≤ M) : f d ≤ M := by
  simp only [hf] at ha hb ⊢
  rcases le_total 0 S with hS | hS
  · have hm := mul_le_mul_of_nonneg_right hd.2 hS
    linarith
  · have hm := mul_le_mul_of_nonpos_right hd.1 hS
    linarith

theorem rowAt_capacity_antitone {κ d C₁ C₂ δ p : ℝ}
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hC : C₁ ≤ C₂) :
    rowAt κ d C₂ δ p ≤ rowAt κ d C₁ δ p := by
  have hm := mul_nonneg (mul_nonneg hδ hp) (sub_nonneg.mpr hC)
  unfold rowAt rowBase
  nlinarith

def newClipLine (d δ p : ℝ) : ℝ := rowAt kappaStar d (slotClip*d) δ p
def newAffineLine (d δ p : ℝ) : ℝ :=
  rowAt kappaStar d ((2*y-(2-SourcePlane.A.B)*d)/SourcePlane.A.lambda) δ p

theorem newClipLine_affine (d δ p : ℝ) :
    newClipLine d δ p=rowCommon δ p+d*(rowSlope δ p-δ*p*slotClip/2) := by
  unfold newClipLine rowAt rowBase rowCommon rowSlope
  ring

theorem newAffineLine_affine (d δ p : ℝ) :
    newAffineLine d δ p=rowCommon δ p-δ*p*y/SourcePlane.A.lambda+
      d*(rowSlope δ p+δ*p*(2-SourcePlane.A.B)/(2*SourcePlane.A.lambda)) := by
  unfold newAffineLine rowAt rowBase rowCommon rowSlope
  ring

theorem newClipLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    newClipLine d δ p ≤ newExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact min_le_left _ _

theorem newAffineLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    newAffineLine d δ p ≤ newExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact min_le_right _ _

theorem new_interval_bound {d δ p : ℝ}
    (hd : d ∈ Set.Icc dMinus dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : newExponent d δ p ≤ theta-reserve := by
  have hlo := Certificates.new_junction_bound hδ hp
  have hhi := Certificates.top_bound hδ hp
  have hc : newClipLine d δ p ≤ theta-reserve := by
    apply affine_interval_le (fun z => newClipLine_affine z δ p) hd
    · exact (newClipLine_le hδ.1 hp.1).trans hlo
    · exact (newClipLine_le hδ.1 hp.1).trans hhi
  have ha : newAffineLine d δ p ≤ theta-reserve := by
    apply affine_interval_le (fun z => newAffineLine_affine z δ p) hd
    · exact (newAffineLine_le hδ.1 hp.1).trans hlo
    · exact (newAffineLine_le hδ.1 hp.1).trans hhi
  rcases le_total (slotClip*d)
    ((2*y-(2-SourcePlane.A.B)*d)/SourcePlane.A.lambda) with hm | hm
  · simpa only [newExponent,newCapacity,min_eq_left hm,newClipLine] using hc
  · simpa only [newExponent,newCapacity,min_eq_right hm,newAffineLine] using ha

def oldLeftLine (d δ p : ℝ) : ℝ := rowAt kappaStar d (d/(6*kappaStar)) δ p
def oldRightLine (d δ p : ℝ) : ℝ := rowAt kappaStar d ((2*y-d)/(6*kappaStar)) δ p

theorem oldLeftLine_affine (d δ p : ℝ) :
    oldLeftLine d δ p=rowCommon δ p+d*(rowSlope δ p-δ*p/(12*kappaStar)) := by
  unfold oldLeftLine rowAt rowBase rowCommon rowSlope
  ring
theorem oldRightLine_affine (d δ p : ℝ) :
    oldRightLine d δ p=rowCommon δ p-δ*p*y/(6*kappaStar)+
      d*(rowSlope δ p+δ*p/(12*kappaStar)) := by
  unfold oldRightLine rowAt rowBase rowCommon rowSlope
  ring
theorem oldLeftLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldLeftLine d δ p ≤ oldExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_left _ _)
    (by norm_num [kappaStar,theta])
theorem oldRightLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldRightLine d δ p ≤ oldExponent d δ p := by
  apply rowAt_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_right _ _)
    (by norm_num [kappaStar,theta])

theorem old_interval_bound {d δ p : ℝ}
    (hd : d ∈ Set.Icc d0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : oldExponent d δ p ≤ theta-reserve := by
  have hlo := Certificates.old_lower_bound hδ hp
  have hhi := Certificates.old_junction_bound hδ hp
  have hl : oldLeftLine d δ p ≤ theta-reserve := by
    apply affine_interval_le (fun z => oldLeftLine_affine z δ p) hd
    · exact (oldLeftLine_le hδ.1 hp.1).trans hlo
    · exact (oldLeftLine_le hδ.1 hp.1).trans hhi
  have hr : oldRightLine d δ p ≤ theta-reserve := by
    apply affine_interval_le (fun z => oldRightLine_affine z δ p) hd
    · exact (oldRightLine_le hδ.1 hp.1).trans hlo
    · exact (oldRightLine_le hδ.1 hp.1).trans hhi
  rcases le_total d (2*y-d) with hm | hm
  · simpa only [oldExponent,oldCapacityAt,min_eq_left hm,oldLeftLine] using hl
  · simpa only [oldExponent,oldCapacityAt,min_eq_right hm,oldRightLine] using hr

end
end OAI.SevenEighths.Target830.Count
#print axioms OAI.SevenEighths.Target830.Count.new_interval_bound
#print axioms OAI.SevenEighths.Target830.Count.old_interval_bound
