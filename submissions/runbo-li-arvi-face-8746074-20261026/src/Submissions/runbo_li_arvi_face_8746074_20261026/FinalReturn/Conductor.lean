/- Repeated marks: fork of Collet's final-stage module Conductor (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountingBridge
import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section

open QRH.Record12518109Return (envelope_gap)
noncomputable abbrev dm : ℝ := ds
noncomputable abbrev cap : ℝ := numeratorCap
def rowAt (bs : List Branch) (κ d C δ p : ℝ) : ℝ :=
  Ebase d C δ p+3*d*envelope bs κ δ p/4
def oldCapacityAt (κ d : ℝ) : ℝ := min d (2*y-d)/(6*κ)
def oldExponent (bs : List Branch) (d δ p : ℝ) : ℝ :=
  rowAt bs kappa d (oldCapacityAt kappa d) δ p
def newExponent (bs : List Branch) (d δ p : ℝ) : ℝ :=
  rowAt bs kappa d (newCapacity d) δ p
def rowCommon (δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p
def rowSlope (bs : List Branch) (δ p : ℝ) : ℝ :=
  -9/100+3*envelope bs kappa δ p/4

theorem affine_interval_le {f : ℝ → ℝ} {a b A S M d : ℝ}
    (hf : ∀ z, f z=A+z*S) (hd : d ∈ Set.Icc a b)
    (ha : f a ≤ M) (hb : f b ≤ M) : f d ≤ M := by
  simp only [hf] at ha hb ⊢
  rcases le_total 0 S with hS | hS
  · have hm := mul_le_mul_of_nonneg_right hd.2 hS
    linarith
  · have hm := mul_le_mul_of_nonpos_right hd.1 hS
    linarith

theorem rowAt_capacity_antitone (bs : List Branch) {κ d C₁ C₂ δ p : ℝ}
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hC : C₁ ≤ C₂) :
    rowAt bs κ d C₂ δ p ≤ rowAt bs κ d C₁ δ p := by
  have hm := mul_nonneg (mul_nonneg hδ hp) (sub_nonneg.mpr hC)
  unfold rowAt Ebase
  nlinarith

def newClipLine (bs : List Branch) (d δ p : ℝ) : ℝ := rowAt bs kappa d (numeratorCap*d) δ p
def newAffineLine (bs : List Branch) (d δ p : ℝ) : ℝ :=
  rowAt bs kappa d ((2*y-(2-physicalB)*d)/physicalLambda) δ p

theorem newClipLine_affine (bs : List Branch) (d δ p : ℝ) :
    newClipLine bs d δ p=rowCommon δ p+d*(rowSlope bs δ p-δ*p*cap/2) := by
  unfold newClipLine rowAt Ebase rowCommon rowSlope cap
  ring

theorem newAffineLine_affine (bs : List Branch) (d δ p : ℝ) :
    newAffineLine bs d δ p=rowCommon δ p-δ*p*y/physicalLambda+
      d*(rowSlope bs δ p+δ*p*(2-physicalB)/(2*physicalLambda)) := by
  unfold newAffineLine rowAt Ebase rowCommon rowSlope
  ring

theorem newClipLine_le (bs : List Branch) {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    newClipLine bs d δ p ≤ newExponent bs d δ p := by
  apply rowAt_capacity_antitone bs hδ hp
  exact min_le_left (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)

theorem newAffineLine_le (bs : List Branch) {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    newAffineLine bs d δ p ≤ newExponent bs d δ p := by
  apply rowAt_capacity_antitone bs hδ hp
  exact min_le_right _ _

theorem new_interval_bound (bs : List Branch) {d δ p : ℝ}
    (hd : d ∈ Set.Icc dm dp) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2))
    (hlo : newExponent bs dm δ p ≤ theta-rowFee)
    (hhi : newExponent bs dp δ p ≤ theta-rowFee) :
    newExponent bs d δ p ≤ theta-rowFee := by
  have hc : newClipLine bs d δ p ≤ theta-rowFee := by
    apply affine_interval_le (fun z => newClipLine_affine bs z δ p) hd
    · exact (newClipLine_le bs hδ.1 hp.1).trans hlo
    · exact (newClipLine_le bs hδ.1 hp.1).trans hhi
  have ha : newAffineLine bs d δ p ≤ theta-rowFee := by
    apply affine_interval_le (fun z => newAffineLine_affine bs z δ p) hd
    · exact (newAffineLine_le bs hδ.1 hp.1).trans hlo
    · exact (newAffineLine_le bs hδ.1 hp.1).trans hhi
  rcases le_total (numeratorCap*d)
    ((2*y-(2-physicalB)*d)/physicalLambda) with hm | hm
  · simpa only [newExponent,newCapacity,min_eq_left hm,newClipLine] using hc
  · simpa only [newExponent,newCapacity,min_eq_right hm,newAffineLine] using ha

def oldLeftLine (bs : List Branch) (d δ p : ℝ) : ℝ := rowAt bs kappa d (d/(6*kappa)) δ p
def oldRightLine (bs : List Branch) (d δ p : ℝ) : ℝ := rowAt bs kappa d ((2*y-d)/(6*kappa)) δ p

theorem oldLeftLine_affine (bs : List Branch) (d δ p : ℝ) :
    oldLeftLine bs d δ p=rowCommon δ p+d*(rowSlope bs δ p-δ*p/(12*kappa)) := by
  unfold oldLeftLine rowAt Ebase rowCommon rowSlope
  ring
theorem oldRightLine_affine (bs : List Branch) (d δ p : ℝ) :
    oldRightLine bs d δ p=rowCommon δ p-δ*p*y/(6*kappa)+
      d*(rowSlope bs δ p+δ*p/(12*kappa)) := by
  unfold oldRightLine rowAt Ebase rowCommon rowSlope
  ring
theorem oldLeftLine_le (bs : List Branch) {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldLeftLine bs d δ p ≤ oldExponent bs d δ p := by
  apply rowAt_capacity_antitone bs hδ hp
  exact div_le_div_of_nonneg_right (min_le_left _ _)
    (by norm_num [kappa,theta,c])
theorem oldRightLine_le (bs : List Branch) {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldRightLine bs d δ p ≤ oldExponent bs d δ p := by
  apply rowAt_capacity_antitone bs hδ hp
  exact div_le_div_of_nonneg_right (min_le_right _ _)
    (by norm_num [kappa,theta,c])

theorem old_interval_bound (bs : List Branch) {d δ p : ℝ}
    (hd : d ∈ Set.Icc d0 dm) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2))
    (hlo : oldExponent bs d0 δ p ≤ theta-rowFee)
    (hhi : oldExponent bs dm δ p ≤ theta-rowFee) :
    oldExponent bs d δ p ≤ theta-rowFee := by
  have hl : oldLeftLine bs d δ p ≤ theta-rowFee := by
    apply affine_interval_le (fun z => oldLeftLine_affine bs z δ p) hd
    · exact (oldLeftLine_le bs hδ.1 hp.1).trans hlo
    · exact (oldLeftLine_le bs hδ.1 hp.1).trans hhi
  have hr : oldRightLine bs d δ p ≤ theta-rowFee := by
    apply affine_interval_le (fun z => oldRightLine_affine bs z δ p) hd
    · exact (oldRightLine_le bs hδ.1 hp.1).trans hlo
    · exact (oldRightLine_le bs hδ.1 hp.1).trans hhi
  rcases le_total d (2*y-d) with hm | hm
  · simpa only [oldExponent,oldCapacityAt,min_eq_left hm,oldLeftLine] using hl
  · simpa only [oldExponent,oldCapacityAt,min_eq_right hm,oldRightLine] using hr

end
end QRH.RepeatedMarks.Return
#print axioms QRH.RepeatedMarks.Return.new_interval_bound
#print axioms QRH.RepeatedMarks.Return.old_interval_bound
