/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Mixed
namespace QRH.Cycle092.Mixed
open QRH.Cycle090 QRH.ContactCertificate
noncomputable section

def branchPrice (lower : Bool) (z : ℝ) : ℝ := if lower then lowerBeta z else upperBeta z
def branchDerivative (lower : Bool) (z : ℝ) : ℝ :=
  if lower then betaSlope+lowerGainSlope z else betaSlope+upperGainSlope z

theorem branchPrice_eq_beta {lower : Bool} {z : ℝ}
    (h : if lower then z ≤ sourceSeam else sourceSeam ≤ z) : branchPrice lower z = beta z := by
  cases lower <;> simp only [branchPrice,Bool.false_eq_true,ite_false,ite_true] at h ⊢
  · exact (beta_upper h).symm
  · exact (beta_lower h).symm

theorem branch_lower_secant {lower : Bool} {a b L : ℝ}
    (hab : a ≤ b) (hb : b ≤ sourceY) (hL : -L ≤ branchDerivative lower a) :
    branchPrice lower a-L*(b-a) ≤ branchPrice lower b := by
  cases lower <;> simp only [branchPrice,branchDerivative,Bool.false_eq_true,ite_false,ite_true] at hL ⊢
  · exact upperBeta_local_secant hab hb hL
  · exact lowerBeta_local_secant hab hL

theorem upperBeta_local_upper_secant {a b A : ℝ} (hab : a ≤ b) (hb : b ≤ sourceY)
    (hA : betaSlope+upperGainSlope b ≤ -A) :
    upperBeta b-upperBeta a ≤ -A*(b-a) := by
  have hc : ContinuousOn upperBeta (Set.Icc a b) := by unfold upperBeta upperGain; fun_prop
  have hd : DifferentiableOn ℝ upperBeta (interior (Set.Icc a b)) :=
    fun z _ => (upperBeta_hasDerivAt z).differentiableAt.differentiableWithinAt
  have hu : ∀ z ∈ interior (Set.Icc a b), deriv upperBeta z ≤ -A := by
    intro z hz
    have hm := interior_subset hz
    rw [(upperBeta_hasDerivAt z).deriv]
    linarith [upperGainSlope_mono hm.2 hb]
  exact (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc hd hu
    a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab

theorem lowerBeta_local_upper_secant {a b A : ℝ} (hab : a ≤ b)
    (hA : betaSlope+lowerGainSlope b ≤ -A) :
    lowerBeta b-lowerBeta a ≤ -A*(b-a) := by
  have hc : ContinuousOn lowerBeta (Set.Icc a b) := by unfold lowerBeta lowerGain upperGain; fun_prop
  have hd : DifferentiableOn ℝ lowerBeta (interior (Set.Icc a b)) :=
    fun z _ => (lowerBeta_hasDerivAt z).differentiableAt.differentiableWithinAt
  have hu : ∀ z ∈ interior (Set.Icc a b), deriv lowerBeta z ≤ -A := by
    intro z hz
    have hm := interior_subset hz
    rw [(lowerBeta_hasDerivAt z).deriv]
    linarith [lowerGainSlope_mono hm.2]
  exact (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc hd hu
    a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab

theorem branch_upper_secant {lower : Bool} {a b A : ℝ}
    (hab : a ≤ b) (hb : b ≤ sourceY) (hA : branchDerivative lower b ≤ -A) :
    branchPrice lower b-branchPrice lower a ≤ -A*(b-a) := by
  cases lower <;> simp only [branchPrice,branchDerivative,Bool.false_eq_true,ite_false,ite_true] at hA ⊢
  · exact upperBeta_local_upper_secant hab hb hA
  · exact lowerBeta_local_upper_secant hab hA

def speed (arm : Bool) (v density k : ℝ) : ℝ := if arm then 1+v/(density*k) else 1

theorem offsetWidth_displacement {arm : Bool} {m ε step v density k a b : ℝ}
    (hab : a ≤ b) (hArm : if arm then step+3*ε ≤ a else b ≤ step+3*ε) :
    offsetWidth m ε step v density k a-offsetWidth m ε step v density k b =
      speed arm v density k*(b-a) := by
  cases arm <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hArm
  · have ha : a-step-3*ε ≤ 0 := by linarith
    have hb : b-step-3*ε ≤ 0 := by linarith
    simp only [offsetWidth,speed,Bool.false_eq_true,ite_false,max_eq_left ha,max_eq_left hb]
    ring
  · have ha : 0 ≤ a-step-3*ε := by linarith
    have hb : 0 ≤ b-step-3*ε := by linarith
    simp only [offsetWidth,speed,ite_true,max_eq_right ha,max_eq_right hb]
    ring


theorem segment_decreasing {lower arm : Bool} {f fee m ε step v density k a b ξ L : ℝ}
    (hf : 0 ≤ f) (hv : 0 ≤ v) (hd : 0 < density) (hk : 0 < k)
    (haξ : a ≤ ξ) (hξb : ξ ≤ b)
    (hY : offsetWidth m ε step v density k a ≤ sourceY)
    (hBranch : if lower then offsetWidth m ε step v density k a ≤ sourceSeam
      else sourceSeam ≤ offsetWidth m ε step v density k b)
    (hArm : if arm then step+3*ε ≤ a else b ≤ step+3*ε)
    (hL : -L ≤ branchDerivative lower (offsetWidth m ε step v density k b))
    (hpaid : f*L*speed arm v density k ≤ k/2) :
    offsetPrice f fee m ε step v density k b ≤ offsetPrice f fee m ε step v density k ξ := by
  have hbw := offsetWidth_antitone (m := m) (ε := ε) (step := step) hv hd hk hξb
  have hwa := offsetWidth_antitone (m := m) (ε := ε) (step := step) hv hd hk haξ
  have hβ := branch_lower_secant hbw (hwa.trans hY) hL
  have hBranchξ : (if lower then offsetWidth m ε step v density k ξ ≤ sourceSeam
      else sourceSeam ≤ offsetWidth m ε step v density k ξ) := by
    cases lower <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hBranch ⊢ <;> linarith
  have hBranchb : (if lower then offsetWidth m ε step v density k b ≤ sourceSeam
      else sourceSeam ≤ offsetWidth m ε step v density k b) := by
    cases lower <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hBranch ⊢ <;> linarith
  rw [branchPrice_eq_beta hBranchξ,branchPrice_eq_beta hBranchb] at hβ
  have hArmξ : (if arm then step+3*ε ≤ ξ else b ≤ step+3*ε) := by
    cases arm <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hArm ⊢ <;> linarith
  have hdiff := offsetWidth_displacement (m := m) (v := v) (density := density) (k := k) hξb hArmξ
  have hm := mul_le_mul_of_nonneg_left hβ hf
  rw [hdiff] at hm
  have hp := mul_le_mul_of_nonneg_right hpaid (sub_nonneg.mpr hξb)
  unfold offsetPrice
  nlinarith

theorem segment_increasing {lower arm : Bool} {f fee m ε step v density k a b ξ A : ℝ}
    (hf : 0 ≤ f) (hv : 0 ≤ v) (hd : 0 < density) (hk : 0 < k)
    (haξ : a ≤ ξ) (hξb : ξ ≤ b)
    (hY : offsetWidth m ε step v density k a ≤ sourceY)
    (hBranch : if lower then offsetWidth m ε step v density k a ≤ sourceSeam
      else sourceSeam ≤ offsetWidth m ε step v density k b)
    (hArm : if arm then step+3*ε ≤ a else b ≤ step+3*ε)
    (hA : branchDerivative lower (offsetWidth m ε step v density k a) ≤ -A)
    (hpaid : k/2 ≤ f*A*speed arm v density k) :
    offsetPrice f fee m ε step v density k a ≤ offsetPrice f fee m ε step v density k ξ := by
  have hbw := offsetWidth_antitone (m := m) (ε := ε) (step := step) hv hd hk hξb
  have hwa := offsetWidth_antitone (m := m) (ε := ε) (step := step) hv hd hk haξ
  have hβ := branch_upper_secant hwa hY hA
  have hBranchξ : (if lower then offsetWidth m ε step v density k ξ ≤ sourceSeam
      else sourceSeam ≤ offsetWidth m ε step v density k ξ) := by
    cases lower <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hBranch ⊢ <;> linarith
  have hBrancha : (if lower then offsetWidth m ε step v density k a ≤ sourceSeam
      else sourceSeam ≤ offsetWidth m ε step v density k a) := by
    cases lower <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hBranch ⊢ <;> linarith
  rw [branchPrice_eq_beta hBranchξ,branchPrice_eq_beta hBrancha] at hβ
  have hArmξ : (if arm then step+3*ε ≤ a else ξ ≤ step+3*ε) := by
    cases arm <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hArm ⊢ <;> linarith
  have hdiff := offsetWidth_displacement (m := m) (v := v) (density := density) (k := k) haξ hArmξ
  have hm := mul_le_mul_of_nonneg_left hβ hf
  rw [hdiff] at hm
  have hp := mul_le_mul_of_nonneg_right hpaid (sub_nonneg.mpr haξ)
  unfold offsetPrice
  nlinarith

def realWidth (box : QRH.Coverage.Box) (B : ℚ) (ξ : ℝ) : ℝ :=
  offsetWidth (rowM box) (1/10000000000000) ((rowGamma box B : ℝ)/65536)
    (rowV box) box.uHi (rowKUpper box) ξ
def realPrice (box : QRH.Coverage.Box) (B : ℚ) (ξ : ℝ) : ℝ :=
  offsetPrice box.vLo (rowFee box B) (rowM box) (1/10000000000000)
    ((rowGamma box B : ℝ)/65536) (rowV box) box.uHi (rowKUpper box) ξ
def actualWitnessPrice (box : QRH.Coverage.Box) (B : ℚ) (ξ z : ℝ) : ℝ :=
  witnessPrice beta box.vLo (rowFee box B) (rowKLower box) (rowKUpper box)
    (-(rowKUpper box : ℝ)*(ξ+3*(1/10000000000000)))
    (((rowV box : ℝ)/box.uHi)*max 0
      (ξ-(rowGamma box B : ℝ)/65536-3*(1/10000000000000)))
    ((rowM box : ℝ)+1/10000000000000) z

theorem rowWidth_real (box : QRH.Coverage.Box) (B ξ : ℚ) :
    (rowWidth box B ξ : ℝ) = realWidth box B ξ := rowWidth_cast box B ξ
theorem rowPrice_real (box : QRH.Coverage.Box) (B ξ : ℚ) :
    (rowPrice box B ξ : ℝ) = realPrice box B ξ := rowPrice_cast box B ξ

theorem rowBudget_cast {B : ℚ} (hB : 0 ≤ B) :
    (rowBudget B : ℝ) = ((B : ℝ)+inwardDebit)/hLower := by
  simp only [rowBudget,max_eq_right hB,Rat.cast_div,Rat.cast_add,
    Rat.cast_one,Rat.cast_ofNat,inwardDebit,hLower]

def rowShapeCheck (box : QRH.Coverage.Box) (B : ℚ) : Bool := decide (
  0 ≤ box.vLo ∧ box.vLo ≤ 1/2 ∧ 0 < box.uHi ∧ 0 ≤ rowV box ∧
  2/5 ≤ rowKLower box ∧ rowKLower box ≤ rowKUpper box ∧ rowKUpper box ≤ 1 ∧
  0 ≤ rowGamma box B ∧ 4643/12500 ≤ rowLo box B ∧ rowHi box B ≤ 947/2500)

structure RowContext (box : QRH.Coverage.Box) (B : ℚ) : Prop where
  hf₀ : (0 : ℝ) ≤ box.vLo
  hf₁ : (box.vLo : ℝ) ≤ 1/2
  hd : (0 : ℝ) < box.uHi
  hv : (0 : ℝ) ≤ rowV box
  hkl : (2/5 : ℝ) ≤ rowKLower box
  hko : (rowKLower box : ℝ) ≤ rowKUpper box
  hku : (rowKUpper box : ℝ) ≤ 1
  hγ : (0 : ℝ) ≤ rowGamma box B
  hlo : widthLo ≤ (rowLo box B : ℝ)
  hhi : (rowHi box B : ℝ) ≤ widthHi

theorem rowShapeCheck_sound {box : QRH.Coverage.Box} {B : ℚ}
    (hc : rowShapeCheck box B = true) : RowContext box B := by
  simp only [rowShapeCheck,decide_eq_true_eq] at hc
  rcases hc with ⟨hf₀,hf₁,hd,hv,hkl,hko,hku,hγ,hlo,hhi⟩
  refine ⟨Rat.cast_nonneg.mpr hf₀,?_,Rat.cast_pos.mpr hd,Rat.cast_nonneg.mpr hv,
    ?_,Rat.cast_le.mpr hko,?_,Rat.cast_nonneg.mpr hγ,?_,?_⟩
  · have h := (Rat.cast_le (K := ℝ)).mpr hf₁
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  · have h := (Rat.cast_le (K := ℝ)).mpr hkl
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  · have h := (Rat.cast_le (K := ℝ)).mpr hku
    simpa only [Rat.cast_one] using h
  · have h := (Rat.cast_le (K := ℝ)).mpr hlo
    simpa only [widthLo,Rat.cast_div,Rat.cast_ofNat] using h
  · have h := (Rat.cast_le (K := ℝ)).mpr hhi
    simpa only [widthHi,Rat.cast_div,Rat.cast_ofNat] using h

theorem RowContext.width_mem {box : QRH.Coverage.Box} {B : ℚ} (hc : RowContext box B)
    {ξ : ℝ} (hξ₀ : 0 ≤ ξ) (hξ₁ : ξ ≤ (rowGamma box B : ℝ)) :
    widthLo ≤ realWidth box B ξ ∧ realWidth box B ξ ≤ widthHi := by
  have hk : (0 : ℝ) < rowKUpper box := by linarith [hc.hkl,hc.hko]
  have h₀ := offsetWidth_antitone (m := (rowM box : ℝ)) (ε := 1/10000000000000)
    (step := (rowGamma box B : ℝ)/65536) hc.hv hc.hd hk hξ₀
  have h₁ := offsetWidth_antitone (m := (rowM box : ℝ)) (ε := 1/10000000000000)
    (step := (rowGamma box B : ℝ)/65536) hc.hv hc.hd hk hξ₁
  have hlo : (rowLo box B : ℝ) = realWidth box B (rowGamma box B) :=
    rowWidth_real box B (rowGamma box B)
  have hhi : (rowHi box B : ℝ) = realWidth box B 0 := by
    simpa only [rowHi,Rat.cast_zero] using rowWidth_real box B 0
  change realWidth box B ξ ≤ realWidth box B 0 at h₀
  change realWidth box B (rowGamma box B) ≤ realWidth box B ξ at h₁
  exact ⟨hc.hlo.trans (hlo ▸ h₁),h₀.trans (hhi ▸ hc.hhi)⟩

theorem realPrice_le_witness {box : QRH.Coverage.Box} {B : ℚ} (hc : RowContext box B)
    {ξ z : ℝ} (hξ₀ : 0 ≤ ξ) (hξ₁ : ξ ≤ (rowGamma box B : ℝ))
    (hz₀ : widthLo ≤ z) (hz₁ : z ≤ widthHi) :
    realPrice box B ξ ≤ actualWitnessPrice box B ξ z := by
  have hm := hc.width_mem hξ₀ hξ₁
  exact bank_witnessPrice_lower hc.hf₀ hc.hf₁ hc.hv hc.hd hc.hkl hc.hko
    (by norm_num) hξ₀ hm.1 hm.2 hz₀ hz₁

inductive SegmentMode where
  | decreasing | increasing | enclosure
  deriving DecidableEq, Repr
structure PriceSegment where
  a : ℚ
  b : ℚ
  mode : SegmentMode
  lower : Bool
  arm : Bool
  deriving Repr

def qBranchDerivative (lower : Bool) (z : ℚ) : ℚ :=
  g1Receipt.lo+(if lower then qLowerSlope z else qUpperSlope z)
def qSpeed (box : QRH.Coverage.Box) (arm : Bool) : ℚ :=
  if arm then 1+rowV box/(box.uHi*rowKUpper box) else 1
def segmentL (box : QRH.Coverage.Box) (B : ℚ) (s : PriceSegment) : ℚ :=
  -qBranchDerivative s.lower (rowWidth box B s.b)
def segmentA (box : QRH.Coverage.Box) (B : ℚ) (s : PriceSegment) : ℚ :=
  -qBranchDerivative s.lower (rowWidth box B s.a)

theorem qBranchDerivative_cast (lower : Bool) (z : ℚ) :
    (qBranchDerivative lower z : ℝ) = branchDerivative lower z := by
  cases lower <;> simp [qBranchDerivative,branchDerivative,betaSlope,
    qLowerSlope_cast,qUpperSlope_cast]
theorem qSpeed_cast (box : QRH.Coverage.Box) (arm : Bool) :
    (qSpeed box arm : ℝ) = speed arm (rowV box) box.uHi (rowKUpper box) := by
  cases arm <;> simp [qSpeed,speed]

def segmentCheck (box : QRH.Coverage.Box) (B : ℚ) (s : PriceSegment) : Bool :=
  decide (0 ≤ s.a ∧ s.a ≤ s.b ∧ s.b ≤ rowGamma box B) &&
  match s.mode with
  | .decreasing => decide (
      (if s.lower then rowWidth box B s.a ≤ 747/2000 else 747/2000 ≤ rowWidth box B s.b) ∧
      (if s.arm then rowGamma box B/65536+3*(1/10000000000000) ≤ s.a
        else s.b ≤ rowGamma box B/65536+3*(1/10000000000000)) ∧
      box.vLo*segmentL box B s*qSpeed box s.arm ≤ rowKUpper box/2 ∧
      1/2000000000 ≤ rowPrice box B s.b)
  | .increasing => decide (
      (if s.lower then rowWidth box B s.a ≤ 747/2000 else 747/2000 ≤ rowWidth box B s.b) ∧
      (if s.arm then rowGamma box B/65536+3*(1/10000000000000) ≤ s.a
        else s.b ≤ rowGamma box B/65536+3*(1/10000000000000)) ∧
      rowKUpper box/2 ≤ box.vLo*segmentA box B s*qSpeed box s.arm ∧
      1/2000000000 ≤ rowPrice box B s.a)
  | .enclosure => decide (1/2000000000 ≤
      min (rowPrice box B s.a) (rowPrice box B s.b)-10*(s.b-s.a))

theorem segment_branch_cast {box : QRH.Coverage.Box} {B : ℚ} {s : PriceSegment}
    (h : if s.lower then rowWidth box B s.a ≤ 747/2000 else 747/2000 ≤ rowWidth box B s.b) :
    (if s.lower then realWidth box B s.a ≤ sourceSeam else sourceSeam ≤ realWidth box B s.b) := by
  cases he : s.lower <;> simp only [he,Bool.false_eq_true,ite_false,ite_true] at h ⊢
  · have ht := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [rowWidth_real,Rat.cast_div,Rat.cast_ofNat,sourceSeam] using ht
  · have ht := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [rowWidth_real,Rat.cast_div,Rat.cast_ofNat,sourceSeam] using ht

theorem segment_arm_cast {box : QRH.Coverage.Box} {B : ℚ} {s : PriceSegment}
    (h : if s.arm then rowGamma box B/65536+3*(1/10000000000000) ≤ s.a
      else s.b ≤ rowGamma box B/65536+3*(1/10000000000000)) :
    (if s.arm then (rowGamma box B : ℝ)/65536+3*(1/10000000000000) ≤ (s.a : ℝ)
      else (s.b : ℝ) ≤ (rowGamma box B : ℝ)/65536+3*(1/10000000000000)) := by
  cases he : s.arm <;> simp only [he,Bool.false_eq_true,ite_false,ite_true] at h ⊢
  · have ht := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_add,Rat.cast_mul] using ht
  · have ht := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_add,Rat.cast_mul] using ht

theorem rowPrice_lower_cast {box : QRH.Coverage.Box} {B ξ : ℚ}
    (h : 1/2000000000 ≤ rowPrice box B ξ) :
    (1/2000000000 : ℝ) ≤ realPrice box B ξ := by
  have ht := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,rowPrice_real] using ht

/-- A checked segment pays its whole closed continuum, using either its true
polynomial derivative guard or the checked narrow stationary enclosure. -/
theorem segmentCheck_sound {box : QRH.Coverage.Box} {B : ℚ} (hc : RowContext box B)
    (s : PriceSegment) (hs : segmentCheck box B s = true) {ξ : ℝ}
    (haξ : (s.a : ℝ) ≤ ξ) (hξb : ξ ≤ (s.b : ℝ)) :
    (1/2000000000 : ℝ) ≤ realPrice box B ξ := by
  unfold segmentCheck at hs
  simp only [Bool.and_eq_true] at hs
  rcases hs with ⟨hb,hm⟩
  simp only [decide_eq_true_eq] at hb
  rcases hb with ⟨ha₀,hab,hbγ⟩
  have ha₀R : (0 : ℝ) ≤ s.a := Rat.cast_nonneg.mpr ha₀
  have habR : (s.a : ℝ) ≤ s.b := Rat.cast_le.mpr hab
  have hbγR : (s.b : ℝ) ≤ rowGamma box B := Rat.cast_le.mpr hbγ
  have hma := hc.width_mem ha₀R (habR.trans hbγR)
  have hmb := hc.width_mem (ha₀R.trans habR) hbγR
  have hk : (0 : ℝ) < rowKUpper box := by linarith [hc.hkl,hc.hko]
  have hY := hma.2.trans width_corridor.2.2.2.le
  cases he : s.mode <;> simp only [he,decide_eq_true_eq] at hm
  · rcases hm with ⟨hbranch,harm,hpaid,hvalue⟩
    have hbranchR := segment_branch_cast hbranch
    have harmR := segment_arm_cast harm
    have hL : -(segmentL box B s : ℝ) ≤ branchDerivative s.lower (realWidth box B s.b) := by
      simp only [segmentL,Rat.cast_neg,qBranchDerivative_cast,rowWidth_real,neg_neg]
      exact le_rfl
    have hpaidR : (box.vLo : ℝ)*(segmentL box B s : ℝ)*
        speed s.arm (rowV box) box.uHi (rowKUpper box) ≤ (rowKUpper box : ℝ)/2 := by
      have ht := (Rat.cast_le (K := ℝ)).mpr hpaid
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,qSpeed_cast] using ht
    have hdec := segment_decreasing (fee := (rowFee box B : ℝ))
      hc.hf₀ hc.hv hc.hd hk haξ hξb hY hbranchR harmR hL hpaidR
    exact (rowPrice_lower_cast hvalue).trans hdec
  · rcases hm with ⟨hbranch,harm,hpaid,hvalue⟩
    have hbranchR := segment_branch_cast hbranch
    have harmR := segment_arm_cast harm
    have hA : branchDerivative s.lower (realWidth box B s.a) ≤ -(segmentA box B s : ℝ) := by
      simp only [segmentA,Rat.cast_neg,qBranchDerivative_cast,rowWidth_real,neg_neg]
      exact le_rfl
    have hpaidR : (rowKUpper box : ℝ)/2 ≤ (box.vLo : ℝ)*(segmentA box B s : ℝ)*
        speed s.arm (rowV box) box.uHi (rowKUpper box) := by
      have ht := (Rat.cast_le (K := ℝ)).mpr hpaid
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,qSpeed_cast] using ht
    have hinc := segment_increasing (fee := (rowFee box B : ℝ))
      hc.hf₀ hc.hv hc.hd hk haξ hξb hY hbranchR harmR hA hpaidR
    exact (rowPrice_lower_cast hvalue).trans hinc
  · have ht := (Rat.cast_le (K := ℝ)).mpr hm
    have htR : (1/2000000000 : ℝ) ≤
        min (realPrice box B s.a) (realPrice box B s.b)-10*((s.b : ℝ)-(s.a : ℝ)) := by
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_mul,
        Rat.cast_min,rowPrice_real] using ht
    have henc := stationary_enclosure_lower (fee := (rowFee box B : ℝ))
      hc.hf₀ hc.hv hc.hd hk hc.hku haξ hξb hmb.1 hma.2
    exact htR.trans henc

def segmentsCover : ℚ → ℚ → List PriceSegment → Bool
  | _,_,[] => false
  | start,stop,[s] => decide (start = s.a ∧ stop = s.b ∧ s.a ≤ s.b)
  | start,stop,s::t::rest => decide (start = s.a ∧ s.a ≤ s.b) && segmentsCover s.b stop (t::rest)

/-- Exact endpoint adjacency of the supplied finite plan covers its whole
closed real offset interval, including every shared endpoint. -/
theorem segmentsCover_sound (ss : List PriceSegment) {start stop : ℚ}
    (hc : segmentsCover start stop ss = true) {ξ : ℝ}
    (ha : (start : ℝ) ≤ ξ) (hb : ξ ≤ (stop : ℝ)) :
    ∃ s ∈ ss, (s.a : ℝ) ≤ ξ ∧ ξ ≤ (s.b : ℝ) := by
  induction ss generalizing start with
  | nil => simp [segmentsCover] at hc
  | cons s ss ih =>
      cases ss with
      | nil =>
          simp only [segmentsCover,decide_eq_true_eq] at hc
          exact ⟨s,by simp,hc.1 ▸ ha,hc.2.1 ▸ hb⟩
      | cons t rest =>
          simp only [segmentsCover,Bool.and_eq_true,decide_eq_true_eq] at hc
          by_cases hξ : ξ ≤ (s.b : ℝ)
          · exact ⟨s,by simp,hc.1.1 ▸ ha,hξ⟩
          · obtain ⟨u,hu,hl,hr⟩ := ih hc.2 (le_of_not_ge hξ)
            exact ⟨u,List.mem_cons_of_mem s hu,hl,hr⟩

structure PricePlan where
  row : QRH.Cycle092.TopData.Row
  segments : List PriceSegment
  deriving Repr
def planCheck (p : PricePlan) : Bool :=
  rowShapeCheck p.row.box p.row.B &&
    (segmentsCover 0 (rowGamma p.row.box p.row.B) p.segments &&
      p.segments.all (segmentCheck p.row.box p.row.B))

/-- The exact finite segment certificate establishes the complete mixed price
for one authentic row and every real offset and ordinary witness length. -/
theorem planCheck_sound (p : PricePlan) (hc : planCheck p = true) {ξ z : ℝ}
    (hξ₀ : 0 ≤ ξ) (hξ₁ : ξ ≤ (rowGamma p.row.box p.row.B : ℝ))
    (hz₀ : widthLo ≤ z) (hz₁ : z ≤ widthHi) :
    (1/2000000000 : ℝ) ≤ actualWitnessPrice p.row.box p.row.B ξ z := by
  simp only [planCheck,Bool.and_eq_true] at hc
  have hrow := rowShapeCheck_sound hc.1
  obtain ⟨s,hs,hsa,hsb⟩ := segmentsCover_sound p.segments hc.2.1 (by simpa using hξ₀) hξ₁
  have hseg := List.all_eq_true.mp hc.2.2 s hs
  exact (segmentCheck_sound hrow s hseg hsa hsb).trans
    (realPrice_le_witness hrow hξ₀ hξ₁ hz₀ hz₁)

end
end QRH.Cycle092.Mixed
