/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-9.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.OldGeometry (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Actual old-band physical reconstruction on new geometry, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Schedule
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.Damping
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.BoxGeometry
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect.OldFourth
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic OAI OAI.SevenEighths
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic QRH.Record12518109Count
open Cycle25.Numerator

def originalBaseCapacity (κ m : ℝ) : ℝ := (2*min m 1-1)/(6*κ)
def reflectedLength (m t : ℝ) : ℝ := max 0 (1-m+t)
lemma reflectedLength_nonneg (m t : ℝ) : 0≤ reflectedLength m t:=le_max_left _ _
lemma reflectedLength_le_of_support {m t e : ℝ} (he : 0≤ e) (ht : t≤ m+e) :
    reflectedLength m t≤1+e := by
  apply max_le <;> linarith

/-- Capacity in row-base units, including the original length cap at one. -/
def baseCapacity (κ d : ℝ) : ℝ := min 1 (2*y/d-1)/(6*κ)
def capOld (κ d t : ℝ) : ℝ := max 0 ((min 1 (2*y/d-1)-2*t)/(6*κ))
def coefficientBoxCount100 (xi : ℝ) : ℕ := ⌈100/xi⌉₊

lemma capped_plain_identity (m : ℝ) : min 1 (2*m-1)=2*min m 1-1 := by
  by_cases hm:m≤1
  · rw [min_eq_left hm,min_eq_right (by linarith : 2*m-1≤1)]
  · rw [min_eq_right (le_of_not_ge hm),min_eq_left (by linarith : 1≤2*m-1)]
    ring

lemma capOld_eq_selected {κ d t : ℝ} (hk : κ≠0) :
    capOld κ d t=selectedCapacity κ (originalBaseCapacity κ (y/d)) t := by
  unfold capOld selectedCapacity originalBaseCapacity
  rw [mul_div_assoc,capped_plain_identity]
  congr 1
  field_simp
  ring

lemma base_scaled {κ d : ℝ} (hd : 0< d) :
    d*baseCapacity κ d=GenericArithmetic.oldCapacityAt κ d := by
  unfold baseCapacity GenericArithmetic.oldCapacityAt
  rw [←mul_div_assoc,mul_min_of_nonneg _ _ hd.le]
  have he:d*(2*y/d-1)=2*y-d:=by
    field_simp [hd.ne']
  rw [mul_one,he]

lemma capOld_nonneg (κ d t : ℝ) : 0≤ capOld κ d t:=le_max_left _ _

lemma physical_y_range {d : ℝ} (hd : d0≤ d ∧ d≤ dm) : 1/2< y/d ∧ y/d≤99 := by
  have hp:0< d:=(show (0:ℝ)<d0 by norm_num [d0]).trans_le hd.1
  constructor
  · apply (lt_div_iff₀ hp).mpr
    linarith [PhysicalSchedule.switch_before_twoy,hd.2]
  · apply (div_le_iff₀ hp).mpr
    have hdmin : (1/200:ℝ)≤d := hd.1
    linarith [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN.ly_coarse.2]

lemma box100_extent {xi : ℝ} (hx : 0< xi) :
    100≤(coefficientBoxCount100 xi:ℝ)*xi := by
  have hh:=mul_le_mul_of_nonneg_right (Nat.le_ceil (100/xi)) hx.le
  simpa only [coefficientBoxCount100,div_mul_cancel₀ _ hx.ne'] using hh

/-- Genuine clipped reflected shortening, including original scales above U. -/
lemma reflected_capacity_or_empty {α : Type*} (T : Finset α) (width : T→ℝ)
    {κ d t slack : ℝ} (hk : 0< κ) (ht : 0≤ t) (hw : ∀i,0< width i)
    (hs : (∑i,width i)≤ capOld κ d (t+slack)) :
    2*(reflectedLength (y/d) t+slack)+6*κ*(∑i,width i)≤1 ∨ T=∅ := by
  let raw:=originalBaseCapacity κ (y/d)-(t+slack)/(3*κ)
  have hsel:(∑i,width i)≤ selectedCapacity κ (originalBaseCapacity κ (y/d)) (t+slack):=by
    simpa only [capOld_eq_selected hk.ne'] using hs
  by_cases hr:0≤ raw
  · left
    have he:selectedCapacity κ (originalBaseCapacity κ (y/d)) (t+slack)=raw:=max_eq_right hr
    rw [he] at hsel
    have hmul:=mul_le_mul_of_nonneg_left hsel (show 0≤6*κ by positivity)
    have hid:6*κ*raw=2*min (y/d) 1-1-2*(t+slack):=by
      dsimp [raw,originalBaseCapacity]
      field_simp
      ring
    rw [hid] at hmul
    by_cases hp:0≤1-y/d+t
    · rw [reflectedLength,max_eq_right hp]
      linarith [min_le_left (y/d) (1:ℝ)]
    · rw [reflectedLength,max_eq_left (le_of_not_ge hp)]
      linarith [min_le_right (y/d) (1:ℝ)]
  · right
    have he:selectedCapacity κ (originalBaseCapacity κ (y/d)) (t+slack)=0:=max_eq_left (le_of_not_ge hr)
    rw [he] at hsel
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hh:width ⟨i,hi⟩≤∑i,width i:=Finset.single_le_sum
      (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
    linarith [hw ⟨i,hi⟩]

/-- Strong physical coefficient damping pays the exact clipped capacity loss. -/
lemma capacity_damping {κ d t q delta : ℝ} (hk : 7/10≤ κ)
    (ht : 0≤ t) (hq : 0≤ q) (hqd : q≤ delta/2) :
    q*baseCapacity κ d/2+delta*t/4≤ delta*t/2+q*capOld κ d t/2 := by
  have hk0:0< κ:=by linarith
  have hd:0≤ delta:=by linarith
  have hc:baseCapacity κ d-capOld κ d t≤ t/(3*κ):=by
    have hm:=le_max_right 0 ((min 1 (2*y/d-1)-2*t)/(6*κ))
    change (min 1 (2*y/d-1)/(6*κ))-max 0 ((min 1 (2*y/d-1)-2*t)/(6*κ))≤ t/(3*κ)
    have he:(min 1 (2*y/d-1)-2*t)/(6*κ)=min 1 (2*y/d-1)/(6*κ)-t/(3*κ):=by field_simp;ring
    rw [he] at hm ⊢
    linarith
  have hpay:t/(3*κ)≤(2/3)*t:=by
    apply (div_le_iff₀ (show 0<3*κ by positivity)).mpr
    nlinarith
  have hmul:=mul_le_mul_of_nonneg_left (hc.trans hpay) hq
  have hqd':=mul_le_mul_of_nonneg_right hqd ht
  nlinarith

end Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect.OldFourth

namespace Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect.OldFourth
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic OAI OAI.SevenEighths
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic QRH.Record12518109Count

lemma capOld_le_supply {κ d t : ℝ} (hk : 7/10≤ κ)
    (hd : d0≤ d ∧ d≤ dm) (ht : 0≤ t) : capOld κ d t≤ ell/d := by
  have hdp:0< d:=(show (0:ℝ)<d0 by norm_num [d0]).trans_le hd.1
  have hkp:0< κ:=by linarith
  have hy:=physical_y_range hd
  have hbase:0≤ baseCapacity κ d:=by
    unfold baseCapacity
    apply div_nonneg
    · rw [mul_div_assoc]
      apply le_min <;> linarith
    · positivity
  have hcap:capOld κ d t≤ baseCapacity κ d:=by
    unfold capOld baseCapacity
    apply max_le hbase
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hmin:min d (2*y-d)≤ y:=by
    by_cases h:d≤ y
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  have htotal:GenericArithmetic.oldCapacityAt κ d≤ ell:=by
    unfold GenericArithmetic.oldCapacityAt
    apply (div_le_iff₀ (show 0<6*κ by positivity)).mpr
    have hyell:y≤ ell*(6*κ):=by
      have he := Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN.ell_interval.1
      have hyhi := Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN.ly_coarse.2
      have hm := mul_le_mul_of_nonneg_left (show 6*(7/10:ℝ)≤6*κ by linarith [hk]) Geometry.ell_pos.le
      linarith
    exact hmin.trans hyell
  have hscaled:=base_scaled (κ:=κ) hdp
  apply hcap.trans
  apply (le_div_iff₀ hdp).mpr
  rw [mul_comm, hscaled]
  exact htotal

end Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect.OldFourth
