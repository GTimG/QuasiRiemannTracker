/- Copyright (c) 2026 Sil, Hailey Collet, Gao and OpenAI. Apache-2.0.
Actual pinned proof bodies with their unnecessary old Bounds/PhysicalSchedule
section parameters removed. Original definitions/data and explicit analytical
inputs are retained. No old Bounds instance, new axiom or replacement estimate.

-/
import Submissions.hailey_collet_1252270103.Record1252270103Return.GenericScalar
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.SourceLedger
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.Public
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.OldGeometry

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Candidate.SilPrior.FourthPower.ReturnScalarBridge
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters]
variable [scheme : QRH.Record1252270103Return.CountScheme]
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return.GenericArithmetic
open QRH.Record12518109Count
open scoped BigOperators
open QRH.Record1252270103Return GenericArithmetic
open QRH.Record1252270103Return.GenericArithmetic QRH.Record12518109Count QRH.Record1252270103Return.GenericPhysical.Scalar
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericPhysical.PhysicalDirect QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.GenericArithmetic
open QRH.Record1252270103Return
open scoped Classical BigOperators
open QRH.Record1252270103Return.GenericArithmetic OAI OAI.SevenEighths
open QRH.Record1252270103Return.GenericArithmetic QRH.Record12518109Count
open Cycle25.Numerator
local notation "O" => HeckeFamily.O
open QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.Source
open QRH.Record1252270103Return.GenericPhysical.Scalar

/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.GenericScalar; original data types unchanged. -/
theorem numerator_packet_exponent (bs : List Branch) (kap d C delta q scalar mass count moment selection mesh slack : ℝ)
    (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    -y/2-(4/25)*ell+slack*ell+
      d*(scalar+mass+q*(ell/d)-q*(C/d)/2+
        (3*(envelope bs kap delta (q/delta)+count)+1+moment)/4+
        selection/2+delta*mesh/4-17/50) =
      numeratorExponent bs kap d C delta (q/delta)+slack*ell+
        d*(scalar+mass+(3*count+moment)/4+selection/2+delta*mesh/4) := by
  unfold numeratorExponent
  have hq : delta*(q/delta)=q := by field_simp
  rw [hq]
  field_simp
  ring

theorem weightedSourceLoss_le_uniform {d delta : ℝ} (L : LossData)
    (hd : d ≤ 1) (hdelta : 0 ≤ delta ∧ delta ≤ 3/4)
    (hscalar : 0 ≤ L.scalar) (hmass : 0 ≤ L.mass) (hcount : 0 ≤ L.count)
    (hmoment : 0 ≤ L.moment) (hselection : 0 ≤ L.selection) (hmesh : 0 ≤ L.mesh) :
    weightedSourceLoss d delta L ≤ uniformSourceLoss L := by
  have hi : 0 ≤ L.scalar+L.mass+(3*L.count+L.moment)/4+
      L.selection/2+delta*L.mesh/4 := by have := hdelta.1; positivity
  have hm := mul_le_mul_of_nonneg_right hd hi
  have hx := mul_le_mul_of_nonneg_right hdelta.2 hmesh
  unfold weightedSourceLoss uniformSourceLoss
  linarith only [hm,hx]

theorem source_packet_exponent (bs : List Branch) (kap d C delta q : ℝ) (L : LossData)
    (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    L.front+L.frequency-y/2-(4/25)*ell+L.slack*ell+
      d*(L.scalar+L.mass+q*(ell/d)-q*(C/d)/2+
        (3*(envelope bs kap delta (q/delta)+L.count)+1+L.moment)/4+
        L.selection/2+delta*L.mesh/4-17/50) =
      numeratorExponent bs kap d C delta (q/delta)+weightedSourceLoss d delta L := by
  have hh := numerator_packet_exponent bs kap d C delta q L.scalar L.mass
    L.count L.moment L.selection L.mesh L.slack hd hdelta
  unfold weightedSourceLoss
  linarith only [hh]

theorem error_main_source_scale {K : ℕ} (J : Finset (Fin K))
    (Y : Fin K→ℝ) (r : ℝ) :
    (∏j:J,(Y j.val)^r)*(∏j:{i:Fin K//i∉J},(Y j.val)^r)=∏j,(Y j)^r := by
  convert Fintype.prod_subtype_mul_prod_subtype (fun j=>j∈J) (fun j=>(Y j)^r) using 1
  congr 1
  apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl

theorem error_main_source_power {K : ℕ} (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0 < Z) (lengths : Fin K→ℝ) :
    (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) =
      Z^(-(4/25:ℝ)*(∑j,lengths j)) := by
  have hm : (∏j:{i:Fin K//i∉J},(Z^(lengths j.val))^(-(4/25:ℝ))) =
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) := by
    simp_rw [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _=>mul_comm _ _)
  have hp := error_main_source_scale J (fun j=>Z^(lengths j)) (-(4/25:ℝ))
  rw [hm] at hp
  rw [hp]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul]
  congr 1
  ring

theorem source_packet_multiplicative_identity (bs : List Branch) {K : ℕ} (J : Finset (Fin K))
    (lengths : Fin K→ℝ) (hlengths : ∑j,lengths j=ell)
    (Z kap d C delta q A : ℝ) (L : LossData)
    (hZ : 0 < Z) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    ((Z^d)^L.scalar*(Z^d)^(-(17/50:ℝ))*Z^L.frequency*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)))*
    (A*Z^L.front*((Z^d)^(y/d))^(-(1/2:ℝ))*
      (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      (Z^d)^(L.mass+q*(ell/d)-q*(C/d)/2+
        (3*(envelope bs kap delta (q/delta)+L.count)+1+L.moment)/4+
        L.selection/2+delta*L.mesh/4+L.slack*(ell/d))) =
    A*Z^(numeratorExponent bs kap d C delta (q/delta)+weightedSourceLoss d delta L) := by
  have hsplit := error_main_source_power J Z hZ lengths
  rw [hlengths] at hsplit
  let E := L.mass+q*(ell/d)-q*(C/d)/2+
    (3*(envelope bs kap delta (q/delta)+L.count)+1+L.moment)/4+
    L.selection/2+delta*L.mesh/4+L.slack*(ell/d)
  calc
    _ = A*((Z^d)^L.scalar*(Z^d)^(-(17/50:ℝ))*Z^L.frequency*
        Z^(-(4/25:ℝ)*ell)*Z^L.front*((Z^d)^(y/d))^(-(1/2:ℝ))*(Z^d)^E) := by
      rw [←hsplit]
      dsimp only [E]
      ring
    _ = A*Z^(d*L.scalar+d*(-(17/50:ℝ))+L.frequency+(-(4/25))*ell+
        L.front+(d*(y/d))*(-(1/2:ℝ))+d*E) := by
      simp_rw [←Real.rpow_mul hZ.le]
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
        ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by
      congr 2
      rw [←source_packet_exponent bs kap d C delta q L hd hdelta]
      dsimp only [E]
      field_simp
      ring

/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.SourceLedger; original data types unchanged. -/
lemma sourceMesh_le {t : ℝ} (ht : 0< t) : Cycle25.sourceMesh t ≤ t := by
  obtain ⟨_,_,ha,_,_,hm,_,hr,_,_⟩ :=
    OAI.SevenEighths.CenteredMomentEnergyWidthSchedule.bounds 2
      (OAI.SevenEighths.CenteredMomentEnergyWidthRanges.finalSourceCap 2 0 1 (t/4))
      (3/4) (t/4) (by norm_num)
      (OAI.SevenEighths.CenteredMomentEnergyWidthRanges.sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
      (by norm_num) (by positivity)
  change OAI.SevenEighths.CenteredMomentEnergyWidthSchedule.mesh 2
    (OAI.SevenEighths.CenteredMomentEnergyWidthRanges.finalSourceCap 2 0 1 (t/4)) (3/4) (t/4) ≤ t
  linarith

lemma physical_loss_bound (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (eps sigma affineError d delta : ℝ)
    (heps : 0 ≤ eps) (hsigma : 0 ≤ sigma) (haff : 0 ≤ affineError)
    (hd : d ≤ 1) (hdelta : 0 ≤ delta ∧ delta ≤ 3/4) :
    weightedSourceLoss d delta (physicalLoss D eps sigma affineError) ≤
      2*eps+3*sigma/4+affineError/4+7*D.t := by
  have hm := (Cycle25.sourceMesh_pos D.t_pos).le
  have ht := D.t_pos.le
  have hl := weightedSourceLoss_le_uniform (physicalLoss D eps sigma affineError) hd hdelta
    (by dsimp [physicalLoss];positivity) ht hsigma (by dsimp [physicalLoss];positivity)
    (by simp [physicalLoss]) (by dsimp [physicalLoss];positivity)
  have hmesh := sourceMesh_le D.t_pos
  have hell : ell ≤ (1/5:ℝ) := by linarith [Geometry.ell_pos,Geometry.ell_lt_fifth]
  have hte := mul_le_mul_of_nonneg_left hell ht
  dsimp [uniformSourceLoss,physicalLoss] at hl
  dsimp only [physicalLoss]
  linarith

/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.Public; original data types unchanged. -/
theorem rescaled_slot_mesh {n : ℕ} (lengths : Fin n → ℝ) (mesh d : ℝ)
    (hd : (1 / 200 : ℝ) ≤ d) (hmesh : 0 ≤ mesh)
    (hfine : ∀ j, lengths j ≤ mesh / 200) :
    ∀ j, lengths j / d ≤ mesh := by
  have hp : 0 < d := by linarith
  intro j
  apply (div_le_iff₀ hp).mpr
  have hm := mul_le_mul_of_nonneg_left hd hmesh
  linarith [hfine j]

theorem source_slot_power (Z d width : ℝ) (hZ : 0 < Z) (hd : d ≠ 0) :
    (Z ^ d) ^ (width / d) = Z ^ width := by
  rw [← Real.rpow_mul hZ.le, mul_div_cancel₀ width hd]

namespace OldFourth
open QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.OldFourth
/- Re-derived from pinned Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.OldGeometry; original data types unchanged. -/
lemma reflectedLength_nonneg (m t : ℝ) : 0≤ reflectedLength m t:=le_max_left _ _

lemma reflectedLength_le_of_support {m t e : ℝ} (he : 0≤ e) (ht : t≤ m+e) :
    reflectedLength m t≤1+e := by
  apply max_le <;> linarith

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

lemma box100_extent {xi : ℝ} (hx : 0< xi) :
    100≤(coefficientBoxCount100 xi:ℝ)*xi := by
  have hh:=mul_le_mul_of_nonneg_right (Nat.le_ceil (100/xi)) hx.le
  simpa only [coefficientBoxCount100,div_mul_cancel₀ _ hx.ne'] using hh

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

end OldFourth
end
end Candidate.SilPrior.FourthPower.ReturnScalarBridge
