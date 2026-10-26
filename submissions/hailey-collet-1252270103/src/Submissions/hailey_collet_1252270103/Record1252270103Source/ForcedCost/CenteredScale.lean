/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The centered scale uses ordinary factor norms. Deleted marked scales remain
in rawReduction; their nonnegative exponents make that deletion contractive. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.ForcedCost.ChildControl
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredChild
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ForcedCost
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentAllocatedDetectorAmplitude
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq ι := Classical.decEq _

def ordinaryNorm (B : Tuple ι) : ℝ :=
  Ideal.absNorm (B (Sum.inr 0)*B (Sum.inr 1))

omit [Fintype ι] in
lemma ordinaryNorm_eq_plainNorm (B : Tuple ι) : ordinaryNorm B=plainNorm B := by
  simp only [ordinaryNorm,plainNorm,map_mul,Nat.cast_mul]

lemma alloc_norm_ge_one (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C)
    (j : ι⊕Fin 2) : (1:ℝ)≤Ideal.absNorm (B.val j) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))

lemma ordinaryNorm_ge_one (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) :
    1≤ordinaryNorm B.val := by
  rw [ordinaryNorm_eq_plainNorm,plainNorm]
  nlinarith [alloc_norm_ge_one s C B (Sum.inr 0),alloc_norm_ge_one s C B (Sum.inr 1)]

theorem child_raw_lower_bound (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t L₀ : ℝ) (hL₀ : 0<L₀)
    (hX₁ : L₀≤s.X₁) (hX₂ : L₀≤s.X₂) (hY₁ : L₀≤s.Y₁) (hY₂ : L₀≤s.Y₂) :
    L₀/ordinaryNorm B.val≤(child s C R B τ t).X₁ ∧
    L₀/ordinaryNorm B.val≤(child s C R B τ t).X₂ ∧
    L₀/ordinaryNorm B.val≤(child s C R B τ t).Y₁ ∧
    L₀/ordinaryNorm B.val≤(child s C R B τ t).Y₂ := by
  have hn₁:=alloc_norm_ge_one s C B (Sum.inr 0)
  have hn₂:=alloc_norm_ge_one s C B (Sum.inr 1)
  have hd₁ : (Ideal.absNorm (B.val (Sum.inr 0)):ℝ)≤ordinaryNorm B.val := by
    rw [ordinaryNorm_eq_plainNorm,plainNorm];nlinarith
  have hd₂ : (Ideal.absNorm (B.val (Sum.inr 1)):ℝ)≤ordinaryNorm B.val := by
    rw [ordinaryNorm_eq_plainNorm,plainNorm];nlinarith
  have hl := div_le_div_of_nonneg_left hL₀.le (alloc_norm_pos s C B (Sum.inr 0)) hd₁
  have hr := div_le_div_of_nonneg_left hL₀.le (alloc_norm_pos s C B (Sum.inr 1)) hd₂
  exact ⟨hl.trans (div_le_div_of_nonneg_right hX₁ (alloc_norm_pos s C B _).le),
    hr.trans (div_le_div_of_nonneg_right hX₂ (alloc_norm_pos s C B _).le),
    hl.trans (div_le_div_of_nonneg_right hY₁ (alloc_norm_pos s C B _).le),
    hr.trans (div_le_div_of_nonneg_right hY₂ (alloc_norm_pos s C B _).le)⟩

theorem child_volume_ordinary_bound (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hP : ∀i,1≤s.P i) :
    volume (child s C R B τ t)≤volume s/ordinaryNorm B.val := by
  have hf : 1≤∏i,frozenScale B.val s.P i := by
    apply Finset.one_le_prod₀
    intro i hi
    dsimp [frozenScale]
    split_ifs
    · exact le_rfl
    · exact hP i
  have hraw : ordinaryNorm B.val≤rawReduction B.val s.P := by
    rw [ordinaryNorm_eq_plainNorm,rawReduction]
    nlinarith [plainNorm_pos B.val (alloc_ne s C B)]
  have he : volume (child s C R B τ t)*rawReduction B.val s.P=volume s := by
    rw [Record1252270103Second.child_volume_remaining]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  apply (le_div_iff₀ (zero_lt_one.trans_le (ordinaryNorm_ge_one s C B))).mpr
  exact (mul_le_mul_of_nonneg_left hraw (volume_pos (child s C R B τ t)).le).trans_eq he

lemma centered_division (V d L₀ α : ℝ) (hV : 0≤V) (hd : 1≤d)
    (hα : 0≤α) (hαhi : α≤1/2) :
    (V/d)*(max 1 (L₀/d))^(-(2*α))≤V*(max 1 L₀)^(-(2*α)) := by
  have hd0 : 0<d := zero_lt_one.trans_le hd
  have hm : 0<max 1 (L₀/d) := zero_lt_one.trans_le (le_max_left _ _)
  have hM : 0<max 1 L₀ := zero_lt_one.trans_le (le_max_left _ _)
  have hbase : max 1 L₀≤d*max 1 (L₀/d) := by
    apply max_le
    · nlinarith [le_max_left (1:ℝ) (L₀/d)]
    · have h:=mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) (L₀/d)) hd0.le
      have he : d*(L₀/d)=L₀ := by field_simp [hd0.ne']
      simpa only [he] using h
  have hdp : d^(2*α)≤d := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd (show 2*α≤1 by linarith)
  have hpow : (max 1 L₀)^(2*α)≤d*(max 1 (L₀/d))^(2*α) := by
    apply (Real.rpow_le_rpow hM.le hbase (by positivity)).trans
    rw [Real.mul_rpow hd0.le hm.le]
    exact mul_le_mul_of_nonneg_right hdp (Real.rpow_nonneg hm.le _)
  rw [Real.rpow_neg hm.le,Real.rpow_neg hM.le]
  calc
    _=V/(d*(max 1 (L₀/d))^(2*α)) := by ring
    _≤V/(max 1 L₀)^(2*α) := div_le_div_of_nonneg_left hV (Real.rpow_pos_of_pos hM _) hpow
    _=_ := by rw [div_eq_mul_inv]

theorem child_centered_scale (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t L₀ α : ℝ)
    (hP : ∀i,1≤s.P i) (hα : 0≤α) (hαhi : α<1/2) :
    volume (child s C R B τ t)*(max 1 (L₀/ordinaryNorm B.val))^(-(2*α))≤
      volume s*(max 1 L₀)^(-(2*α)) := by
  apply (mul_le_mul_of_nonneg_right (child_volume_ordinary_bound s C R B τ t hP)
    (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)).trans
  exact centered_division (volume s) (ordinaryNorm B.val) L₀ α
    (volume_pos s).le (ordinaryNorm_ge_one s C B) hα hαhi.le

theorem child_control_centered_scale (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t L₀ α : ℝ)
    (hP : ∀i,1≤s.P i) (hα : 0≤α) (hαhi : α<1/2) :
    slotControl (child s C R B τ t).toData*volume (child s C R B τ t)*
      (max 1 (L₀/ordinaryNorm B.val))^(-(2*α))≤
    slotControl s.toData*volume s*(max 1 L₀)^(-(2*α)) := by
  rw [mul_assoc,mul_assoc]
  exact mul_le_mul (child_slotControl s C R B τ t)
    (child_centered_scale s C R B τ t L₀ α hP hα hαhi)
    (mul_nonneg (volume_pos (child s C R B τ t)).le
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
    (slotControl_nonneg s.toData)
end
end QRH.Record1252270103Source.ForcedCost
#print axioms QRH.Record1252270103Source.ForcedCost.child_raw_lower_bound
#print axioms QRH.Record1252270103Source.ForcedCost.child_volume_ordinary_bound
#print axioms QRH.Record1252270103Source.ForcedCost.child_centered_scale

#print axioms QRH.Record1252270103Source.ForcedCost.child_control_centered_scale
