/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceWidthDensity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Graph.GraphContract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103StepScalar
noncomputable section
open Record1252270103Finite QRH.Record1252270103Graph

theorem inherit_below_crossing (n low : Source)
    (hL : n.L < low.L) (hcap : crossing n low ≤ low.cap)
    (hlow : ParentGood low) {s m₁ m₂ : ℝ}
    (hs : s ∈ Set.Icc 0 (crossing n low : ℝ))
    (hm₁ : 0≤m₁) (hm₂ : 0≤m₂)
    (hbudget : m₁+m₂+(n.L:ℝ)*s≤(n.B:ℝ)) :
    (Record1252270103Source.globalFace (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ)).Admissible m₁ m₂ s 1 := by
  have hd : 0<(low.L:ℝ)-(n.L:ℝ) := by exact_mod_cast sub_pos.mpr hL
  have hc : (crossing n low:ℝ)=((low.B:ℝ)-(n.B:ℝ))/((low.L:ℝ)-(n.L:ℝ)) := by simp [crossing]
  have hx : ((low.L:ℝ)-(n.L:ℝ))*s≤(low.B:ℝ)-(n.B:ℝ) := by
    have := (le_div_iff₀ hd).mp (hc ▸ hs.2)
    nlinarith
  apply (Record1252270103Source.globalFace_admissible_iff hm₁ hm₂ hs.1
    (show 0≤(low.L:ℝ) by exact_mod_cast (le_of_lt (lt_trans (by norm_num) hlow.2.2.1)))).mpr
  constructor
  · simpa using hs.2.trans (show (crossing n low:ℝ)≤(low.cap:ℝ) by exact_mod_cast hcap)
  · nlinarith

structure RealGeometry (K : ℚ) (n low : Source) (b : ℝ) : Prop where
  lowL_pos : 0<(low.L:ℝ)
  denominator_pos : 0<(sourceDen n low:ℝ)
  width_room : 2*(n.allowance:ℝ)<b
  a_pos : 0<sourceAReal n low b
  a_small : sourceAReal n low b<1/75
  raw_factor_room : (sourceTReal n b+b)/2+4*(n.allowance:ℝ)<sourceFReal n low b
  parent_budget_room : sourceTReal n b+b+4*(n.allowance:ℝ)<(low.B:ℝ)*sourceFReal n low b
  qcap_room : (n.q:ℝ)*(low.cap:ℝ)<1
  low_fee_room : ((n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ)+(n.q:ℝ)*(low.cap:ℝ)+4)*(n.allowance:ℝ)+10*(n.allowance:ℝ)<(n.lowFee:ℝ)
  a_allowance : 20*(n.allowance:ℝ)<sourceAReal n low b
  reference_pos : 0<49/100-(K:ℝ)*b
  reference_gap : 1/2+(K:ℝ)*b+10*(n.allowance:ℝ)<1-(49/100-(K:ℝ)*b)
  centered_499 : sourceTReal n b+b+9*sourceAReal n low b+(n.highFee:ℝ)<5/6+(499/1000)*(49/100-(K:ℝ)*b)
  first_tail : sourceTReal n b+b+5*sourceAReal n low b+(n.highFee:ℝ)<1
  second_tail : sourceTReal n b+b+4*sourceAReal n low b+(n.highFee:ℝ)<1-1/50
  mixed_tail : sourceTReal n b+b+(9/2)*sourceAReal n low b+(n.highFee:ℝ)<1-1/50
  reference_tail : 7*sourceAReal n low b+(n.highFee:ℝ)<49/100-(K:ℝ)*b
  weak_cap : ((low.B:ℝ)*sourceFReal n low b-sourceTReal n b)/(low.L:ℝ)≤(low.cap:ℝ)*sourceFReal n low b
  fee_identity : sourceAReal n low b-(n.q:ℝ)*(b+(sourceTReal n b-(low.B:ℝ)*sourceFReal n low b)/(low.L:ℝ))=(n.lowFee:ℝ)

lemma fee_identity (n low : Source) (b : ℝ) (hL : (low.L:ℝ)≠0)
    (hD : (sourceDen n low:ℝ)≠0) :
    sourceAReal n low b-(n.q:ℝ)*(b+(sourceTReal n b-(low.B:ℝ)*sourceFReal n low b)/(low.L:ℝ))=(n.lowFee:ℝ) := by
  have hd : (sourceDen n low:ℝ)=1-6*(n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ) := by simp [sourceDen]
  have ha : sourceAReal n low b*(sourceDen n low:ℝ)=
      (n.q:ℝ)*(b+(sourceTReal n b-(low.B:ℝ))/(low.L:ℝ))+(n.lowFee:ℝ) := by
    exact div_mul_cancel₀ _ hD
  rw [hd] at ha
  dsimp only [sourceFReal]
  field_simp at ha ⊢
  nlinarith [ha]

lemma real_geometry_of_gates (K : ℚ) (n low : Source) (b : ℝ)
    (hlow : ParentGood low) (hg : ∀j,0<sourceScalarReal K n low b j)
    (hw : 0≤sourceWeakReal n low b) : RealGeometry K n low b := by
  have hL : 0<(low.L:ℝ) := by exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<1) hlow.2.2.1)
  have g0:=hg 0;have g1:=hg 1;have g2:=hg 2;have g3:=hg 3
  have g4:=hg 4;have g5:=hg 5;have g6:=hg 6;have g7:=hg 7
  have g8:=hg 8;have g9:=hg 9;have g10:=hg 10;have g11:=hg 11
  have g12:=hg 12;have g13:=hg 13;have g14:=hg 14;have g15:=hg 15
  norm_num [sourceScalarReal] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
  have g0r : 0<(sourceDen n low:ℝ) := by exact_mod_cast g0
  refine ⟨hL,g0r,by linarith,g2,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,?_,fee_identity n low b (ne_of_gt hL) (ne_of_gt g0r)⟩
  dsimp [sourceWeakReal] at hw
  linarith

theorem nf_real_geometry (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (hlow : ParentGood low) {b : ℝ}
    (hb : b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    RealGeometry (11243277/2500000) n low b := by
  have hν : (n.q:ℝ)∈Set.Icc (n.q:ℝ) (3/4) := ⟨le_rfl,by
    have h : (n.q:ℝ)≤((3/4:ℚ):ℝ) := Rat.cast_le.mpr hv.2.2.2.2.2.2.1
    norm_num at h ⊢
    exact h⟩
  obtain ⟨hg,hw,_⟩:=source_full_width_gates n low high hv hb hν
  exact real_geometry_of_gates _ _ _ _ hlow hg hw

theorem seed_real_geometry (n low : Source) (hv : SeedSourceValid n low)
    (hlow : ParentGood low) {b : ℝ}
    (hb : b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    RealGeometry (112445673/25000000) n low b := by
  have hν : (n.q:ℝ)∈Set.Icc (n.q:ℝ) (3/4) := ⟨le_rfl,by
    have h : (n.q:ℝ)≤((3/4:ℚ):ℝ) := Rat.cast_le.mpr hv.2.2.2.2.2.2.1.le
    norm_num at h ⊢
    exact h⟩
  obtain ⟨hg,hw,_⟩:=seed_full_width_gates n low hv hb hν
  exact real_geometry_of_gates _ _ _ _ hlow hg hw
end
end QRH.Record1252270103StepScalar
#print axioms QRH.Record1252270103StepScalar.inherit_below_crossing
#print axioms QRH.Record1252270103StepScalar.nf_real_geometry
#print axioms QRH.Record1252270103StepScalar.seed_real_geometry
