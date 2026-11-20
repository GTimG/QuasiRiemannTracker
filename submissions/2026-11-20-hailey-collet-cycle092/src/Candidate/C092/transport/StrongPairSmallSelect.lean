/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairSmallNative
import Candidate.C092.transport.StrongPairSmallFinite

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

open QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle092.SmallCore

/-- Whole slots are selected before rows, also for a live finite subproduct. -/
theorem small_select_on {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (J : Finset Slot) (w : Slot→ℝ) (mesh q : ℝ)
    (hw : ∀ i,0  ≤  w i) (hwm : ∀ i,w i  ≤  mesh) (hm : 0  ≤  mesh) (hq : 0  ≤  q) :
    ∃ T ⊆ J,(∑ i∈T,w i)  ≤  q ∧
      (∑ i∈J\T,w i)  ≤  max 0 ((∑ i∈J,w i)-q+mesh) := by
  let w' : Slot→ℝ:=fun i=>if i∈J then w i else 0
  have hw' : ∀ i,0  ≤  w' i:=by intro i; dsimp [w']; split_ifs <;> simp_all
  have hm' : ∀ i,w' i  ≤  mesh:=by intro i; dsimp [w']; split_ifs <;> simp_all
  obtain ⟨F,hF,hR,_⟩:=select_before_rows w' mesh q hw' hm' hm hq
  have hsum : (∑ i,w' i)=(∑ i∈J,w i):=by
    simp only [w',←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  refine ⟨F∩J,Finset.inter_subset_right,?_,?_⟩
  · have he : (∑ i∈F,w' i)=(∑ i∈F∩J,w i):=by
      simp only [w',←Finset.sum_filter,Finset.filter_mem_eq_inter]
    simpa only [he] using hF
  · have he : (∑ i∈Finset.univ\F,w' i)=(∑ i∈J\(F∩J),w i):=by
      rw [show J\(F∩J)=(Finset.univ\F)∩J by ext i; simp; tauto]
      simp only [w',←Finset.sum_filter,Finset.filter_mem_eq_inter]
    simpa only [he,hsum] using hR

theorem small_quota_margin {n y V : ℝ}
    (hy1 : y  ≤  sourceY) (hn1 : n  ≤  sourceRatio*y) (hV0 : radiusMin  ≤  V) :
    (1/50:ℝ)  ≤  SmallCore.quota n y V := by
  have hnc:=hn1.trans (mul_le_mul_of_nonneg_left hy1 (by norm_num [sourceRatio]))
  norm_num [SmallCore.quota,sourceRatio,sourceY,radiusMin] at *
  linarith

/-- The original scalar payment still has room for two slot roundings,
the unmarked boundary fourth, and one fixed buffer fee. -/
theorem small_high_paid {n y V e L rounding buffer : ℝ} {k : ℕ}
    (hy0 : sourceY0  ≤  y) (hy1 : y  ≤  sourceY)
    (hV0 : radiusMin  ≤  V) (hV1 : V  ≤  98/100)
    (he0 : 0  ≤  e) (he1 : e  ≤  1)
    (hL : L  ≤  sourceWidth n y-(u:ℝ)) (hr : rounding  ≤  1/100000)
    (hb : buffer*(k:ℝ)  ≤  1/10000) :
    V+1/10000+buffer*(k:ℝ)+e*max 0 (L-SmallCore.quota n y V+rounding)  ≤ 
      V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V) := by
  have hg:=sourceGain_antitone hy0 hy1
  have hg0 : sourceGain sourceY0  ≤  (3/1000:ℝ):=by
    norm_num [sourceGain,sourceY0,sourceSeam,lowerGain,QRH.Cycle090.upperGain,sourceY]
  have hleft : L-SmallCore.quota n y V+rounding  ≤  (1-V)/2+401/100000 := by
    dsimp [SmallCore.quota,sourceWidth] at *
    norm_num [u] at hL
    linarith
  have hnonneg : 0  ≤  (1-V)/2+401/100000:=by linarith
  have hmax:=max_le hnonneg hleft
  have he:=mul_le_mul he1 hmax (le_max_left _ _) (by norm_num : (0:ℝ)  ≤  1)
  have hH : 0  ≤  (H:ℝ)-V:=by norm_num [H,u] at *; linarith
  rw [max_eq_right hH]
  norm_num [u,rho,H] at *
  linarith

#print axioms small_select_on
#print axioms small_high_paid
end
end QRH.Cycle092.StrongPair
