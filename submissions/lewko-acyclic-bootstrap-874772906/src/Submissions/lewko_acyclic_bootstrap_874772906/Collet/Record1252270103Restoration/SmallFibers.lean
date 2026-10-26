/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.CompletedEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily Record1252270103KernelMass
local notation "O" => HeckeFamily.O

def smallPair (n : IdealPair) : IdealPair := (smallFactor smallPrimes n.1,smallFactor smallPrimes n.2)
def residualPair (n : IdealPair) : IdealPair := (residualFactor smallPrimes n.1,residualFactor smallPrimes n.2)
def smallExpanded (D : Finset IdealPair) : Finset (IdealPair×IdealPair) :=
  D.image (fun n=>(smallPair n,residualPair n))
def smallPool (D : Finset IdealPair) : Finset IdealPair := D.image smallPair
def smallResidualPool (D : Finset IdealPair) (d : IdealPair) : Finset IdealPair :=
  ((smallExpanded D).filter (fun p=>p.1=d)).image Prod.snd

theorem small_reconstruct {n : IdealPair} (hn : n.1≠0 ∧ n.2≠0) :
    multiplyPair (smallPair n) (residualPair n)=n := by
  exact Prod.ext (split_identity smallPrimes hn.1) (split_identity smallPrimes hn.2)

theorem smallPool_nonzero {D : Finset IdealPair} {d : IdealPair} (hd : d∈smallPool D) : d.1≠0 ∧ d.2≠0 := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hd
  exact ⟨decode_ne_zero _ _,decode_ne_zero _ _⟩

theorem smallPool_support {D : Finset IdealPair} {d : IdealPair} (hd : d∈smallPool D) :
    pairSupport d.1 d.2 ⊆ primeValues smallPrimes := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hd
  exact Finset.union_subset (smallFactor_support _ _) (smallFactor_support _ _)

theorem smallFactor_mul_good {d a : Ideal O} (hd : d≠0) (ha : a≠0)
    (hs : primeSupport d⊆primeValues smallPrimes)
    (hz : ∀P∈smallPrimes,valuation a P.val=0) : smallFactor smallPrimes (d*a)=d := by
  unfold smallFactor
  calc
    _ = decode smallPrimes (fun P=>valuation d P.val.val) := by
      congr 1
      funext P
      rw [valuation_mul hd ha,hz P.val P.property,add_zero]
    _ = d := decode_encode smallPrimes hd hs

theorem smallPair_multiply {D : Finset IdealPair} {d a : IdealPair}
    (hd : d∈smallPool D) (ha : GoodPair a) : smallPair (multiplyPair d a)=d := by
  have hdn := smallPool_nonzero hd
  have hds := smallPool_support hd
  have hah := (ordinarySmallHole_iff_good ha.1 ha.2.1).mpr ha
  exact Prod.ext
    (smallFactor_mul_good hdn.1 ha.1 (Finset.Subset.trans Finset.subset_union_left hds) (fun P hP=>(hah P hP).1))
    (smallFactor_mul_good hdn.2 ha.2.1 (Finset.Subset.trans Finset.subset_union_right hds) (fun P hP=>(hah P hP).2))

theorem residualPair_multiply {D : Finset IdealPair} {d a : IdealPair}
    (hd : d∈smallPool D) (ha : GoodPair a) : residualPair (multiplyPair d a)=a := by
  have hdn := smallPool_nonzero hd
  have h := small_reconstruct (show (multiplyPair d a).1≠0 ∧ (multiplyPair d a).2≠0 from
    ⟨mul_ne_zero hdn.1 ha.1,mul_ne_zero hdn.2 ha.2.1⟩)
  rw [smallPair_multiply hd ha] at h
  exact Prod.ext (mul_left_cancel₀ hdn.1 (congrArg Prod.fst h))
    (mul_left_cancel₀ hdn.2 (congrArg Prod.snd h))

theorem smallResidualPool_eq_hole {b X₁ X₂ : ℝ} {d : IdealPair}
    (hd : d∈smallPool (plainPairPool b X₁ X₂)) :
    smallResidualPool (plainPairPool b X₁ X₂) d =
      holePairPool b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  ext a
  constructor
  · intro ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hp,heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp
    have hnz := plainPairPool_nonzero hn
    have hg := residual_good hnz.1 hnz.2
    have hh := small_reconstruct hnz
    change multiplyPair (smallPair n) (residualPair n)=n at hh
    change smallPair n=d at heq
    rw [heq] at hh
    apply Finset.mem_filter.mpr
    exact ⟨(plainPairPool_multiply_iff (smallPool_nonzero hd)).mp (hh.symm ▸ hn),
      (ordinarySmallHole_iff_good hg.1 hg.2.1).mpr hg⟩
  · intro ha
    have hag := holePairPool_good ha
    have hn := (plainPairPool_multiply_iff (smallPool_nonzero hd)).mpr (Finset.mem_filter.mp ha).1
    apply Finset.mem_image.mpr
    refine ⟨(d,a),Finset.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨multiplyPair d a,hn,?_⟩
    rw [smallPair_multiply hd hag,residualPair_multiply hd hag]

theorem small_sum_reindex (D : Finset IdealPair) (hnz : ∀n∈D,n.1≠0 ∧ n.2≠0)
    (F : IdealPair→ℂ) :
    (∑n∈D,F n) = ∑p∈smallExpanded D,F (multiplyPair p.1 p.2) := by
  rw [smallExpanded,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [small_reconstruct (hnz n hn)]
  · intro n hn m hm he
    have h := congrArg (fun p : IdealPair×IdealPair=>multiplyPair p.1 p.2) he
    simpa only [small_reconstruct (hnz n hn),small_reconstruct (hnz m hm)] using h

theorem smallExpanded_grouped (D : Finset IdealPair) (F : IdealPair→IdealPair→ℂ) :
    (∑p∈smallExpanded D,F p.1 p.2)=∑d∈smallPool D,∑a∈smallResidualPool D d,F d a := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=smallExpanded D) (t:=smallPool D) (g:=Prod.fst)
    (by intro p hp;obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hp;exact Finset.mem_image.mpr ⟨n,hn,rfl⟩)
    (fun p=>F p.1 p.2)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [smallResidualPool,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  · intro p hp q hq he
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.smallResidualPool_eq_hole
