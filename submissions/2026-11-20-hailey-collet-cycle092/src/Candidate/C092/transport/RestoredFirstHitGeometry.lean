/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Physical H.18 inputs for a genuine collision/inverse-restored canonical
source and its actual selected first allocation, including subunit scales. -/
import Candidate.C092.transport.FirstRootInverseGeometry
import Candidate.C092.transport.OrderedPairActualRestoredGeometry
import Candidate.C092.transport.RawSidesZeroTailGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CenteredMomentEnergyBands
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass Candidate.FourthPower
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations
open MixedPrincipalWindow MixedInnerExceptionalBlock MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.NativeStrip QRH.Cycle090
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAddedZeroUniform
namespace QRH.Cycle092.FixedFramePacking
local notation "O" => HeckeFamily.O
local notation "Id"=>Ideal HeckeFamily.O
variable {ι:Type} [Fintype ι]
local instance (priority := 2000) c092LocalInst_Candidate_C092_transport_RestoredFirstHitGeometry_c0c18e7db3e48dad_001 {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _

theorem exact_restored_ledger (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M ≤ Hr) (r:QRH.SilDensitySplit.CubeFree.FP.RestoredRootSource.Data M Hr ι)
    (X₁ X₂ Y₁ Y₂ t₁ t₂ n y l:ℝ) (d:IdealPair)
    (hd₁:d.1≠0) (hd₂:d.2≠0) (g:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d)
    (hx₁:length r.Z X₁ ≤ n) (hx₂:length r.Z X₂ ≤ y)
    (hy0:sourceY0 ≤ y) (hy1:y ≤ sourceY) (hn:n ≤ sourceRatio*y)
    (hws:(∑i,r.w i) ≤ l) (hl:l ≤ sourceWidth n y)
    (hshort:∀ X∈({X₁,X₂,Y₁,Y₂}:Finset ℝ),r.Z^(115/1000:ℝ) ≤ X) :
    let s:=dividedCanonicalSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g
    ∀ (cover:OriginalEnclosure s) (G:Id) (hG:G≠0) (B:actualAllocations (tuplePools s) G)
      (J:Finset (liveIndices B.val)),
    let u':=∑j∈J,r.w j.val
    let child:=renorm (restOf s (by norm_num) cover G B J)
    let c:=Real.logb r.Z (((d.1.absNorm:ℝ)*d.2.absNorm)*(G.absNorm:ℝ))
    Real.logb r.Z (sourceVolume child)  ≤  9179599/10000000-c-u'+Real.logb r.Z ((2:ℝ)^Fintype.card ι) ∧
    max 0 (115/1000-c)  ≤  Real.logb r.Z (max 1 child.L) := by
  intro s cover G hG B J u' child c
  have hZ:=r.hZ
  have h0:=zero_lt_one.trans hZ
  have q0:=Real.rpow_pos_of_pos h0 (115/1000:ℝ)
  have h1:=hshort X₁ (by simp)
  have h2:=hshort X₂ (by simp)
  have h3:=hshort Y₁ (by simp)
  have h4:=hshort Y₂ (by simp)
  have hx:=q0.trans_le h1
  have hy:=q0.trans_le h2
  have hb:Box n y (sourceWidth n y) (length r.Z X₁) (length r.Z X₂) (∑i,r.w i) :=
    ⟨Real.logb_nonneg hZ (le_max_left _ _),Real.logb_nonneg hZ (le_max_left _ _),
    Or.inl ⟨hx₁,hx₂⟩,Finset.sum_nonneg (fun i _=>r.hw i),hws.trans hl⟩
  have hparent:=MeasuredBall.support_cap hZ hx hy hy0 hy1 hn hb
  have d1:0<(d.1.absNorm:ℝ):=nrm_pos hd₁
  have d2:0<(d.2.absNorm:ℝ):=nrm_pos hd₂
  have ng:0<(G.absNorm:ℝ):=nrm_pos hG
  have hv:sourceVolume s*((d.1.absNorm:ℝ)*d.2.absNorm) ≤ r.Z^(9179599/10000000:ℝ) := by
    change ((X₁/(d.1.absNorm:ℝ))*(X₂/(d.2.absNorm:ℝ))*(∏i,r.Z^(r.w i)))*_ ≤ _
    rw [←Real.rpow_sum_of_pos h0]
    calc
      _ = X₁*X₂*r.Z^(∑i,r.w i) := by field_simp [d1.ne',d2.ne']
      _  ≤  _ := hparent
  have he: (∏j:J,s.P j.val.val)=r.Z^u' := by
    change (∏j:J,r.Z^(r.w j.val.val))=r.Z^(∑j∈J,r.w j.val)
    rw [←Finset.sum_coe_sort,Real.rpow_sum_of_pos h0]
  have hv' := first_volume s (by norm_num) cover G B J
  rw [he] at hv'
  have hc:0 < (2:ℝ)^Fintype.card ι := by positivity
  have hfee := Real.rpow_logb h0 hZ.ne' hc
  rw [←hfee] at hv'
  have hmin : r.Z^(115/1000:ℝ)/((d.1.absNorm:ℝ)*d.2.absNorm)  ≤  s.L :=
    minimum_divisors _ _ _ _ _ _ _ ⟨h1,h2,h3,h4⟩ q0 (nrm_one_le hd₁) (nrm_one_le hd₂)
  have hmin' := hmin.trans (first_minimum s (by norm_num) cover G B J rfl)
  have hpay : r.Z^(115/1000:ℝ)  ≤  child.L*((d.1.absNorm:ℝ)*d.2.absNorm)*(G.absNorm:ℝ) := by
    have h := (div_le_iff₀ (mul_pos d1 d2)).mp hmin'
    convert h using 1 <;> ring
  exact inverse_common_ledger r.Z _ _ child.L _ _ _ _ u' _ _ (115/1000) hZ
    (sourceVolume_pos s) (sourceVolume_pos child) child.hL d1 d2 ng hv hv' hpay le_rfl

#print axioms exact_restored_ledger
end QRH.Cycle092.FixedFramePacking
