/- Copyright (c) 2026 Sil. Apache-2.0.
Diagonal support of the allocated live sources after positive Cauchy.
This is distinct from the diagonal of the unallocated residual.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstLiveSource
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstNonexceptionalAllocation
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedInnerExceptionalLedger

set_option autoImplicit false
namespace Candidate.FourthPower.MixedFirstLiveRemainders
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentCommonProfile QRH.Record1252270103KernelMass
open CenteredMomentSourceSecondZeroEnergy CenteredMomentAddedZeroUniform
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedOriginalNormCap MixedOriginalTail MixedOriginalSecondZero
open MixedCommonCoefficient MixedCommonRestriction MixedLiveNormalization
open MixedFirstLiveSource MixedFirstNonexceptionalAllocation MixedInnerExceptionalLedger
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem live_card_le (s : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools s) G) :
    Fintype.card (liveIndices B.val)≤Fintype.card ι := by
  rw [Fintype.card_coe]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq Finset.card_univ

theorem source_cap_factored (s : Source ι a b) :
    sourceNormCap s.P b s.T s.d=
      b^2*(2:ℝ)^Fintype.card ι*((s.T*∏i,s.P i)/pairNorm s.d) := by
  simp only [sourceNormCap,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  ring

/-- A nonzero actual frozen coefficient gives the full common-norm
shortening of the live support. No radical replaces N(G). -/
theorem allocated_cap_shortening (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (hG : G≠0)
    (B : actualAllocations (tuplePools s) G)
    (hf : frozenCoefficient B.val G s.R s.ν s.Wslot s.P≠0) :
    sourceNormCap (allocatedLiveSource s hb cover G B).P b
      (allocatedLiveSource s hb cover G B).T (allocatedLiveSource s hb cover G B).d≤
      (2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d/(G.absNorm:ℝ) := by
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hprod := (Finset.mem_filter.mp B.property).2
  have hP : ∀i,0<s.P i := fun i=>zero_lt_one.trans_le (s.hP i)
  have hr := rawReduction_pos B.val hB s.P hP
  have hg : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hraw := (actual_reduction_norm B.val hB G s.R hprod s.ν s.Wslot s.P hP
    1 2 zero_lt_one s.hW hf).2
  rw [max_eq_right (by norm_num : (1:ℝ)≤2)] at hraw
  have hi : (1:ℝ)/rawReduction B.val s.P≤(2:ℝ)^Fintype.card ι/(G.absNorm:ℝ) := by
    apply (div_le_div_iff₀ hr hg).mpr
    simpa only [one_mul] using hraw
  have hdim := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (live_card_le s G B)
  have hT : 0<s.T := by rw [←s.hpX];exact mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
  have hV : 0≤(s.T*∏i,s.P i)/pairNorm s.d :=
    div_nonneg (mul_nonneg hT.le (Finset.prod_nonneg (fun i _=>(hP i).le)))
      (pairNorm_pos s.hd.1 s.hd.2).le
  have hm := mul_le_mul hdim hi (div_nonneg zero_le_one hr.le) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hm (mul_nonneg (sq_nonneg b) hV)
  rw [source_cap_factored]
  change b^2*(2:ℝ)^Fintype.card (liveIndices B.val)*
      ((s.T*∏i : liveIndices B.val,s.P i.val)/
        pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))≤_
  rw [live_volume_ratio B.val hB s.d s.T s.P hP,source_cap_factored]
  convert hh using 1 <;> ring

/-- Diagonal of EACH allocated live source. The caller supplies only
the actual frozen nonzero gate and a numerical original support cap.
The coefficient, divisor and norm bounds are proved here. -/
theorem allocated_second_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,∀hb : 0≤b,∀cover : OriginalEnclosure s,
      ∀(G D : Id),G≠0→D≠0→∀B : actualAllocations (tuplePools s) G,
      frozenCoefficient B.val G s.R s.ν s.Wslot s.P≠0→
      ∀(τ : Character)(t Y : ℝ),1≤Y→
      (2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d≤Y→
      let live := allocatedLiveSource s hb cover G B
      ‖sourceSecondZero (sourceColumns live) (sourceCoefficient live ha D) τ t‖≤
        C*(profileCap live)^2*Y^(1+ε)/((G.absNorm:ℝ)*(D.absNorm:ℝ)) := by
  obtain ⟨C0,hC0,hbound⟩ := original_column_bound N (ε/2) (half_pos hε)
  refine ⟨128*C0^2,by positivity,?_⟩
  intro ι instι a b s hcard ha hb cover G D hG hD B hf τ t Y hY hcap
  let live := allocatedLiveSource s hb cover G B
  have hg : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hg1 : 1≤(G.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hs : sourceNormCap live.P b live.T live.d≤Y/(G.absNorm:ℝ) :=
    (allocated_cap_shortening s hb cover G hG B hf).trans
      (div_le_div_of_nonneg_right hcap hg.le)
  have hboundY : Y/(G.absNorm:ℝ)≤Y := div_le_self hY0.le hg1
  have hsize (I : Id) (hI : I∈supportedColumns (sourceColumns live))
      (hi : sourceCoefficient live ha D I≠0) : (I.absNorm:ℝ)≤Y/(G.absNorm:ℝ) :=
    (original_coefficient_cap live ha D I hi).2.trans hs
  have hcoeff (I : Id) (hI : I∈supportedColumns (sourceColumns live))
      (hi : sourceCoefficient live ha D I≠0) :
      ‖sourceCoefficient live ha D I‖≤C0*profileCap live*Y^(ε/2) :=
    hbound (liveIndices B.val) a b live ((live_card_le s G B).trans hcard) ha D I Y
      (original_coefficient_cap live ha D I hi).1 hY ((hsize I hI hi).trans hboundY)
  have hh := sourceSecondZero_divisor_bound (sourceColumns live) (sourceCoefficient live ha D)
    τ t (C0*profileCap live*Y^(ε/2)) (Y/(G.absNorm:ℝ))
    (by have := profileCap_nonneg live;positivity) (div_nonneg hY0.le hg.le) D hD hcoeff
    (fun I _ hi=>source_coefficient_seed live ha D I hi) hsize
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  apply hh.trans_eq
  calc
    _=(128*C0^2)*(profileCap live)^2*((Y^(ε/2))^2*Y)/
      ((G.absNorm:ℝ)*(D.absNorm:ℝ)) := by ring
    _=_ := by rw [hp]

end
end Candidate.FourthPower.MixedFirstLiveRemainders
