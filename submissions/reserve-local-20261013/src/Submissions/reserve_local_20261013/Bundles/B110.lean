/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below.
Affine-capacity adaptation: the source module hashes below identify the
pre-adaptation provenance, not the modified declarations in this file. -/
import Submissions.reserve_local_20261013.Bundles.B029
import Submissions.reserve_local_20261013.Bundles.B069
import Submissions.reserve_local_20261013.Bundles.B087
import Submissions.reserve_local_20261013.Bundles.B097
import Submissions.reserve_local_20261013.Bundles.B104
import Submissions.reserve_local_20261013.Bundles.B108
import Submissions.reserve_local_20261013.Bundles.B109
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps

/- BEGIN ORIGINAL MODULE Analytic.JointFirstBinSourceGates ; sha256 e117d79bba220bd0ab0a7c42177e8c79e69a17b54c445c75b1710dd22a3081dc -/
section



/-! Literal source facts inherited by the actual high packet image:
principal first masks, squarefree projectors, the shared bin, retained
frequency support, and nonzero selected physical blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentCanonicalFirst CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair CenteredMomentFirstDiscardedEnergy
open CenteredMomentCompleteCommon CenteredMomentActive
local notation "O" => HeckeFamily.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

namespace ActualFirstSecondSource
variable (src : Input ι) (R seed : Ideal O) (Kfirst : ℝ)
  (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
  (side : Bool) (Z A M omega ξ : ℝ)
  (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
  (bin : NonzeroElement → Option κ) (b : κ)
  (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
  (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))

abbrev LivePacket := Packet src R seed Kfirst radius side
  (mainScale src R seed Kfirst radius side Z A M omega)
  (mainRadius src R seed Kfirst radius side Z A M omega ξ)
  (mainHeight src R seed Kfirst radius side)

theorem live_packet_principal (x : LivePacket src R seed Kfirst radius side Z A M omega ξ) :
    (row x).E ∈ (principalSupport Finset.univ (leftExponent (row x).first.val.1 (row x).first.val.2)
      (rightExponent (row x).first.val.1 (row x).first.val.2)).powerset := x.1.1.2.1.property

theorem live_packet_squarefree (x : LivePacket src R seed Kfirst radius side Z A M omega ξ) :
    Squarefree (row x).L :=
  (firstSourceOuterLabel src R seed Kfirst radius x.1.1).projector_squarefree x.1.2.1.val x.1.2.1.property

theorem live_packet_bin
    (x : LivePacket src R seed Kfirst radius side Z A M omega ξ)
    (hx : x∈liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels) :
    bin ((row x).reconstructed src.η x.1.2.2.1 x.1.2.2.2⁻¹
      (liveBinPackets_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels x hx))=some b := by
  have hm := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hx).2).2
  have hg := liveBinRows_gates src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W
    x.1 x.2.1 x.2.2 hm
  have hb := (Finset.mem_filter.mp hg.1).2
  have hz := liveBinPackets_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels x hx
  have hz' : x.2.2≠0 := hz
  unfold FirstSidePresentation.sourceBin at hb
  rw [dif_pos hz'] at hb
  exact hb

theorem live_packet_frequency
    (x : LivePacket src R seed Kfirst radius side Z A M omega ξ)
    (hx : x∈liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels) :
    (row x).z ∈ ActualJointSourceRow.liveFrequencyRows (row x).second.val.1 (row x).second.val.2 (row x).U
      (mainRadius src R seed Kfirst radius side Z A M omega ξ x.1) := by
  have hm := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hx).2).2
  have hg := liveBinRows_gates src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W
    x.1 x.2.1 x.2.2 hm
  exact (Finset.mem_filter.mp hg.1).1

/-- The bin classifier is inherited exactly, including the inverse raw
right ray and the original first presentation on the right side. -/
theorem live_rayRows_bin
    (fallback : First src R seed Kfirst radius) (χ₁ ξ₁ : RayCharacter)
    (q : NonzeroJointSourceRow (original src R seed) side)
    (hq : q∈rayRows fallback
      (liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels)
      (liveBinPackets_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels) χ₁ ξ₁) :
    bin (q.val.reconstructed src.η χ₁ ξ₁⁻¹ q.property)=some b := by
  obtain ⟨x,hx,hχ,hξ,hrow⟩ := mem_rayRows_witness fallback _ _ χ₁ ξ₁ q hq
  have hb := live_packet_bin src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels x hx
  subst χ₁; subst ξ₁
  simpa only [hrow] using hb

theorem live_rayRows_first_gates
    (fallback : First src R seed Kfirst radius) (χ₁ ξ₁ : RayCharacter)
    (q : NonzeroJointSourceRow (original src R seed) side)
    (hq : q∈rayRows fallback
      (liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels)
      (liveBinPackets_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels) χ₁ ξ₁) :
    Squarefree q.val.L ∧ q.val.E ∈
      (principalSupport Finset.univ (leftExponent q.val.first.val.1 q.val.first.val.2)
        (rightExponent q.val.first.val.1 q.val.first.val.2)).powerset := by
  obtain ⟨x,hx,hχ,hξ,hrow⟩ := mem_rayRows_witness fallback _ _ χ₁ ξ₁ q hq
  have hsquare := live_packet_squarefree src R seed Kfirst radius side Z A M omega ξ x
  have hprincipal := live_packet_principal src R seed Kfirst radius side Z A M omega ξ x
  exact (congrArg (fun v : ActualJointSourceRow (original src R seed) side =>
    Squarefree v.L ∧ v.E ∈ (principalSupport Finset.univ
      (leftExponent v.first.val.1 v.first.val.2)
      (rightExponent v.first.val.1 v.first.val.2)).powerset) hrow).mp ⟨hsquare,hprincipal⟩

end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.live_rayRows_bin
#print axioms ActualFirstSecondSource.live_rayRows_first_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstBinSourceGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowLocalGates ; sha256 6859da9d3bf200aa130e5a923f4cb080a6f1dc114e7e6d679e46bc73e95ef1d5 -/
section





/-! Original source scales and fixed profile constants discharge the live
low-budget gates in the normalized local window. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentExceptionalAmplitudePair CenteredMomentOriginalCommonHarmonic
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open ActualEisensteinCubic ConcretePrimeRowBridge CenteredMomentActive
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sourceRadius_eq_profile_volume (s : Input ι) :
    sourceRadius s = ((∏ i,s.hi i)*s.b₁*s.b₂)*volume s.toData := by
  unfold sourceRadius volume
  ring

lemma sourceRadius_le_fixed_volume (s : Input ι) (upper b₁ b₂ : ℝ)
    (hhi : ∀ i, |s.hi i| ≤ upper) (hb₁ : |s.b₁| ≤ b₁) (hb₂ : |s.b₂| ≤ b₂) :
    sourceRadius s ≤ (max 1 upper)^Fintype.card ι*max 1 b₁*max 1 b₂*volume s.toData := by
  rw [sourceRadius_eq_profile_volume]
  have hv := (volume_pos s.toData).le
  apply mul_le_mul_of_nonneg_right _ hv
  calc
    _ ≤ |(∏ i,s.hi i)*s.b₁*s.b₂| := le_abs_self _
    _ = (∏ i,|s.hi i|)*|s.b₁| * |s.b₂| := by simp only [abs_mul,Finset.abs_prod]
    _ ≤ (∏ _i : ι,max 1 upper)*max 1 b₁*max 1 b₂ := by
      gcongr
      · exact (hhi _).trans (le_max_right _ _)
      · exact hb₁.trans (le_max_right _ _)
      · exact hb₂.trans (le_max_right _ _)
    _ = _ := by simp

lemma eventually_fixed_logb_le (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ Real.logb Z C ≤ ε := by
  filter_upwards [(tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C),
    eventually_gt_atTop (1:ℝ)] with Z hpow hZ
  refine ⟨hZ,?_⟩
  have hh := Real.logb_le_logb_of_le hZ hC hpow
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

lemma eventually_low_fixed_profile_gates (upper b₁ b₂ b ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    (∀ s : Input ι, 0 < sourceRadius s →
      (∀ i, |s.hi i| ≤ upper) → |s.b₁| ≤ b₁ → |s.b₂| ≤ b₂ → s.upper ≤ upper →
      Real.logb Z (sourceRadius s) ≤ Real.logb Z (volume s.toData)+ε ∧
      (Fintype.card ι : ℝ)*Real.logb Z (max 1 s.upper) ≤ ε) ∧
    Real.logb Z (max 1 b*max 1 b) ≤ 2*ε ∧
    0 ≤ Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)) ∧
    Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)) ≤ ε := by
  let C := (max 1 upper)^Fintype.card ι*max 1 b₁*max 1 b₂
  have hC : 0 < C := by dsimp only [C]; positivity
  have hfixed : (1:ℝ) ≤ 16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ) := by
    have hp : (1:ℝ) ≤ CenteredMomentSecondRadicalBudget.fixedFactor := by
      exact_mod_cast CenteredMomentSecondRadicalBudget.fixedFactor_pos
    linarith
  filter_upwards [eventually_fixed_logb_le C ε hC hε,
    eventually_fixed_logb_le ((max 1 upper)^Fintype.card ι) ε (by positivity) hε,
    eventually_fixed_logb_le (max 1 b*max 1 b) (2*ε) (by positivity) (by positivity),
    eventually_fixed_logb_le (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)) ε (by linarith) hε]
    with Z hsource hprofile hclip hfactor
  refine ⟨hsource.1,?_,hclip.2,Real.logb_nonneg hsource.1 hfixed,hfactor.2⟩
  intro s hs hhi hb₁ hb₂ hu
  have hh := Real.logb_le_logb_of_le hsource.1 hs (sourceRadius_le_fixed_volume s upper b₁ b₂ hhi hb₁ hb₂)
  rw [Real.logb_mul hC.ne' (volume_pos s.toData).ne'] at hh
  refine ⟨by linarith [hsource.2],?_⟩
  have hu' : max 1 s.upper ≤ max 1 upper := max_le_max le_rfl hu
  have hp := Real.logb_le_logb_of_le hsource.1
    (show (0:ℝ) < (max 1 s.upper)^Fintype.card ι by positivity)
    (pow_le_pow_left₀ (by positivity) hu' (Fintype.card ι))
  rw [Real.logb_pow] at hp
  exact hp.trans hprofile.2

lemma local_capacity_of_volume (Z n₁ n₂ z A : ℝ)
    (hA : A = n₁+n₂+z) (hn₁ : n₁ ≤ 423/1000) (hn₂ : n₂ ≤ 423/1000)
    (hz : z ≤ 37/1000) (hcap : localRegion n₁ n₂ z) :
    A ≤ 881/1000 ∧
    A+(7/2)*z ≤ 1+max (n₁+n₂+(9/2)*z-1) 0 ∧
    0 ≤ max (n₁+n₂+(9/2)*z-1) 0 ∧
    max (n₁+n₂+(9/2)*z-1) 0 ≤ 1/250 := by
  have hh := local_parent_geometry n₁ n₂ z hn₁ hn₂ hz hcap
  refine ⟨by linarith [hh.1],?_,hh.2⟩
  linarith [le_max_left (n₁+n₂+(9/2)*z-1) 0]

lemma firstLowRadius_fixed_cap (q : FirstJointLabel ι) (left : Bool)
    (Hsource Z A sourceLoss omega ξ : ℝ) (hZ : 1 < Z)
    (hH : 0 ≤ Hsource) (hsource : Hsource ≤ Z^(A+sourceLoss))
    (homega : 0 ≤ omega) (hsmall : 2*sourceLoss+ξ/2 ≤ 1) :
    firstLowRadius q left Hsource Z A 1 omega ξ ≤ Z^(2:ℝ) := by
  let C := q.sideCommon left
  let D := q.sideCommon (!left)
  let c := Real.logb Z (C.absNorm : ℝ)
  let d := Real.logb Z (D.absNorm : ℝ)
  let R := Real.logb Z (normValue (activeConductor q.C q.D))
  let E := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex q.C q.D => P.val) q.E))
  have hz := zero_lt_one.trans hZ
  have hn : 0 < (C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (q.sideCommon_supported left).1)
  have hc : (C.absNorm : ℝ) = Z^c := (Real.rpow_logb hz hZ.ne' hn).symm
  have hR : 0 ≤ R := (q.target_auxiliary_widths_nonneg Z hZ).2.1
  have hE : 0 ≤ E := Real.logb_nonneg hZ
    (normValue_ge_one _ (primeSubsetGenerator_ne_zero _ _))
  change (Hsource/(C.absNorm : ℝ))^2 /
    Z^(2*A-c-d+R+E-1+max (d-c) 0+6*(3/500)+omega)*Z^(ξ/2) ≤ _
  rw [hc]
  calc
    _ ≤ (Z^(A+sourceLoss)/Z^c)^2 /
        Z^(2*A-c-d+R+E-1+max (d-c) 0+6*(3/500)+omega)*Z^(ξ/2) := by gcongr
    _ = Z^(1-R-E-max (c-d) 0-6*(3/500)-omega+2*sourceLoss+ξ/2) := by
      rw [←Real.rpow_sub hz,←Real.rpow_natCast (Z^(A+sourceLoss-c)) 2,
        ←Real.rpow_mul hz.le,←Real.rpow_sub hz,←Real.rpow_add hz]
      congr 1
      have hm : max (c-d) 0-max (d-c) 0 = c-d := by
        rcases le_total c d with h | h
        · rw [max_eq_right (sub_nonpos.mpr h),max_eq_left (sub_nonneg.mpr h)]; ring
        · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)]; ring
      push_cast
      linarith
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [le_max_right (c-d) 0])

def lowLocalTiny : ℝ := 1/10000000

def lowLocalMesh : ℝ := min (Cycle25.Energy.commonMesh 2 0 1 (lowLocalTiny/4)) (lowLocalTiny/4)

def lowLocalSlotLoss (N : ℕ) : ℝ := lowLocalTiny/(16*(N+1))

def lowLocalBinCap (N : ℕ) : ℝ := min (lowLocalSlotLoss N/32) (1/2000)

lemma low_local_parameter_choices (N : ℕ) :
    0 < lowLocalMesh ∧ lowLocalMesh ≤ Cycle25.Energy.commonMesh 2 0 1 (lowLocalTiny/4) ∧
    lowLocalMesh ≤ 2 ∧
    lowLocalTiny/4+(67/100)*lowLocalMesh+2*2*lowLocalSlotLoss N*N ≤ lowLocalTiny ∧
    0 < lowLocalBinCap N ∧ 0 < lowLocalSlotLoss N ∧
    ∀ e : ℝ, 0 < e → e ≤ lowLocalBinCap N →
      e < 1/1000 ∧ 0 < lowLocalSlotLoss N/4 ∧ 8*e+lowLocalSlotLoss N/4 ≤ lowLocalSlotLoss N := by
  have ht : 0 < lowLocalTiny := by norm_num [lowLocalTiny]
  have hm := Cycle25.Energy.commonMesh_pos 2 0 1 (lowLocalTiny/4) (by norm_num) (by norm_num) (by positivity)
  have hmpos : 0 < lowLocalMesh := lt_min hm (by positivity)
  have hmcap : lowLocalMesh ≤ lowLocalTiny/4 := min_le_right _ _
  have he := low_mesh_independent_of_slot_count lowLocalTiny 2 lowLocalMesh (lowLocalTiny/4)
    ht (by norm_num) hmpos.le hmcap le_rfl N
  norm_num only [show (8:ℝ)*2=16 by norm_num] at he
  change 0 < lowLocalSlotLoss N ∧ _ at he
  refine ⟨hmpos,min_le_left _ _,by norm_num [lowLocalTiny] at hmcap ⊢; linarith,
    (by simpa only [show (2:ℝ)*2=4 by norm_num, lowLocalSlotLoss] using he.2),lt_min (by dsimp [lowLocalSlotLoss]; positivity) (by norm_num),he.1,?_⟩
  intro e he0 hecap
  have he1 : e ≤ lowLocalSlotLoss N/32 := hecap.trans (min_le_left _ _)
  have he2 : e ≤ 1/2000 := hecap.trans (min_le_right _ _)
  exact ⟨by linarith,div_pos he.1 (by norm_num),by linarith [he.1]⟩

lemma low_local_live_budgets (ω ξ logFixed : ℝ)
    (hω : 0 ≤ ω) (hω' : ω ≤ lowLocalTiny) (hξ : 0 ≤ ξ) (hξ' : ξ ≤ lowLocalTiny)
    (hf : 0 ≤ logFixed) (hf' : logFixed ≤ lowLocalTiny) :
    let pad := 2*lowLocalTiny+lowLocalTiny+ξ/2+logFixed;
    0 ≤ pad ∧
    pad+lowLocalTiny+(67/450)*((ω+lowLocalTiny)+2*lowLocalTiny) ≤ 1/45000 ∧
    1+pad ≤ 2 ∧ 1+pad+0+lowLocalTiny ≤ 2 ∧
    2*lowLocalTiny+ξ/2 ≤ 1 := by
  dsimp only
  norm_num [lowLocalTiny] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma original_volume_log (s : Input ι) (Z : ℝ) (w : ι → ℝ) (hZ : 1 < Z)
    (hP : ∀ i,s.P i = Z^(w i)) :
    Real.logb Z (volume s.toData) = Real.logb Z s.X₁+Real.logb Z s.X₂+∑ i,w i := by
  unfold volume
  rw [Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne' (Finset.prod_pos (fun i _ => s.P_pos i)).ne',
    Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne',Real.logb_prod Finset.univ s.P (fun i _ => (s.P_pos i).ne')]
  simp only [hP,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

/-- The source pointwise gate only requires a comparison scale below Z;
its exponent need not satisfy the narrower original plain-length window. -/
lemma plain_scale_le_base_of_log_le_one (X Z : ℝ) (hX : 0 < X) (hZ : 1 < Z)
    (hlog : Real.logb Z X ≤ 1) : X ≤ Z^(1:ℝ) := by
  calc
    X = Z^(Real.logb Z X) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hlog

lemma plain_scale_le_base (X Z : ℝ) (hX : 0 < X) (hZ : 1 < Z)
    (hlog : Real.logb Z X ≤ 423/1000) : X ≤ Z^(1:ℝ) := by
  calc
    X = Z^(Real.logb Z X) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

#print axioms eventually_low_fixed_profile_gates
#print axioms firstLowRadius_fixed_cap
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowLocalGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalLocalGates ; sha256 554793d8fa958b6e610c43f5b415a99d3959a5027a01fa85f2727543ae996d55 -/
section








/-! Fixed-source polynomial gates for the coherent exceptional part. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstScale CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma firstNominalScale_swap (C D E : Ideal O) (K V : ℝ) :
    firstNominalScale D C E K V = firstNominalScale C D E K V := by
  unfold firstNominalScale
  rw [CenteredMomentFirstMixedRoot.active_span_swap]
  ring

lemma firstLowMainScale_actual_radius (q : FirstJointLabel ι) (left : Bool)
    (Z A M omega : ℝ) (hZ : 1 < Z) :
    firstLowMainScale q left Z A M omega =
      mainCommonRadius Z (q.sideWidth (!left) Z)
        (nominalLog (q.sideCommon left) (q.sideCommon (!left))
          (Ideal.span {q.puncture}) (Z^M) (Z^A) Z)
        (q.sideWidth left Z) (9/500) omega 0 := by
  cases left
  · simp only [FirstJointLabel.sideCommon,FirstJointLabel.sideWidth,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
    rw [nominalLog,firstNominalScale_swap]
    change _ = mainCommonRadius Z (q.leftWidth Z)
      (nominalLog q.C q.D (Ideal.span {q.puncture}) (Z^M) (Z^A) Z) (q.rightWidth Z) (9/500) omega 0
    rw [q.nominal_log_power Z A M hZ]
    unfold firstLowMainScale mainCommonRadius
    simp only [FirstJointLabel.sideCommon,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
    rw [←q.activeWidth_normValue Z,←q.punctureWidth_normValue Z]
    congr 1
    unfold FirstJointLabel.leftWidth FirstJointLabel.rightWidth
    ring
  · simp only [FirstJointLabel.sideCommon,FirstJointLabel.sideWidth,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
    rw [q.nominal_log_power Z A M hZ]
    unfold firstLowMainScale mainCommonRadius
    simp only [FirstJointLabel.sideCommon,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
    rw [←q.activeWidth_normValue Z,←q.punctureWidth_normValue Z]
    congr 1
    unfold FirstJointLabel.leftWidth FirstJointLabel.rightWidth
    ring

lemma coherent_exceptional_fixed_presentation_one : (1:ℝ) ≤ fixedPresentationCost := by
  have hb : (1:ℝ) ≤ (Ideal.span {fixedBadMask}).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h72 : (1:ℝ) ≤ (Ideal.span {(72:O)}).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O) ≠ 0)))
  exact one_le_mul_of_one_le_of_one_le hb h72

lemma first_side_expanded_factor_cap (q : FirstJointLabel ι) (left : Bool) :
    (expandedFactor (q.sideCharacter left) : ℝ) ≤
      (1296*fixedPresentationCost*(q.parent.modulus.absNorm : ℝ)*
        (CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm)*
          (q.C.absNorm : ℝ)^2 := by
  have hh := CenteredMomentFirstSourceConductorCaps.fixed_pair_caps q.parent q.C q.D q.hC q.E q.leftRay q.rightRay q.pair
  have hp : ((q.sideCharacter left).modulus.absNorm : ℝ) ≤
      fixedPresentationCost*(q.parent.modulus.absNorm : ℝ)*(q.C.absNorm : ℝ)^2 := by
    cases left
    · exact hh.2
    · exact hh.1
  unfold expandedFactor
  push_cast
  calc
    _ ≤ 1296*(fixedPresentationCost*(q.parent.modulus.absNorm : ℝ)*(q.C.absNorm : ℝ)^2)*
        (CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm := by gcongr
    _ = _ := by ring

lemma coherent_exceptional_slot_fixed (src : Input ι) (M upper : ℝ)
    (hM : 0 ≤ M) (hs : ∀ i,src.M i ≤ M) (hu : src.upper ≤ upper) :
    slotControl src.toData^2*frozenProfile src^2 ≤
      ((128*max 1 upper)^Fintype.card ι)^2*((max 1 upper)^Fintype.card ι)^2*
        (M^Fintype.card ι)^6 := by
  have hm := input_profile_mass_le src M hM hs
  have hh := CenteredMomentFirstChildProfileControl.exceptional_slot_bound src
    (Fintype.card ι) (max 1 upper) (M^Fintype.card ι) (le_max_left _ _)
    (hu.trans (le_max_right _ _)) le_rfl hm
  apply hh.trans
  calc
    _ ≤ ((128*max 1 upper)^Fintype.card ι)^2*((max 1 upper)^Fintype.card ι)^2*
        (M^Fintype.card ι)^4*(M^Fintype.card ι)^2 := by
      gcongr
      · exact CenteredMomentFirstChildProfileControl.mass_nonneg src
      · exact hm
    _ = _ := by ring

#print axioms firstLowMainScale_actual_radius
#print axioms first_side_expanded_factor_cap
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalLocalGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstHighPartition ; sha256 1caa763d13313616fb2aba516b13a6488524df7b3ebd380a6a5e0d4c4c2f158b -/
section


/-! A finite width partition of the actual live packet sum. The partition
retains both dyadic indices and both rays; it does not duplicate arithmetic
rows or insert a cardinality bound for source labels. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι κ Cell : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
  [Fintype Cell] [DecidableEq Cell]
namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

theorem sum_packet_cells
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (cell : Packet src R seed Kfirst radius side K Radius H → Cell)
    (V P : ℝ) (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ)) :
    (∑ x∈X,packetValue hs hz₁ hz₂ V P t W x) =
      ∑ c : Cell, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        ∑ x∈rayPackets (X.filter (fun x => cell x=c)) χ ξ,
          packetValue hs hz₁ hz₂ V P t W x := by
  simp_rw [←sum_ray_partition hs hz₁ hz₂]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

variable (src R seed Kfirst radius side) (Z A M omega ξ : ℝ)
  (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
  (bin : NonzeroElement → Option κ) (b : κ)
  (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))

theorem actual_first_high_cell_majorant
    (hZ : 0< Z) (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (P : ℝ) (hP : 0< P)
    (cell : LivePacket src R seed Kfirst radius side Z A M omega ξ → Cell) :
    let X := liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels
    (∑ k∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _ => sourceRadius src) side,
      ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k side
        Z A M omega ξ (t k) W bin b‖/(volume src.toData*P)) ≤
      ∑ c : Cell, ∑ χ₁ : RayCharacter, ∑ ξ₁ : RayCharacter,
        ∑ x∈rayPackets (X.filter (fun x => cell x=c)) χ₁ ξ₁,
          packetValue hs hz₁ hz₂ (volume src.toData) P t W x := by
  dsimp only
  exact (actual_first_live_bin_packet_majorant src R seed Kfirst radius side Z A M omega ξ
    hs hz₁ hz₂ bin b t W hZ labels P hP).trans_eq
      (sum_packet_cells hs hz₁ hz₂ _ cell _ P t W)

#print axioms actual_first_high_cell_majorant
end ActualFirstSecondSource
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstHighPartition -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstLowHighSplit ; sha256 f019243fe6d0b2b46db6838463f8d27e09c2d507657941aa919dc08ca84ef961 -/
section


/-! The coherent second decomposition into the five literal contributions:
zero, exceptional, low bins, high bins, and the discarded source tail. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSupportedTailAggregate CenteredMomentCommonRadialData
open CenteredMomentSecondHeightFamily
open CenteredExceptionalProfile RayFourExpansion EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_first_common_low_high_split
    (src : Input ι) (R seed : Ideal O) (hs : Squarefree seed)
    (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (Kfirst : ℝ) (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (left : Bool) (Z A M omega ξ : ℝ) (hZ : 0 < Z)
    (W : 𝓢(ℝ,ℂ)) (P : ℝ) (hP : 0 < P)
    (I : ℕ) (e : ℝ)
    (bin : HeckeInverseAmplification.NonzeroElement → Option (Fin (I+1) × Fin (I+1)))
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w,bin w = none ↔ FixedInducingRow src.η Q fixedBadMask 1 w.val)
    (hbinUpper : ∀ w b,bin w = some b → 51/100+(e/2)*(b.2.val : ℝ) ≤ 7/8)
    (χ : RayCharacter) (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) :
    let q := firstSourceOuterLabel src R seed Kfirst radius
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
    let Index := (i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex
    let child := fun k : Index => (q k.1).sourceChild k.2
    let columns := fun k : Index => commonSecondColumns (CenteredMomentAmplificationChildInput.original src R seed)
      ((q k.1).sideCommon left) ((q k.1).sideCommon_supported left)
    let β := fun k : Index => commonSecondBeta (CenteredMomentAmplificationChildInput.original src R seed)
      ((q k.1).sideCommon left) k.2.1.val
    let Kmain := fun k : Index => firstLowMainScale (q k.1) left Z A M omega
    let Tsec := fun k : Index => (sourceRadius src/((q k.1).sideCommon left).absNorm)^2/Kmain k
    let Hsource := fun k : Index => sourceRadius src/((q k.1).sideCommon left).absNorm
    ∀ t : Index → ℝ,
    (∑ k ∈ domain,(child k).sideEnergy left (t k) W (Kmain k)/
      (CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) ≤
      (∑ k ∈ domain, ‖((Kmain k : ℂ)*paperRadialFourier W 0)*
        sourceSecondZero (columns k) (β k) ((child k).sideParent left) (t k)‖/
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) +
      (∑ k ∈ domain, ‖partEnergy true ((child k).sideParent left) χ Q m (t k)
        (columns k) (β k) W (Kmain k) (Tsec k) Z ξ (Hsource k)‖/
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) +
      ((∑ b ∈ actualLowBins I e, ∑ k ∈ domain, ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k left
        Z A M omega ξ (t k) W bin b‖/(CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) +
      (∑ b ∈ actualHighBins I e, ∑ k ∈ domain, ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k left
        Z A M omega ξ (t k) W bin b‖/(CenteredMomentExceptionalAmplitudePair.volume src.toData*P))) +
      (∑ k ∈ domain, ‖secondDiscardedEnergy ((child k).sideParent left) (t k)
        (columns k) (β k) W (Kmain k) (Tsec k) Z ξ‖/
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) := by
  intro q domain Index child columns β Kmain Tsec Hsource t
  have hh := actual_first_common_normalized_split src R seed hs hz₁ hz₂ Kfirst radius labels left
    Z A M omega ξ hZ W P hP bin Q hQ72 hbin χ m hm hmLam hm2 t
  let f : (Fin (I+1) × Fin (I+1)) → ℝ := fun b =>
    ∑ k ∈ domain, ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k left
      Z A M omega ξ (t k) W bin b‖/(CenteredMomentExceptionalAmplitudePair.volume src.toData*P)
  have hzero (b : Fin (I+1) × Fin (I+1)) (habove : 7/8 < 51/100+(e/2)*(b.2.val : ℝ)) : f b = 0 := by
    have hempty (w) : bin w ≠ some b := fun heq => not_lt_of_ge (hbinUpper w b heq) habove
    apply Finset.sum_eq_zero
    intro k hk
    rw [firstLowBinBlock_zero_of_empty src R seed hs hz₁ hz₂ Kfirst radius k left
      Z A M omega ξ (t k) W bin b hempty]
    simp
  have hbins := sum_actual_low_high_bins I e f hzero
  dsimp only [f] at hbins
  dsimp only at hh
  rw [hbins] at hh
  exact hh

#print axioms actual_first_common_low_high_split
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstLowHighSplit -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstRecoveredScales ; sha256 cc9218b5038ba8c804785dcdbe2699d2c982f0c1a08405b675d61096138aa3cb -/
section


/-! Recovery on every genuine first dyadic block has the same original
first arithmetic data. Consequently all actual second scales are independent
of the artificial default used outside the arithmetic source image. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

def replaceFirstDyadic (k : First src R seed Kfirst radius)
    (n : CenteredMomentFirstPhysicalDyadicAssembly.Blocks
      (effectiveScale k.1.1.val.1 k.1.1.val.2 k.1.2.1.val Kfirst) (radius k.1.1 k.1.2.1.val)
      (sourceRadius src/k.1.1.val.1.absNorm) (sourceRadius src/k.1.1.val.2.absNorm)) :
    First src R seed Kfirst radius :=
  ⟨⟨k.1.1,k.1.2.1,n⟩,⟨⟨k.2.1.val,k.2.1.property⟩,k.2.2⟩⟩

theorem firstAt_packet_all (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H)
    (n : (row x).FirstDyadic Kfirst (radius (row x).first (row x).E) (sourceRadius src)) :
    firstAt fallback (row x) x.1.2.2.1 x.1.2.2.2 n = replaceFirstDyadic x.1 n := by
  exact recoverFirst_key fallback (replaceFirstDyadic x.1 n)

theorem secondScale_mainScale (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H) (Z A M omega : ℝ)
    (n : (row x).FirstDyadic Kfirst (radius (row x).first (row x).E) (sourceRadius src)) :
    secondScale fallback (mainScale src R seed Kfirst radius side Z A M omega)
      x.1.2.2.1 x.1.2.2.2 (row x) n = mainScale src R seed Kfirst radius side Z A M omega x.1 := by
  unfold secondScale
  rw [firstAt_packet_all]
  rfl

theorem secondScale_mainRadius (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H) (Z A M omega ξ : ℝ)
    (n : (row x).FirstDyadic Kfirst (radius (row x).first (row x).E) (sourceRadius src)) :
    secondScale fallback (mainRadius src R seed Kfirst radius side Z A M omega ξ)
      x.1.2.2.1 x.1.2.2.2 (row x) n = mainRadius src R seed Kfirst radius side Z A M omega ξ x.1 := by
  unfold secondScale
  rw [firstAt_packet_all]
  rfl

theorem secondScale_mainHeight (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H)
    (n : (row x).FirstDyadic Kfirst (radius (row x).first (row x).E) (sourceRadius src)) :
    secondScale fallback (mainHeight src R seed Kfirst radius side)
      x.1.2.2.1 x.1.2.2.2 (row x) n = mainHeight src R seed Kfirst radius side x.1 := by
  unfold secondScale
  rw [firstAt_packet_all]
  rfl

theorem mainRadius_actual (k : First src R seed Kfirst radius) (Z A M omega ξ : ℝ) :
    mainRadius src R seed Kfirst radius side Z A M omega ξ k =
      frequencyRadius ((mainHeight src R seed Kfirst radius side k)^2 /
        mainScale src R seed Kfirst radius side Z A M omega k) Z ξ := rfl

theorem mainHeight_row (x : Packet src R seed Kfirst radius side K Radius H) :
    mainHeight src R seed Kfirst radius side x.1 = sourceRadius src/((row x).label.C₁.absNorm : ℝ) := by
  cases side <;> rfl

end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.firstAt_packet_all
#print axioms ActualFirstSecondSource.mainRadius_actual
#print axioms ActualFirstSecondSource.mainHeight_row
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstRecoveredScales -/
