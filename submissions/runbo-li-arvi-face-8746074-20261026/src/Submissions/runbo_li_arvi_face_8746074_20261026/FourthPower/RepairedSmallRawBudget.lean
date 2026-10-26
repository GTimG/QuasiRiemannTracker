/- Copyright (c) 2026 Sil. Apache-2.0.
The LINEAR ordinary-row volume budget after the same G2 allocation.
All actual prefixes, rawReduction and allocation counts are explicit.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallRowAllocation
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstNonexceptionalAllocation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRawCost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallRawBudget
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentSourceLiveColumn CenteredMomentSourceMass CenteredMomentSourceProfileMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedInnerExceptionalBlock
open MixedCommonCoefficient MixedCommonEnergy MixedLiveNormalization MixedFirstLiveSource
open MixedFirstAvoidance MixedFirstNonexceptionalAllocation RepairedSmallRowAllocation
open MixedSourceAssembly
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def slotCost (s : Source ι a b) : ℝ := (∏i,s.M i)^2*(2:ℝ)^Fintype.card ι

theorem slot_cost_nonneg (s : Source ι a b) : 0≤slotCost s := by
  unfold slotCost
  positivity

theorem live_volume (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) :
    sourceVolume (allocatedLiveSource s hb cover G B)/
        pairNorm (allocatedLiveSource s hb cover G B).d=
      (sourceVolume s/pairNorm s.d)/rawReduction B.val s.P := by
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have he := live_volume_ratio B.val hB s.d s.T s.P
    (fun i => zero_lt_one.trans_le (s.hP i))
  simpa only [sourceVolume,allocatedLiveSource,liveSource,allocationSource,
    Source.prefixPair,s.hpX] using he

/-- Only one reciprocal rawReduction occurs in the native ORDINARY energy. -/
theorem frozen_linear_cost (s : Source ι a b) (G : Id) (hG : G≠0)
    (B : actualAllocations (tuplePools s) G) (hM : ∀i,1≤s.M i) :
    ‖frozenScalar s G B‖^2/rawReduction B.val s.P≤slotCost s/(G.absNorm:ℝ) := by
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hr := rawReduction_pos B.val hB s.P (fun i => zero_lt_one.trans_le (s.hP i))
  have hc := frozen_normalized_cost B.val hB G s.R hG
    (Finset.mem_filter.mp B.property).2 s.ν s.Wslot s.P s.M
    (fun i => zero_lt_one.trans_le (s.hP i)) s.hν s.hWnorm hM 1 2 zero_lt_one s.hW
  rw [max_eq_right (by norm_num : (1:ℝ)≤2)] at hc
  apply (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (frozen_scalar_norm_le _ _ _) 2) hr.le).trans
  exact hc

theorem frozen_live_volume (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (hG : G≠0) (B : actualAllocations (tuplePools s) G)
    (hM : ∀i,1≤s.M i) :
    ‖frozenScalar s G B‖^2*
        (sourceVolume (allocatedLiveSource s hb cover G B)/
          pairNorm (allocatedLiveSource s hb cover G B).d)≤
      slotCost s*(sourceVolume s/pairNorm s.d)/(G.absNorm:ℝ) := by
  rw [live_volume]
  have hv : 0≤sourceVolume s/pairNorm s.d :=
    div_nonneg (sourceVolume_pos s).le (pairNorm_pos s.hd.1 s.hd.2).le
  have hh := mul_le_mul_of_nonneg_right (frozen_linear_cost s G hG B hM) hv
  convert hh using 1 <;> ring

/-- Finite analytic adapter. The child input is the actual canonical live
ordinary energy; its unconditional native supplier is instantiated separately. -/
theorem avoided_energy_of_live_bounds (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (u G seed D : Id) (hG : Supported G)
    (hseed : seed∣G) (hu : u∣s.R*G) (hM : ∀i,1≤s.M i)
    (f : Id → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (A : ℝ) (hA : 0≤A)
    (hbound : ∀B : actualAllocations (tuplePools s) G,
      liveEnergy s ha hb cover G B D f keep Φ K≤
        A*(sourceVolume (allocatedLiveSource s hb cover G B)/
          pairNorm (allocatedLiveSource s hb cover G B).d)) :
    sectorEnergy (avoidSource s u) ha G hG seed D f keep Φ K≤
      ((actualAllocations (tuplePools s) G).card:ℝ)^2*
        (slotCost s*A*(sourceVolume s/pairNorm s.d)/(G.absNorm:ℝ)) := by
  apply (avoided_sector_energy_le s ha hb cover u G seed D hG hseed hu
    f keep Φ K hK hΦ).trans
  have hterm (B : actualAllocations (tuplePools s) G) :
      ‖frozenScalar s G B‖^2*liveEnergy s ha hb cover G B D f keep Φ K≤
        slotCost s*A*(sourceVolume s/pairNorm s.d)/(G.absNorm:ℝ) := by
    apply (mul_le_mul_of_nonneg_left (hbound B) (sq_nonneg _)).trans
    have hh := mul_le_mul_of_nonneg_left (frozen_live_volume s hb cover G hG.1 B hM) hA
    convert hh using 1 <;> ring
  calc
    _≤((actualAllocations (tuplePools s) G).card:ℝ)*
        ∑_B : actualAllocations (tuplePools s) G,
          slotCost s*A*(sourceVolume s/pairNorm s.d)/(G.absNorm:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _ => hterm B)) (Nat.cast_nonneg _)
    _=_ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring

/-- Genuine allocation cardinality, paid only by a caller-chosen subpower. -/
theorem uniform_allocation_count (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type u} [Fintype ι],Fintype.card ι≤N →
      ∀a b : ℝ,∀s : Source ι a b,∀G : Id,G≠0 →
        ((actualAllocations (tuplePools s) G).card:ℝ)^2≤C*(G.absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hcount⟩ := genuine_count_squared (N+2) δ hδ
  refine ⟨C,hC,?_⟩
  intro ι instι hn a b s G hG
  have hdim : Fintype.card (ι ⊕ Fin 2)≤N+2 := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hn 2
  exact hcount hdim (tuplePools s) G hG

/-- The moving f conductor is canceled with the RAW residual volume and
the original u=f*seed, rather than hidden in a normalized energy. -/
theorem small_modulus_volume_cancel
    (Nσ Nτ Cf nf F Vr Vfirst p nseed nu k : ℝ)
    (hτ : 0≤Nτ) (hCf : 0≤Cf) (hnf : 0<nf) (hF : 0<F)
    (hp : 0<p) (hseed : 0<nseed) (hk : 0≤k)
    (hmod : Nσ≤Cf*Nτ*nf) (hf : nf≤k*F)
    (hvolume : Vr*F=Vfirst) (hseedprod : nu=nf*nseed) :
    Nσ*(Vr/p)^2/nseed≤Cf*k^2*Nτ*(Vfirst/p)^2/nu := by
  have hnu : 0<nu := hseedprod.symm ▸ mul_pos hnf hseed
  have hratio : nf/F≤k := (div_le_iff₀ hF).mpr hf
  have hs := pow_le_pow_left₀ (div_nonneg hnf.le hF.le) hratio 2
  have hfront : 0≤Cf*Nτ*(Vfirst/p)^2/nu := by positivity
  calc
    _≤(Cf*Nτ*nf)*(Vr/p)^2/nseed :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmod (sq_nonneg _)) hseed.le
    _=(Cf*Nτ*(Vfirst/p)^2/nu)*(nf/F)^2 := by
      rw [hseedprod,←hvolume]
      field_simp [hnf.ne',hF.ne',hp.ne',hseed.ne']
      <;> ring
    _≤(Cf*Nτ*(Vfirst/p)^2/nu)*k^2 := mul_le_mul_of_nonneg_left hs hfront
    _=_ := by ring

end
end Candidate.FourthPower.RepairedSmallRawBudget
