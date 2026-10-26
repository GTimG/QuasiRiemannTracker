/- Copyright (c) 2026 Sil. Apache-2.0.
The small native cost in the actual raw supplier and first-common budgets.
No energy assumption: exact volume/conductor cancellation, first frozen
quadratic payment, and independent-height extraction.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallCostControl

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedSmallSideAlgebra
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonRawScale CenteredMomentSecondWindowBudget
open CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open MixedFirstNonexceptionalAllocation MixedFirstProfileEnvelope
open RepairedSmallRowAllocation RepairedSmallRawBudget RepairedSmallCostControl
local notation "Id" => Ideal HeckeFamily.O
local instance {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Before converting seed to original u, this is precisely the F*seed
denominator consumed by rawSupplierCost at empty selected width W=1. -/
theorem native_cost_to_frozen_budget
    (Nσ Nτ Cf nf F Vr Vfirst p nseed k : ℝ)
    (hτ : 0≤Nτ) (hCf : 0≤Cf) (hF : 0<F) (hp : 0<p)
    (hseed : 0<nseed) (hmod : Nσ≤Cf*Nτ*nf) (hf : nf≤k*F)
    (hvolume : Vr*F=Vfirst) :
    Nσ*(Vr/p)^2/nseed≤Cf*k*Nτ*(Vfirst/p)^2/(F*nseed) := by
  have hn := hmod.trans (mul_le_mul_of_nonneg_left hf (mul_nonneg hCf hτ))
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hn (sq_nonneg _)) hseed.le).trans_eq
  rw [←hvolume]
  field_simp [hF.ne',hp.ne',hseed.ne']
  <;> ring

/-- The actual first frozen coefficient pays both powers of the first
common norm. No prefix is replaced by a radical or absorbed in a constant. -/
theorem first_frozen_native_geometry (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (hG : G≠0)
    (B : actualAllocations (tuplePools s) G) (hM : ∀i,1≤s.M i) :
    ‖frozenScalar s G B‖^2*
      (sourceVolume (allocatedLiveSource s hb cover G B)/
        pairNorm (allocatedLiveSource s hb cover G B).d)^2≤
      (∏i,s.M i)^2*((2:ℝ)^Fintype.card ι)^2*
        (sourceVolume s/pairNorm s.d)^2/(G.absNorm:ℝ)^2 := by
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hc := frozen_quadratic_cost (MixedCommonRestriction.punctureProduct s.S s.H)
    B.val hB G s.R hG (Finset.mem_filter.mp B.property).2
    s.ν s.Wslot s.P s.M (fun i=>zero_lt_one.trans_le (s.hP i))
    s.hν s.hWnorm hM s.hW
  have he := mul_le_mul_of_nonneg_right hc (sq_nonneg (sourceVolume s/pairNorm s.d))
  rw [live_volume]
  convert he using 1 <;> simp only [frozenScalar,div_pow] <;> ring

theorem height_envelope_le_zero (v : ℝ) :
    heightEnvelope v≤heightEnvelope 0*(1+‖v‖) := by
  have h : 1+‖v‖+2*Real.pi≤(1+2*Real.pi)*(1+‖v‖) := by
    nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg v)]
  have hh := mul_le_mul_of_nonneg_right h (show 0≤1+2*Real.pi by positivity)
  convert hh using 1 <;> simp only [heightEnvelope,norm_zero,add_zero] <;> ring

theorem simple_cost_independent_height (s : Source ι a b) (C : ℝ)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (t₀ V tp Z exponent : ℝ)
    (η : Character) (seed : Id) (hC : 0≤C) (hV : 0≤V) (hZ : 0≤Z) :
    simpleCost s C J control t₀ V tp Z exponent η seed≤
      simpleCost s C J control t₀ V 0 Z exponent η seed*(1+‖tp‖)^(2*J) := by
  have hp := pow_le_pow_left₀ (heightEnvelope_pos tp).le (height_envelope_le_zero tp) (2*J)
  rw [mul_pow] at hp
  let A:=C*slotCost s*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
    (height t₀ V s.t₁ s.t₂)^J*Z^exponent*(η.modulus.absNorm:ℝ)*
    (sourceVolume s/pairNorm s.d)^2/(seed.absNorm:ℝ)
  have hA : 0≤A := by
    have hs := slot_cost_nonneg s
    have hh : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
    have hz := Real.rpow_nonneg hZ exponent
    dsimp only [A]
    positivity
  have he := mul_le_mul_of_nonneg_left hp hA
  convert he using 1 <;> dsimp only [A,simpleCost] <;> ring

end
end Candidate.FourthPower.RepairedSmallSideAlgebra
