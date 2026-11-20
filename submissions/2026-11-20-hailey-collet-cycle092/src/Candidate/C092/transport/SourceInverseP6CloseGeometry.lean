/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original attaining slot supplies both inverse and independent-long native
spikes after literal rescaling and exact fixed-character/height transport. -/
import Candidate.C092.transport.SourceInverseP6CloseMember
import Candidate.C092.transport.PairMarkAnnulus

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ConcretePrimeRowBridge
open CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily CenteredMomentPrimeSlot
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.PairMarkAnchor
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6CloseGeometry_ba47d530b2f6441e_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

theorem descriptor_inverse_scale (η η₀ : Character) (W : ℝ→ℂ)
    {Z d : ℝ} (hZ : 0<Z) (hd : d≠0) (θ : Slot→RayQuotient.Characters M H)
    (w v : Slot→ℝ) (t : ℝ) (u : FreeRow) (j : Slot) :
    annularMark M H hH η η₀ W (Z^d) (θ j) (w j/d) (v j) (fun _=>t) u=
      descriptor M H hH η η₀ W Z θ w v t u j := by
  unfold annularMark descriptor
  rw [←Real.rpow_mul hZ.le,mul_div_cancel₀ _ hd]
  rfl

/-- The same actual descriptor is a native spike at the retained long
ordinary character and height; neither a new measured response nor a new
slot lower bound is postulated. -/
theorem descriptor_native_spike (η η₀ ηlong : Character) (W : ℝ→ℂ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    {Z pay b e : ℝ} (hZ : 1<Z) (hpay : 1≤pay)
    (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (tMark tLong : ℝ)
    (rows : Finset FreeRow) (j : Slot)
    (hlarge : (ηlong.modulus.absNorm:ℝ)<Z^(w j))
    (he : ∀ u∈descriptorRows M H hH rows η η₀ W Z pay b θ w v tMark j,
      e ≤ measured M H hH η η₀ W Z pay θ w v tMark u)
    (hw : 0≤w j) :
    ∀ u∈descriptorRows M H hH rows η η₀ W Z pay b θ w v tMark j,
      Z^(e*w j)≤‖normalizedSlot ηlong (fixedBadMask*idealGenerator 1) 1 u.val
        (primePool M H 2 (Z^(w j)))
        (fun I=>idealCoeff (relativeCharacter M H hH (anchoredBase η₀ η ηlong) (θ j)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w j)) (33/50) (tMark+v j-tLong) I)
        tLong (Z^(w j))‖^2 := by
  intro u hu
  have heq := QRH.Cycle092.PairMarkAnchor.full_annulus_norm M H hH η₀ η ηlong (θ j)
    (fixedBadMask*idealGenerator 1) 1 u.val (Z^(w j)) (33/50) tMark tLong (v j)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) W hWs hlarge
  rw [heq,unit_mask_slot η u]
  obtain ⟨_,_,hamp⟩ := Finset.mem_filter.mp hu
  change Z^(e*w j)≤‖descriptor M H hH η η₀ W Z θ w v tMark u j‖^2
  rw [hamp]
  exact (Real.rpow_le_rpow_of_exponent_le hZ.le
    (mul_le_mul_of_nonneg_right (he u hu) hw)).trans
    (le_mul_of_one_le_left (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hpay)

/-- A fixed positive attaining-width floor removes the finite new-character
holes uniformly before the actual arrays or attaining index are chosen. -/
theorem attaining_annuli_eventually (ηlong : Character) {b : ℝ} (hb : 0<b) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ w : ℝ,b≤w → (ηlong.modulus.absNorm:ℝ)<Z^w := by
  filter_upwards [(tendsto_rpow_atTop hb).eventually
    (eventually_gt_atTop (ηlong.modulus.absNorm:ℝ)),eventually_gt_atTop (1:ℝ)] with Z hZb hZ
  exact ⟨hZ,fun w hw=>hZb.trans_le (Real.rpow_le_rpow_of_exponent_le hZ.le hw)⟩

#print axioms descriptor_inverse_scale
#print axioms descriptor_native_spike
#print axioms attaining_annuli_eventually
end
end QRH.Cycle092.SourceInverseP6
