/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original calibrated high-response rows have a genuine finite descriptor
cover with b=buffer/2; no late positive-width or calibration premise is needed. -/
import Candidate.C092.transport.SourceInverseP6CloseDescriptors

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O

theorem calibration_eventually {F buffer Cslot : ℝ} (hb : 0<buffer) (hC : 0<Cslot) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ 1≤Cslot*Z^buffer ∧ F*Z^(buffer/2)≤Cslot*Z^buffer := by
  have hb' : 0<buffer/2 := by positivity
  filter_upwards [(tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (1/Cslot)),
    (tendsto_rpow_atTop hb').eventually (eventually_ge_atTop (F/Cslot)),
    eventually_gt_atTop (1:ℝ)] with Z h1 h2 hZ
  refine ⟨hZ,by simpa only [mul_comm] using (div_le_iff₀ hC).mp h1,?_⟩
  have hf : F≤Cslot*Z^(buffer/2) := by simpa only [mul_comm] using (div_le_iff₀ hC).mp h2
  calc
    F*Z^(buffer/2) ≤ (Cslot*Z^(buffer/2))*Z^(buffer/2) :=
      mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _ = Cslot*Z^buffer := by rw [mul_assoc,←Real.rpow_add (zero_lt_one.trans hZ)];congr 2;ring

theorem actual_calibrated_descriptor_cover {Slot : Type*} [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    {buffer Cslot : ℝ} (hb : 0<buffer) (hC : 0<Cslot) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ (η η₀ : Character)
      (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t : ℝ) (rows : Finset FreeRow),
      (∀ j,0≤w j) →
      (∀ u∈rows,0 < measured M H hH η η₀ W Z (Cslot*Z^buffer) θ w v t u) →
      ∀ u∈rows,∃ j,u∈descriptorRows M H hH rows η η₀ W Z (Cslot*Z^buffer) (buffer/2) θ w v t j := by
  letI : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
  obtain ⟨F,hF,hcover⟩ := actual_descriptor_cover (Slot:=Slot) M H hH W hW hWs
  filter_upwards [calibration_eventually (F:=F) hb hC] with Z hcal
  refine ⟨hcal.1,?_⟩
  intro η η₀ θ w v t rows hw hpos
  exact (hcover Z (Cslot*Z^buffer) (buffer/2) hcal.1 hcal.2.1 (by positivity) hcal.2.2
    η η₀ θ w v t rows hw hpos).1

#print axioms actual_calibrated_descriptor_cover
end
end QRH.Cycle092.SourceInverseP6
