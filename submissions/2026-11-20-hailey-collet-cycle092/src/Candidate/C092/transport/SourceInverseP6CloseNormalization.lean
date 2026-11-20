/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Keep the full original mark product and its calibration payment. -/
import Candidate.C092.transport.SourceInverseP6CloseWindows

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O

theorem norm_div_sqrt_sq (z : ℂ) {K : ℝ} (hK : 0<K) :
    ‖z/(Real.sqrt K:ℂ)‖^2=‖z‖^2/K := by
  rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hK.le]

theorem energy_div_sqrt (rows : Finset FreeRow) (A B Q : FreeRow→ℂ)
    {K : ℝ} (hK : 0<K) :
    (∑ u∈rows,‖A u*B u*Q u‖^2)=
      K*(∑ u∈rows,‖A u*B u*(Q u/(Real.sqrt K:ℂ))‖^2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [←mul_div_assoc,norm_div_sqrt_sq _ hK]
  field_simp

/-- Upper and lower response endpoints can differ. The difference is an
explicit scalar power, not an assumed upper event for the mark product. -/
theorem normalized_original_product_upper {Slot : Type*} [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    {Z pay F b el eu L : ℝ} (hZ : 1<Z) (hpay : 0<pay) (hb : 0≤b) (hF : 0≤F)
    (hcal : F*Z^b≤pay) (hel : 0≤el) (heu : 0≤eu)
    (η η₀ : Character) (W : ℝ→ℂ) (θ : Slot→RayQuotient.Characters M H)
    (w v : Slot→ℝ) (t : ℝ) (u : FreeRow) (hw : ∀ j,0≤w j)
    (hbound : ∀ j,‖descriptor M H hH η η₀ W Z θ w v t u j‖^2≤F*Z^(w j))
    (hresponse : measured M H hH η η₀ W Z pay θ w v t u≤eu)
    (hwidth : ∑ j,w j≤L) :
    ‖(∏ j,descriptor M H hH η η₀ W Z θ w v t u j)/
      (Real.sqrt (pay^(Fintype.card Slot)*Z^((eu-el)*L)):ℂ)‖^2≤Z^(el*L) := by
  have hZp := zero_lt_one.trans hZ
  have hK : 0<pay^(Fintype.card Slot)*Z^((eu-el)*L) := by positivity
  rw [norm_div_sqrt_sq _ hK]
  apply (div_le_iff₀ hK).mpr
  have h := actual_product_upper M H hH hZ hpay hb hF hcal heu η η₀ W θ w v t u hw hbound hresponse
  have hw' := Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_left hwidth heu)
  have h' := h.trans (mul_le_mul_of_nonneg_left hw' (pow_nonneg hpay.le _))
  convert h' using 1
  rw [mul_left_comm (Z^(el*L)),←Real.rpow_add hZp]
  congr 2
  ring

#print axioms normalized_original_product_upper
#print axioms energy_div_sqrt
end
end QRH.Cycle092.SourceInverseP6
