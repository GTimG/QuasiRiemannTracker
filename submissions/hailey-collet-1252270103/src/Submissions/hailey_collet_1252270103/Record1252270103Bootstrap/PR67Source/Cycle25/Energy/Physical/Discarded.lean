import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.RowConductor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowCount
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
noncomputable section
set_option maxHeartbeats 800000
open scoped Classical BigOperators SchwartzMap
namespace Cycle25.Weighted.Numerator.PhysicalTail
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentUniformReflectionApproximation CenteredMomentNaturalPrimitive
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectionMass
local notation "O" => HeckeFamily.O

/-- Polynomial pointwise tails are negligible even with all selected factors. -/
theorem selected_tail_fourth {ι : Type*} (s : Finset ι) (T Q : ι→ℂ)
    (U r q saving Ccard Ctail Cslot : ℝ) (hU : 0<U)
    (_hc : 0≤Ccard) (_ht : 0≤Ctail) (_hq : 0≤Cslot)
    (hcard : (s.card:ℝ)≤Ccard*U^r)
    (htail : ∀i∈s,‖T i‖≤Ctail*U^(-saving))
    (hslot : ∀i∈s,‖Q i‖≤Cslot*U^q) :
    (∑i∈s,‖T i‖^4*‖Q i‖^2)≤Ccard*Ctail^4*Cslot^2*U^(r+2*q-4*saving) := by
  calc
    _ ≤ ∑i∈s,(Ctail*U^(-saving))^4*(Cslot*U^q)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (htail i hi) 4)
        (pow_le_pow_left₀ (norm_nonneg _) (hslot i hi) 2) (sq_nonneg _) (by positivity)
    _ = (s.card:ℝ)*((Ctail*U^(-saving))^4*(Cslot*U^q)^2) := by simp
    _ ≤ (Ccard*U^r)*((Ctail*U^(-saving))^4*(Cslot*U^q)^2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have hpow (e : ℝ) (n : ℕ) : (U^e)^n=U^(e*n) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
      rw [mul_pow,mul_pow,hpow,hpow]
      calc
        _ = Ccard*Ctail^4*Cslot^2*(U^r*U^(-saving*4)*U^(q*2)) := by ring_nf
        _ = _ := by rw [←Real.rpow_add hU,←Real.rpow_add hU];congr 2;ring

end Cycle25.Weighted.Numerator.PhysicalTail
end

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/

end Record1252270103Bootstrap.PR67
