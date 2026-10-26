/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full homogeneous gain in the actual four-coordinate HIGH binning. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.GainAllocation
import Submissions.hailey_collet_1252270103.Record12518109Natural.HighBins

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural.JointHigh
noncomputable section
open scoped Classical BigOperators
open Cycle61InitialMass Record12518109Gain

theorem full_gain_frequency_monotone {ν core : ℝ} (hνlo : 31/50≤ν)
    (hνhi : ν≤3/4) (hcore : 0≤core) (S : ℝ) :
    Monotone (fun q=>gain ν S (core*q)) := by
  intro q r hqr
  exact gain_mono hνlo hνhi le_rfl (mul_le_mul_of_nonneg_left hqr hcore)

/-- The fixed conductor enlargement costs only its explicit density term;
the full gain is monotone in the enlarged frequency. -/
theorem full_gain_conductor_payment {ν core S q δ : ℝ}
    (hνlo : 31/50≤ν) (hνhi : ν≤3/4) (hcore : 0≤core) (hδ : 0≤δ) :
    rho ν*(q+δ)-gain ν S (core*(q+δ))≤
      rho ν*q-gain ν S (core*q)+rho ν*δ := by
  have hg := full_gain_frequency_monotone hνlo hνhi hcore S
    (show q≤q+δ by linarith)
  linarith

theorem full_gain_binned_sum {κ : Type*} (rows : Finset κ) (x : κ→Fin 4→ℝ)
    (energy : κ→ℝ) (width B ν Z C target reserve core S : ℝ)
    (hw : 0<width) (hZ : 1≤Z) (hC : 0≤C)
    (hνlo : 31/50≤ν) (hνhi : ν≤3/4) (hcore : 0≤core)
    (hx : ∀k∈rows,∀i,-B≤x k i ∧ x k i≤B)
    (hpoint : ∀k∈rows,highExponentValue ν (x k)-gain ν S (core*x k 2)≤target-reserve)
    (hbin : ∀key∈rows.image (fun k=>exponentBin width (x k)),
      (∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k)≤
        C*Z^(highExponentValue ν (exponentBinUpper width key)-
          gain ν S (core*exponentBinUpper width key 2))) :
    (∑k∈rows,energy k)≤
      ((Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋).card^4:ℕ)*
        (C*Z^(target-reserve+4*width)) := by
  exact retained_high_binned_sum rows x energy width B ν Z C target reserve
    hw hZ hC ⟨hνlo,hνhi⟩ (fun q=>gain ν S (core*q))
    (full_gain_frequency_monotone hνlo hνhi hcore S) hx hpoint hbin

end
end OAI.SevenEighths.Record12518109Natural.JointHigh
#print axioms OAI.SevenEighths.Record12518109Natural.JointHigh.full_gain_conductor_payment
#print axioms OAI.SevenEighths.Record12518109Natural.JointHigh.full_gain_binned_sum
