/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The canonical preselected width grid fits the actual LOW geometric guard. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.PhysicalLowGuardSource
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.FixedWidthPhysicalCells
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalLowGuard
noncomputable section
open Record1252270103Finite QRH.Record1252270103Graph QRH.Record1252270103Low
open OAI.SevenEighths.CenteredMomentEnergyBands

theorem width_le_step (n : Source) (loss width : ℝ) (hL : 0≤(n.L:ℝ))
    (hwidth : 0≤width) (hloss : 16*((n.L:ℝ)+1)≤|loss|)
    (hpay : |loss| *width≤(n.allowance:ℝ)) : width≤step n := by
  apply (le_div_iff₀ (by positivity : 0<16*((n.L:ℝ)+1))).mpr
  have hh := (mul_le_mul_of_nonneg_right hloss hwidth).trans hpay
  simpa only [mul_comm] using hh

theorem nf_width_le_step (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (ha : NFAccounting n) (loss : ℝ)
    (hloss : 16*((n.L:ℝ)+1)≤|loss|) : nfWidthDelta n low high hv ha loss≤step n := by
  have hcert := nf_width_certificate n low high hv ha loss
  have hL : 0≤(n.L:ℝ) := by
    have hh : (1:ℝ)<n.L := by exact_mod_cast hv.2.2.1
    linarith
  exact width_le_step n loss _ hL hcert.2.1.le hloss hcert.2.2.2.1

theorem seed_width_le_step (n low : Source) (hv : SeedSourceValid n low) (loss : ℝ)
    (hloss : 16*((n.L:ℝ)+1)≤|loss|) : seedWidthDelta n low hv loss≤step n := by
  have hcert := seed_width_certificate n low hv loss
  have hL : 0≤(n.L:ℝ) := by
    have hh : (1:ℝ)<n.L := by exact_mod_cast hv.2.2.1
    linarith
  exact width_le_step n loss _ hL hcert.2.1.le hloss hcert.2.2.2.1

/-- The actual global face and upper width cell supply the ordinary-length
upper bound; no separate ordinary budget is required at the caller. -/
theorem initial_plain_bound (n : Source) (b width m₁ m₂ slots : ℝ)
    (hL : 0≤(n.L:ℝ)) (he : 0≤(n.allowance:ℝ))
    (hslots : b-width≤slots)
    (hface : (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible m₁ m₂ slots 1) :
    m₁+m₂≤sourceTReal n b+(n.L:ℝ)*width := by
  have hh : m₁+m₂+(n.L:ℝ)*slots≤(n.B:ℝ) := by
    simpa only [globalFace,mul_one] using hface.2.2.2.2.2.2
  have hs := mul_le_mul_of_nonneg_left hslots hL
  have hp := mul_nonneg hL he
  dsimp only [sourceTReal]
  nlinarith only [hh,hs,hp]

end
end QRH.Record1252270103Source.PhysicalLowGuard
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.width_le_step
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.nf_width_le_step
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.seed_width_le_step
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.initial_plain_bound
