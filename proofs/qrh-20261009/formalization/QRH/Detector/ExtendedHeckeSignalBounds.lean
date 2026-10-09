/- Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Lower principal analytic region; original functions unchanged. Every estimate is re-proved and kernel checked. -/
import OAI.NumberTheory.DirichletL.Hecke.SignalBounds
import QRH.Detector.ExtendedHeckeSignalShift
import OAI.NumberTheory.DirichletL.Hecke.SignalShift
import OAI.NumberTheory.DirichletL.Hecke.ReciprocalGrowth

namespace OAI

noncomputable section
open scoped Topology
open MeasureTheory Set Filter Asymptotics
namespace SevenEighths.QRHHeckeSignalBounds
open HeckeFamily HeckeSignal Continuation

open HeckeSignalBounds
theorem contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 87/100<s.re})
    (hb : ∀ s : ℂ, 87/100<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (87/100 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) {x : ℝ} (hx : 1≤x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*Complex.I) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact QRHHeckeSignalShift.contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

theorem signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 87/100<s.re})
    (hb : ∀ s : ℂ, 87/100<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (87/100 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact QRHHeckeSignalShift.signal_isBigO_atTop χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs)

end SevenEighths.QRHHeckeSignalBounds
end
end OAI
