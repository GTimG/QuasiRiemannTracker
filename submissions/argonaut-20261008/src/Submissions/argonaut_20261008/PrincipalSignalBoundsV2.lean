import Submissions.argonaut_20261008.PrincipalSignalShiftV2
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalBounds

/- NEW LOCAL CANDIDATE. Kernel NOT_RUN. Same actual mathematical objects;
   only analytic x boundary and Sigma evidence are adapted. No final estimate assumption. -/
namespace OAI.SevenEighths.LocalPrincipalSignalBoundsV2
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Set MeasureTheory Filter Asymptotics
open HeckeFamily HeckeSignal Continuation
local notation "Id" => Ideal HeckeFamily.O

theorem contour_shift_left_pc2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0<s.re})
    (hb : ∀ s : ℂ, analyticBoundaryB0<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (analyticBoundaryB0 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) {x : ℝ} (hx : 1≤x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*Complex.I) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact LocalPrincipalSignalShiftV2.contour_shift_left_pc2 χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

theorem signal_isBigO_atTop_pc2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0<s.re})
    (hb : ∀ s : ℂ, analyticBoundaryB0<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (analyticBoundaryB0 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact LocalPrincipalSignalShiftV2.signal_isBigO_atTop_pc2 χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs)


end
end OAI.SevenEighths.LocalPrincipalSignalBoundsV2
