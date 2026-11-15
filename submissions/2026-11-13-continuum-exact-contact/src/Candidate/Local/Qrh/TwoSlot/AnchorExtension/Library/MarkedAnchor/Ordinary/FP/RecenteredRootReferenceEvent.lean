/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
One event pays fixed conductor, support and dimension factors for the
kept reference. All moving rectangles follow this event.
Modified by Sil (2026-10-26): threaded through the parametric root: StepData D and StepGates G (RootParameters.omegaLoss/omega_spec/NeedsCentering/centeredExponent/reference_gates G in place of the FP RepairedRootParameters face literals), Setup M H D, the explicit root input hs₀ : s₀ ≤ markedWidth, and the face cap c ≤ 1/6 (Setup.hD) in place of 3/50; numeric omega bound 1/10⁷ (RootParameters) in place of 1/10¹⁰.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceEvent`; `reference_total_cap` (a consequence
of the removed native reference gates, used only by the native reference proof) is removed.
-/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceDictionary

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceEvent
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSecondHeightFamily MixedFirstReferenceEnergy
open Qrh.MarkedAnchor.Ordinary.RootParameters
variable {D:Qrh.MarkedAnchor.Ordinary.StepData}(G:Qrh.MarkedAnchor.Ordinary.StepGates D)

def conductorUpper (η:Character)(bΦ Z:ℝ) : ℝ :=
  max 1 (conductorFactor η fixedBadMask 1*(bΦ*Z))

def Event (N:ℕ)(η:Character)(bΦ ε Z:ℝ) : Prop :=
  1<Z ∧ 16≤Z ∧ ((9/4+4:ℝ)*(9/4)*2^N≤Z^(omegaLoss G ε)) ∧
    bΦ*Z≤Z^(1+omegaLoss G ε) ∧ conductorUpper η bΦ Z≤Z^(1+2*omegaLoss G ε)

theorem eventual_event (N:ℕ)(η:Character)(bΦ ε:ℝ)(hε:0<ε) :
    ∀ᶠ Z:ℝ in atTop,Event G N η bΦ ε Z := by
  have hω:0<omegaLoss G ε := (omega_spec G ε hε).1
  have hp (A:ℝ) : ∀ᶠ Z:ℝ in atTop,A≤Z^(omegaLoss G ε) :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hω)) A
  filter_upwards [eventually_ge_atTop (16:ℝ),hp ((9/4+4:ℝ)*(9/4)*2^N),
    hp bΦ,hp (conductorFactor η fixedBadMask 1*bΦ)] with Z hZ16 hdim hb hc
  have hZ:1<Z := by linarith
  have hz:0<Z := zero_lt_one.trans hZ
  have hb':bΦ*Z≤Z^(1+omegaLoss G ε) := by
    calc
      _≤Z^(omegaLoss G ε)*Z := mul_le_mul_of_nonneg_right hb hz.le
      _=_ := by rw [Real.rpow_add hz,Real.rpow_one];ring
  have hc':conductorFactor η fixedBadMask 1*(bΦ*Z)≤Z^(1+omegaLoss G ε) := by
    calc
      _=(conductorFactor η fixedBadMask 1*bΦ)*Z := by ring
      _≤Z^(omegaLoss G ε)*Z := mul_le_mul_of_nonneg_right hc hz.le
      _=_ := by rw [Real.rpow_add hz,Real.rpow_one];ring
  have hunit:1≤Z^(1+omegaLoss G ε) := Real.one_le_rpow hZ.le (by linarith)
  have hupper:conductorUpper η bΦ Z≤Z^(1+omegaLoss G ε) := max_le hunit hc'
  refine ⟨hZ,hZ16,hdim,hb',?_⟩
  exact hupper.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

theorem event_dimension {N n:ℕ}{η:Character}{bΦ ε Z:ℝ}(hn:n≤N)
    (h:Event G N η bΦ ε Z) : ((9/4+4:ℝ)*(9/4)*2^n)≤Z^(omegaLoss G ε) :=
  (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hn) (by norm_num)).trans h.2.2.1

theorem conductor_upper_gates {N:ℕ}{η:Character}{bΦ ε Z Lcap:ℝ}(hε:0<ε)
    (hLcap:8≤Lcap)(h:Event G N η bΦ ε Z) :
    1≤conductorUpper η bΦ Z ∧ conductorUpper η bΦ Z≤Z^(Lcap+8) ∧
      conductorUpper η bΦ Z≤Z^((1+omegaLoss G ε)+omegaLoss G ε) ∧
      conductorFactor η fixedBadMask 1*(bΦ*Z)≤conductorUpper η bΦ Z := by
  have hω:omegaLoss G ε≤1/10000000 := (omega_spec G ε hε).2.2.2
  refine ⟨le_max_left _ _,?_,?_,le_max_right _ _⟩
  · exact h.2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le h.1.le (by linarith))
  · convert h.2.2.2.2 using 1 <;> congr 1 <;> ring

end
end Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootReferenceEvent
