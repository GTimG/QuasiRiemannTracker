import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildNonunitWidth
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoFrequency
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildRowMultiplier
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The energy scale of the child of a live final daughter of a LOW child: added to the log norm of the multiplier of its
row, it is at most the second coordinate of the high chain of the first label, up to the constants of the presentation.
Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondRetainedWidth CenteredMomentSecondCanonicalNonunit
open Cycle63Moment Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The energy scale of the retained state of a live row, plus the log norm of the child multiplier of the row, is at most
the second coordinate of the high chain of the first label `first` plus `log 4 + 2 N log b + ξ/2`. The datum of the row
has the frequency radius of `first` (`hradius`) and the second pair and inactive set `(C₂, D₂, U₂)` of the prefix, the
factors `unit` are units, the fixed row `u₀` has log norm at most `ε`, and the multiplier is nonzero. The `-ε` of the
scale identity cancels the `+ε` of the coordinate when the log norm of `u₀` is at most `ε`. -/
theorem live_main_row_scale_le {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b N) (hZ : 1 < Z) (hb : 0 < b)
    (reflected left second : Bool) (first : FirstSourceLabel) (reserve ε : ℝ)
    (hfirst₁ : Supported first.1.1) (hfirst₂ : Supported first.1.2)
    (hfirst : primeSupport first.1.1 = primeSupport first.1.2)
    (hradius : g.datum.radius = frequencyRadius
      (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N first) Z ξ)
    (C₂ D₂ : Ideal O) (U₂ : Finset (CommonIndex C₂ D₂))
    (hC : g.datum.C = C₂) (hD : g.datum.D = D₂) (hU : HEq g.datum.inactive U₂)
    (u₀ : O) (unit : FirstSourceLabel → O) (hunit : ∀ l, IsUnit (unit l))
    (hu₀ : Real.logb Z (normValue u₀) ≤ ε)
    (hmult : childMultiplier left u₀ unit ⟨first, (C₂, D₂), U₂⟩ ≠ 0)
    {Bmask : ℝ} (τ : Character) (Q P : Ideal O) (hP : P ≠ 0) (hPN : (P.absNorm : ℝ) ≤ Z^Bmask) :
    (retainedState Z Bmask hZ τ Q P hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive).rowWidth +
        Real.logb Z ((Ideal.span {childMultiplier left u₀ unit ⟨first, (C₂, D₂), U₂⟩}).absNorm : ℝ) ≤
      actualHighCoordinates reflected left second first C₂ D₂ U₂ Z Mrow (Real.logb Z (volume s)) amp ξ reserve ε 2 +
        (Real.logb Z 4 + 2*(N : ℝ)*Real.logb Z b + ξ/2) := by
  have hfit := live_frequency_generators_fit (fun _ : Unit => g.datum) g.row
  change normValue (commonFrequencyGenerator g.datum.C g.datum.D) *
    normValue (nonunitFrequencyGenerator g.datum.C g.datum.D g.datum.inactive) ≤ 4 * g.datum.radius at hfit
  subst hC hD
  have hU' : g.datum.inactive = U₂ := eq_of_heq hU
  subst hU'
  rw [hradius] at hfit
  have hfun : (fun l => ((hunit l).unit : O)) = unit := funext fun l => (hunit l).unit_spec
  have hid : Real.logb Z (retainedScale (frequencyRadius
        (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N first) Z ξ)
        g.datum.C g.datum.D g.datum.inactive) +
      Real.logb Z (normValue (childMultiplier left u₀ unit ⟨first, (g.datum.C, g.datum.D), g.datum.inactive⟩)) =
    actualHighCoordinates reflected left second first g.datum.C g.datum.D g.datum.inactive Z Mrow
      (Real.logb Z (volume s)) amp ξ reserve ε 2 - ε + Real.logb Z (normValue u₀) +
      (Real.logb Z 4 + 2*(N : ℝ)*Real.logb Z b + ξ/2) := by
    have h := depth_two_scale_identity reflected left second u₀ (fun l => (hunit l).unit)
      ⟨first, (g.datum.C, g.datum.D), g.datum.inactive⟩ hfirst₁ hfirst₂ hfirst (by rw [hfun]; exact hmult)
      Z (volume s) Mrow (Real.logb Z (volume s)) amp ξ reserve ε b N hZ (volume_pos s) hb hfit
    rw [hfun] at h
    exact h
  change Real.logb Z (retainedScale g.datum.radius g.datum.C g.datum.D g.datum.inactive) +
    Real.logb Z (normValue (childMultiplier left u₀ unit ⟨first, (g.datum.C, g.datum.D), g.datum.inactive⟩)) ≤ _
  rw [hradius]
  linarith only [hid, hu₀]

/-- The scale of a row of the second expansion of the children of the first labels `first`, in the form of the facts of the
first level: the energy scale of the retained state of the live geometry `g` of the row, plus the log norm of the
multiplier `firstRowMultiplier first left u₀ unit r` of the row, is at most the second coordinate of the high chain of the
first label of the row and the supported label `label` of its second block, plus `log 4 + 2 N log b + ξ/2`. See
`live_main_row_scale_le`. -/
theorem low_row_scale_le {s₀ : Input α} {q : Chain s₀} {Z Mrow amp omega ξ b : ℝ} {N : ℕ}
    {Label : Type*} {slots : Label → Finset α} {child : (l : Label) → Input (slots l)}
    {R seed : Label → Ideal O} {K Tsec : Label → ℝ}
    (g : LiveMainGeometry s₀ q Z Mrow amp omega ξ b N) (hZ : 1 < Z) (hb : 0 < b)
    (reflected left second : Bool) (first : Label → FirstSourceLabel) (reserve ε : ℝ)
    (r : (l : Label) × ActualSecondBlockIndex (child l) (R l) (seed l) (K l) (Tsec l) Z ξ)
    (hU : ActualSecondBlockIndex.IsInactive r.2) (label : FirstSourceLabel)
    (hlabel : label = actualSecondSupportedLabel (child r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2 hU)
    (hfirst₁ : Supported (first r.1).1.1) (hfirst₂ : Supported (first r.1).1.2)
    (hfirst : primeSupport (first r.1).1.1 = primeSupport (first r.1).1.2)
    (hradius : g.datum.radius = frequencyRadius
      (firstMainFourierScale reflected (Z^Mrow) (volume s₀) Z ξ (3*amp) reserve b N (first r.1)) Z ξ)
    (hC : g.datum.C = label.1.1) (hD : g.datum.D = label.1.2) (hU' : HEq g.datum.inactive label.2.val)
    (u₀ : O) (unit : FirstSourceLabel → O) (hunit : ∀ l, IsUnit (unit l))
    (hu₀ : Real.logb Z (normValue u₀) ≤ ε)
    (hmult : firstRowMultiplier first left u₀ unit r ≠ 0)
    {Bmask : ℝ} (τ : Character) (Q P : Ideal O) (hP : P ≠ 0) (hPN : (P.absNorm : ℝ) ≤ Z^Bmask) :
    (retainedState Z Bmask hZ τ Q P hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive).rowWidth +
        Real.logb Z ((Ideal.span {firstRowMultiplier first left u₀ unit r}).absNorm : ℝ) ≤
      actualHighCoordinates reflected left second (first r.1) label.1.1 label.1.2 label.2.val Z Mrow
        (Real.logb Z (volume s₀)) amp ξ reserve ε 2 + (Real.logb Z 4 + 2*(N : ℝ)*Real.logb Z b + ξ/2) := by
  subst hlabel
  exact live_main_row_scale_le g hZ hb reflected left second (first r.1) reserve ε hfirst₁ hfirst₂ hfirst hradius
    _ _ _ hC hD hU' u₀ unit hunit hu₀ hmult τ Q P hP hPN

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
