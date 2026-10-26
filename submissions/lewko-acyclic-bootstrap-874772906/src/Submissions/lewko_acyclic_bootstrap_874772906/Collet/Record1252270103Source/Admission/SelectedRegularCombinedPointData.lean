/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Shared canonical data and fixed-scale gates for the actual LOW/HIGH point fusion. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularHighPointSome
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularHighPointNatural
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularLowPoint
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularPointBudget
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularCombinedPoint
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization
open Cycle61InitialMass Cycle61Moment LocalMoment Record1252270103Finite
open QRH.Record1252270103Low SelectedRegularSourceData SelectedRegularHighPoint
open High.GlobalPhysical SelectedRegularLowPoint
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

variable {α:Type}[Fintype α]{M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Z:ℝ}

def initialCanonical (i:Initial (α:=α) M H Z)(hH:RayOrthogonality.globalUnits M≤H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (hZ:1<Z)(ηanchor η₀:Character)(R₀:Ideal O):
    Canonical M H hH W hW hWs ηanchor η₀ R₀ Z hZ (i.input hH W hW hWs hZ ηanchor η₀ R₀) where
  w:=i.w
  v:=i.freq
  ray:=i.θ
  origin:=i.t₀
  p:=i.p
  X₁:=i.X₁
  X₂:=i.X₂
  Y₁:=i.Y₁
  Y₂:=i.Y₂
  X₁_pos:=i.hX₁
  X₂_pos:=i.hX₂
  Y₁_pos:=i.hY₁
  Y₂_pos:=i.hY₂
  product:=i.same
  input:=rfl

/-- The eventual guard precedes every moving input and selected row family. -/
theorem eventual_scale_guards (N:ℕ)(θ ξ:ℝ)(hθ:0<θ)(hξ:0≤ξ)(hξθ:ξ≤θ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ (9/4:ℝ)^2≤Z ∧
      (2:ℝ)^N*(9/4)^2*Z≤Z^(2:ℝ) ∧ (2:ℝ)^(3*N)≤Z ∧
      0≤frequencyLoss Z 32 ξ+θ ∧ frequencyLoss Z 32 ξ+θ≤2*θ := by
  have hp:∀ᶠZ:ℝ in atTop,(128:ℝ)≤Z^(θ/2):=
    (tendsto_rpow_atTop (by positivity : 0<θ/2)).eventually (eventually_ge_atTop _)
  filter_upwards [InitialPhysical.eventual_radius_absorption N 1 (by norm_num),
    eventually_ge_atTop ((9/4:ℝ)^2),eventually_ge_atTop ((2:ℝ)^(3*N)),hp] with Z hZ hlarge hann hpow
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:Real.logb Z (128:ℝ)≤θ/2:=by
    have hh:=Real.logb_le_logb_of_le hZ.1 (by norm_num : (0:ℝ)<128) hpow
    simpa only [Real.logb_rpow hz hZ.1.ne'] using hh
  have hfreq:=frequencyLoss_nonneg Z 32 ξ hZ.1 (by norm_num) hξ
  refine ⟨hZ.1,hlarge,?_,hann,add_nonneg hfreq hθ.le,?_⟩
  · simpa only [show (1:ℝ)+1=2 by norm_num] using hZ.2
  · dsimp [frequencyLoss]
    norm_num at hlog ⊢
    linarith

theorem low_loss_eq (n:Source)(θ εslot:ℝ)(N:ℕ):
    SelectedRegularLowPoint.lowExponent n θ εslot N=regularLowLoss (n.allowance:ℝ) θ εslot N:=rfl
end
end QRH.Record1252270103Source.Admission.SelectedRegularCombinedPoint
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCombinedPoint.eventual_scale_guards
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCombinedPoint.low_loss_eq
