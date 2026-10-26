/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The one pending analytic leaf is the literal marked first physical norm on
canonical initial data. All source/reflection/quantifier joins are separate. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyContract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low.Anchor
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentExceptionalAmplitudePair
open QRH.Record1252270103Source
open QRH.Record1252270103Source.High.CoupledFirst
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O

/-- Exact physical leaf. The bound is on physicalMass, not InitialAffineAt or
an arbitrary modified-energy family. Its radial bump is fixed before Z and all
moving data. The fixed eta0, Q and R0 precede degree and seminorms, matching GlobalSource;
all moving heights and profiles follow those choices. -/
def InitialMarkedPhysicalSupplier (B lam cap cross K mesh ξ ε : ℝ) (cell : ℝ → ℝ) : Prop :=
  ∀(α : Type)[Fintype α][DecidableEq α],
  ∀(rayM : Ideal O)[NeZero rayM],
  ∀(H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H),
  ∀(W : ℝ → ℂ)(hW : ContDiff ℝ ∞ W)(hsW : Function.support W⊆Set.Icc (1:ℝ) 2),
  ∀(bΦ : ℝ)(hbΦ : 2≤bΦ),∀η : Character,
  ∀η₀ : Character,∀Q : Ideal O,Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    internalQ Q η₀≤Ideal.span {(72:O)} →
  ∀R₀ : Ideal O,R₀≠0 → ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),
  ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
  ∀hZ : 1<Z,∀T : Finset α,
  ∀(θ : T → RayQuotient.Characters rayM H)(w v : T → ℝ)(t height : ℝ),
    (∀i,0≤w i) → (∀i,w i≤mesh) → 0≤height → (∀i,|v i|≤height) →
  ∀p : Profiles (1/4) (9/4),∀X₁ X₂ : ℝ,∀hX₁ : 0<X₁,∀hX₂ : 0<X₂,
    (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1 →
    cross≤∑i,w i →
  let r:=49/100-K*cell (∑i,w i)
  Z^r≤X₁ → Z^r≤X₂ →
  let Y₂:=Z^r
  let Y₁:=X₁*X₂/Y₂
  let hY₂ : 0<Y₂:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  let hY₁ : 0<Y₁:=div_pos (mul_pos hX₁ hX₂) hY₂
  let hprod : Y₁*Y₂=X₁*X₂:=div_mul_cancel₀ _ hY₂.ne'
  let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  physicalMass s (markedSourceModifier 1 1 1 1 (fun _=>1)) R₀ 1
    (fixedBadMask*idealGenerator R₀) 1 (initialRadialBump bΦ (by linarith)) Z Z ξ/volume s.toData≤
      C*(p.control controls)^2*(1+|t|+height)^degree*Z^(1+ε)

end
end QRH.Record1252270103Low.Anchor
#print axioms QRH.Record1252270103Low.Anchor.InitialMarkedPhysicalSupplier
