/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact initial-data analytic inlet: only the bounded first budget remains.
The physical contraction and all-height extensions are supplied separately. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.HeightAnchorContract
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstTruncatedHeights
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstTruncatedBalance
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialTruncated
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentExceptionalAmplitudePair Cycle61InitialMass
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.FirstTruncatedHeights
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O

def FixedSubsetTruncatedSupplier (B lam cap cross K mesh ξ ε b δ : ℝ) : Prop :=
  ∀(α : Type)[Fintype α][DecidableEq α],
  ∀(rayM : Ideal O)[NeZero rayM],
  ∀(H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H),
  ∀(W : ℝ → ℂ)(hW : ContDiff ℝ ∞ W)(hsW : Function.support W⊆Set.Icc (1:ℝ) 2),
  ∀(bΦ : ℝ)(hbΦ : 2≤bΦ),∀η : Character,
  ∀η₀ : Character,∀Q : Ideal O,Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    internalQ Q η₀≤Ideal.span {(72:O)} →
  ∀R₀ : Ideal O,R₀≠0 → ∀T : Finset α,∃degree : ℕ,∃controls : Finset (ℕ×ℕ),(0,0)∈controls ∧
  ∃C τ : ℝ,0<C ∧ 0<τ ∧ ∀ᶠZ : ℝ in Filter.atTop,
  ∀hZ : 1<Z,
  ∀(θ : T → RayQuotient.Characters rayM H)(w v : T → ℝ)(t height : ℝ),
    (∀i,0≤w i) → (∀i,w i≤mesh) → 0≤height → (∀i,|v i|≤height) → 1+|t|+height≤Z^τ →
  ∀p : Profiles (1/4) (9/4),∀X₁ X₂ : ℝ,∀hX₁ : 0<X₁,∀hX₂ : 0<X₂,
    (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1 →
    cross≤∑i,w i → b-δ≤∑i,w i → (∑i,w i)≤b →
  let r:=49/100-K*b
  Z^r≤X₁ → Z^r≤X₂ →
  let Y₂:=Z^r
  let Y₁:=X₁*X₂/Y₂
  let hY₂ : 0<Y₂:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  let hY₁ : 0<Y₁:=div_pos (mul_pos hX₁ hX₂) hY₂
  let hprod : Y₁*Y₂=X₁*X₂:=div_mul_cancel₀ _ hY₂.ne'
  let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
  TruncatedBudget (initialRadialBump bΦ (by linarith)) s
    (markedSourceModifier 1 1 1 1 (fun _=>1)) R₀ 1 Z Z ξ 1 (Real.logb Z (volume s.toData))
    τ 0 (1+|t|+height) C (zero_lt_one.trans hZ) degree
    (fun _=>(p.control controls)^2) geometryDCompensator
end
end QRH.Record1252270103Source.InitialTruncated
#print axioms QRH.Record1252270103Source.InitialTruncated.FixedSubsetTruncatedSupplier
