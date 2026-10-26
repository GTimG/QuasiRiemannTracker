/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal canonical input fields used by both actual selected HIGH point applications. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularHighParameters
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularPhase
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalCofactorBox
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialPhysicalChildBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.Admission.SelectedRegularHighPoint
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open Cycle61Moment Cycle61InitialMass LocalMoment Record12518109Raw
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Record1252270103Finite PhysicalAnalytic High.GlobalPhysical
open SelectedRegularSourceData SelectedHighCofactorFamily QRH.Record1252270103Low
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
variable {α:Type}[Fintype α]

structure Canonical (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(R₀:Ideal O)(Z:ℝ)(hZ:1<Z)(s:Input α) where
  w : α→ℝ
  v : α→ℝ
  ray : α→RayQuotient.Characters M H
  origin : ℝ
  p : Profiles (1/4) (9/4)
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  product : Y₁*Y₂=X₁*X₂
  input : s=initialInput M H hH W hW hWs Z (zero_lt_one.trans hZ) ηanchor η₀ R₀ ray w v origin
    p (by norm_num) X₁ X₂ Y₁ Y₂ X₁_pos X₂_pos Y₁_pos Y₂_pos product

namespace Canonical
variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{hH:RayOrthogonality.globalUnits M≤H}
  {W:ℝ→ℂ}{hW:ContDiff ℝ ∞ W}{hWs:Function.support W⊆Icc (1:ℝ) 2}
  {ηanchor η₀:Character}{R₀:Ideal O}{Z:ℝ}{hZ:1<Z}{s:Input α}
  (c:Canonical M H hH W hW hWs ηanchor η₀ R₀ Z hZ s)

theorem fields : s.η=ηanchor ∧ s.lower=1 ∧ s.upper=2 ∧
    s.W₁=(c.p.profile 0:ℝ→ℂ) ∧ s.W₂=(c.p.profile 1:ℝ→ℂ) ∧
    (∀i,s.P i=Z^(c.w i)) ∧ (∀i,s.hi i=2) ∧ s.b₁=9/4 ∧ s.b₂=9/4 ∧
    (∀i,s.slots i=CenteredMomentPrimeSlot.primePool M H 2 (Z^(c.w i))) := by
  simp [c.input,initialInput]

include c in
theorem ordinary_lower : (∀x,s.W₁ x≠0→1/4≤x) ∧ (∀x,s.W₂ x≠0→1/4≤x) := by
  constructor
  · intro x hx;rw [c.fields.2.2.2.1] at hx;exact (c.p.support 0 hx).1
  · intro x hx;rw [c.fields.2.2.2.2.1] at hx;exact (c.p.support 1 hx).1

theorem volume_cap (n:Source)(hB:(n.B:ℝ)≤1)(hL:1≤(n.L:ℝ))(hw:∀i,0≤c.w i)
    (hadm:(globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z c.X₁) (length Z c.X₂) (∑i,c.w i) 1):volume s≤Z := by
  rw [c.input]
  exact InitialPhysical.initial_volume_cap M H hH W hW hWs Z (zero_lt_one.trans hZ) ηanchor η₀ R₀
    c.ray c.w c.v c.origin c.p c.X₁ c.X₂ c.Y₁ c.Y₂ c.X₁_pos c.X₂_pos c.Y₁_pos c.Y₂_pos c.product
    (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hZ hB hL hw hadm

theorem long_corners (n:Source)(r:ℝ)(hB:(n.B:ℝ)≤1)(hL:1≤(n.L:ℝ))(hw:∀i,0≤c.w i)
    (hadm:(globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z c.X₁) (length Z c.X₂) (∑i,c.w i) 1)
    (hr:0≤r)(hl1:Z^r≤c.X₁)(hl2:Z^r≤c.X₂)(href:c.Y₂=Z^r):
    s.X₁≤Z ∧ s.X₂≤Z ∧ s.Y₁≤Z ∧ s.Y₂≤Z ∧ s.X₁*s.X₂≤Z ∧ 1≤volume s := by
  have hh:=SelectedRegularCanonicalGeometry.initial_long_corners M H hH W hW hWs Z hZ ηanchor η₀ R₀
    c.ray c.w c.v c.origin c.p c.X₁ c.X₂ c.Y₁ c.Y₂ c.X₁_pos c.X₂_pos c.Y₁_pos c.Y₂_pos c.product
    (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) r hB hL hw hadm hr hl1 hl2 href
  rw [c.input]
  refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,?_⟩
  change 1≤c.X₁*c.X₂*(∏i,Z^(c.w i))
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le ((Real.one_le_rpow hZ.le hr).trans hl1)
      ((Real.one_le_rpow hZ.le hr).trans hl2))
    (Finset.one_le_prod₀ (fun i _=>Real.one_le_rpow hZ.le (hw i)))

theorem radius_cap (N:ℕ)(hN:Fintype.card α≤N)(n:Source)(hB:(n.B:ℝ)≤1)(hL:1≤(n.L:ℝ))
    (hw:∀i,0≤c.w i)(hadm:(globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z c.X₁) (length Z c.X₂) (∑i,c.w i) 1)
    (habsorb:(2:ℝ)^N*(9/4)^2*Z≤Z^(2:ℝ)):sourceRadius s≤Z^(2:ℝ) := by
  rw [c.input]
  exact (InitialPhysical.initial_source_radius_cap M H hH W hW hWs Z (zero_lt_one.trans hZ)
    ηanchor η₀ R₀ c.ray c.w c.v c.origin c.p c.X₁ c.X₂ c.Y₁ c.Y₂ c.X₁_pos c.X₂_pos c.Y₁_pos c.Y₂_pos c.product
    N hN (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hZ hB hL hw hadm).trans habsorb

theorem child_radius (C R:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (hw:∀i,0≤c.w i):sourceRadius (child s C R B τ t)≤sourceRadius s := by
  apply InitialPhysical.child_source_radius_le s C R B τ t
  · intro i;rw [c.fields.2.2.2.2.2.2.1];norm_num
  · intro i;rw [c.fields.2.2.2.2.2.1];exact Real.one_le_rpow hZ.le (hw i)
  · rw [c.fields.2.2.2.2.2.2.2.1];norm_num
  · rw [c.fields.2.2.2.2.2.2.2.2.1];norm_num

end Canonical

/-- The actual signed nonzero integer frequency forces the radial exponent nonnegative. -/
theorem radial_nonnegative {left:Bool}{u:O}{unit:FirstSourceLabel→O}
    (key:NonzeroJointSourceLabel left u unit)(Z x:ℝ)(hZ:1<Z)
    (h:rawFrequencyNorm (nonzeroJointSourceRow key)≤Z^x):0≤x := by
  have hi:Ideal.span {(nonzeroJointSourceRow key).val}≠0:=by
    change Ideal.span {(nonzeroJointSourceRow key).val}≠⊥
    intro hh
    exact (nonzeroJointSourceRow key).property (Ideal.span_singleton_eq_bot.mp hh)
  have hn:(1:ℝ)≤rawFrequencyNorm (nonzeroJointSourceRow key):=by
    unfold rawFrequencyNorm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi)
  by_contra hx
  have hlt:Z^x<1:=Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hx)
  linarith
end
end QRH.Record1252270103Source.Admission.SelectedRegularHighPoint
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighPoint.Canonical.long_corners
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighPoint.Canonical.radius_cap
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighPoint.radial_nonnegative
