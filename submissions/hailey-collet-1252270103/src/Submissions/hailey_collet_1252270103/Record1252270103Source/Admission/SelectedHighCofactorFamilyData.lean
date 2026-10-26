/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal selected triple allocations for the actual annular family caller. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedHighCofactorCoordinates
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighCofactorFamily
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst Cycle61Moment Cycle61InitialMass
open Record12518109Natural.MarkedPlain Record1252270103Second
open OAI.SevenEighths.Record1252270103Source SelectedHighSlots SelectedHighCofactorCoordinates
local notation "O" => HeckeFamily.O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

structure Selection {α : Type} [Fintype α] (s : Input α) (reflected second : Bool)
    (l : FirstSourceLabel) (C₂ D₂ R : Ideal O) where
  B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1)
  τ₁ : Character
  t₁ : ℝ
  hf₁ : frozenCoefficient B₁.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0
  B₂ : actualAllocations (child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁).pools
    (if second then D₂ else C₂)
  τ₂ : Character
  t₂ : ℝ
  hf₂ : let s₁:=child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁
    frozenCoefficient B₂.val (if second then D₂ else C₂)
      (R*(if reflected then l.1.2 else l.1.1)) s₁.ν s₁.W s₁.P≠0
  Cf : Ideal O
  Bf : actualAllocations (child (child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁)
    (if second then D₂ else C₂) (R*(if reflected then l.1.2 else l.1.1)) B₂ τ₂ t₂).pools Cf
  τf : Character
  tf : ℝ
  hff : let s₂:=(child (child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁)
      (if second then D₂ else C₂) (R*(if reflected then l.1.2 else l.1.1)) B₂ τ₂ t₂)
    frozenCoefficient Bf.val Cf ((R*(if reflected then l.1.2 else l.1.1))*(if second then D₂ else C₂))
      s₂.ν s₂.W s₂.P≠0

namespace Selection
variable {α : Type} [Fintype α] {s : Input α} {reflected second : Bool}
    {l : FirstSourceLabel} {C₂ D₂ R : Ideal O}
variable (d : Selection s reflected second l C₂ D₂ R)

def firstInput := child s (if reflected then l.1.2 else l.1.1) R d.B₁ d.τ₁ d.t₁
def finalInput := child (child d.firstInput (if second then D₂ else C₂)
  (R*(if reflected then l.1.2 else l.1.1)) d.B₂ d.τ₂ d.t₂)
  d.Cf ((R*(if reflected then l.1.2 else l.1.1))*(if second then D₂ else C₂)) d.Bf d.τf d.tf

def full : Finset α := finalImage d.B₁.val d.B₂.val d.Bf.val
def live (w : α→ℝ) (wmin : ℝ) : ℝ := ∑i∈largeSlots d.full w wmin,w i
def forced (Z : ℝ) : ℝ := Real.logb Z (d.Cf.absNorm:ℝ)
def denom : ℝ := (max 1 (forcedProfileCost d.firstInput))^2

def raw (U : Finset (CommonIndex C₂ D₂)) (Z M amp ξ reserve : ℝ) : ℝ :=
  secondAllocationCoefficient s reflected second l R d.B₁ d.τ₁ d.t₁ C₂ D₂ U d.B₂ d.τ₂ d.t₂
    Z M amp ξ reserve

def coordinate (U : Finset (CommonIndex C₂ D₂)) (Z M amp ξ reserve err errv annular : ℝ)
    (w : α→ℝ) (wmin : ℝ) (T : Finset α) : Fin 4→ℝ :=
  cofactorCoordinates reflected second l C₂ D₂ U Z M (Real.logb Z (volume s)) amp ξ reserve err errv
    (d.forced Z) (d.live w wmin) (∑j∈largeSlots T w wmin,w j) annular

theorem denom_pos : 0<d.denom := sq_pos_of_pos (zero_lt_one.trans_le (le_max_left _ _))

theorem denom_le_original : d.denom≤(max 1 (forcedProfileCost s))^2 := by
  apply pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
  exact max_le_max_left 1 (child_forcedProfileCost s _ R d.B₁ d.τ₁ d.t₁)

theorem geometry (U : Finset (CommonIndex C₂ D₂))
    (N : ℕ) (upper Z M amp ξ reserve err errv wmin b δ allowance : ℝ)
    (hN : Fintype.card α≤N) (hupper : 1≤upper) (hsupper : s.upper≤upper)
    (hslower : 1≤s.lower) (hZ : 1<Z) (hmin : 0≤wmin)
    (w : α→ℝ) (hscale : ∀i,s.P i=Z^(w i)) (hw : ∀i,0≤w i)
    (htotal : b-δ≤∑i,w i) (hwidth : (∑i,w i)≤b)
    (hloss : δ+(N:ℝ)*wmin≤2*allowance) (T : Finset α) (hT : T⊆d.full) :
    0≤d.forced Z ∧ (∑i∈largeSlots T w wmin,w i)≤d.live w wmin ∧ d.live w wmin≤b ∧
    b-2*allowance≤d.live w wmin+Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)+d.forced Z ∧
    d.finalInput.X₁*d.finalInput.X₂≤
      Z^(d.coordinate U Z M amp ξ reserve err errv (3*(N:ℝ)*Real.logb Z upper) w wmin T 3-∑i∈T,w i) ∧
    d.finalInput.X₁≤s.X₁ ∧ d.finalInput.X₂≤s.X₂ ∧ d.finalInput.Y₁≤s.Y₁ ∧ d.finalInput.Y₂≤s.Y₂ := by
  have hg:=actual_coordinate_geometry s reflected second l R d.B₁ d.τ₁ d.t₁ C₂ D₂ d.B₂ d.τ₂ d.t₂
    d.Cf d.Bf d.τf d.tf U N upper Z M amp ξ reserve err errv wmin b δ allowance
    hN hupper hsupper hslower hZ hmin w hscale hw htotal hwidth hloss T hT d.hf₁ d.hf₂ d.hff
  exact ⟨hg.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2.1,
    hg.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.1,
    hg.2.2.2.2.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem raw_caps (X₁ X₂ Y₁ Y₂ : ℝ) (hx₁ : s.X₁≤X₁) (hx₂ : s.X₂≤X₂)
    (hy₁ : s.Y₁≤Y₁) (hy₂ : s.Y₂≤Y₂) :
    d.finalInput.X₁≤X₁ ∧ d.finalInput.X₂≤X₂ ∧ d.finalInput.Y₁≤Y₁ ∧ d.finalInput.Y₂≤Y₂ :=
  SelectedForcedGeometry.third_child_raw_caps s _ R d.B₁ d.τ₁ d.t₁ _ d.B₂ d.τ₂ d.t₂
    d.Cf d.Bf d.τf d.tf X₁ X₂ Y₁ Y₂ hx₁ hx₂ hy₁ hy₂

end Selection
end
end QRH.Record1252270103Source.Admission.SelectedHighCofactorFamily
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorFamily.Selection.denom_pos
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorFamily.Selection.denom_le_original
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorFamily.Selection.geometry

#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorFamily.Selection.raw_caps
