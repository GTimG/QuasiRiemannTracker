import Candidate.Target830.Source.LowPhysical.AffineSourceGates
import Candidate.Target830.Source.CellGeometry
import Candidate.Cycle63.Physical.CoarseEnergy
import Candidate.Cycle63.Physical.SecondZero.Source
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryExceptionalErrorNormPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePoolCaps
import Candidate.Target830.Source.Reconstruction.GeometryAffinePrimeGates
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Cycle63.Moment.InitialState
import Candidate.Cycle63.Moment.CellGeometry

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Target830.Source.Reconstruction
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CanonicalQuadraticSieve
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedRayDictionary CenteredMomentPrimeElements
open CenteredMomentCommonAllocationSum
open Cycle63InitialSource Cycle63Moment
local notation "O" => HeckeFamily.O

variable {plane : SourcePlane}
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineExceptionalFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

/-- Actual amplifier primes are coprime to every stored first-child slot,
including slots whose smooth coefficient vanishes. The first allocation
and both heights are chosen after the common scale threshold. -/
theorem eventual_actual_affine_exceptional_child_coprime
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (mesh : ℝ) (hmesh : mesh<Source.amplifierMinimum/2) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι : Type*}[Fintype ι][DecidableEq ι]
        (η₀ : Character)(θ : ι→RayQuotient.Characters rayM H)
        (w σ freq : ι→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,w i≤ mesh) → ∀beta : ℝ,widthLower≤beta → beta≤widthUpper →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(plane.amp beta))
      ∀(q : elementPool P)(C R : Ideal O)(B : actualAllocations inp.pools C)
        (τ : Character)(height : ℝ),
      ∀i I,I∈(child inp C R B τ height).slots i→IsCoprime (Ideal.span {q.val}) I := by
  filter_upwards [eventual_geometry_affine_prime_coprime (plane:=plane) rayM H hH Sbad hbad 2 mesh hmesh]
    with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hwm beta hb₁ hb₂ inp P q C R B τ height
  have hm : Matches rayM H hH inp η₀ θ w σ freq W 2 Z := by
    constructor <;> intros <;> rfl
  exact actual_child_full_slot_coprime inp (Ideal.span {q.val})
    (hz.2 beta hb₁ hb₂ inp η₀ θ w σ freq W hm hwm q) C R B τ height

/-- Fixed-parent specialization retains the exact conductor; it does not
require a threshold uniform over arbitrary moving NaturalState characters. -/
theorem affine_exceptional_fixed_parent_character (η : Character) (Q : Ideal O)
    (Φ : 𝓢(ℝ,ℂ)) (bΦ Z : ℝ) (hZ : 1<Z)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ) (hp : ∀x,0≤(Φ x).re) :
    (fixedParentState η Q Φ bΦ Z 1 hZ (by norm_num) hs hp).character=η ∧
      (fixedParentState η Q Φ bΦ Z 1 hZ (by norm_num) hs hp).characterWidth=
        Real.logb Z (η.modulus.absNorm:ℝ) := ⟨rfl,rfl⟩

/-- The literal logarithmic volume is paid by the original canonical cell,
before extraction changes any child scale or allocation. -/
theorem affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (Z n₁ n₂ slots : ℝ)
    (hvolume : Real.logb Z (volume s)=n₁+n₂+slots)
    (hslots : (17/500:ℝ)≤ slots ∧ slots≤1/25)
    (hcone : n₁+n₂+plane.lambda*slots≤plane.B) :
    Real.logb Z (volume s)≤plane.total
      (Source.widthCellUpper slots) := by
  rw [hvolume]
  exact Source.normalized_cell_volume plane hslots hcone

/-- The canonical-cell ledger applied to the literal affine input; the
volume identity is proved here, rather than supplied as a source premise. -/
theorem actual_affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (θ : ι→RayQuotient.Characters rayM H)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : ι→ℝ) (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    {Z bΦ : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hZ : 1<Z)
    (hlo₁ : (81/200:ℝ)≤length Z X₁) (hlo₂ : (81/200:ℝ)≤length Z X₂)
    (hslots : (17/500:ℝ)≤∑i,w i ∧ (∑i,w i)≤1/25)
    (hcone : length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤plane.B) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    Real.logb Z (volume inp)≤plane.total
      (Source.widthCellUpper (∑i,w i)) := by
  intro inp
  apply affine_exceptional_volume_cell (plane:=plane) inp Z (length Z X₁) (length Z X₂) (∑i,w i) _ hslots hcone
  exact Source.LowPhysical.affine_volume_log_exact rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂ hZ
    (by norm_num) (by simpa only [mul_one] using hlo₁) (by simpa only [mul_one] using hlo₂)

/-- These are the main exponent after its one prime cancellation and the
extracted-error exponent after its already included 56/P payment. All
density, shell, frequency and height fees are charged to loss. -/
theorem affine_exceptional_exponent_saving (beta logV ell loss : ℝ)
    (hbeta : widthLower≤beta ∧ beta≤widthUpper)
    (hV : logV≤plane.total beta) (hell : 0≤ell) (hloss : loss≤1/100) :
    loss+logV-(1+ell)+4*plane.amp beta+2*(ell/4)/3≤-(1/100:ℝ) ∧
      loss+logV-(1+ell)+3*(3*plane.amp beta)/2+2*(ell/4)/3≤-(1/100:ℝ) := by
  obtain ⟨hg,hmin,hamin,hamp,h9,hm,he,hrest⟩:=Source.source_guards plane hbeta
  constructor <;> linarith

/-- One concrete choice pays the larger error density exponent 252, the
original label/projector shell, and both independent height windows. -/
theorem affine_exceptional_small_loss (εaffine omega heightLoss primeLoss : ℝ)
    (hε : 0<εaffine)
    (hω : omega≤33*geometryLossUnit 1 εaffine/128)
    (hh : heightLoss≤geometryLossUnit 1 εaffine/8)
    (hp : primeLoss≤geometryLossUnit 1 εaffine/8) :
    let μ:=geometryLossUnit 1 εaffine
    0<μ/128 ∧ 0<μ/2048 ∧
      2*(μ/128)+2*(μ/128)+252*(μ/2048)+5*omega/6+
        3*(μ/128)+3*(μ/128)+heightLoss+primeLoss≤1/100 := by
  intro μ
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hcap : μ≤1/128 := by
    exact (min_le_right (εaffine/128) _).trans
      ((min_le_right ((7/30000000)*1/128) _).trans (min_le_right (1/128) (1/128)))
  refine ⟨by positivity,by positivity,?_⟩
  change omega≤33*μ/128 at hω
  change heightLoss≤μ/8 at hh
  change primeLoss≤μ/8 at hp
  linarith

end
end OAI.SevenEighths.Target830.Source.Reconstruction
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.eventual_actual_affine_exceptional_child_coprime
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.affine_exceptional_fixed_parent_character
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.affine_exceptional_volume_cell
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.actual_affine_exceptional_volume_cell
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.affine_exceptional_exponent_saving
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.affine_exceptional_small_loss
