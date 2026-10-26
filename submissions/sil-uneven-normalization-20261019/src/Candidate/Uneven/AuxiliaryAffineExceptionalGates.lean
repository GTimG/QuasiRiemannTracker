import Candidate.Uneven.AuxiliaryCellGeometry
import Candidate.Cycle63.Physical.CoarseEnergy
import Candidate.Cycle63.Physical.SecondZero.Source
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorCoprime
import Candidate.Cycle63.Arithmetic.LocalReserves
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeElements
import Candidate.Uneven.AuxiliaryPhysicalGates
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
import Candidate.Cycle63.Physical.InitialMass.GeometryExceptionalErrorNormPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePoolCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Cycle63.Moment.InitialState
import Candidate.Cycle63.Moment.CellGeometry

/- Original module: Candidate.Uneven.AuxiliaryAffinePrimeGates. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryReconstruction
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAllocatedRayDictionary
open CenteredMomentAmplificationSlotGap CenteredMomentPrimeElements
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance affinePrimeGatesFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- One threshold separates every amplifier cell from all stored slots.
It does not discard entries whose smooth profile happens to vanish. -/
theorem eventual_geometry_affine_prime_coprime
    (S : Finset (Ideal O)) (hS : fixedBadPrimes⊆S) (b mesh : ℝ)
    (hmesh : mesh< Sil.Uneven.AuxiliarySource.amplifierMinimum/2) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀beta : ℝ,Sil.Uneven.AuxiliarySource.widthLo≤ beta → beta≤ Sil.Uneven.AuxiliarySource.widthHi →
      let P:=CenteredMomentPrimePool.primePool M H S (1/2) 1
        (Z^(Sil.Uneven.AuxiliarySource.amp beta))
      ∀{α : Type*}[Fintype α][DecidableEq α]
        (s : Input α)(η₀ : Character)(θ : α→RayQuotient.Characters M H)
        (w σ v : α→ℝ)(W : ℝ→ℂ),
        Matches M H hH s η₀ θ w σ v W b Z → (∀i,w i≤ mesh) →
        ∀q : elementPool P,∀i I,I∈s.slots i→IsCoprime (Ideal.span {q.val}) I := by
  let ell : ℝ:=Sil.Uneven.AuxiliarySource.amplifierMinimum/2
  have hell : 0< ell := by norm_num [ell,Sil.Uneven.AuxiliarySource.amplifierMinimum]
  filter_upwards [eventually_scale_gap (max 1 b) mesh ell hmesh,
    (tendsto_rpow_atTop hell).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hgap hlarge hZ
  refine ⟨hZ,?_⟩
  intro beta hlo hhi P α _ _ s η₀ θ w σ v W hm hw q i I hI
  have hz : 0< Z:=zero_lt_one.trans hZ
  have hp : ∀Q∈P,Prime Q:=fun Q hQ=>(primePool_data M H S hS _ _ _ Q hQ).1
  have hbad : ∀Q∈P,Q∉fixedBadPrimes:=fun Q hQ=>(primePool_data M H S hS _ _ _ Q hQ).2
  have hq:=elementPool_data P hp hbad q.val q.property
  have hn:=PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos hz _) (Finset.mem_sdiff.mp hq.2.1).1
  have hlow : Z^ell≤(1/2:ℝ)*Z^(Sil.Uneven.AuxiliarySource.amp beta) := by
    have ha : ell+ell≤ Sil.Uneven.AuxiliarySource.amp beta := by
      have h:=(Sil.Uneven.AuxiliarySource.scheduling_guards  ⟨hlo,hhi⟩).2.2.1
      dsimp only [ell]
      linarith
    have hr:=Real.rpow_le_rpow_of_exponent_le hZ.le ha
    rw [Real.rpow_add hz] at hr
    have hnonneg:=Real.rpow_nonneg hz.le ell
    have hx : 2 * Z^ell ≤ Z^(Sil.Uneven.AuxiliarySource.amp beta) :=
      (mul_le_mul_of_nonneg_right hlarge hnonneg).trans hr
    calc
      Z^ell = (1/2:ℝ) * (2 * Z^ell) := by ring
      _ ≤ (1/2:ℝ) * Z^(Sil.Uneven.AuxiliarySource.amp beta) :=
        mul_le_mul_of_nonneg_left hx (by norm_num)
  exact actual_full_slot_coprime M H hH s η₀ θ w σ v W b Z mesh ell hZ.le hm hw
    (Ideal.span {q.val}) (hp _ hq.2.1)
    (hlow.trans (by simpa only [mul_comm] using hn.1.le)) hgap.2 i I hI

end
end OAI.SevenEighths.AuxiliaryReconstruction
end

/- Original module: Candidate.Uneven.AuxiliaryAffineExceptionalGates. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.AuxiliaryReconstruction
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

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineExceptionalFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤ H)

/-- Actual amplifier primes are coprime to every stored first-child slot,
including slots whose smooth coefficient vanishes. The first allocation
and both heights are chosen after the common scale threshold. -/
theorem eventual_actual_affine_exceptional_child_coprime
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (mesh : ℝ) (hmesh : mesh< Sil.Uneven.AuxiliarySource.amplifierMinimum/2) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{ι : Type*}[Fintype ι][DecidableEq ι]
        (η₀ : Character)(θ : ι→RayQuotient.Characters rayM H)
        (w σ freq : ι→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,w i≤ mesh) → ∀beta : ℝ,Sil.Uneven.AuxiliarySource.widthLo≤ beta → beta≤ Sil.Uneven.AuxiliarySource.widthHi →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(Sil.Uneven.AuxiliarySource.amp beta))
      ∀(q : elementPool P)(C R : Ideal O)(B : actualAllocations inp.pools C)
        (τ : Character)(height : ℝ),
      ∀i I,I∈(child inp C R B τ height).slots i→IsCoprime (Ideal.span {q.val}) I := by
  filter_upwards [eventual_geometry_affine_prime_coprime  rayM H hH Sbad hbad 2 mesh hmesh]
    with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hwm beta hb₁ hb₂ inp P q C R B τ height
  have hm : Matches rayM H hH inp η₀ θ w σ freq W 2 Z := by
    constructor <;> intros <;> rfl
  exact actual_child_full_slot_coprime inp (Ideal.span {q.val})
    (hz.2 beta hb₁ hb₂ inp η₀ θ w σ freq W hm hwm q) C R B τ height


/-- The literal logarithmic volume is paid by the original canonical cell,
before extraction changes any child scale or allocation. -/
theorem affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (Z n₁ n₂ slots : ℝ)
    (hvolume : Real.logb Z (volume s)=n₁+n₂+slots)
    (hslots : (1/50:ℝ)≤ slots ∧ slots≤7/250)
    (hcone : n₁+n₂+Sil.Uneven.AuxiliarySource.lambda*slots≤ Sil.Uneven.AuxiliarySource.B) :
    Real.logb Z (volume s)≤ Sil.Uneven.AuxiliarySource.total
      (Sil.Uneven.AuxiliarySource.widthCellUpper slots) := by
  rw [hvolume]
  exact Sil.Uneven.AuxiliarySource.normalized_cell_volume hslots hcone

/-- The canonical-cell ledger applied to the literal affine input; the
volume identity is proved here, rather than supplied as a source premise. -/
theorem actual_affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (θ : ι→RayQuotient.Characters rayM H)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : ι→ℝ) (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    {Z bΦ : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hZ : 1< Z)
    (hlo₁ : (81/200:ℝ)≤ length Z X₁) (hlo₂ : (81/200:ℝ)≤ length Z X₂)
    (hslots : (1/50:ℝ)≤∑i,w i ∧ (∑i,w i)≤7/250)
    (hcone : length Z X₁+length Z X₂+Sil.Uneven.AuxiliarySource.lambda*(∑i,w i)≤ Sil.Uneven.AuxiliarySource.B) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    Real.logb Z (volume inp)≤ Sil.Uneven.AuxiliarySource.total
      (Sil.Uneven.AuxiliarySource.widthCellUpper (∑i,w i)) := by
  intro inp
  apply affine_exceptional_volume_cell  inp Z (length Z X₁) (length Z X₂) (∑i,w i) _ hslots hcone
  exact AuxiliaryPhysical.affine_volume_log_exact rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂ hZ
    (by norm_num) (by simpa only [mul_one] using hlo₁) (by simpa only [mul_one] using hlo₂)

/-- These are the main exponent after its one prime cancellation and the
extracted-error exponent after its already included 56/P payment. All
density, shell, frequency and height fees are charged to loss. -/
theorem affine_exceptional_exponent_saving (beta logV ell loss : ℝ)
    (hbeta : Sil.Uneven.AuxiliarySource.widthLo≤ beta ∧ beta≤ Sil.Uneven.AuxiliarySource.widthHi)
    (hV : logV≤ Sil.Uneven.AuxiliarySource.total beta) (hell : 0≤ ell) (hloss : loss≤1/100) :
    loss+logV-(1+ell)+4*Sil.Uneven.AuxiliarySource.amp beta+2*(ell/4)/3≤-(1/100:ℝ) ∧
      loss+logV-(1+ell)+3*(3*Sil.Uneven.AuxiliarySource.amp beta)/2+2*(ell/4)/3≤-(1/100:ℝ) := by
  obtain ⟨hg,hmin,hamin,hamp,h9,hm,he,hrest⟩:=Sil.Uneven.AuxiliarySource.scheduling_guards  hbeta
  constructor <;> linarith

/-- One concrete choice pays the larger error density exponent 252, the
original label/projector shell, and both independent height windows. -/
theorem affine_exceptional_small_loss (εaffine omega heightLoss primeLoss : ℝ)
    (hε : 0<εaffine)
    (hω : omega≤33*geometryLossUnit 1 εaffine/128)
    (hh : heightLoss≤ geometryLossUnit 1 εaffine/8)
    (hp : primeLoss≤ geometryLossUnit 1 εaffine/8) :
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
end OAI.SevenEighths.AuxiliaryReconstruction
end
