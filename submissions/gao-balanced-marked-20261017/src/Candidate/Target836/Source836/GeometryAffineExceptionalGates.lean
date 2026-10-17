import Candidate.Target836.Source836.GlobalNamed
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryExceptionalErrorNormPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePoolCaps
import Candidate.Target836.Source836.GeometryAffinePrimeGates
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Cycle63.Moment.InitialState
import Candidate.Cycle63.Moment.CellGeometry

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Target836SourceAssembly
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

/-- Actual affine source receipts used by both exceptional payments. The
plain loss is the exact fixed-parent conductor logarithm divided by four. -/
private theorem affine_exceptional_quarter (Z X₁ X₂ ell : ℝ)
    (hZ : 1<Z) (hX₁ : 0<X₁) (_hX₂ : 0<X₂)
    (hlo₁ : (41/100:ℝ)≤length Z X₁) (hlo₂ : (41/100:ℝ)≤length Z X₂) :
    let r:=Z^((1+ell)/4-ell/4)
    r≤X₁ ∧ r≤X₂ ∧ r≤comparisonFirst Z 1 ∧
      r≤comparisonSecond Z 1 X₁ X₂ := by
  intro r
  have hr : r=Z^(1/4:ℝ) := congrArg (fun e : ℝ=>Z^e) (by ring)
  have hq : 0<Z^(1/4:ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hx (X : ℝ) (hlo : (41/100:ℝ)≤length Z X) : Z^(1/4:ℝ)≤X := by
    rw [initial_scale_exact Z X 1 hZ (by norm_num) (by simpa only [mul_one] using hlo)]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hx₁:=hx X₁ hlo₁
  have hx₂:=hx X₂ hlo₂
  rw [hr]
  refine ⟨hx₁,hx₂,le_rfl,?_⟩
  exact (le_div_iff₀ hq).mpr (mul_le_mul hx₁ hx₂ hq.le hX₁.le)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineExceptionalFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

/-- The threshold and profile cap precede every slot subset, smooth plain
profile, fixed-parent radial function, and both heights. No energy is assumed. -/
theorem eventual_actual_affine_exceptional_source_gates
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) :
    ∃Cs : ℝ,1≤Cs ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
        (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (41/100:ℝ)≤length Z X₁ → (41/100:ℝ)≤length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) → (∑i,w i)≤(1/25:ℝ) →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      GeometryAffineExceptionalSourceGates inp p (Fintype.card α) Cs Z := by
  obtain ⟨Cs,bs,bp,hCs,hbs,hbp,hfixed⟩:=fixed_affine_source_caps (α:=α) rayM H hH W hW
    1 2 (33/50) (33/50) (1/4) (9/4) (by norm_num) hWs
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [eventual_affine_polynomial_caps (α:=α) rayM H hH W hW
      1 2 (33/50) (33/50) (1/4) (9/4) 1 (by norm_num) hWs
      (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (9/4:ℝ)] with Z hc hlarge
  refine ⟨hc.1,?_⟩
  intro T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi inp
  have hcaps:=hc.2 T η₀ θ w σ freq hσ bΦ state p 1 t X₁ X₂ hX₁ hX₂
    (by norm_num) le_rfl hw (by simpa only [mul_one] using hlo₁)
    (by simpa only [mul_one] using hlo₂) (by simpa only [mul_one] using hhi₁)
    (by simpa only [mul_one] using hhi₂) (by simpa only [one_div] using hwhi)
  have hfixed':=hfixed T η₀ θ w σ freq hσ state p 1 t X₁ X₂ hX₁ hX₂
  have he:=affine_endpoints rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    (by norm_num) (by norm_num)
  have hplain (j : Fin 2)(x : ℝ)(hne : p.profile j x≠0) : (1/4:ℝ)≤x :=
    (p.support j hne).1
  have hzero (j : Fin 2) : p.profile j 0=0 := by
    by_contra hne
    have hh:=hplain j 0 hne
    norm_num at hh
  have hpool:=affine_individual_pool_cap rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    1 hc.1 (by norm_num) le_rfl (by norm_num)
    (by norm_num; linarith) hlarge hw (by simpa using hwhi) (by simpa using hhi₁) (by simpa using hhi₂)
  have hquarter:=affine_exceptional_quarter Z X₁ X₂
    (Real.logb Z (inp.η.modulus.absNorm:ℝ)) hc.1 hX₁ hX₂ hlo₁ hlo₂
  refine ⟨hfixed'.1,hfixed'.2.1,rfl,rfl,rfl,?_,?_,rfl,rfl,hzero 0,hzero 1,
    hplain 0,hplain 1,?_,?_,?_,?_,?_,hquarter.1,hquarter.2.1,hquarter.2.2.1,hquarter.2.2.2⟩
  · exact ⟨he.1.trans (by norm_num),he.2⟩
  · intro i
    exact Real.one_le_rpow hc.1.le (hw i)
  · simpa only [show (1:ℝ)+1=2 by norm_num] using hcaps.2.2.1
  · exact hcaps.2.1.trans (by norm_num)
  · change 0<(∏i : T,(2:ℝ))*(9/4)*(9/4)*(X₁*X₂)*(∏i : T,Z^(w i))
    exact mul_pos (mul_pos (mul_pos (mul_pos (Finset.prod_pos (fun _ _=>by norm_num))
      (by norm_num)) (by norm_num)) (mul_pos hX₁ hX₂))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (zero_lt_one.trans hc.1) _))
  · simpa only [show (1:ℝ)+2=3 by norm_num] using hcaps.2.2.2.1
  · intro i I hI
    exact (hpool i I hI).trans (Real.rpow_le_rpow_of_exponent_le hc.1.le (by norm_num))

/-- Actual amplifier primes are coprime to every stored first-child slot,
including slots whose smooth coefficient vanishes. The first allocation
and both heights are chosen after the common scale threshold. -/
theorem eventual_actual_affine_exceptional_child_coprime
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (mesh : ℝ) (hmesh : mesh<(902420521/120632400000:ℝ)/2) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι : Type*}[Fintype ι][DecidableEq ι]
        (η₀ : Character)(θ : ι→RayQuotient.Characters rayM H)
        (w σ freq : ι→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,w i≤ mesh) → ∀beta : ℝ,3401/100000≤beta → beta≤1/25 →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(GlobalNamed.amp beta))
      ∀(q : elementPool P)(C R : Ideal O)(B : actualAllocations inp.pools C)
        (τ : Character)(height : ℝ),
      ∀i I,I∈(child inp C R B τ height).slots i→IsCoprime (Ideal.span {q.val}) I := by
  filter_upwards [eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh]
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
    (hcone : n₁+n₂+GlobalNamed.lambda*slots≤GlobalNamed.B) :
    Real.logb Z (volume s)≤GlobalNamed.totalA
      (GlobalNamed.cellUpper (Cycle63.Moment.originalCell slots)) := by
  have hh:=Target874836.SourceProvider.normalized_cell_bounds (M:=1) (n₁:=n₁) (n₂:=n₂)
    (z:=slots) (by norm_num) (by simpa only [mul_one] using hslots)
    (by simpa only [mul_one] using hcone)
  simpa only [div_one,one_mul,hvolume] using hh.2.2.2.1

/-- The canonical-cell ledger applied to the literal affine input; the
volume identity is proved here, rather than supplied as a source premise. -/
theorem actual_affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (θ : ι→RayQuotient.Characters rayM H)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : ι→ℝ) (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    {Z bΦ : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hZ : 1<Z)
    (hlo₁ : (41/100:ℝ)≤length Z X₁) (hlo₂ : (41/100:ℝ)≤length Z X₂)
    (hslots : (17/500:ℝ)≤∑i,w i ∧ (∑i,w i)≤1/25)
    (hcone : length Z X₁+length Z X₂+GlobalNamed.lambda*(∑i,w i)≤GlobalNamed.B) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    Real.logb Z (volume inp)≤GlobalNamed.totalA
      (GlobalNamed.cellUpper (Cycle63.Moment.originalCell (∑i,w i))) := by
  intro inp
  apply affine_exceptional_volume_cell inp Z (length Z X₁) (length Z X₂) (∑i,w i) _ hslots hcone
  exact affine_volume_log_exact rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂ hZ
    (by norm_num) (by simpa only [mul_one] using hlo₁) (by simpa only [mul_one] using hlo₂)

/-- These are the main exponent after its one prime cancellation and the
extracted-error exponent after its already included 56/P payment. All
density, shell, frequency and height fees are charged to loss. -/
theorem affine_exceptional_exponent_saving (beta logV ell loss : ℝ)
    (hbeta : 3401/100000≤beta ∧ beta≤1/25)
    (hV : logV≤GlobalNamed.totalA beta) (hell : 0≤ell) (hloss : loss≤1/100) :
    loss+logV-(1+ell)+4*GlobalNamed.amp beta+2*(ell/4)/3≤-(1/100:ℝ) ∧
      loss+logV-(1+ell)+3*(3*GlobalNamed.amp beta)/2+2*(ell/4)/3≤-(1/100:ℝ) := by
  have hm:=GlobalNamed.main_fixed_reserve hbeta
  have he:=GlobalNamed.error_fixed_reserve hbeta
  have ha:=(GlobalNamed.amp_pos hbeta).le
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
end OAI.SevenEighths.Target836SourceAssembly
#print axioms OAI.SevenEighths.Target836SourceAssembly.eventual_actual_affine_exceptional_source_gates
#print axioms OAI.SevenEighths.Target836SourceAssembly.eventual_actual_affine_exceptional_child_coprime
#print axioms OAI.SevenEighths.Target836SourceAssembly.affine_exceptional_fixed_parent_character
#print axioms OAI.SevenEighths.Target836SourceAssembly.affine_exceptional_volume_cell
#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_affine_exceptional_volume_cell
#print axioms OAI.SevenEighths.Target836SourceAssembly.affine_exceptional_exponent_saving
#print axioms OAI.SevenEighths.Target836SourceAssembly.affine_exceptional_small_loss
