import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePoolCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePrimeGates
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryExceptionalClosure
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRetainedContraction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CanonicalQuadraticSieve
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedRayDictionary CenteredMomentPrimeElements
open CenteredMomentCommonAllocationSum
open Cycle63InitialSource Cycle63Moment Cycle63FirstGeometry

variable [Cycle63.AffineLedger]

/-- Actual affine source receipts used by both exceptional payments. The
plain loss is the exact fixed-parent conductor logarithm divided by four, increased by the
plain loss cap of the ledger. -/
structure GeometryAffineExceptionalSourceGates {ι : Type*} [Fintype ι]
    (s : Input ι) (p : Profiles (1/4) (9/4)) (N : ℕ) (Cs Z : ℝ) : Prop where
  card : Fintype.card ι≤N
  controls : ∀i,s.M i≤Cs
  lower : s.lower=1
  lo : s.lo=fun _=>1
  hi : s.hi=fun _=>2
  endpoints : Endpoints (9/4) (9/4) (9/4) s
  scales : ∀i,1≤ s.P i
  profile₁ : s.W₁=p.profile 0
  profile₂ : s.W₂=p.profile 1
  zero₁ : s.W₁ 0=0
  zero₂ : s.W₂ 0=0
  support₁ : ∀x,s.W₁ x≠0→(1/4:ℝ)≤x
  support₂ : ∀x,s.W₂ x≠0→(1/4:ℝ)≤x
  volume : CenteredMomentAmplificationChildInput.volume s≤Z^(2:ℝ)
  volumeLog : |Real.logb Z (CenteredMomentAmplificationChildInput.volume s)|≤3
  sourcePositive : 0<sourceRadius s
  sourceCap : sourceRadius s≤Z^(3:ℝ)
  poolCap : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^(3:ℝ)
  plain₁ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
    (Real.logb Z (s.η.modulus.absNorm:ℝ)/4+Cycle63.AffineLedger.plainLossCap))≤ s.X₁
  plain₂ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
    (Real.logb Z (s.η.modulus.absNorm:ℝ)/4+Cycle63.AffineLedger.plainLossCap))≤ s.X₂
  plain₃ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
    (Real.logb Z (s.η.modulus.absNorm:ℝ)/4+Cycle63.AffineLedger.plainLossCap))≤ s.Y₁
  plain₄ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
    (Real.logb Z (s.η.modulus.absNorm:ℝ)/4+Cycle63.AffineLedger.plainLossCap))≤ s.Y₂

private theorem affine_exceptional_quarter {ι : Type*} [Fintype ι] (Z X₁ X₂ ell : ℝ) (w : ι→ℝ)
    (hZ : 1<Z)
    (hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i)) :
    let r:=Z^((1+ell)/4-(ell/4+Cycle63.AffineLedger.plainLossCap))
    r≤X₁ ∧ r≤X₂ ∧
      r≤ comparisonFirstAt Z
        (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) ∧
      r≤ comparisonSecondAt Z
        (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) X₁ X₂ := by
  intro r
  have hr : r=Z^(1/4-Cycle63.AffineLedger.plainLossCap) := congrArg (fun e : ℝ=>Z^e) (by ring)
  have hloss := Cycle63.AffineLedger.plainLoss_le _ _ _ hwin
  have hlong := Cycle63.AffineLedger.long_factor _ _ _ hwin
  have hcap := Cycle63.AffineLedger.plainLossCap_nonneg
  have hX₁ := initial_scale_exact Z X₁ 1 hZ one_pos (by simpa only [mul_one] using hwin.left_ge)
  have hX₂ := initial_scale_exact Z X₂ 1 hZ one_pos (by simpa only [mul_one] using hwin.right_ge)
  have hpow (a b : ℝ) (h : a≤b) : Z^a≤Z^b := Real.rpow_le_rpow_of_exponent_le hZ.le h
  have hsecond := comparisonSecondAt_pow Z
    (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i))
    (length Z X₁) (length Z X₂) hZ
  rw [←hX₁,←hX₂] at hsecond
  rw [hr]
  refine ⟨(hpow _ _ (by linarith [hloss.1])).trans_eq hX₁.symm,
    (hpow _ _ (by linarith [hloss.2.1])).trans_eq hX₂.symm,
    hpow _ _ (by linarith [hloss.2.2]),?_⟩
  rw [hsecond]
  exact hpow _ _ (by linarith)

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
        {Bmask : ℝ}(bΦ : ℝ)(state : NaturalState Z Bmask bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
      GeometryAffineExceptionalSourceGates inp p (Fintype.card α) Cs Z := by
  obtain ⟨Cs,bs,bp,hCs,hbs,hbp,hfixed⟩:=fixed_affine_source_caps (α:=α) rayM H hH W hW
    1 2 (33/50) (33/50) (1/4) (9/4) (by norm_num) hWs
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [eventual_affine_polynomial_caps (α:=α) rayM H hH W hW
      1 2 (33/50) (33/50) (1/4) (9/4) (by norm_num) hWs
      (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (9/4:ℝ)] with Z hc hlarge
  refine ⟨hc.1,?_⟩
  intro T η₀ θ w σ freq hσ Bmask bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin inp
  have hcaps:=hc.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin
  have hvol:=hwin.volume_le (Finset.sum_nonneg (fun i _=>hw i))
  have hLc₀:=Cycle63.AffineLedger.comparisonLength_nonneg _ _ _ hwin
  have hLc:=Cycle63.AffineLedger.comparisonLength_le _ _ _ hwin
  have hfixed':=hfixed T η₀ θ w σ freq hσ state p
    (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
  have he:=affine_endpoints rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    (by norm_num) (by norm_num)
  have hplain (j : Fin 2)(x : ℝ)(hne : p.profile j x≠0) : (1/4:ℝ)≤x :=
    (p.support j hne).1
  have hzero (j : Fin 2) : p.profile j 0=0 := by
    by_contra hne
    have hh:=hplain j 0 hne
    norm_num at hh
  have hpool:=affine_individual_pool_cap rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) 1 t X₁ X₂ hX₁ hX₂
    1 hc.1 (by norm_num) le_rfl (by norm_num)
    (by norm_num; linarith) hlarge hw hLc₀ hLc hvol
  have hquarter:=affine_exceptional_quarter Z X₁ X₂
    (Real.logb Z (inp.η.modulus.absNorm:ℝ)) w hc.1 hwin
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
    (mesh : ℝ) (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι : Type*}[Fintype ι][DecidableEq ι]
        (η₀ : Character)(θ : ι→RayQuotient.Characters rayM H)
        (w σ freq : ι→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        {Bmask : ℝ}(bΦ : ℝ)(state : NaturalState Z Bmask bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,w i≤ mesh) → ∀beta : ℝ,Cycle63.AffineLedger.firstCellTop≤beta → beta≤Cycle63.AffineLedger.slotTop →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(Cycle63.AffineLedger.amp beta))
      ∀(q : elementPool P)(C R : Ideal O)(B : actualAllocations inp.pools C)
        (τ : Character)(height : ℝ),
      ∀i I,I∈(child inp C R B τ height).slots i→ IsCoprime (Ideal.span {q.val}) I := by
  filter_upwards [eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh]
    with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ η₀ θ w σ freq hσ Bmask bΦ state p t X₁ X₂ hX₁ hX₂ hwm beta hb₁ hb₂ inp P q C R B τ height
  have hm : Matches rayM H hH inp η₀ θ w σ freq W 2 Z := by
    constructor <;> intros <;> rfl
  exact actual_child_full_slot_coprime inp (Ideal.span {q.val})
    (hz.2 beta hb₁ hb₂ inp η₀ θ w σ freq W hm hwm q) C R B τ height

/-- The literal logarithmic volume is paid by the original canonical cell,
before extraction changes any child scale or allocation. -/
theorem affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (Z n₁ n₂ slots : ℝ)
    (hvolume : Real.logb Z (volume s)=n₁+n₂+slots)
    (hwin : Cycle63.AffineLedger.PlainWindow n₁ n₂ slots) :
    Real.logb Z (volume s)≤Cycle63.AffineLedger.totalA
      (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell slots)) := by
  have hh:=Cycle63.AffineLedger.normalized_cell_bounds (M:=1) (n₁:=n₁) (n₂:=n₂)
    (z:=slots) (by norm_num) (by simp only [mul_one]; exact ⟨hwin.slots_ge,hwin.slots_le⟩)
    (by simp only [mul_one]; exact hwin.plane)
  simpa only [div_one,one_mul,hvolume] using hh.2.2.2.1

/-- The canonical-cell ledger applied to the literal affine input; the
volume identity is proved here, rather than supplied as a source premise. -/
theorem actual_affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (θ : ι→RayQuotient.Characters rayM H)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : ι→ℝ) (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    {Z Bmask bΦ : ℝ} (state : NaturalState Z Bmask bΦ) (p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hZ : 1<Z)
    (hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i)) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    Real.logb Z (volume inp)≤Cycle63.AffineLedger.totalA
      (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))) := by
  intro inp
  apply affine_exceptional_volume_cell inp Z (length Z X₁) (length Z X₂) (∑i,w i) _ hwin
  exact affine_volume_log_exact rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num)
    (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) 1 t X₁ X₂ hX₁ hX₂ hZ
    (by norm_num) (by simpa only [mul_one] using hwin.left_ge)
    (by simpa only [mul_one] using hwin.right_ge)

/-- These are the main exponent after its one prime cancellation and the
extracted-error exponent after its already included 56/P payment. All
density, shell, frequency and height fees are charged to loss. -/
theorem affine_exceptional_exponent_saving (beta logV ell loss : ℝ)
    (hbeta : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop)
    (hV : logV≤Cycle63.AffineLedger.totalA beta) (hell : 0≤ell) (hloss : loss≤1/100) :
    loss+logV-(1+ell)+4*Cycle63.AffineLedger.amp beta+
        2*(ell/4+Cycle63.AffineLedger.plainLossCap)/3≤-(1/100:ℝ) ∧
      loss+logV-(1+ell)+3*(3*Cycle63.AffineLedger.amp beta)/2+
        2*(ell/4+Cycle63.AffineLedger.plainLossCap)/3≤-(1/100:ℝ) := by
  have hm:=Cycle63.AffineLedger.main_fixed_reserve hbeta
  have ha:=(Cycle63.AffineLedger.amp_pos hbeta).le
  -- The loss budget `1/100` and the saving `1/100` fit in both fixed-inducing reserves.
  have hm' : 1/50+2/3*Cycle63.AffineLedger.plainLossCap ≤ Cycle63.AffineLedger.mainFixedReserve :=
    Cycle63.AffineLedger.mainFixedReserve_ge
  have he' : 1/50+2/3*Cycle63.AffineLedger.plainLossCap ≤
      1-Cycle63.AffineLedger.totalA beta-(9/2)*Cycle63.AffineLedger.amp beta :=
    Cycle63.AffineLedger.exceptionalReserve_ge.trans (Cycle63.AffineLedger.exceptional_reserve hbeta)
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
      ((min_le_right ((Cycle63.AffineLedger.lowReserve)*1/128) _).trans (min_le_right (1/128) (1/128)))
  refine ⟨by positivity,by positivity,?_⟩
  change omega≤33*μ/128 at hω
  change heightLoss≤μ/8 at hh
  change primeLoss≤μ/8 at hp
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
