/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorScalar

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion CompletedGauss
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstAnnularInput CenteredMomentPrimeElements
open CenteredMomentSecondRadicalBudget CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentAmplifiedRetainedRadius Cycle63FinalErrorCapacity
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
open Cycle63InitialSource CenteredMomentEnergyState CenteredMomentAllocatedRayDictionary
open Cycle63Moment CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentEnergyBands ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
local instance errorScalarTransportSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

private theorem error_scalar_power_pair (Z r r' e e' V F : ℝ)
    (hZ : 0<Z) (hsum : r+e=r'+e') :
    (Z^r/V)*F*Z^e=(Z^r'/V)*F*Z^e' := by
  calc
    _=(F/V)*(Z^r*Z^e) := by ring
    _=(F/V)*Z^(r+e) := by rw [Real.rpow_add hZ]
    _=(F/V)*Z^(r'+e') := by rw [hsum]
    _=(F/V)*(Z^r'*Z^e') := by rw [Real.rpow_add hZ]
    _=_ := by ring

/-- The enlarged radius and nominal exponent cancel their common shift;
no division cancellation or positivity of the extracted volume is needed. -/
theorem extracted_error_label_scalar_delta {Z : ℝ} (hZ : 0<Z)
    (reflected second : Bool) (l v : FirstSourceLabel)
    (M a δ δ' reserve error εcommon V Vextract : ℝ) (p : O) (k : ℕ) :
    extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon V Vextract p k=
      extractedErrorLabelScalar reflected second l v Z M a δ' reserve error εcommon V Vextract p k := by
  unfold extractedErrorLabelScalar firstErrorTailRadius errorCommonRadius errorNominal
  apply error_scalar_power_pair _ _ _ _ _ _ _ hZ
  ring

theorem geometry_error_physical_packet_delta {Z : ℝ} (hZ : 0<Z)
    {ι : Type} [Fintype ι] (s : Input ι) (reflected second : Bool)
    (l : FirstSourceLabel) (L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character) (t : ℝ) (υ : Character) (vheight : ℝ) (q : O) (k : ℕ)
    (M a δ δ' reserve error εcommon : ℝ) :
    geometryErrorPhysicalScalarPacket s reflected second l L R B₁ χ t υ vheight q k
      Z M a δ reserve error εcommon=
    geometryErrorPhysicalScalarPacket s reflected second l L R B₁ χ t υ vheight q k
      Z M a δ' reserve error εcommon := by
  unfold geometryErrorPhysicalScalarPacket
  apply Finset.sum_congr rfl
  intro Bp _
  apply Finset.sum_congr rfl
  intro v _
  exact extracted_error_label_scalar_delta hZ reflected second l v M a δ δ' reserve error εcommon _ _ q k

theorem geometry_error_physical_complete_cost_delta {Z : ℝ} (hZ : 0<Z)
    {ι : Type} [Fintype ι] (s : Input ι) (reflected second : Bool)
    (l : FirstSourceLabel) (L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character) (t : ℝ) (P : Finset (Ideal O))
    (υ : elementPool P→Fin 3→RayCharacter→Character) (vheight : ℝ)
    (M a δ δ' reserve error εcommon : ℝ) :
    geometryErrorPhysicalCompleteCost s reflected second l L R B₁ χ t P υ vheight
      Z M a δ reserve error εcommon=
    geometryErrorPhysicalCompleteCost s reflected second l L R B₁ χ t P υ vheight
      Z M a δ' reserve error εcommon := by
  unfold geometryErrorPhysicalCompleteCost
  simp_rw [geometry_error_physical_packet_delta hZ (δ:=δ) (δ':=δ')]

private theorem error_scalar_sum_transport {J : Type*} [Fintype J]
    {A : J→Type*} [∀j,Fintype (A j)]
    (mass raw paid : (j : J)→A j→ℝ) (R : ℝ)
    (hcost : ∀j b,raw j b=paid j b)
    (hpaid : (∑j,∑b,mass j b*paid j b)≤R) :
    (∑j,∑b,mass j b*raw j b)≤R := by
  calc
    _=(∑j,∑b,mass j b*paid j b) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro b _
      exact congrArg (fun x=>mass j b*x) (hcost j b)
    _≤R := hpaid

variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

def AffineErrorFrequencyLossScalarBound (Sbad : Finset (Ideal O))
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εv ε εaffine εshell ξ εalloc mesh K Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
    (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
  (∀i,0≤w i) → (∀i,w i≤mesh) →
  (41/100:ℝ)≤length Z X₁ → (41/100:ℝ)≤length Z X₂ →
  length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
  (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
  let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
  let beta:=Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i))
  let amp:=Cycle63.Arithmetic.amp beta
  let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
  ∀(reflected second : Bool)(error εcommon reserve : ℝ),
  0≤εcommon → error+εv+4*εcommon+ε≤64*geometryLossUnit 1 εaffine →
  ∀(Φ : 𝓢(ℝ,ℂ))(bin : ℤ×(Fin 5→ℤ)),
  let hK:=zero_lt_one.trans hZ
  let rows:=firstLiveColumns (geometryFirstSource inp 1 1 Z Z ξ hK bin) (fun _=>logAnnulus)
  let C:=fun j : rows=>geometryColumnIdeal reflected inp 1 1 Z Z ξ hK bin j.val
  ∀(height : ℝ)(υ : (j : rows)→actualAllocations inp.pools (C j)→
    elementPool P→Fin 3→RayCharacter→Character)(vheight : ℝ),
  let A:=Real.logb Z (CenteredMomentAmplificationChildInput.volume inp)
  let weight:=fun q=>normPhase (coordinateBlock inp 1 1 Φ Z Z ξ q)
  (∑j : rows,∑alloc : actualAllocations inp.pools (C j),
    geometryAllocationWeight reflected inp 1 1 Z Z ξ 1 A hK bin weight (Fintype.card α) (9/4) j.val alloc*
      geometryErrorPhysicalCompleteCost inp reflected second
        (geometryFirstLabel inp 1 1 Z Z ξ hK bin j.val) j.val.2.1.val 1 alloc
        (geometryColumnCharacter reflected inp 1 1 Z Z ξ hK bin j.val) height P (υ j alloc)
        vheight Z 1 amp (frequencyLoss Z 32 ξ) reserve error εcommon)≤
    16*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*K*
      Z^(4*εalloc+εshell-(7/60000000:ℝ))

set_option maxHeartbeats 1600000 in
omit [DecidableEq α] in
theorem affine_error_scalar_bound_frequency_loss
    (Sbad : Finset (Ideal O)) (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εv ε εaffine εshell ξ εalloc mesh K Z : ℝ)
    (h : AffineErrorScalarBound (α:=α) rayM H hH Sbad W hW hWs
      εv ε εaffine εshell ξ εalloc mesh K Z) :
    AffineErrorFrequencyLossScalarBound (α:=α) rayM H hH Sbad W hW hWs
      εv ε εaffine εshell ξ εalloc mesh K Z := by
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
    inp beta amp P reflected second error εcommon reserve hecommon hloss Φ bin hK rows C height υ vheight A weight
  have hp:=h hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi reflected second error εcommon reserve hecommon hloss Φ bin height υ vheight
  refine error_scalar_sum_transport _ _ _ _ ?_ hp
  intro j alloc
  exact geometry_error_physical_complete_cost_delta (zero_lt_one.trans hZ)
    inp reflected second (geometryFirstLabel inp 1 1 Z Z ξ hK bin j.val)
    j.val.2.1.val 1 alloc (geometryColumnCharacter reflected inp 1 1 Z Z ξ hK bin j.val)
    height P (υ j alloc) vheight 1 amp (frequencyLoss Z 32 ξ) (3*amp) reserve error εcommon

theorem eventual_actual_affine_error_frequency_loss_payment
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εv ε εaffine εshell ξ εalloc mesh : ℝ)
    (hev : 0<εv) (he : 0<ε) (heshell : 0<εshell) (hξ : 0≤ξ) (healloc : 0<εalloc)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      AffineErrorFrequencyLossScalarBound (α:=α) rayM H hH Sbad W hW hWs
        εv ε εaffine εshell ξ εalloc mesh K Z := by
  obtain ⟨K,hK,hpaid⟩:=eventual_actual_affine_error_scalar_payment (α:=α) rayM H hH
    Sbad hbad W hW hWs εv ε εaffine εshell ξ εalloc mesh hev he heshell hξ healloc hmesh
  refine ⟨K,hK,?_⟩
  filter_upwards [hpaid] with Z hz
  exact ⟨hz.1,affine_error_scalar_bound_frequency_loss rayM H hH Sbad W hW hWs
    εv ε εaffine εshell ξ εalloc mesh K Z hz.2⟩

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.extracted_error_label_scalar_delta
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_error_physical_packet_delta
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_error_physical_complete_cost_delta
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_error_scalar_bound_frequency_loss
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_affine_error_frequency_loss_payment
