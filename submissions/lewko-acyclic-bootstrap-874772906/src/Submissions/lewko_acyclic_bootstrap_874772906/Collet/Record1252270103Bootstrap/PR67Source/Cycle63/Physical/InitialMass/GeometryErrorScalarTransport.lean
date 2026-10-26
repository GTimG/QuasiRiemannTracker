import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineErrorScalar
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLossSchedule
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
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

variable [Cycle63.AffineLedger] in
/-- The enlarged radius and nominal exponent cancel their common shift;
no division cancellation or positivity of the extracted volume is needed. -/
theorem extracted_error_label_scalar_delta {Z : ℝ} (hZ : 0<Z)
    (reflected second : Bool) (l v : FirstSourceLabel)
    (unit M a δ δ' reserve error εcommon V Vextract : ℝ) (p : O) (k : ℕ) :
    extractedErrorLabelScalar reflected second l v Z unit M a δ reserve error εcommon V Vextract p k=
      extractedErrorLabelScalar reflected second l v Z unit M a δ' reserve error εcommon V Vextract p k := by
  unfold extractedErrorLabelScalar firstErrorTailRadius errorCommonRadius errorNominal
  apply error_scalar_power_pair _ _ _ _ _ _ _ hZ
  ring

variable [Cycle63.AffineLedger] in
theorem geometry_error_physical_packet_delta {Z : ℝ} (hZ : 0<Z)
    {ι : Type} [Fintype ι] (s : Input ι) (reflected second : Bool)
    (l : FirstSourceLabel) (L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character) (t : ℝ) (υ : Character) (vheight : ℝ) (q : O) (k : ℕ)
    (unit M a δ δ' reserve error εcommon : ℝ) :
    geometryErrorPhysicalScalarPacket s reflected second l L R B₁ χ t υ vheight q k
      Z unit M a δ reserve error εcommon=
    geometryErrorPhysicalScalarPacket s reflected second l L R B₁ χ t υ vheight q k
      Z unit M a δ' reserve error εcommon := by
  unfold geometryErrorPhysicalScalarPacket
  refine Finset.sum_congr rfl fun Bp _ => Finset.sum_congr rfl fun v _ => ?_
  exact extracted_error_label_scalar_delta hZ reflected second l v unit M a δ δ' reserve error εcommon _ _ q k

variable [Cycle63.AffineLedger] in
theorem geometry_error_physical_complete_cost_delta {Z : ℝ} (hZ : 0<Z)
    {ι : Type} [Fintype ι] (s : Input ι) (reflected second : Bool)
    (l : FirstSourceLabel) (L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character) (t : ℝ) (P : Finset (Ideal O))
    (υ : elementPool P→Fin 3→RayCharacter→ Character) (vheight : ℝ)
    (unit M a δ δ' reserve error εcommon : ℝ) :
    geometryErrorPhysicalCompleteCost s reflected second l L R B₁ χ t P υ vheight
      Z unit M a δ reserve error εcommon=
    geometryErrorPhysicalCompleteCost s reflected second l L R B₁ χ t P υ vheight
      Z unit M a δ' reserve error εcommon := by
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
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
      exact congrArg (fun x=>mass j b*x) (hcost j b)
    _≤R := hpaid

variable {α : Type} [Fintype α] [DecidableEq α]

variable [Cycle63.AffineLedger] in
/-- The parent scalar payment with the frequency loss of the normalized menu in place of the
scalar's free amplifier argument. -/
def AffineErrorFrequencyLossScalarBound (Cs εv ε εaffine εshell ξ εalloc K Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(T : Finset α)(s : Input T)(p : Profiles (1/4) (9/4)),
  GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z →
  ∀(P : Finset (Ideal O)),P.Nonempty → (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
    (∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I) →
  ∀(R seed : Ideal O),Squarefree seed → seed≠0 → ∀Mrow : ℝ,0≤ Mrow →
  ∀(reflected second : Bool)(amp error εcommon reserve : ℝ),
  0≤εcommon → error+εv+4*εcommon+ε≤64*geometryLossUnit 1 εaffine →
  ∀(Φ : 𝓢(ℝ,ℂ))(bin : ℤ×(Fin 5→ℤ)),
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let rows:=firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK bin) (fun _=>logAnnulus)
  let C:=fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK bin j.val
  ∀(height : ℝ)(υ : (j : rows)→actualAllocations s.pools (C j)→
    elementPool P→Fin 3→RayCharacter→ Character)(vheight : ℝ),
  let A:=Real.logb Z (CenteredMomentAmplificationChildInput.volume s)
  let weight:=fun q=>normPhase (coordinateBlock s R seed Φ (Z^Mrow) Z ξ q)
  (∑j : rows,∑alloc : actualAllocations s.pools (C j),
    geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mrow A hK bin weight (Fintype.card α) (9/4) j.val alloc*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ hK bin j.val) j.val.2.1.val R alloc
        (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK bin j.val) height P (υ j alloc)
        vheight Z 1 Mrow amp (frequencyLoss Z 32 ξ) reserve error εcommon)≤
    16*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*K*
      Z^(4*εalloc+εshell-((Cycle63.AffineLedger.lowReserve/2):ℝ))/(seed.absNorm:ℝ)

set_option maxHeartbeats 1600000 in
variable [Cycle63.AffineLedger] in
omit [DecidableEq α] in
theorem affine_error_scalar_bound_frequency_loss
    (Cs εv ε εaffine εshell ξ εalloc K Z : ℝ)
    (h : AffineErrorScalarBound (α:=α) Cs εv ε εaffine εshell ξ εalloc K Z) :
    AffineErrorFrequencyLossScalarBound (α:=α) Cs εv ε εaffine εshell ξ εalloc K Z := by
  intro hZ T s p caps P hP hprime hbad hslot R seed hs hs0 Mrow hMrow reflected second amp error
    εcommon reserve hecommon hloss Φ bin hK rows C height υ vheight A weight
  have hp:=h hZ T s p caps P hP hprime hbad hslot R seed hs hs0 Mrow hMrow reflected second amp error
    εcommon reserve hecommon hloss Φ bin height υ vheight
  refine error_scalar_sum_transport _ _ _ _ ?_ hp
  intro j alloc
  exact geometry_error_physical_complete_cost_delta (zero_lt_one.trans hZ)
    s reflected second (geometryFirstLabel s R seed (Z^Mrow) Z ξ hK bin j.val)
    j.val.2.1.val R alloc (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK bin j.val)
    height P (υ j alloc) vheight 1 Mrow amp (frequencyLoss Z 32 ξ) (3*amp) reserve error εcommon

variable [Cycle63.AffineLedger] in
theorem eventual_actual_affine_error_frequency_loss_payment
    (Cs εv ε εaffine εshell ξ εalloc : ℝ)(hCs : 1≤Cs)
    (hev : 0<εv) (he : 0<ε) (heshell : 0<εshell) (hξ : 0≤ξ) (healloc : 0<εalloc) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      AffineErrorFrequencyLossScalarBound (α:=α) Cs εv ε εaffine εshell ξ εalloc K Z := by
  obtain ⟨K,hK,hpaid⟩:=eventual_actual_affine_error_scalar_payment (α:=α)
    Cs εv ε εaffine εshell ξ εalloc hCs hev he heshell hξ healloc
  refine ⟨K,hK,?_⟩
  filter_upwards [hpaid] with Z hz
  exact ⟨hz.1,affine_error_scalar_bound_frequency_loss (α:=α) Cs εv ε εaffine εshell ξ εalloc K Z hz.2⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
