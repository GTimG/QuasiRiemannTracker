/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.DaughterGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
universe u
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentNaturalRowSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentPrimeSlot
open CenteredMomentAllocatedRayDictionary ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def rawHeightProfile {a b : ℝ} (ha : 0<a) (p : Profiles a b) (j : Fin 2) (v : ℝ) : 𝓢(ℝ,ℂ) :=
  CenteredMomentLattice.normPowerProfile (p.profile j) a b ha (p.support j)
    ((p.profile j).smooth ⊤) v

def canonicalRawProduct {α : Type*} (F : Finset α)(η : Character)
    (z : {z : O // z≠0})(mask : Ideal O)(W₁ W₂ : 𝓢(ℝ,ℂ))
    (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)(height X₁ X₂ : ℝ) : ℂ :=
  let χ:=excluded (naturalRow η z.val z.property).character mask
  HeckeDyadic.polynomial χ false W₁ X₁ 0 0*HeckeDyadic.polynomial χ false W₂ X₂ 0 0*
    ∏i∈F,CenteredMomentCommonMaskExpansion.naturalSlot χ (pool i)
      (CenteredMomentCommonMaskEnergy.heightCoefficient (β i) height) (P i)

theorem geometry_raw_fixed_mask_ne_zero {α : Type*}[Fintype α] (s : Input α)
    (R : Ideal O)(hR : R≠0) : geometryRawFixedMask s R≠0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero s.η.modulus_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))) hR

/-- Fixed physical input and first geometry. This records only original
constructor arguments and zero-at-origin facts, not a moment estimate. -/
structure RawGeometry (α : Type u)[Fintype α][DecidableEq α] where
  reflected : Bool
  side : Bool
  input : Input α
  puncture : Ideal O
  seed : Ideal O
  Z : ℝ
  root : ℝ
  amp : ℝ
  xi : ℝ
  reserve : ℝ
  upper : ℝ
  firstHeight : ℝ
  count : ℕ
  base_gt_one : 1<Z
  bin : ℤ×(Fin 5→ℤ)
  zero₁ : input.W₁ 0=0
  zero₂ : input.W₂ 0=0

namespace RawGeometry
variable {α : Type u}[Fintype α][DecidableEq α](g : RawGeometry α)

def First : Type u := GeometryLowFirstIndex g.reflected g.input g.puncture g.seed (g.Z^g.root) g.Z g.xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans g.base_gt_one) _) g.bin
def Second (q : g.First) : Type := GeometryLowSecondIndex g.reflected g.input g.puncture g.seed g.Z g.root
  g.amp g.xi g.reserve g.upper g.firstHeight g.count g.base_gt_one g.bin q
def datum (q : g.First)(n : g.Second q) : SecondInputDatum α :=
  geometryLowSecondDatum g.reflected g.input g.puncture g.seed g.Z g.root g.amp g.xi g.reserve
    g.upper g.firstHeight g.count g.base_gt_one g.bin q g.zero₁ g.zero₂ n
def unit (l : FirstSourceLabel) : O := (fixedParentUnit (!g.reflected) g.input.η l:O)
def Key : Type := NonzeroJointSourceLabel (!g.reflected) 1 g.unit
def fixedMask := geometryRawFixedMask g.input g.puncture

attribute [local irreducible] First Second datum

structure Daughter : Type u where
  first : g.First
  second : g.Second first
  physical : PhysicalDaughter (g.datum first second) g.side

attribute [local semireducible] First Second datum

namespace Daughter
variable {g : RawGeometry α}(d : g.Daughter)

def rawKey : g.Key := daughterRawKey g.reflected g.side g.input g.puncture g.seed g.Z g.root
  g.amp g.xi g.reserve g.upper g.firstHeight g.count g.base_gt_one g.bin
  d.first g.zero₁ g.zero₂ d.second d.physical
def slotSet : Finset α := daughterSlotSet g.reflected g.side g.input g.puncture g.seed g.Z g.root
  g.amp g.xi g.reserve g.upper g.firstHeight g.count g.base_gt_one g.bin
  d.first g.zero₁ g.zero₂ d.second d.physical
def ray : RayCharacter := geometryDictionaryRay g.reflected g.input g.puncture g.seed
  (g.Z^g.root) g.Z g.xi (Real.rpow_pos_of_pos (zero_lt_one.trans g.base_gt_one) _) g.bin d.first.1.val
def firstLabel : FirstSourceLabel := geometryFirstLabel g.input g.puncture g.seed (g.Z^g.root)
  g.Z g.xi (Real.rpow_pos_of_pos (zero_lt_one.trans g.base_gt_one) _) g.bin d.first.1.val
def scale (j : Fin 2) := d.physical.scale j
def value (ψ : RayCharacter)(v : ℝ) := d.physical.value ψ v
def Ordinary (χ : RayCharacter)(Q : Ideal O)(m : O) : Prop :=
  d.physical.row.val.2.2.2.val∈CenteredMomentSecondEnergySplit.partRows false
    (g.datum d.first d.second).input.η χ Q m (g.datum d.first d.second).C
    (g.datum d.first d.second).D (g.datum d.first d.second).inactive (g.datum d.first d.second).radius

theorem scale_pos (j : Fin 2) : 0<d.scale j := d.physical.scale_pos j

theorem first_eq : d.rawKey.val.1=d.firstLabel :=
  daughter_first_eq g.reflected g.side g.input g.puncture g.seed g.Z g.root g.amp g.xi g.reserve
    g.upper g.firstHeight g.count g.base_gt_one g.bin d.first g.zero₁ g.zero₂ d.second d.physical

theorem supported :
    Supported d.rawKey.val.1.1.1 ∧ Supported d.rawKey.val.1.1.2 ∧
    Supported d.rawKey.val.2.1.1 ∧ Supported d.rawKey.val.2.1.2 ∧
    CompletedGauss.primeSupport d.rawKey.val.1.1.1=CompletedGauss.primeSupport d.rawKey.val.1.1.2 ∧
    CompletedGauss.primeSupport d.rawKey.val.2.1.1=CompletedGauss.primeSupport d.rawKey.val.2.1.2 :=
  daughter_supported g.reflected g.side g.input g.puncture g.seed g.Z g.root g.amp g.xi g.reserve
    g.upper g.firstHeight g.count g.base_gt_one g.bin d.first g.zero₁ g.zero₂ d.second d.physical

theorem ordinary_keep (hR : g.puncture≠0)(χ ψ : RayCharacter)(Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)})(m : O)(hm : m≠0)(hml : goodLambda∣m)(hm2 : (2:O)∣m)
    (ho : d.Ordinary χ Q m) : initialKeep (secondFixedDictionary g.input.η (d.ray,ψ)) Q
      (nonzeroJointSourceRow d.rawKey).val :=
  daughter_ordinary_keep g.reflected g.side g.input g.puncture g.seed g.Z g.root g.amp g.xi g.reserve
    g.upper g.firstHeight g.count g.base_gt_one g.bin d.first g.zero₁ g.zero₂ d.second d.physical
    hR χ ψ Q hQ m hm hml hm2 ho

theorem value_le_common (hR : g.puncture≠0)(η₀ : Character)
    (rayM : Ideal O)[NeZero rayM](Hray : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤Hray)
    (θ : α→RayQuotient.Characters rayM Hray)(w σ freq : α→ℝ)(W : ℝ→ℂ)(bslot : ℝ)
    (hm : Matches rayM Hray hH g.input η₀ θ w σ freq W bslot g.Z)
    (a b : ℝ)(ha : 0<a)(p : Profiles a b)
    (hp₁ : g.input.W₁=p.profile 0)(hp₂ : g.input.W₂=p.profile 1)(ψ : RayCharacter)(v : ℝ) :
    ‖d.value ψ v‖^2≤
      ‖canonicalRawProduct d.slotSet (secondFixedDictionary g.input.η (d.ray,ψ))
        (nonzeroJointSourceRow d.rawKey) (g.fixedMask*firstSourceMissing (!g.reflected) d.firstLabel)
        (rawHeightProfile ha p 0 v) (rawHeightProfile ha p 1 v)
        (fun i=>primePool rayM Hray bslot (g.Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter rayM Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (g.Z^(w i)) (σ i) (freq i) I)
        (fun i=>g.Z^(w i)) v (d.scale 0) (d.scale 1)‖^2 := by
  exact daughter_value_le_common g.reflected g.side g.input g.puncture g.seed g.Z g.root g.amp g.xi
    g.reserve g.upper g.firstHeight g.count g.base_gt_one g.bin d.first g.zero₁ g.zero₂ d.second d.physical
    hR η₀ rayM Hray hH θ w σ freq W bslot hm a b ha p hp₁ hp₂ ψ v

end Daughter
end RawGeometry
end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.RawGeometry.Daughter.supported
#print axioms OAI.SevenEighths.Record12518109Raw.RawGeometry.Daughter.ordinary_keep
#print axioms OAI.SevenEighths.Record12518109Raw.RawGeometry.Daughter.value_le_common
