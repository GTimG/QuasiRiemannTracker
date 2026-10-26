import Candidate.Uneven.MainAllocationTransfer
import Candidate.Cycle63.Physical.InitialMass.GeometryCostSelection
import Candidate.Uneven.MainInitialContract
import Candidate.Uneven.MainZeroPayment
import Candidate.Uneven.MainAffineAmplification
import Candidate.Uneven.MainHighBudgetJoin
import Candidate.Uneven.MainAssemblyUniformRemainder
import Candidate.Uneven.MainCellGeometry
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePaidBudget
import Candidate.Uneven.MainAssemblyUniformBudget
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineBudgetTransport

/- Original module: Candidate.Uneven.MainAssemblyErrorWeight. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.MainAssembly
noncomputable section
open Target830.Source.Uneven
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63InitialMass
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentLogDyadic
open CenteredMomentFirstAmplificationChoice CenteredMomentPrimeElements RayFourExpansion
local notation "O" => HeckeFamily.O

/-- ERROR costs are positive, so the uneven allocation comparison can be
performed before their complete prime/ray/branch sums are estimated. -/
theorem uneven_error_cost_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A sigma reserve b t : ℝ) (hK : 0< K) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ)
    (P : Finset (Ideal O))
    (τ : (j : ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=> logAnnulus)))→
      actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val)→
      elementPool P→Fin 3→RayCharacter→Character) :
    (∑j : ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=> logAnnulus)),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val),
      unevenAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val B*
        actualErrorSources
          (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val) R B
            (geometryColumnCharacter reflected s R seed K Z ξ hK key j.val) t)
          (geometryBranch reflected s R seed K Z ξ hK key j.val) Z sigma 1 ξ reserve P (τ j B))≤
    ∑j : ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=> logAnnulus)),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val),
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val B*
        actualErrorSources
          (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val) R B
            (geometryColumnCharacter reflected s R seed K Z ξ hK key j.val) t)
          (geometryBranch reflected s R seed K Z ξ hK key j.val) Z sigma 1 ξ reserve P (τ j B) := by
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro B _
  exact mul_le_mul_of_nonneg_right
    (actual_uneven_allocation_weight_le reflected s R seed K Z ξ M A hK hZ key weight N b j.val B)
    (actual_error_sources_nonneg _ _ _ _ _ _ _ (zero_lt_one.trans hZ) _ _)
end
end OAI.SevenEighths.MainAssembly
end

/- Original module: Candidate.Uneven.MainAssemblyRetainedBudget. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.MainAssembly
open Target830.Source.Uneven
noncomputable section
open Sil.Uneven.MainSource
open MainReconstruction
variable {plane : Sil.Uneven.MainSource.Plane}
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationRadicalChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentLogDyadic RayFourExpansion
open CenteredMomentChildRows CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAllocatedRayDictionary
local notation "O" => HeckeFamily.O

private theorem retained_remainder_join
    (budget main error nm ne average coeff Cm Ce factor : ℝ)
    (havg : 0 ≤ average) (havg56 : average ≤ 56)
    (hcoeff : 0 ≤ coeff) (hcoeff2000000 : coeff ≤ 2000000)
    (hCm : 0 ≤ Cm) (hfactor : 0 ≤ factor)
    (hb : budget ≤ average * (coeff * main + error))
    (hm : main ≤ Cm * factor + nm)
    (he : average * error ≤ Ce * factor + average * ne) :
    budget ≤ (56 * 2000000 * Cm + Ce) * factor + average * (coeff * nm + ne) := by
  have hmain := mul_le_mul_of_nonneg_left hm (mul_nonneg havg hcoeff)
  have hcoef : average * coeff * Cm ≤ 56 * 2000000 * Cm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul havg56 hcoeff2000000 hcoeff (by norm_num)) hCm
  have hpaid := mul_le_mul_of_nonneg_right hcoef hfactor
  nlinarith only [hb, hmain, he, hpaid]

private def amplifiedRadiusFrame {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (Z amp μ : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ))
    (Ψ : 𝓢(ℝ,ℂ)) (height : ℝ) (P : Finset (Ideal O)) (radius : ℝ) (hK : 0 < radius) : Prop :=
  let Label := ↥(firstLiveColumns (geometryFirstSource s 1 1 radius Z (μ/64) hK key) (fun _ => logAnnulus))
  let C := fun j : Label => geometryColumnIdeal reflected s 1 1 radius Z (μ/64) hK key j.val
  let χ := fun j : Label => geometryColumnCharacter reflected s 1 1 radius Z (μ/64) hK key j.val
  let g := fun j : Label => geometryBranch reflected s 1 1 radius Z (μ/64) hK key j.val
  let mass := fun j : Label => unevenAllocationWeight reflected s 1 1 radius Z (μ/64) 1
    (Real.logb Z (volume s)) hK key
    (fun q => normPhase (coordinateBlock s 1 1 Ψ radius Z (μ/64) q)) (Fintype.card ι) (9/4) j.val
  let oldmass := fun j : Label => geometryAllocationWeight reflected s 1 1 radius Z (μ/64) 1
    (Real.logb Z (volume s)) hK key
    (fun q => normPhase (coordinateBlock s 1 1 Ψ radius Z (μ/64) q)) (Fintype.card ι) (9/4) j.val
  ∃ τ : (j : Label) → actualAllocations s.pools (C j) → elementPool P → Fin 3 → RayCharacter → Character,
    (∀ j B q i ψ, (τ j B q i ψ).modulus.absNorm ≤
      radicalBound (childCharacter (χ j) ψ) fixedBadMask q.val (errorMovingExponent (errorIndex i))) ∧
    unevenLiveBudget reflected s 1 1 radius Z (μ/64) 1 (Real.logb Z (volume s)) hK key
      (fun q => normPhase (coordinateBlock s 1 1 Ψ radius Z (μ/64) q)) (Fintype.card ι) (9/4) height ≤
    (56/(P.card : ℝ))*
      (((amplifierCap 2 0 1+6*amp)/(amp/2))*
        (∑ j, ∑ B, mass j B * actualMainSource (child s (C j) 1 B (χ j) height) (g j)
          Z (3*amp) 1 (μ/64) (μ/8)) +
        ∑ j, ∑ B, oldmass j B * actualErrorSources (child s (C j) 1 B (χ j) height) (g j)
          Z (3*amp) 1 (μ/64) (μ/8) P (τ j B))

variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineRetainedBudgetFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The actual affine amplifier pays zero and tail terms uniformly over the
original slot subset. Its chosen radical family and exact retained sums remain. -/
theorem actual_affine_geometry_retained_budget
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (W : ℝ → ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (loss mesh μ : ℝ) (hloss : 0 < loss) (hμ : 0 < μ) (hμcap : μ ≤ 1/128)
    (hmesh : mesh < Sil.Uneven.MainSource.amplifierMinimum/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ (hZ : 1 < Z)
      (T : Finset α) (η₀ : Character) (θ : T → RayQuotient.Characters rayM H)
      (w σ freq : T → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc (33/50 : ℝ) (33/50))
      (bΦ : ℝ) (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
      (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (81/200 : ℝ) ≤ length Z X₁ → (81/200 : ℝ) ≤ length Z X₂ →
      length Z X₁ ≤ (45/100 : ℝ) → length Z X₂ ≤ (45/100 : ℝ) →
      (17/500 : ℝ) ≤ ∑ i, w i → (∑ i, w i) ≤ (1/25 : ℝ) →
      length Z X₁ + length Z X₂ + plane.lambda * (∑ i, w i) ≤ plane.B →
      let inp := affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta := Sil.Uneven.MainSource.widthCellUpper (∑ i, w i)
      let amp := Sil.Uneven.MainSource.amp plane beta
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      P.Nonempty ∧ Z^(amp-loss) ≤ (P.card : ℝ) ∧
      ∀ (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)) (Ψ : 𝓢(ℝ,ℂ)) (height : ℝ),
      let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1 : ℝ)
      let First := GeometryLowFirstIndex reflected inp 1 1 (Z^(1 : ℝ)) Z (μ/64) hK key
      ∃ υ : First → elementPool P → Fin 3 → RayCharacter → Character,
        (∀ f q i ψ, (υ f q i ψ).modulus.absNorm ≤
          radicalBound (childCharacter
            (geometryColumnCharacter reflected inp 1 1 (Z^(1 : ℝ)) Z (μ/64) hK key f.1.val) ψ)
            fixedBadMask q.val (errorMovingExponent (errorIndex i))) ∧
        unevenLiveBudget reflected inp 1 1 (Z^(1 : ℝ)) Z (μ/64) 1
          (Real.logb Z (volume inp)) hK key
          (fun q => normPhase (coordinateBlock inp 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))
          (Fintype.card T) (9/4) height ≤
        C * (p.control {(0,0)})^2 *
          geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
          Z^(-(1/20 : ℝ)) +
        (56/(P.card : ℝ)) *
          (((amplifierCap 2 0 1 + 6*amp)/(amp/2)) *
            ‖unevenMainRetainedSum reflected inp 1 1 Z 1 amp (μ/64) (μ/8) (9/4) height hZ key
              1 (Real.logb Z (volume inp))
              (fun q => normPhase (coordinateBlock inp 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))‖ +
            ‖geometryAffineErrorRetainedSum inp Ψ Z amp (μ/64) (μ/8) height hZ reflected key P υ‖) := by
  obtain ⟨Cs, hCs, hsources⟩ := AuxiliaryPhysical.eventual_actual_affine_exceptional_source_gates (α := α)
    rayM H hH W hW hWs
  obtain ⟨Cm, hCm, hmain⟩ := uniform_actual_affine_main_remainder (plane:=plane) (α := α) Cs μ hCs hμ hμcap
  obtain ⟨Ce, hCe, herror⟩ := uniform_actual_affine_error_remainder (plane:=plane) (α := α) Cs μ hCs hμ hμcap
  refine ⟨56*2000000*Cm+Ce, by positivity, ?_⟩
  have hamp := MainReconstruction.actual_affine_geometry_amplification (plane:=plane) (α := α) rayM H hH Sbad hbad W hW hWs
    loss mesh (μ/64) (μ/8) hloss hmesh (by positivity) (by linarith) (by positivity)
  have hcop := MainReconstruction.eventual_geometry_affine_prime_coprime (plane:=plane) rayM H hH Sbad hbad 2 mesh hmesh
  filter_upwards [hsources, hmain, herror, hamp, hcop] with Z hs hm he ha hc
  refine ⟨hs.1, ?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone inp beta amp P
  have capsAmbient := hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have caps : GeometryAffineExceptionalSourceGates inp p (Fintype.card T) Cs Z :=
    { capsAmbient with card := le_rfl }
  have hb := (Sil.Uneven.MainSource.widthCellUpper_bounds ⟨hwlo,hwhi⟩).1
  have hV := MainReconstruction.actual_affine_exceptional_volume_cell (plane:=plane) rayM H hH η₀ θ W hW hWs w σ freq hσ
    state p t X₁ X₂ hX₁ hX₂ hZ hlo₁ hlo₂ ⟨hwlo, hwhi⟩ hcone
  have amplified := ha.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
  refine ⟨amplified.1, amplified.2.1, ?_⟩
  intro reflected key Ψ height hK First
  have hp : ∀ Q ∈ P, Prime Q := fun Q hQ => (primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  have hgood : ∀ Q ∈ P, Q ∉ fixedBadPrimes := fun Q hQ =>
    (primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  have hpcap : ∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z^amp := by
    intro Q hQ
    have hn := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) amp) (Finset.mem_sdiff.mp hQ).1
    simpa only [mul_one] using hn.2
  have hmatches : Matches rayM H hH inp η₀ θ w σ freq W 2 Z := by
    constructor <;> intros <;> rfl
  have hslots := hc.2 beta hb.1 hb.2 inp η₀ θ w σ freq W hmatches hwm
  have main := hm hZ T inp p caps beta hb hV Ψ height reflected key
  have errors := he hZ T inp p caps beta hb hV P amplified.1 hp hgood hpcap hslots Ψ height reflected key
  have hframeZ : amplifiedRadiusFrame inp Z amp μ reflected key Ψ height P Z (zero_lt_one.trans hZ) := by
    obtain ⟨τ,hτ,hbound⟩ := amplified.2.2 reflected key
      (fun q => normPhase (coordinateBlock inp 1 1 Ψ Z Z (μ/64) q)) (Fintype.card T) height
    have herr := uneven_error_cost_le reflected inp 1 1 Z Z (μ/64) 1
      (Real.logb Z (volume inp)) (3*amp) (μ/8) (9/4) height
      (zero_lt_one.trans hZ) hZ key
      (fun q => normPhase (coordinateBlock inp 1 1 Ψ Z Z (μ/64) q)) (Fintype.card T) P τ
    exact ⟨τ,hτ,hbound.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) herr)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
  have hRadius : (⟨Z,zero_lt_one.trans hZ⟩ : {r : ℝ // 0 < r}) = ⟨Z^(1 : ℝ),hK⟩ :=
    Subtype.ext (Real.rpow_one Z).symm
  have hType := congrArg (fun r : {r : ℝ // 0 < r} =>
    amplifiedRadiusFrame inp Z amp μ reflected key Ψ height P r.val r.property) hRadius
  have hframePow := Eq.mp hType hframeZ
  obtain ⟨τ, hτ, hbound⟩ := hframePow
  let υ := fun f : First => τ f.1 f.2
  refine ⟨υ, ?_, ?_⟩
  · intro f q i ψ
    exact hτ f.1 f.2 q i ψ
  have hn : (1 : ℝ) ≤ P.card := by exact_mod_cast amplified.1.card_pos
  have havg : 0 ≤ 56/(P.card : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have havg56 : 56/(P.card : ℝ) ≤ 56 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr
    linarith
  have hcoefficient := MainHigh.geometry_affine_main_amplifier_bound plane beta hb
  have hfactor : 0 ≤ (p.control {(0,0)})^2 *
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simp only [mul_assoc] at hfactor
  have main' := main
  simp only [unevenAffineMainSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, mul_assoc] at main'
  have errors' := errors υ
  simp only [geometryAffineErrorSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, υ, mul_assoc] at errors'
  have joined := retained_remainder_join _ _ _ _ _ _ _ Cm Ce _ havg havg56
    hcoefficient.1 hcoefficient.2 hCm.le hfactor hbound main' errors'
  convert joined using 1
  simp only [mul_assoc, amp, υ]

end
end OAI.SevenEighths.MainAssembly
end

/- Original module: Candidate.Uneven.MainAssemblyPaidAssembly. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.MainAssembly
open Target830.Source.Uneven
noncomputable section
open Sil.Uneven.MainSource
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily QuadraticInitialBound CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle63InitialSource CenteredMomentLogDyadic Cycle63Moment
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyFirstAnnularAdmission ConcretePrimeRowBridge
open RayFourExpansion CenteredMomentPrimePool CenteredMomentAmplificationRadicalFamily
open CenteredMomentPrimeElements CenteredMomentChildRows CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationActiveFactor CenteredMomentAllocatedRayDictionary
open CenteredMomentAmplificationRadicalChoice CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O
local instance paidAssemblySumDecidable {ι : Type} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ geometryAffineErrorRetainedSum unevenMainRetainedSum unevenLiveBudget

/-- Separate the actual shifted first height from the original source
height. This transport changes only polynomial scalar factors. -/
theorem affine_paid_height_product (t firstHeight height : ℝ)(D : ℕ)(hh : 0≤ height) :
    (1+|firstHeight|+height)^D≤(1+|t|+height)^D*(1+‖firstHeight‖)^D := by
  rw [←mul_pow,Real.norm_eq_abs]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [abs_nonneg t,abs_nonneg firstHeight,
    mul_nonneg (abs_nonneg t) (abs_nonneg firstHeight),
    mul_nonneg hh (abs_nonneg firstHeight)]

/-- Join the two already-paid physical components with the retained
zero/tail remainder. The prime average is consumed exactly once. -/
theorem affine_paid_budget_of_components
    (p : Profiles (1/4) (9/4))(Sm Se : Finset (ℕ×ℕ))
    (budget main error average coefficient Cr Cm Ce H t firstHeight height Z εmass : ℝ)
    (Dm De : ℕ)(hCr : 0≤ Cr)(hCm : 0≤ Cm)(hCe : 0≤ Ce)(hH : 0≤ H)
    (hh : 0≤ height)(hZ : 1< Z)(hε : 0≤εmass)
    (hbudget : budget≤ Cr*(p.control {(0,0)})^2*H*Z^(-(1/20:ℝ))+
      average*(coefficient*main+error))
    (hmain : average*coefficient*main≤ Cm*(p.control Sm)^2*H*
      (1+|firstHeight|+height)^Dm*Z^(-(1/2000000000:ℝ)))
    (herror : average*error≤ Ce*(p.control Se)^2*H*
      (1+|firstHeight|+height)^De*Z^(-(1/4000000000:ℝ))) :
    let S:=({(0,0)}∪Sm)∪Se
    budget≤(Cr+Cm+Ce)*H*(p.control S)^2*(1+|t|+height)^(max Dm De)*
      (1+‖firstHeight‖)^(max Dm De)*Z^εmass := by
  intro S
  have hm : average*coefficient*main≤ Cm*H*(p.control Sm)^2*
      (1+|t|+height)^Dm*(1+‖firstHeight‖)^Dm*Z^(-(1/2000000000:ℝ)) := by
    apply hmain.trans
    have hh:=mul_le_mul_of_nonneg_left (affine_paid_height_product t firstHeight height Dm hh)
      (by positivity : 0≤ Cm*(p.control Sm)^2*H)
    have hz:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (zero_lt_one.trans hZ).le (-(1/2000000000:ℝ)))
    convert hz using 1;ring
  have he : average*error≤ Ce*H*(p.control Se)^2*
      (1+|t|+height)^De*(1+‖firstHeight‖)^De*Z^(-(1/4000000000:ℝ)) := by
    apply herror.trans
    have hh:=mul_le_mul_of_nonneg_left (affine_paid_height_product t firstHeight height De hh)
      (by positivity : 0≤ Ce*(p.control Se)^2*H)
    have hz:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (zero_lt_one.trans hZ).le (-(1/4000000000:ℝ)))
    convert hz using 1;ring
  apply geometry_affine_paid_branch_budget p Sm Se budget main error average coefficient
    Cr Cm Ce H (1+|t|+height) (1+‖firstHeight‖) Z (-(1/2000000000)) (-(1/4000000000)) εmass
    Dm De Dm De hCr hCm hCe hH (by linarith [abs_nonneg t])
    (by linarith [norm_nonneg firstHeight]) hZ (by linarith) (by linarith) hε _ hm he
  convert hbudget using 1;ring

variable {plane : Sil.Uneven.MainSource.Plane}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance paidAssemblyFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hray : Subgroup (O⧸rayM)ˣ) (hHray : RayOrthogonality.globalUnits rayM≤ Hray)

/-- Explicit pending paid components on the literal actual subset source.
The error receipt is universal in the original retained radical witness;
the assembly therefore cannot silently replace that witness. -/
def GeometryAffinePaidSubsetComponents
    (Sbad : Finset (Ideal O))
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh μ τ : ℝ)(Ψ : 𝓢(ℝ,ℂ))(T : Finset α)
    (Sm Se : Finset (ℕ×ℕ))(Dm De : ℕ)(Cm Ce Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(θ : T→RayQuotient.Characters rayM Hray)(w σ freq : T→ℝ)(t height : ℝ),
    (∀i,0≤ w i) → (∀i,w i≤ mesh) →
  ∀(hσlo : ∀i,(33/50:ℝ)≤σ i)(hσhi : ∀i,σ i≤(33/50:ℝ)),
    0≤ height → (∀i,|freq i|≤ height) → 1+|t|+height≤ Z^τ →
  ∀(Φ : 𝓢(ℝ,ℂ))(hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hpΦ : ∀x,0≤(Φ x).re)(p : Profiles (1/4) (9/4))(X₁ X₂ : ℝ)
    (hX₁ : 0< X₁)(hX₂ : 0< X₂),
    (81/200:ℝ)≤ length Z X₁ → length Z X₁≤(45/100:ℝ) →
    (81/200:ℝ)≤ length Z X₂ → length Z X₂≤(45/100:ℝ) →
    (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
    length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤ plane.B →
  let state:=fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
  let s:=affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
    1 t X₁ X₂ hX₁ hX₂
  let amp:=Sil.Uneven.MainSource.amp plane (Sil.Uneven.MainSource.widthCellUpper (∑i,w i))
  let P:=CenteredMomentPrimePool.primePool rayM Hray Sbad (1/2) 1 (Z^amp)
  ∀key∈commonGeometryBins s 1 1 Z Z (μ/64),∀(reflected : Bool)(firstHeight : ℝ),
  let side:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key
  let phase:=fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q)
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let First:=GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key
  (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
    ‖unevenMainRetainedSum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight hZ key
      1 (Real.logb Z (volume s)) phase‖≤
    Cm*(p.control Sm)^2*side*(1+|firstHeight|+height)^Dm*Z^(-(1/2000000000:ℝ)) ∧
  ∀υ : First→elementPool P→Fin 3→RayCharacter→Character,
    (∀f q i ψ,(υ f q i ψ).modulus.absNorm≤
      radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key f.1.val) ψ)
        fixedBadMask q.val (errorMovingExponent (errorIndex i))) →
    (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z amp (μ/64) (μ/8)
      firstHeight hZ reflected key P υ‖≤
      Ce*(p.control Se)^2*side*(1+|firstHeight|+height)^De*Z^(-(1/4000000000:ℝ))

/-- Compose the retained budget with explicit already-paid components.
The common cutoff precedes the detector; subset controls and degrees are
chosen after it and before the moving source. This is conditional on the
component receipts and makes no unconditional endpoint claim. -/
theorem literal_affine_geometry_budget_of_paid_components
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ loss mesh μ εmass τ : ℝ)
    (hloss : 0< loss)(hμ : 0<μ)(hμcap : μ≤1/128)
    (hmesh : mesh< Sil.Uneven.MainSource.amplifierMinimum/2)(hεmass : 0≤εmass)
    (hcomponents :
      ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
        (∀x,0≤(Ψ x).re) →
      ∀T : Finset α,∃(Sm Se : Finset (ℕ×ℕ))(Dm De : ℕ)(Cm Ce : ℝ),0≤ Cm ∧ 0≤ Ce ∧
        ∀ᶠZ : ℝ in atTop,GeometryAffinePaidSubsetComponents (plane:=plane) rayM Hray hHray Sbad W hW hWs
          η η₀ Q bΦ mesh μ τ Ψ T Sm Se Dm De Cm Ce Z) :
    LiteralAffineGeometryBudget (plane:=plane) (α:=α) rayM Hray hHray W hW hWs
      η η₀ Q bΦ mesh εmass τ (μ/64) := by
  obtain ⟨Cr,hCr,hretained⟩:=actual_affine_geometry_retained_budget (plane:=plane) (α:=α) rayM Hray hHray
    Sbad hbad W hW hWs loss mesh μ hloss hμ hμcap hmesh
  apply literal_affine_geometry_budget_of_subset_budgets (plane:=plane) rayM Hray hHray W hW hWs
    η η₀ Q bΦ mesh εmass τ (μ/64)
  intro Ψ hΨ hpΨ T
  obtain ⟨Sm,Se,Dm,De,Cm,Ce,hCm,hCe,hpaid⟩:=hcomponents Ψ hΨ hpΨ T
  refine ⟨max Dm De,max Dm De,({(0,0)}∪Sm)∪Se,Cr+Cm+Ce,by linarith,?_⟩
  filter_upwards [hretained,hpaid] with Z hr hp
  intro hZ θ w σ freq t height hw hwm hσlo hσhi hh hv hcut Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂
    hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcone state s key hkey reflected t' u
  let firstHeight:=s.t+2*Real.pi*(u-(if reflected then -t' else t'))
  have hb:=hr.2 hZ T η₀ θ w σ freq (fun i=>⟨hσlo i,hσhi i⟩) bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone
  obtain ⟨υ,hυ,hbudget⟩:=hb.2.2 reflected key Ψ firstHeight
  have hc:=hp hZ θ w σ freq t height hw hwm hσlo hσhi hh hv hcut Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂
    hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcone key hkey reflected firstHeight
  have he:=hc.2 υ hυ
  have hside:=geometry_high_factor_pos reflected 64 key (by norm_num)
  have joined:=affine_paid_budget_of_components p Sm Se _ _ _ _ _ Cr Cm Ce
    (geometryHighFactor reflected 64 key) t firstHeight height Z εmass Dm De
    hCr.le hCm hCe hside.le hh hZ hεmass
    (by simpa only [geometry_affine_support_constant] using hbudget)
    (by simpa only [geometry_affine_support_constant] using hc.1)
    (by simpa only [geometry_affine_support_constant] using he)
  exact joined

end
end OAI.SevenEighths.MainAssembly
end
