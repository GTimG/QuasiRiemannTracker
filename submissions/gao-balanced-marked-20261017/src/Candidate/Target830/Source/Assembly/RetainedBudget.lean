import Candidate.Target830.Source.Reconstruction.BalancedAffineAmplification
import Candidate.Target830.Source.Assembly.ErrorWeight
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target830.High.BudgetJoin
import Candidate.Target830.Source.Assembly.UniformRemainder

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open Reconstruction
variable {plane : SourcePlane}
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
    (hcoeff : 0 ≤ coeff) (hcoeff4096 : coeff ≤ 4096)
    (hCm : 0 ≤ Cm) (hfactor : 0 ≤ factor)
    (hb : budget ≤ average * (coeff * main + error))
    (hm : main ≤ Cm * factor + nm)
    (he : average * error ≤ Ce * factor + average * ne) :
    budget ≤ (56 * 4096 * Cm + Ce) * factor + average * (coeff * nm + ne) := by
  have hmain := mul_le_mul_of_nonneg_left hm (mul_nonneg havg hcoeff)
  have hcoef : average * coeff * Cm ≤ 56 * 4096 * Cm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul havg56 hcoeff4096 hcoeff (by norm_num)) hCm
  have hpaid := mul_le_mul_of_nonneg_right hcoef hfactor
  nlinarith only [hb, hmain, he, hpaid]

private def amplifiedRadiusFrame {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (Z amp μ : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ))
    (Ψ : 𝓢(ℝ,ℂ)) (height : ℝ) (P : Finset (Ideal O)) (radius : ℝ) (hK : 0 < radius) : Prop :=
  let Label := ↥(firstLiveColumns (geometryFirstSource s 1 1 radius Z (μ/64) hK key) (fun _ => logAnnulus))
  let C := fun j : Label => geometryColumnIdeal reflected s 1 1 radius Z (μ/64) hK key j.val
  let χ := fun j : Label => geometryColumnCharacter reflected s 1 1 radius Z (μ/64) hK key j.val
  let g := fun j : Label => geometryBranch reflected s 1 1 radius Z (μ/64) hK key j.val
  let mass := fun j : Label => balancedAllocationWeight reflected s 1 1 radius Z (μ/64) 1
    (Real.logb Z (volume s)) hK key
    (fun q => normPhase (coordinateBlock s 1 1 Ψ radius Z (μ/64) q)) (Fintype.card ι) (9/4) j.val
  let oldmass := fun j : Label => geometryAllocationWeight reflected s 1 1 radius Z (μ/64) 1
    (Real.logb Z (volume s)) hK key
    (fun q => normPhase (coordinateBlock s 1 1 Ψ radius Z (μ/64) q)) (Fintype.card ι) (9/4) j.val
  ∃ τ : (j : Label) → actualAllocations s.pools (C j) → elementPool P → Fin 3 → RayCharacter → Character,
    (∀ j B q i ψ, (τ j B q i ψ).modulus.absNorm ≤
      radicalBound (childCharacter (χ j) ψ) fixedBadMask q.val (errorMovingExponent (errorIndex i))) ∧
    balancedLiveBudget reflected s 1 1 radius Z (μ/64) 1 (Real.logb Z (volume s)) hK key
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
    (hmesh : mesh < Source.amplifierMinimum/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ (hZ : 1 < Z)
      (T : Finset α) (η₀ : Character) (θ : T → RayQuotient.Characters rayM H)
      (w σ freq : T → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc (33/50 : ℝ) (33/50))
      (bΦ : ℝ) (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
      (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (81/200 : ℝ) ≤ length Z X₁ → (81/200 : ℝ) ≤ length Z X₂ →
      length Z X₁ ≤ (44/100 : ℝ) → length Z X₂ ≤ (44/100 : ℝ) →
      (17/500 : ℝ) ≤ ∑ i, w i → (∑ i, w i) ≤ (1/25 : ℝ) →
      length Z X₁ + length Z X₂ + plane.lambda * (∑ i, w i) ≤ plane.B →
      let inp := affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta := Source.widthCellUpper (∑ i, w i)
      let amp := plane.amp beta
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
        balancedLiveBudget reflected inp 1 1 (Z^(1 : ℝ)) Z (μ/64) 1
          (Real.logb Z (volume inp)) hK key
          (fun q => normPhase (coordinateBlock inp 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))
          (Fintype.card T) (9/4) height ≤
        C * (p.control {(0,0)})^2 *
          geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
          Z^(-(1/20 : ℝ)) +
        (56/(P.card : ℝ)) *
          (((amplifierCap 2 0 1 + 6*amp)/(amp/2)) *
            ‖balancedMainRetainedSum reflected inp 1 1 Z 1 amp (μ/64) (μ/8) (9/4) height hZ key
              1 (Real.logb Z (volume inp))
              (fun q => normPhase (coordinateBlock inp 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))‖ +
            ‖geometryAffineErrorRetainedSum inp Ψ Z amp (μ/64) (μ/8) height hZ reflected key P υ‖) := by
  obtain ⟨Cs, hCs, hsources⟩ := LowPhysical.eventual_actual_affine_exceptional_source_gates (α := α)
    rayM H hH W hW hWs
  obtain ⟨Cm, hCm, hmain⟩ := uniform_actual_affine_main_remainder (plane:=plane) (α := α) Cs μ hCs hμ hμcap
  obtain ⟨Ce, hCe, herror⟩ := uniform_actual_affine_error_remainder (plane:=plane) (α := α) Cs μ hCs hμ hμcap
  refine ⟨56*4096*Cm+Ce, by positivity, ?_⟩
  have hamp := Reconstruction.actual_affine_balanced_amplification (plane:=plane) (α := α) rayM H hH Sbad hbad W hW hWs
    loss mesh (μ/64) (μ/8) hloss hmesh (by positivity) (by linarith) (by positivity)
  have hcop := Reconstruction.eventual_geometry_affine_prime_coprime (plane:=plane) rayM H hH Sbad hbad 2 mesh hmesh
  filter_upwards [hsources, hmain, herror, hamp, hcop] with Z hs hm he ha hc
  refine ⟨hs.1, ?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone inp beta amp P
  have capsAmbient := hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have caps : GeometryAffineExceptionalSourceGates inp p (Fintype.card T) Cs Z :=
    { capsAmbient with card := le_rfl }
  have hb := (Source.widthCellUpper_bounds ⟨hwlo,hwhi⟩).1
  have hV := Reconstruction.actual_affine_exceptional_volume_cell (plane:=plane) rayM H hH η₀ θ W hW hWs w σ freq hσ
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
    have herr := balanced_error_cost_le reflected inp 1 1 Z Z (μ/64) 1
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
  have hcoefficient := TargetHigh830.geometry_affine_main_amplifier_bound plane beta hb
  have hfactor : 0 ≤ (p.control {(0,0)})^2 *
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simp only [mul_assoc] at hfactor
  have main' := main
  simp only [balancedAffineMainSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, mul_assoc] at main'
  have errors' := errors υ
  simp only [geometryAffineErrorSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, υ, mul_assoc] at errors'
  have joined := retained_remainder_join _ _ _ _ _ _ _ Cm Ce _ havg havg56
    hcoefficient.1 hcoefficient.2 hCm.le hfactor hbound main' errors'
  convert joined using 1
  simp only [mul_assoc, amp, υ]

end
end OAI.SevenEighths.Target830.Source.Assembly

#print axioms OAI.SevenEighths.Target830.Source.Assembly.actual_affine_geometry_retained_budget
