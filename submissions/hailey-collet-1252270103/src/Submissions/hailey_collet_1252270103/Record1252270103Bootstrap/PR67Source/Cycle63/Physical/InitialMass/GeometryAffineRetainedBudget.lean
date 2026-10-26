import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryBudgetJoin
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineUniformRemainder
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineExceptionalPayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
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

private theorem retained_remainder_join
    (budget main error nm ne average coeff cap Cm Ce factor : ℝ)
    (havg : 0 ≤ average) (havg56 : average ≤ 56)
    (hcoeff : 0 ≤ coeff) (hcoeffCap : coeff ≤ cap)
    (hCm : 0 ≤ Cm) (hfactor : 0 ≤ factor)
    (hb : budget ≤ average * (coeff * main + error))
    (hm : main ≤ Cm * factor + nm)
    (he : average * error ≤ Ce * factor + average * ne) :
    budget ≤ (56 * cap * Cm + Ce) * factor + average * (coeff * nm + ne) := by
  have hmain := mul_le_mul_of_nonneg_left hm (mul_nonneg havg hcoeff)
  have hcoef : average * coeff * Cm ≤ 56 * cap * Cm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul havg56 hcoeffCap hcoeff (by norm_num)) hCm
  have hpaid := mul_le_mul_of_nonneg_right hcoef hfactor
  nlinarith only [hb, hmain, he, hpaid]

private def amplifiedRadiusFrame {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (Z amp μ : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ))
    (Ψ : 𝓢(ℝ,ℂ)) (height : ℝ) (P : Finset (Ideal O)) (radius : ℝ) (hK : 0 < radius) : Prop :=
  let Label := ↥(firstLiveColumns (geometryFirstSource s 1 1 radius Z (μ/64) hK key) (fun _ => logAnnulus))
  let C := fun j : Label => geometryColumnIdeal reflected s 1 1 radius Z (μ/64) hK key j.val
  let χ := fun j : Label => geometryColumnCharacter reflected s 1 1 radius Z (μ/64) hK key j.val
  let g := fun j : Label => geometryBranch reflected s 1 1 radius Z (μ/64) hK key j.val
  let mass := fun j : Label => geometryAllocationWeight reflected s 1 1 radius Z (μ/64) 1
    (Real.logb Z (volume s)) hK key
    (fun q => normPhase (coordinateBlock s 1 1 Ψ radius Z (μ/64) q)) (Fintype.card ι) (9/4) j.val
  ∃ τ : (j : Label) → actualAllocations s.pools (C j) → elementPool P → Fin 3 → RayCharacter → Character,
    (∀ j B q i ψ, (τ j B q i ψ).modulus.absNorm ≤
      radicalBound (childCharacter (χ j) ψ) fixedBadMask q.val (errorMovingExponent (errorIndex i))) ∧
    geometryLiveBudget reflected s 1 1 radius Z (μ/64) 1 (Real.logb Z (volume s)) hK key
      (fun q => normPhase (coordinateBlock s 1 1 Ψ radius Z (μ/64) q)) (Fintype.card ι) (9/4) height ≤
    (56/(P.card : ℝ))*
      (((amplifierCap 2 0 1+6*amp)/(amp/2))*
        (∑ j, ∑ B, mass j B * actualMainSource (child s (C j) 1 B (χ j) height) (g j)
          Z (3*amp) 1 (μ/64) (μ/8)) +
        ∑ j, ∑ B, mass j B * actualErrorSources (child s (C j) 1 B (χ j) height) (g j)
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
    (hmesh : mesh < ((Cycle63.AffineLedger.amplifierFloor) : ℝ)/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ (hZ : 1 < Z)
      (T : Finset α) (η₀ : Character) (θ : T → RayQuotient.Characters rayM H)
      (w σ freq : T → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc (33/50 : ℝ) (33/50))
      (bΦ : ℝ) (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
      (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
      let inp := affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
      let beta := Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑ i, w i))
      let amp := Cycle63.AffineLedger.amp beta
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
        geometryLiveBudget reflected inp 1 1 (Z^(1 : ℝ)) Z (μ/64) 1
          (Real.logb Z (volume inp)) hK key
          (fun q => normPhase (coordinateBlock inp 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))
          (Fintype.card T) (9/4) height ≤
        C * (p.control {(0,0)})^2 *
          geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
          Z^(-(1/20 : ℝ)) +
        (56/(P.card : ℝ)) *
          (((amplifierCap 2 0 1 + 6*amp)/(amp/2)) *
            ‖geometryMainRetainedSum reflected inp 1 1 Z 1 amp (μ/64) (μ/8) (9/4) height hZ key
              1 (Real.logb Z (volume inp))
              (fun q => normPhase (coordinateBlock inp 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))‖ +
            ‖geometryAffineErrorRetainedSum inp 1 1 Ψ Z 1 amp (μ/64) (μ/8) height hZ reflected key P υ‖) := by
  obtain ⟨Cs, hCs, hsources⟩ := eventual_actual_affine_exceptional_source_gates (α := α)
    rayM H hH W hW hWs
  obtain ⟨Cm, hCm, hmain⟩ := uniform_actual_affine_main_remainder (α := α) Cs μ hCs hμ hμcap
  obtain ⟨Ce, hCe, herror⟩ := uniform_actual_affine_error_remainder (α := α) Cs μ hCs hμ hμcap
  refine ⟨56*geometryAmplifierCoefficientCap*Cm+Ce, by have := geometryAmplifierCoefficientCap_pos; positivity, ?_⟩
  have hamp := actual_affine_geometry_amplification (α := α) rayM H hH Sbad hbad W hW hWs
    loss mesh (μ/64) (μ/8) hloss hmesh (by positivity) (by linarith) (by positivity)
  have hcop := eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh
  filter_upwards [hsources, hmain, herror, hamp, hcop] with Z hs hm he ha hc
  refine ⟨hs.1, ?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hwin inp beta amp P
  have capsAmbient := hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwin
  have caps : GeometryAffineExceptionalSourceGates inp p (Fintype.card T) Cs Z :=
    { capsAmbient with card := le_rfl }
  have hcell := Cycle63.AffineLedger.originalCell_mem ⟨hwin.slots_ge,hwin.slots_le⟩
  have hb := Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hV := actual_affine_exceptional_volume_cell rayM H hH η₀ θ W hW hWs w σ freq hσ
    state p t X₁ X₂ hX₁ hX₂ hZ hwin
  have amplified := ha.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hwin
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
  have hframeZ : amplifiedRadiusFrame inp Z amp μ reflected key Ψ height P Z (zero_lt_one.trans hZ) :=
    amplified.2.2 reflected key
    (fun q => normPhase (coordinateBlock inp 1 1 Ψ Z Z (μ/64) q)) (Fintype.card T) height
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
  have hcoefficient := geometry_affine_main_amplifier_bound beta hb
  have hfactor : 0 ≤ (p.control {(0,0)})^2 *
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simp only [mul_assoc] at hfactor
  have main' := main
  simp only [geometryAffineMainSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, mul_assoc] at main'
  have errors' := errors υ
  simp only [geometryAffineErrorSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, υ, mul_assoc] at errors'
  have joined := retained_remainder_join _ _ _ _ _ _ _ _ Cm Ce _ havg havg56
    hcoefficient.1 hcoefficient.2 hCm.le hfactor hbound main' errors'
  convert joined using 1
  simp only [mul_assoc, amp, υ]

variable [Cycle63.AffineLedger] in
/-- The actual affine amplifier pays zero and tail terms uniformly over the original slot subset, at a parent with puncture `R`,
seed `seed` and radial scale `Z^Mrow`. Its chosen radical family and exact retained sums remain. -/
theorem actual_affine_geometry_parent_retained_budget
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad) (W : ℝ → ℂ)
    (loss mesh μ : ℝ) (hloss : 0 < loss) (hμ : 0 < μ) (hμcap : μ ≤ 1/128)
    (hmesh : mesh < ((Cycle63.AffineLedger.amplifierFloor) : ℝ)/2) (Cs : ℝ) (hCs : 1 ≤ Cs) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ (hZ : 1 < Z)
      (T : Finset α) (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ (η₀ : Character) (θ : T → RayQuotient.Characters rayM H) (w σ freq : T → ℝ),
      Matches rayM H hH s η₀ θ w σ freq W 2 Z →
      (∀ v : (T ⊕ Fin 2) → Ideal O, (∀ j, v j ∈ s.pools j) → ((CenteredMomentAddedZeroUniform.finiteTupleProduct v).absNorm : ℝ) ≤ Z^(3:ℝ)) →
    ∀ (R seed : Ideal O) (Mrow : ℝ), R ≠ 0 → Squarefree seed → (R.absNorm : ℝ) ≤ Z^(20:ℝ) → 0 ≤ Mrow →
      Mrow ≤ 1 → (∀ j, w j ≤ mesh) →
      (Cycle63.AffineLedger.slotFloor ≤ ∑ j, Real.logb Z (s.P j) ∧
        (∑ j, Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.slotTop) →
      length Z s.X₁ + length Z s.X₂ + Cycle63.AffineLedger.lam * (∑ j, Real.logb Z (s.P j)) ≤
        Cycle63.AffineLedger.B →
    ∀ beta : ℝ, beta = Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑ j, Real.logb Z (s.P j))) →
      let amp := Cycle63.AffineLedger.amp beta
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      P.Nonempty ∧ Z^(amp-loss) ≤ (P.card : ℝ) ∧
      ∀ (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)) (Ψ : 𝓢(ℝ,ℂ)) (height : ℝ),
      let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
      let First := GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (μ/64) hK key
      ∃ υ : First → elementPool P → Fin 3 → RayCharacter → Character,
        (∀ f q i ψ, (υ f q i ψ).modulus.absNorm ≤
          radicalBound (childCharacter
            (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64) hK key f.1.val) ψ)
            fixedBadMask q.val (errorMovingExponent (errorIndex i))) ∧
        geometryLiveBudget reflected s R seed (Z^Mrow) Z (μ/64) Mrow
          (Real.logb Z (volume s)) hK key
          (fun q => normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (μ/64) q))
          (Fintype.card T) (9/4) height ≤
        C * (p.control {(0,0)})^2 *
          geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
          Z^(-(Cycle63.AffineLedger.zeroSaving : ℝ) + (1 - Mrow)) / (seed.absNorm : ℝ) +
        (56/(P.card : ℝ)) *
          (((amplifierCap 2 0 1 + 6*amp)/(amp/2)) *
            ‖geometryMainRetainedSum reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) height hZ key
              Mrow (Real.logb Z (volume s))
              (fun q => normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (μ/64) q))‖ +
            ‖geometryAffineErrorRetainedSum s R seed Ψ Z Mrow amp (μ/64) (μ/8) height hZ reflected key P υ‖) := by
  obtain ⟨Cm, hCm, hmain⟩ := uniform_actual_affine_main_parent_remainder (α := α) Cs μ hCs hμ hμcap
  obtain ⟨Ce, hCe, herror⟩ := uniform_actual_affine_error_parent_remainder (α := α) Cs μ hCs hμ hμcap
  refine ⟨56*geometryAmplifierCoefficientCap*Cm+Ce, by have := geometryAmplifierCoefficientCap_pos; positivity, ?_⟩
  have hdata (T : Finset α) (j : ↥(Finset.Icc 1 Cycle63.AffineLedger.cellCount)) :=
    actual_geometry_budget_amplification (ι := T) rayM H hH Sbad hbad
      (3*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper j.val)) loss
      20 3 2 0 1 3 (9/4) mesh (μ/64) (μ/8)
      (by have hh := Cycle63.AffineLedger.amp_pos
            (Cycle63.AffineLedger.cellUpper_bounds (Finset.mem_Icc.mp j.property).1
              (Finset.mem_Icc.mp j.property).2)
          positivity)
      hloss (by norm_num [amplifierCap]) (by norm_num)
      (by have hh := (Cycle63.AffineLedger.amp_bounds
            (Cycle63.AffineLedger.cellUpper_bounds (Finset.mem_Icc.mp j.property).1
              (Finset.mem_Icc.mp j.property).2)).1
          linarith)
      (by positivity) (by linarith) (by positivity)
  have hamp := Filter.eventually_all.mpr (fun T : Finset α =>
    Filter.eventually_all.mpr (fun j : ↥(Finset.Icc 1 Cycle63.AffineLedger.cellCount) => hdata T j))
  have hcop := eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh
  filter_upwards [hmain, herror, hamp, hcop] with Z hm he ha hc
  refine ⟨hc.1, ?_⟩
  intro hZ T s p caps η₀ θ w σ freq hmatch hcolumns R seed Mrow hR hseed hRcap hMrow hMrow1 hwm hzslot haff
    beta hbeta amp P
  have hcell := Cycle63.AffineLedger.originalCell_mem hzslot
  have hb : Cycle63.AffineLedger.firstCellTop ≤ beta ∧ beta ≤ Cycle63.AffineLedger.slotTop := by
    rw [hbeta]
    exact Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hV : Real.logb Z (volume s) ≤ Cycle63.AffineLedger.totalA beta := by
    rw [hbeta]
    exact input_log_volume_cell_bound s Z hZ hzslot haff
  let j : ↥(Finset.Icc 1 Cycle63.AffineLedger.cellCount) :=
    ⟨Cycle63.AffineLedger.originalCell (∑ i, Real.logb Z (s.P i)),
      Finset.mem_Icc.mpr ⟨hcell.1, hcell.2.1⟩⟩
  have hg := ha T j
  have hdiv : ∀ x : ℝ, 3*x/3 = x := by intro x; ring
  have hpool : Z^(amp-loss) ≤ (P.card : ℝ) := by
    simpa only [P, amp, hbeta, j, hdiv] using hg.2.2.1
  have hne : P.Nonempty := by
    simpa only [P, amp, hbeta, j, hdiv] using hg.2.1
  refine ⟨hne, hpool, ?_⟩
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
  have hslots := hc.2 beta hb.1 hb.2 s η₀ θ w σ freq W hmatch hwm
  have main := hm hZ T s p caps R seed Mrow hseed hMrow hMrow1 beta hb hV Ψ height reflected key
  have hKi : (Z^Mrow)⁻¹ ≤ Z^(0:ℝ) := by
    rw [Real.rpow_zero]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hZ.le hMrow)
  have hsupp : ∀ i, Function.support (s.W i) ⊆ Set.Iic (9/4 : ℝ) := fun i x hx =>
    ((s.slot_support i hx).2).trans caps.endpoints.1
  have hh := hg.2.2.2 reflected s R seed (Z^Mrow) Mrow (Real.logb Z (volume s)) hK key
    (fun q => normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (μ/64) q)) (Fintype.card T) height
    (by simpa only [CenteredMomentExceptionalAmplitudePair.volume,
      CenteredMomentAmplificationChildInput.volume] using caps.volume)
    hKi hR hRcap hseed caps.zero₁ caps.zero₂ caps.sourceCap
    (by
      intro I hI
      simp only [finiteColumns, Finset.mem_image, Fintype.mem_piFinset] at hI
      obtain ⟨v, hv, rfl⟩ := hI
      exact hcolumns v hv)
    hsupp w hwm hmatch.scale
  have hf : ∀ a : ℝ, (amplifierCap 2 0 1 + 2*(3*a))/(3*a/6) = (amplifierCap 2 0 1 + 6*a)/(a/2) := by
    intro a
    ring
  have hjb : Cycle63.AffineLedger.cellUpper j.val = beta := hbeta.symm
  rw [hjb, hdiv] at hh
  simp only [hf] at hh
  obtain ⟨τ, hτ, hbound⟩ := hh
  let υ := fun f : First => τ f.1 f.2
  have errors := he hZ T s p caps R seed Mrow hseed hMrow hMrow1 beta hb hV P hne hp hgood hpcap hslots
    Ψ height reflected key υ
  refine ⟨υ, ?_, ?_⟩
  · intro f q i ψ
    exact hτ f.1 f.2 q i ψ
  have hn : (1 : ℝ) ≤ P.card := by exact_mod_cast hne.card_pos
  have havg : 0 ≤ 56/(P.card : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have havg56 : 56/(P.card : ℝ) ≤ 56 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr
    linarith
  have hcoefficient := geometry_affine_main_amplifier_bound beta hb
  have hseedNorm : 0 < (seed.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed.ne_zero)
  have hfactor : 0 ≤ (p.control {(0,0)})^2 *
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(Cycle63.AffineLedger.zeroSaving : ℝ) + (1 - Mrow)) / (seed.absNorm : ℝ) := by
    have hside := (geometry_high_factor_pos reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key
      (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
    positivity
  simp only [mul_assoc, mul_div_assoc] at hfactor
  have main' := main
  simp only [geometryAffineMainSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, mul_assoc,
    mul_div_assoc] at main'
  simp only [geometryAffineErrorSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, υ, mul_assoc,
    mul_div_assoc] at errors
  have joined := retained_remainder_join _ _ _ _ _ _ _ _ Cm Ce _ havg havg56 hcoefficient.1
    hcoefficient.2 hCm.le hfactor hbound main' errors
  convert joined using 1
  simp only [mul_assoc, mul_div_assoc, amp, υ]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
