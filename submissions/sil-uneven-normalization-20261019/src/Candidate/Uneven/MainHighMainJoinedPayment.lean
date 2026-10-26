import Candidate.Uneven.HighMass
import Candidate.Uneven.SecondWeight
import Candidate.Uneven.SelectionAffine
import Candidate.Cycle63.Physical.InitialMass.SecondFullNormalizedContraction
import Candidate.Uneven.SecondNorm
import Candidate.Uneven.MainParameters
import Candidate.Uneven.MainRetained
import Candidate.Uneven.MainAffineExceptionalPayment
import Candidate.Uneven.MainHighBudgetJoin
import Candidate.Uneven.SelectionCostReduction
import Candidate.Uneven.MainHighMainBranches
import Candidate.Uneven.MainHighMainRatioPayment

/- Original module: Candidate.Uneven.SelectionNormalized. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.UnevenSelection
noncomputable section
open OAI.SevenEighths.TargetHigh830
open OAI.SevenEighths.Target830.Source.Uneven
open OAI.SevenEighths.Cycle63InitialMass
open OAI.SevenEighths.Target830.Source
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
local instance affineMainNormalizedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The genuine physical selection receipt turns complete selected costs
into the original full-family normalized contract. Every selected first
allocation retains its complete second-block row sum. -/
theorem actual_affine_main_normalized_of_selected
    (Cs ε ξ K Z C : ℝ) (degree : ℕ) (hZ : 1< Z)
    (hK : 0≤ K) (hC : 0≤ C)
    (hselection : GeometryAffinePhysicalSelectionSpec (ι:=α) Cs ε ξ K Z)
    (reflected : Bool) (s : Input α) (p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z)
    (amp reserve height : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter) (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hselected : ∀(second : Bool)(t₀ u : ℝ),
      let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
      let rows:=firstLiveColumns (geometryFirstSource s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key) (fun _=> logAnnulus)
      let ideal:=fun j : rows=> geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key j.val
      let mass:=fun j : rows=> unevenFirstHighMass reflected s 1 1 Ψ 1 Z ξ ε hKfirst key j.val
      ∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key (column j).val,
          (column j).val.2.1.val)) →
      ∀alloc : (j : Label)→actualAllocations s.pools (ideal (column j)),
        (∀j,frozenCoefficient (alloc j).val (ideal (column j)) 1 s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*OAI.SevenEighths.UnevenSelection.geometryMainFirstCost reflected s 1 1 Z 1 amp ξ reserve
          (9/4) height (Fintype.card α) hZ key hz₁ hz₂ χ Q m 1 (1/4) second t₀ u
          ⟨column j,alloc j⟩)≤(C*(1+‖t₀‖)^degree)*(1+‖u‖)^degree) :
    let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) height
      (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=> geometryMainOrdinaryDatum reflected s 1 1 Z 1 amp ξ reserve
      (9/4) height (Fintype.card α) hZ key hz₁ hz₂ χ Q m j.val
    let weight:=fun j : selected=> unevenMainSecondWeight reflected s 1 1 Z 1 amp ξ reserve
      (9/4) height (Fintype.card α) hZ key 1 (Real.logb Z (volume s))
      (fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)) j.val
    SecondNormalizedBound W degree degree datum weight (fun _=> K*Z^ε*C) (fun _=>1) := by
  intro selected datum weight
  apply second_normalized_bound_of_full
  intro second t₀ u
  have hs := hselection hZ reflected s p caps amp reserve height key Ψ χ Q m W second t₀ u
    ((C*(1+‖t₀‖)^degree)*(1+‖u‖)^degree) hz₁ hz₂ (hselected second t₀ u)
  have hu : (1+‖u‖)^degree≤(1+‖u‖)^(2*degree) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg u]) (by omega)
  have hc : 0≤(K*Z^ε)*(C*(1+‖t₀‖)^degree) := by positivity
  have he := mul_le_mul_of_nonneg_left hu hc
  apply hs.trans
  convert he using 1 <;> ring

end
end OAI.SevenEighths.UnevenSelection
end

/- Original module: Candidate.Uneven.SecondComparison. -/
section
/- Adapted from PR63 by Sil, with OpenAI Codex assistance.
   Original attribution and Apache-2.0 license are retained. -/

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Uneven
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
variable (Mprice Aprice : ℝ)
variable (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)

/-- Actual common surplus decreases the second weight pointwise.
No cancellation or HIGH source estimate is replaced by this comparison. -/
theorem uneven_main_second_weight_norm_le
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    ‖unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j‖≤
      ‖geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j‖ := by
  have hs := actual_allocation_nonneg reflected s R seed (Z^Mrow) Z ξ hZ j.1.1.val.1.val
  have hp : Z^(-allocation reflected (geometryExponents s R seed (Z^Mrow) Z ξ j.1.1.val.1.val))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hZ.le (neg_nonpos.mpr hs)
  rw [unevenMainSecondWeight_eq]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (norm_nonneg (geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j))

theorem uneven_main_second_product_norm_le
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)
    (value : ℂ) :
    ‖unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j*value‖≤
      ‖geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j*value‖ := by
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    (uneven_main_second_weight_norm_le reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j)
    (norm_nonneg _)

/-- Complete selected exceptional families retain the same indices and
values; only their actual first-allocation weight is reduced. -/
theorem uneven_main_second_norm_sum_le {Label : Type*} [Fintype Label]
    (column : Label→GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)
    (value : Label→ℂ) :
    (∑j,‖unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight (column j)*value j‖)≤
      ∑j,‖geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight (column j)*value j‖ := by
  exact Finset.sum_le_sum (fun j _=> uneven_main_second_product_norm_le
    reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight (column j) (value j))

end
end OAI.SevenEighths.Target830.Source.Uneven
end

/- Original module: Candidate.Uneven.MainHighMainContraction. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

namespace OAI.SevenEighths.MainHigh
noncomputable section
open Sil.Uneven.MainSource
open Target830.Source.Uneven
open MainReconstruction
open MainAssembly
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.MainAssembly
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentAllocatedRayDictionary
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

private theorem affine_main_plain_zero (p : Profiles (1/4) (9/4)) (i : Fin 2) :
    p.profile i 0 = 0 := by
  by_contra h
  have hh := (p.support i h).1
  norm_num at hh

private theorem main_paid_join (average coefficient norm exceptional ordinary C payment : ℝ)
    (ha : 0 ≤ average) (hc : 0 ≤ coefficient)
    (hn : norm ≤ exceptional + C*ordinary)
    (he : average*coefficient*exceptional ≤ payment) :
    average*coefficient*norm ≤ payment+C*average*coefficient*ordinary := by
  have h := mul_le_mul_of_nonneg_left hn (mul_nonneg ha hc)
  nlinarith only [h, he]

variable {plane : Plane}
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The ordinary contraction constant is collected before the original subset,
while each source keeps its own actual Fourier cardinality. -/
theorem uniform_actual_geometry_main_ordinary_contraction (A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ, 0< C ∧ ∀(T : Finset α){Label : Type}[Fintype Label]
      (d : Label→SecondInputDatum T)(w : Label→ℂ)(χ : Label→RayCharacter)
      (Q : Ideal O)(m : O)(E H : ℤ→ℝ),
      (∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0≤ E r) →
      (∀r∈secondRatioBins (fun l=>(d l).block),0< H r) →
      SecondNormalizedBound ballProfile degree windowDegree
        (fun l=> ordinarySecondDatum (d l) (χ l) Q m) w E H →
      ‖∑l,w l*(d l).block.value ballProfile‖ ≤
        (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value ballProfile‖)+
        C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A := by
  have data (T : Finset α) := main_original_from_normalized.{0,0} (α:=T)
    ballProfile A degree windowDegree hc hs
  choose C hC bound using data
  let total := 1+∑T : Finset α,C T
  have hnonneg : ∀T : Finset α,0≤ C T := hC
  have htotal : 0< total := by
    have hsum := Finset.sum_nonneg (s:=Finset.univ) (fun T _=> hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T≤ total := by
    have hsum := Finset.single_le_sum (fun T _=> hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total,htotal,?_⟩
  intro T Label _ d w χ Q m E H hrows hE hH hnorm
  apply (bound T d w χ Q m E H hrows hE hH hnorm).trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right (hle T)
  exact Finset.sum_nonneg (fun r hr=> div_nonneg (hE r hr)
    (pow_nonneg (by linarith [dyadicScale_pos r]) _))

variable (rayM : Ideal O) [NeZero rayM]
local instance affineMainContractionFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤ H)

/-- The exact prime average and amplifier coefficient are paid once. The
ordinary input remains the full joint normalized bound, after the original
full-zero filter and before any ratio-fiber contraction. -/
theorem actual_affine_main_retained_contraction
    (A ordinaryDegree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η : Character) (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh< Sil.Uneven.MainSource.amplifierMinimum/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤ Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃Ce : ℝ,0< Ce ∧ ∃Sp : Finset (ℕ×ℕ),∃exceptionalDegree : ℕ,
    ∃Co : ℝ,0< Co ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=η)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) →
      (81/200:ℝ)≤ length Z X₁ → (81/200:ℝ)≤ length Z X₂ →
      length Z X₁≤(45/100:ℝ) → length Z X₂≤(45/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤ plane.B →
      let s := affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta := Sil.Uneven.MainSource.widthCellUpper (∑i,w i)
      let amp := Sil.Uneven.MainSource.amp plane beta
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let μ := geometryLossUnit 1 εaffine
      ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ),
      let phase := fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q)
      let selected := geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight
        (Fintype.card T) hZ key (affine_main_plain_zero p 0) (affine_main_plain_zero p 1)
      let datum := fun j : selected=> geometryLowSecondDatum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key j.val.1 (affine_main_plain_zero p 0)
          (affine_main_plain_zero p 1) j.val.2
      let coeff := fun j : selected=> unevenMainSecondWeight reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key 1 (Real.logb Z (volume s)) phase j.val
      ∀(χ : selected→RayCharacter)(E Hratio : ℤ→ℝ),
      (∀r∈secondRatioBins (fun j=>(datum j).block),0≤ E r) →
      (∀r∈secondRatioBins (fun j=>(datum j).block),0< Hratio r) →
      SecondNormalizedBound ballProfile ordinaryDegree windowDegree
        (fun j=> ordinarySecondDatum (datum j) (χ j) Qfix m) coeff E Hratio →
      (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
        ‖unevenMainRetainedSum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight hZ key
          1 (Real.logb Z (volume s)) phase‖ ≤
        Ce*OAI.SevenEighths.MainReconstruction.geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
          (1+‖firstHeight‖)^exceptionalDegree*Z^(-(1/100:ℝ))+
        Co*(56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
          (∑r∈secondRatioBins (fun j=>(datum j).block),E r/(1+dyadicScale r)^A) := by
  obtain ⟨Co,hCo,hordinary⟩ := uniform_actual_geometry_main_ordinary_contraction (α:=α)
    A ordinaryDegree windowDegree hc hs
  obtain ⟨Ce,hCe,Sp,exceptionalDegree,hexceptional⟩ := MainReconstruction.actual_affine_main_exceptional_payment (plane:=plane) (α:=α)
    rayM H hH Sbad hbad W hW hWs η εaffine mesh hε hmesh Qfix hQ hQt hQ72 m hm hml hm2
  refine ⟨Ce,hCe,Sp,exceptionalDegree,Co,hCo,?_⟩
  filter_upwards [hexceptional] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone s beta amp P μ Ψ reflected key firstHeight
    phase selected datum coeff χ E Hratio hE hHratio hnorm
  have hrows : ∀j : selected,(datum j).rows=sourceRows (datum j).C (datum j).D
      (datum j).inactive (datum j).radius := by
    intro j
    unfold datum geometryLowSecondDatum actualSecondBlockDatum actualSecondInputDatum
    rfl
  have ho := hordinary T datum coeff χ Qfix m E Hratio hrows hE hHratio hnorm
  have hretained := MainAssembly.actual_main_retained_nonzero_sum reflected s 1 1 Z 1 amp (μ/64) (μ/8)
    (9/4) firstHeight hZ key (affine_main_plain_zero p 0) (affine_main_plain_zero p 1)
    1 (Real.logb Z (volume s)) phase
  rw [←hretained] at ho
  have he := hz.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone Ψ reflected key firstHeight χ
  have hb := (Sil.Uneven.MainSource.widthCellUpper_bounds ⟨hwlo,hwhi⟩).1
  have hcoef := (geometry_affine_main_amplifier_bound plane beta hb).1
  have havg : 0≤56/(P.card:ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  simp only [MainReconstruction.geometryAffineMainExceptionalNorm] at he
  have hcompare := uneven_main_second_norm_sum_le reflected s 1 1 Z 1 amp (μ/64) (μ/8)
    (9/4) firstHeight (Fintype.card T) hZ key 1 (Real.logb Z (volume s)) phase
    (fun j : selected=> j.val) (fun j=>(mainExceptionalDatum (datum j) (χ j) Qfix m).block.value ballProfile)
  have he' := (mul_le_mul_of_nonneg_left hcompare (mul_nonneg havg hcoef)).trans he
  exact main_paid_join _ _ _ _ _ _ _ havg hcoef ho he'

end
end OAI.SevenEighths.MainHigh
end

/- Original module: Candidate.Uneven.MainHighFirstCostEquality. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.MainHigh
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum Cycle63InitialMass
local notation "O" => HeckeFamily.O
attribute [local irreducible] Finset.univ

/-- The adapted selection retains precisely the predecessor's second-block
cost; only its external first-allocation weight has changed. -/
theorem uneven_first_cost_eq {α : Type*} [Fintype α] [DecidableEq α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo : ℝ) (second : Bool) (t₀ u : ℝ)
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) :
    UnevenSelection.geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u j =
    Cycle63InitialMass.geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u j := by
  unfold UnevenSelection.geometryMainFirstCost Cycle63InitialMass.geometryMainFirstCost
  apply congrArg (fun x : ℝ => x /
    volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t j))
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> rfl

end
end OAI.SevenEighths.MainHigh
end

/- Original module: Candidate.Uneven.MainHighMainJoinedPayment. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.MainHigh
noncomputable section
open Sil.Uneven.MainSource
open Target830.Source.Uneven
open TargetHigh830
open MainAssembly UnevenSelection
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.MainAssembly
open OAI.SevenEighths.MainPhysical
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
local notation "O" => HeckeFamily.O
local instance newMainPaymentSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ MainPhysical.mainLowPhysicalCompleteCost


variable {plane : Plane}
variable {α : Type} [Fintype α] [DecidableEq α]


theorem actual_affine_main_normalized_of_selected_low_high
    (Cs ε ξ K Z CL CH : ℝ) (dl dh : ℕ) (hZ : 1< Z)
    (hK : 0≤ K) (hCL : 0≤ CL) (hCH : 0≤ CH)
    (hselection : UnevenSelection.GeometryAffinePhysicalSelectionSpec (ι:=α) Cs ε ξ K Z)
    (reflected : Bool) (s : Input α) (p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z)
    (amp reserve baseHeight : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter) (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hbranches : GeometryAffineMainSelectedBranches plane ε ξ Z amp reserve baseHeight CL CH dl dh hZ
      reflected s key Ψ χ Q m hz₁ hz₂) :
    let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight
      (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=> geometryMainOrdinaryDatum reflected s 1 1 Z 1 amp ξ reserve
      (9/4) baseHeight (Fintype.card α) hZ key hz₁ hz₂ χ Q m j.val
    let weight:=fun j : selected=> unevenMainSecondWeight reflected s 1 1 Z 1 amp ξ reserve
      (9/4) baseHeight (Fintype.card α) hZ key 1 (Real.logb Z (volume s))
      (fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)) j.val
    SecondNormalizedBound W (max dl dh) (max dl dh) datum weight (fun _=> K*Z^ε*(CL+CH)) (fun _=>1) := by
  apply UnevenSelection.actual_affine_main_normalized_of_selected Cs ε ξ K Z (CL+CH) (max dl dh) hZ hK
    (add_nonneg hCL hCH) hselection reflected s p caps amp reserve baseHeight key Ψ χ Q m W hz₁ hz₂
  intro second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf
  obtain ⟨e,select,hlow,hhigh⟩:=hbranches second t₀ u column hinj alloc hf
  have hb:=actual_main_selected_low_high_cost plane reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight
    (Fintype.card α) hZ key hz₁ hz₂ (fun j=>⟨column j,alloc j⟩)
    (fun j=> mass (column j)) χ Q m 1 (1/4) second t₀ u e select
    ((CL*(1+‖t₀‖)^dl)*(1+‖u‖)^dl) ((CH*(1+‖t₀‖)^dh)*(1+‖u‖)^dh) hlow hhigh
  simpa only [uneven_first_cost_eq] using
    hb.trans (affine_main_two_height_join CL CH t₀ u dl dh hCL hCH)







variable (M : Ideal O) [NeZero M]
local instance mainPaymentQuotient : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)



theorem actual_affine_main_source_selection
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (δ ξ : ℝ)(hδ : 0<δ)(hξ : 0≤ξ) :
    ∃Cs : ℝ,1≤ Cs ∧ ∃Ksel : ℝ,0< Ksel ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀T : Finset α,UnevenSelection.GeometryAffinePhysicalSelectionSpec (ι:=T) Cs δ ξ Ksel Z ∧
    ∀(η₀ : Character)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ)
      (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))(bΦ : ℝ)(state : NaturalState Z 0 bΦ)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,0≤ w i) → (81/200:ℝ)≤ length Z X₁ → (81/200:ℝ)≤ length Z X₂ →
      length Z X₁≤(45/100:ℝ) → length Z X₂≤(45/100:ℝ) → (∑i,w i)≤(1/25:ℝ) →
      let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z := by
  obtain ⟨Cs,hCs,hcaps⟩:=AuxiliaryPhysical.eventual_actual_affine_exceptional_source_gates (α:=α) M H hH W hW hWs
  obtain ⟨Ksel,hKsel,hselection⟩:=UnevenSelection.uniform_actual_affine_physical_selection (α:=α) Cs δ ξ hCs hδ hξ
  refine ⟨Cs,hCs,Ksel,hKsel,?_⟩
  filter_upwards [hcaps,hselection] with Z hz hs
  refine ⟨hz.1,?_⟩
  intro T
  refine ⟨hs T,?_⟩
  intro η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots s
  exact UnevenSelection.geometry_affine_source_gates_actual_card s p (Fintype.card α) Cs Z
    (hz.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots)



end
end OAI.SevenEighths.MainHigh
end
