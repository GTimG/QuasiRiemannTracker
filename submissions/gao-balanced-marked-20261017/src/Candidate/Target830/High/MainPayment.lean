import Candidate.Target830.High.MainBranches
import Candidate.Target830.High.MainNormalized
import Candidate.Target830.High.MainContraction
import Candidate.Target830.High.MainRatioPayment
import Candidate.Target830.Source.Assembly.BalancedRetained
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.Target830.Source.Assembly
open OAI.SevenEighths.Target830.Source.LowPhysical
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
attribute [local irreducible] Finset.univ Target830.Source.LowPhysical.mainLowPhysicalCompleteCost


variable {plane : SourcePlane}
variable {α : Type} [Fintype α] [DecidableEq α]


theorem actual_affine_main_normalized_of_selected_low_high
    (Cs ε ξ K Z CL CH : ℝ) (dl dh : ℕ) (hZ : 1<Z)
    (hK : 0≤K) (hCL : 0≤CL) (hCH : 0≤CH)
    (hselection : GeometryAffinePhysicalSelectionSpec (ι:=α) Cs ε ξ K Z)
    (reflected : Bool) (s : Input α) (p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z)
    (amp reserve baseHeight : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter) (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hbranches : GeometryAffineMainSelectedBranches plane ε ξ Z amp reserve baseHeight CL CH dl dh hZ
      reflected s key Ψ χ Q m hz₁ hz₂) :
    let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight
      (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=>geometryMainOrdinaryDatum reflected s 1 1 Z 1 amp ξ reserve
      (9/4) baseHeight (Fintype.card α) hZ key hz₁ hz₂ χ Q m j.val
    let weight:=fun j : selected=>balancedMainSecondWeight reflected s 1 1 Z 1 amp ξ reserve
      (9/4) baseHeight (Fintype.card α) hZ key 1 (Real.logb Z (volume s))
      (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)) j.val
    SecondNormalizedBound W (max dl dh) (max dl dh) datum weight (fun _=>K*Z^ε*(CL+CH)) (fun _=>1) := by
  apply actual_affine_main_normalized_of_selected Cs ε ξ K Z (CL+CH) (max dl dh) hZ hK
    (add_nonneg hCL hCH) hselection reflected s p caps amp reserve baseHeight key Ψ χ Q m W hz₁ hz₂
  intro second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf
  obtain ⟨e,select,hlow,hhigh⟩:=hbranches second t₀ u column hinj alloc hf
  have hb:=actual_main_selected_low_high_cost plane reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight
    (Fintype.card α) hZ key hz₁ hz₂ (fun j=>⟨column j,alloc j⟩)
    (fun j=>mass (column j)) χ Q m 1 (1/4) second t₀ u e select
    ((CL*(1+‖t₀‖)^dl)*(1+‖u‖)^dl) ((CH*(1+‖t₀‖)^dh)*(1+‖u‖)^dh) hlow hhigh
  exact hb.trans (affine_main_two_height_join CL CH t₀ u dl dh hCL hCH)


theorem actual_affine_main_retained_of_selected_low_high
    (A dl dh : ℕ) (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :
    ∃Co : ℝ,0≤Co ∧
    ∀(Cs ε ξ K Z CL CH : ℝ)(hZ : 1<Z),
      0≤K → 0≤CL → 0≤CH →
      GeometryAffinePhysicalSelectionSpec (ι:=α) Cs ε ξ K Z →
    ∀(reflected : Bool)(s : Input α)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z →
    ∀(amp reserve baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))
      (χ : RayCharacter)(Q : Ideal O)(m : O)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      GeometryAffineMainSelectedBranches plane ε ξ Z amp reserve baseHeight CL CH dl dh hZ
        reflected s key Ψ χ Q m hz₁ hz₂ →
    let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight
      (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=>geometryLowSecondDatum reflected s 1 1 Z 1 amp ξ reserve (9/4)
      baseHeight (Fintype.card α) hZ key j.val.1 hz₁ hz₂ j.val.2
    let phase:=fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)
    let weight:=fun j : selected=>balancedMainSecondWeight reflected s 1 1 Z 1 amp ξ reserve
      (9/4) baseHeight (Fintype.card α) hZ key 1 (Real.logb Z (volume s)) phase j.val
    ‖balancedMainRetainedSum reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight hZ key
      1 (Real.logb Z (volume s)) phase‖≤
      (∑j,‖weight j*(mainExceptionalDatum (datum j) χ Q m).block.value ballProfile‖)+
      Co*∑r∈secondRatioBins (fun j=>(datum j).block),
        (K*Z^ε*(CL+CH))/(1+dyadicScale r)^A := by
  obtain ⟨Co,hCo,hordinary⟩:=main_original_from_normalized (α:=α)
    ballProfile A (max dl dh) (max dl dh) hc hs
  refine ⟨Co,hCo,?_⟩
  intro Cs ε ξ K Z CL CH hZ hK hCL hCH hselection reflected s p caps amp reserve baseHeight
    key Ψ χ Q m hz₁ hz₂ hbranches selected datum phase weight
  have hnorm:=actual_affine_main_normalized_of_selected_low_high Cs ε ξ K Z CL CH dl dh hZ
    hK hCL hCH hselection reflected s p caps amp reserve baseHeight key Ψ χ Q m ballProfile
    hz₁ hz₂ hbranches
  have hrows : ∀j : selected,(datum j).rows=sourceRows (datum j).C (datum j).D
      (datum j).inactive (datum j).radius := by
    intro j
    unfold datum geometryLowSecondDatum actualSecondBlockDatum actualSecondInputDatum
    rfl
  have hb:=hordinary datum weight (fun _=>χ) Q m (fun _=>K*Z^ε*(CL+CH)) (fun _=>1) hrows
    (fun _ _=>by positivity) (fun _ _=>by norm_num) hnorm
  have he:=Source.Assembly.actual_main_retained_nonzero_sum reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight
    hZ key hz₁ hz₂ 1 (Real.logb Z (volume s)) phase
  rw [←he] at hb
  exact hb


theorem actual_affine_main_paid_of_selected_low_high
    (A dl dh : ℕ) (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :
    ∃Co : ℝ,0≤Co ∧
    ∀(Cs δ ξ Ksel Z CL CH low high target Cb Ce control : ℝ)(hZ : 1<Z),
      0≤Ksel → 0≤CL → 0≤CH → 0≤Cb → 0≤control →
      GeometryAffinePhysicalSelectionSpec (ι:=α) Cs δ ξ Ksel Z →
    ∀(reflected : Bool)(s : Input α)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z →
    ∀(beta reserve baseHeight : ℝ)(_hb : 17/500≤beta ∧ beta≤1/25)
      (key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ : RayCharacter)(Q : Ideal O)(m : O)
      (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(P : Finset (Ideal O)),
    let amp:=plane.amp beta
    let coefficient:=(amplifierCap 2 0 1+6*amp)/(amp/2)
    Z^(amp-δ)≤(P.card:ℝ) →
    low+3*δ-amp≤target → high+3*δ-amp≤target →
    GeometryAffineMainSelectedBranches plane δ ξ Z amp reserve baseHeight
      ((CL*control)*Z^low) ((CH*control)*Z^high) dl dh hZ
      reflected s key Ψ χ Q m hz₁ hz₂ →
    let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight
      (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=>geometryLowSecondDatum reflected s 1 1 Z 1 amp ξ reserve (9/4)
      baseHeight (Fintype.card α) hZ key j.val.1 hz₁ hz₂ j.val.2
    let phase:=fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)
    let weight:=fun j : selected=>balancedMainSecondWeight reflected s 1 1 Z 1 amp ξ reserve
      (9/4) baseHeight (Fintype.card α) hZ key 1 (Real.logb Z (volume s)) phase j.val
    ((56/(P.card:ℝ))*coefficient*
      (∑j,‖weight j*(mainExceptionalDatum (datum j) χ Q m).block.value ballProfile‖)≤
        Ce*control*Z^target) →
    (∀E : ℝ,0≤E →
      (∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A)≤Cb*E*Z^δ) →
    (56/(P.card:ℝ))*coefficient*
      ‖balancedMainRetainedSum reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight hZ key
        1 (Real.logb Z (volume s)) phase‖≤
      (Ce+Co*(56*4096*Cb*Ksel*(CL+CH)))*control*Z^target := by
  obtain ⟨Co,hCo,hcontract⟩:=actual_affine_main_retained_of_selected_low_high (α:=α) A dl dh hc hs
  refine ⟨Co,hCo,?_⟩
  intro Cs δ ξ Ksel Z CL CH low high target Cb Ce control hZ hKsel hCL hCH hCb hcontrol
    hselection reflected s p caps beta reserve baseHeight hb key Ψ χ Q m hz₁ hz₂ P amp coefficient
    hprime hlow hhigh hbranches selected datum phase weight hexceptional hratio
  let E:=Ksel*Z^δ*((CL*control)*Z^low+(CH*control)*Z^high)
  let ratio:=∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A
  have hE : 0≤E := by dsimp only [E];positivity
  have hn:=hcontract Cs δ ξ Ksel Z ((CL*control)*Z^low) ((CH*control)*Z^high) hZ
    hKsel (by positivity) (by positivity) hselection reflected s p caps amp reserve baseHeight
    key Ψ χ Q m hz₁ hz₂ hbranches
  have hcoef:=geometry_affine_main_amplifier_bound plane beta hb
  have havg : 0≤56/(P.card:ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hp:=mul_le_mul_of_nonneg_left hn (mul_nonneg havg hcoef.1)
  have hpaid : (56/(P.card:ℝ))*coefficient*
      ‖balancedMainRetainedSum reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight hZ key
        1 (Real.logb Z (volume s)) phase‖≤
      (56/(P.card:ℝ))*coefficient*
        (∑j,‖weight j*(mainExceptionalDatum (datum j) χ Q m).block.value ballProfile‖)+
      Co*((56/(P.card:ℝ))*coefficient*ratio) := by
    convert hp using 1; ring
  exact geometry_affine_main_contracted_payment Z (P.card:ℝ) amp δ low high target coefficient
    4096 Cb Ksel CL CH Ce Co control
    (‖balancedMainRetainedSum reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight hZ key
      1 (Real.logb Z (volume s)) phase‖)
    ((56/(P.card:ℝ))*coefficient*
      (∑j,‖weight j*(mainExceptionalDatum (datum j) χ Q m).block.value ballProfile‖)) ratio
    hZ hprime hcoef.1 hcoef.2 hCb hKsel hCL hCH hCo hcontrol hpaid hexceptional
    (hratio E hE) hlow hhigh



variable (M : Ideal O) [NeZero M]
local instance mainPaymentQuotient : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_affine_main_normalized_of_canonical_high
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (ηseed : Character)(SL : Finset (ℕ×ℕ))(dl : ℕ)(KL : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (Z : ℝ)(hlow : Target830.Source.LowPhysical.GeometryAffineMainLowSpec (P:=plane) (α:=α) M H hH W hW hWs hβlo g ηseed SL dl KL η₀ Q hQM hQ72 Z)
    (hZ : 1<Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)
    (height mesh : ℝ)(hw : ∀i,0≤w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwm : ∀i,w i≤ mesh)
    (hheight : 0≤height)(hfreq : ∀i,|freq i|≤height)(hT : 2<Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hlo₁ : (81/200:ℝ)≤length Z X₁)(hlo₂ : (81/200:ℝ)≤length Z X₂)
    (hhi₁ : length Z X₁≤(44/100:ℝ))(hhi₂ : length Z X₂≤(44/100:ℝ))
    (hslots : (17/500:ℝ)≤∑i,w i ∧ (∑i,w i)≤1/25)
    (hcone : length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤plane.B)
    (reflected : Bool)(baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ₀ : RayCharacter)
    (KH : ℝ)(SH : Finset (ℕ×ℕ))(dh : ℕ)(highSaving : ℝ)
    (hKL : 0≤KL)(hKH : 0≤KH)(Cs Ksel : ℝ)(hKsel : 0≤Ksel)
    (hselection : GeometryAffinePhysicalSelectionSpec (ι:=α) Cs g.δ (g.μ/64) Ksel Z) :
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_main_low_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_main_low_profile_zero p 1
    let amp:=(1:ℝ)*plane.amp (widthCellUpper ((∑j,Real.logb Z (s.P j))/(1:ℝ)))
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    GeometryAffineMainCanonicalHighReceipt M H hH plane g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT
      reflected s p amp baseHeight height key Ψ χ₀ hz₁ hz₂ KH SH dh highSaving →
    GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z →
    let CL:=KL*(p.control SL)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*
      Z^(lowTarget (P:=plane) g (Fintype.card α) amp omega mesh)*(1+|baseHeight|+height)^dl
    let CH:=KH*(p.control SH)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*
      Z^(amp+highSaving)*(1+|baseHeight|+height)^dh
    let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
      baseHeight (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=>geometryMainOrdinaryDatum reflected s 1 1 Z 1 amp (g.μ/64)
      (g.μ/8) (9/4) baseHeight (Fintype.card α) hZ key hz₁ hz₂ χ₀ (internalQ Q η₀) fixedBadMask j.val
    let weight:=fun j : selected=>balancedMainSecondWeight reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8)
      (9/4) baseHeight (Fintype.card α) hZ key 1 (Real.logb Z (volume s))
      (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (g.μ/64) q)) j.val
    SecondNormalizedBound ballProfile (max dl dh) (max dl dh) datum weight
      (fun _=>Ksel*Z^g.δ*(CL+CH)) (fun _=>1) := by
  intro s hz₁ hz₂ amp omega hhigh caps CL CH selected datum weight
  have hbranches:=actual_affine_main_selected_branches M H hH plane W hW hWs hβlo g ηseed SL dl KL
    η₀ Q hQM hQ72 Z hlow hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂
    height mesh hw hmesh hmeshcap hwm hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂ hslots hcone
    reflected baseHeight key Ψ χ₀ KH SH dh highSaving hhigh
  have hside : 0<geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key :=
    geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)
  have hCL : 0≤CL := by dsimp only [CL];positivity
  have hCH : 0≤CH := by dsimp only [CH];positivity
  exact actual_affine_main_normalized_of_selected_low_high Cs g.δ (g.μ/64) Ksel Z CL CH dl dh
    hZ hKsel hCL hCH hselection reflected s p caps amp (g.μ/8) baseHeight key Ψ χ₀
    (internalQ Q η₀) fixedBadMask ballProfile hz₁ hz₂ hbranches


theorem affine_main_final_branch_exponents
    (g : GeometryAffineLowSchedule) (εaffine : ℝ) (hε : 0<εaffine)
    (hμ : g.μ=geometryLossUnit 1 εaffine) (n N : ℕ) (hn : n≤N)
    (B L amp omega mesh : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)
    (hω : omega≤33*g.μ/128) (hmesh : mesh≤g.μ/8) :
    geometryAffineLowTarget g n amp omega mesh+3*g.δ-amp≤-(7/60000000:ℝ) ∧
    (amp+(-(1/1000000:ℝ)+4*g.μ-3*g.δ))+3*g.δ-amp≤
      -(7/60000000:ℝ) := by
  have hm : 0<geometryLossUnit 1 εaffine :=
    geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hl := geometry_affine_subset_low_target_ledger g B L n N hn amp omega mesh hB hL hδ hω hmesh
  have hb := geometry_paid_loss 1 εaffine 1 (7/30000000) (2*g.μ)
    (by norm_num) le_rfl le_rfl (by rw [hμ];linarith)
  have hh := geometry_paid_loss 1 εaffine 1 (1/1000000) (4*g.μ)
    (by norm_num) le_rfl (by norm_num) (by rw [hμ];linarith)
  constructor <;> linarith only [hl,hb,hh]


theorem actual_affine_main_source_selection
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (δ ξ : ℝ)(hδ : 0<δ)(hξ : 0≤ξ) :
    ∃Cs : ℝ,1≤Cs ∧ ∃Ksel : ℝ,0<Ksel ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀T : Finset α,GeometryAffinePhysicalSelectionSpec (ι:=T) Cs δ ξ Ksel Z ∧
    ∀(η₀ : Character)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ)
      (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))(bΦ : ℝ)(state : NaturalState Z 0 bΦ)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (81/200:ℝ)≤length Z X₁ → (81/200:ℝ)≤length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) → (∑i,w i)≤(1/25:ℝ) →
      let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z := by
  obtain ⟨Cs,hCs,hcaps⟩:=Source.LowPhysical.eventual_actual_affine_exceptional_source_gates (α:=α) M H hH W hW hWs
  obtain ⟨Ksel,hKsel,hselection⟩:=uniform_actual_affine_physical_selection (α:=α) Cs δ ξ hCs hδ hξ
  refine ⟨Cs,hCs,Ksel,hKsel,?_⟩
  filter_upwards [hcaps,hselection] with Z hz hs
  refine ⟨hz.1,?_⟩
  intro T
  refine ⟨hs T,?_⟩
  intro η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots s
  exact geometry_affine_source_gates_actual_card s p (Fintype.card α) Cs Z
    (hz.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots)



end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_affine_main_normalized_of_selected_low_high
#print axioms OAI.SevenEighths.TargetHigh830.actual_affine_main_normalized_of_canonical_high
#print axioms OAI.SevenEighths.TargetHigh830.actual_affine_main_source_selection
