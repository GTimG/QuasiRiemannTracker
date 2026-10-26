import Candidate.Uneven.MainLowTargetSchedule
import Candidate.Uneven.MainCellGeometry
import Candidate.Uneven.MainHighAffinePayment
import Candidate.Uneven.MainHighMainBranches
import Candidate.Uneven.MainHighMainJoinedPayment
import Candidate.Uneven.MainAffineAmplification

/- Original module: Candidate.Uneven.MainHighMainHighReceipt. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.MainHigh
noncomputable section
open Sil.Uneven.MainSource
open MainPhysical Target830.Source.Uneven
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentAllocatedRayDictionary CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge Cycle63Moment
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional
open Cycle63InitialSource
local notation "O" => HeckeFamily.O

variable {plane : Plane}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)


/-- The literal affine high estimate supplies the exact selected branch
used by the main payment, with source admission already discharged. -/
theorem actual_affine_main_high_receipt
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (P : HighSourceParameters)(hPe : P.e=g.e)(hPτ : P.τ=g.τ)
    (ηseed : Character)(SH : Finset (ℕ×ℕ))(dh : ℕ)(KH target : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (Z : ℝ)(hspec : MainHigh.GeometryAffineMainHighSpec (α:=α) M H hH plane W hW hWs hβlo P
      g.μ g.δ target ηseed SH dh KH η₀ Q hQM hQ72 Z)
    (hZ : 1< Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)
    (height mesh : ℝ)(hw : ∀i,0≤ w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwm : ∀i,w i≤ mesh)
    (hwmarked : ∀i,w i≤ BootstrapPlain.bootstrapRawMesh*SaturatedPlain.fineRawCore)
    (hheight : 0≤ height)(hfreq : ∀i,|freq i|≤ height)(hT : 2< Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hlo₁ : (81/200:ℝ)≤ length Z X₁)(hlo₂ : (81/200:ℝ)≤ length Z X₂)
    (hhi₁ : length Z X₁≤(45/100:ℝ))(hhi₂ : length Z X₂≤(45/100:ℝ))
    (hslots : (17/500:ℝ)≤∑i,w i ∧ (∑i,w i)≤1/25)
    (hcone : length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤ plane.B)
    (reflected : Bool)(baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ₀ : RayCharacter) :
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=MainPhysical.affine_main_low_profile_zero (P:=plane) p 0
    let hz₂ : s.W₂ 0=0:=MainPhysical.affine_main_low_profile_zero (P:=plane) p 1
    let amp:=(1:ℝ)*Sil.Uneven.MainSource.amp plane (Sil.Uneven.MainSource.widthCellUpper ((∑j,Real.logb Z (s.P j))/(1:ℝ)))
    GeometryAffineMainCanonicalHighReceipt M H hH plane g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT
      reflected s p amp baseHeight height key Ψ χ₀ hz₁ hz₂ KH SH dh target := by
  cases P
  cases g
  dsimp only at hPe hPτ
  cases hPe
  cases hPτ
  intro s hz₁ hz₂ amp second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf
    firstIndex selected raw datum coefficient hP hPN canonical
  have hb:=hspec hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh
    hw hmesh hmeshcap hwm hwmarked hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂ hslots hcone
    reflected second key baseHeight firstIndex hf hinj χ₀ fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Ψ t₀ u hP hPN
  convert hb using 1
  rfl

end
end OAI.SevenEighths.MainHigh
end

/- Original module: Candidate.Uneven.MainHighMainComponentPayment. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.MainHigh
noncomputable section
open Sil.Uneven.MainSource
open MainPhysical Target830.Source.Uneven MainAssembly UnevenSelection
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
local instance newMainComponentSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ MainPhysical.mainLowPhysicalCompleteCost


variable {plane : Plane}
variable {α : Type} [Fintype α] [DecidableEq α]



variable (M : Ideal O) [NeZero M]
local instance mainComponentQuotient : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
theorem actual_affine_main_uniform_component_payment
    (A dl dh : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hεcap : εaffine≤1/10000000000000000000000000000)
    (hmesh : mesh< Sil.Uneven.MainSource.amplifierMinimum/2)(hmesh0 : 0 ≤ mesh)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤ N)(B L : ℝ)(hB : 0≤ B)(hL : 0≤ L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤ g.μ/8)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤ Ideal.span {(72:O)})
    (KL KH : ℝ)(hKL : 0≤ KL)(hKH : 0≤ KH) :
    ∃Cs : ℝ,1≤ Cs ∧ ∃Ksel : ℝ,0< Ksel ∧ ∃Cm : ℝ,0≤ Cm ∧
    ∃SE : Finset (ℕ×ℕ),∃dE : ℕ,∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters M H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) →
      (81/200:ℝ)≤ length Z X₁ → (81/200:ℝ)≤ length Z X₂ →
      length Z X₁≤(45/100:ℝ) → length Z X₂≤(45/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤ plane.B →
    ∀(S : Finset (ℕ×ℕ))(D : ℕ),SE⊆S → dE≤ D →
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤ height →
    ∀χ₀ : RayCharacter,
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=MainPhysical.affine_main_low_profile_zero (P:=plane) p 0
    let hz₂ : s.W₂ 0=0:=MainPhysical.affine_main_low_profile_zero (P:=plane) p 1
    let beta:=Sil.Uneven.MainSource.widthCellUpper (∑i,w i)
    let amp:=Sil.Uneven.MainSource.amp plane beta
    let P:=CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^amp)
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    let low:=lowTarget (P:=plane) g (Fintype.card T) amp omega mesh
    let high:=amp+(-mainHighReserve+4*g.μ-3*g.δ)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    GeometryAffineMainSelectedBranches plane g.δ (g.μ/64) Z amp (g.μ/8) firstHeight
      ((KL*control)*Z^low) ((KH*control)*Z^high) dl dh hZ
      reflected s key Ψ χ₀ Qfix fixedBadMask hz₁ hz₂ →
    (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      ‖unevenMainRetainedSum reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight hZ key 1 (Real.logb Z (volume s))
        (fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (g.μ/64) q))‖≤
      Cm*control*Z^(-(1/2000000000:ℝ)) := by
  obtain ⟨Cs,hCs,Ksel,hKsel,hsource⟩:=actual_affine_main_source_selection (α:=α) M H hH
    W hW hWs g.δ (g.μ/64) g.δ_pos (div_nonneg g.μ_pos.le (by norm_num))
  obtain ⟨Ce,hCe,SE,dE,Co,hCo,hcontract⟩:=actual_affine_main_retained_contraction (plane:=plane) (α:=α)
    M H hH A (max dl dh) (max dl dh) hc hs Sbad hbad W hW hWs ηseed εaffine mesh hε hmesh
    Qfix hQ hQt hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
  obtain ⟨Cb,hCb,hratio⟩:=uniform_actual_affine_main_ratio_payment (plane:=plane) (α:=α) M H hH
    W hW hWs εaffine g.δ hε g.δ_pos
  have hbudget:=MainReconstruction.actual_affine_geometry_amplification (plane:=plane) (α:=α) M H hH
    Sbad hbad W hW hWs g.δ mesh (g.μ/64) (g.μ/8) g.δ_pos hmesh (by linarith [g.μ_pos])
    (by linarith [g.μ_cap]) (by linarith [g.μ_pos])
  let Cm:=Ce+Co*(56*2000000*Cb*Ksel*(KL+KH))
  refine ⟨Cs,hCs,Ksel,hKsel,Cm,by dsimp only [Cm];positivity,SE,dE,?_⟩
  filter_upwards [hsource,hcontract,hratio,hbudget,eventual_geometry_small_frequency g.μ g.μ_pos]
    with Z hz hcZ hrZ hpZ hfZ
  rw [←hμ] at hcZ hrZ
  refine ⟨hz.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone S D hSE hdE Ψ reflected key firstHeight height hheight χ₀
    s hz₁ hz₂ beta amp P omega low high control hbranches
  have caps:=(hz.2 T).2 η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have hside : 0< geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)
  have hcontrol : 0≤ control := by dsimp only [control];positivity
  have hn:=actual_affine_main_normalized_of_selected_low_high Cs g.δ (g.μ/64) Ksel Z
    ((KL*control)*Z^low) ((KH*control)*Z^high) dl dh hZ hKsel.le (by positivity) (by positivity)
    (hz.2 T).1 reflected s p caps amp (g.μ/8) firstHeight key Ψ χ₀ Qfix fixedBadMask
    ballProfile hz₁ hz₂ hbranches
  let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
    firstHeight (Fintype.card T) hZ key hz₁ hz₂
  let datum:=fun j : selected=> geometryLowSecondDatum reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8)
    (9/4) firstHeight (Fintype.card T) hZ key j.val.1 hz₁ hz₂ j.val.2
  let E:=Ksel*Z^g.δ*((KL*control)*Z^low+(KH*control)*Z^high)
  have hE : 0≤ E := by dsimp only [E];positivity
  let ratio:=∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A
  have hnorm : SecondNormalizedBound ballProfile (max dl dh) (max dl dh)
      (fun j=> ordinarySecondDatum (datum j) χ₀ Qfix fixedBadMask)
      (fun j=> unevenMainSecondWeight reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key 1 (Real.logb Z (volume s))
        (fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (g.μ/64) q)) j.val)
      (fun _=> E) (fun _=>1) := by
    simpa only [geometryMainOrdinaryDatum] using hn
  have hp:=hcZ.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone Ψ reflected key firstHeight
    (fun _=>χ₀) (fun _=> E) (fun _=>1) (fun _ _=> hE) (fun _ _=> by norm_num)
    (by simpa only [datum,selected,s,amp,beta] using hnorm)
  have hratioZ:=hrZ.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
  have hratioPaid : ratio≤ Cb*E*Z^g.δ := by
    simpa only [ratio,datum,selected,s,amp,beta] using
      (hratioZ.2.2 reflected key firstHeight).2.1 E hE A
  have hprime:=(hpZ.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi).2.1
  have hcount : Fintype.card T≤ N :=
    (Fintype.card_le_of_injective (fun i : T=> i.val) Subtype.val_injective).trans hN
  have htargets:=MainPhysical.final_branch_exponents_of_schedule plane g εaffine hεcap hμ
    (Fintype.card T) N hcount B L amp omega mesh hδ hfZ.2.2 hmeshμ
  have htargetsLow : low+3*g.δ-amp≤-(1/2000000000:ℝ) := by
    exact htargets.1
  have hex : Ce*MainReconstruction.geometryAffineExceptionalShell reflected Z key*(p.control SE)^2*
      (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ))≤ Ce*control*Z^(-(1/2000000000:ℝ)) := by
    change Ce*Cycle63InitialMass.geometryAffineExceptionalShell reflected Z key*(p.control SE)^2*
      (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ))≤ Ce*control*Z^(-(1/2000000000:ℝ))
    rw [geometry_affine_exceptional_shell_eq (Fintype.card T) Z hZ]
    have hprofile:=pow_le_pow_left₀ (p.control_nonneg SE) (Cycle63Physical.profile_control_mono p hSE) 2
    have hbase : (1+‖firstHeight‖)^dE≤(1+|firstHeight|+height)^D := by
      rw [Real.norm_eq_abs]
      exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdE)
    have hpow:=Real.rpow_le_rpow_of_exponent_le hZ.le
      (by norm_num : -(1/100:ℝ)≤-(1/2000000000:ℝ))
    have hh : Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control SE)^2*
        (1+‖firstHeight‖)^dE≤ Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control S)^2*
        (1+|firstHeight|+height)^D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprofile (mul_nonneg hCe.le hside.le))
        hbase (pow_nonneg (by positivity) _) (by positivity)
    have hm:=mul_le_mul hh hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity)
    convert hm using 1;dsimp only [control];ring
  have hb:=(Sil.Uneven.MainSource.widthCellUpper_bounds ⟨hwlo,hwhi⟩).1
  have hcoef:=geometry_affine_main_amplifier_bound plane beta hb
  exact geometry_affine_main_contracted_payment Z (P.card:ℝ) amp g.δ low high (-(1/2000000000))
    ((amplifierCap 2 0 1+6*amp)/(amp/2)) 2000000 Cb Ksel KL KH Ce Co control
    _ _ ratio hZ hprime hcoef.1 hcoef.2 hCb.le hKsel.le hKL hKH hCo.le hcontrol
    (by simpa only [P,s,amp,beta,ratio,datum,selected,mul_assoc] using hp) hex hratioPaid htargetsLow htargets.2

end
end OAI.SevenEighths.MainHigh
end

/- Original module: Candidate.Uneven.MainHighMainCompletePayment. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.MainHigh
noncomputable section
open Sil.Uneven.MainSource
open MainPhysical Target830.Source.Uneven MainAssembly UnevenSelection
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.MainAssembly
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open Cycle63MarkedPlain
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

variable {plane : Plane}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The paid retained main estimate, uniform in the actual moving source. -/
def GeometryAffineMainPaidSpec
    (Sbad : Finset (Ideal O))
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (ηseed η₀ : Character)(mesh μ : ℝ)(T : Finset α)
    (S : Finset (ℕ×ℕ))(D : ℕ)(Cm Z : ℝ) : Prop :=
    ∀(hZ : 1< Z)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ)
      (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) →
      (81/200:ℝ)≤ length Z X₁ → (81/200:ℝ)≤ length Z X₂ →
      length Z X₁≤(45/100:ℝ) → length Z X₂≤(45/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤ plane.B →
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),
      0≤ height → (∀i,|freq i|≤ height) →
    ∀χ₀ : RayCharacter,
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let amp:=Sil.Uneven.MainSource.amp plane (Sil.Uneven.MainSource.widthCellUpper (∑i,w i))
    let primes:=CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^amp)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    (56/(primes.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      ‖unevenMainRetainedSum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
        firstHeight hZ key 1 (Real.logb Z (volume s))
        (fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖≤
      Cm*control*Z^(-(1/2000000000:ℝ))

/-- Assemble the checked literal low and high estimates with the complete
retained main contraction. The actual subset remains the Fourier carrier;
the ambient cardinality enters only the outside loss ledger. -/
theorem actual_affine_main_complete_payment
    (T : Finset α)(A dl dh : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤ plane.incumbent)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hεcap : εaffine≤1/10000000000000000000000000000)
    (hmesh : mesh< Sil.Uneven.MainSource.amplifierMinimum/2)(hmesh0 : 0≤ mesh)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤ N)(B L : ℝ)(hB : 0≤ B)(hL : 0≤ L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤ g.μ/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hmarkedmesh : mesh≤ BootstrapPlain.bootstrapRawMesh*SaturatedPlain.fineRawCore)
    (P : HighSourceParameters)(hPe : P.e=g.e)(hPτ : P.τ=g.τ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (SL SH : Finset (ℕ×ℕ))(KL KH : ℝ)(hKL : 0≤ KL)(hKH : 0≤ KH)
    (hlow : ∀ᶠZ : ℝ in atTop,MainPhysical.GeometryAffineMainLowSpec (P:=plane) (α:=T) M H hH W hW hWs hβlo hκbeta
      g ηseed SL dl KL η₀ Q hQM hQ72 Z)
    (hhigh : ∀ᶠZ : ℝ in atTop,MainHigh.GeometryAffineMainHighSpec (α:=T) M H hH plane W hW hWs hβlo
      P g.μ g.δ (MainHigh.geometryAffineHighTarget g.μ g.δ) ηseed SH dh KH η₀ Q hQM hQ72 Z) :
    ∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
    ∀ᶠZ : ℝ in atTop,1< Z ∧
    GeometryAffineMainPaidSpec (plane:=plane) M H hH Sbad W hW hWs ηseed η₀ mesh g.μ T S D Cm Z := by
  obtain ⟨Cs,hCs,Ksel,hKsel,Cm,hCm,SE,dE,hpaid⟩:=
    actual_affine_main_uniform_component_payment (α:=α) M H hH A dl dh hc hs Sbad hbad
      W hW hWs ηseed εaffine mesh hε hεcap hmesh hmesh0 g hμ N hN B L hB hL hδ hmeshμ
      (internalQ Q η₀) hQ hQt hQ72 KL KH hKL hKH
  let S:=(SE∪SL)∪SH
  let D:=max dE (max dl dh)
  have hSE : SE⊆S := fun _ hx=> Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hSL : SL⊆S := fun _ hx=> Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hSH : SH⊆S := fun _ hx=> Finset.mem_union_right _ hx
  have hdE : dE≤ D := le_max_left _ _
  have hdl : dl≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hdh : dh≤ D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨S,D,Cm,hCm,?_⟩
  filter_upwards [hpaid,hlow,hhigh,(tendsto_rpow_atTop g.τ_pos).eventually
    (eventually_gt_atTop (2:ℝ))] with Z hp hl hh hT
  refine ⟨hp.1,?_⟩
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone Ψ reflected key firstHeight height hheight hfreq χ₀ s amp primes control
  have highReceipt:=actual_affine_main_high_receipt (plane:=plane) (α:=T) M H hH W hW hWs hβlo g P hPe hPτ
    ηseed SH dh KH (MainHigh.geometryAffineHighTarget g.μ g.δ) η₀ Q hQM hQ72 Z hh hZ θ w σ freq hσ
    bΦ state hη p t X₁ X₂ hX₁ hX₂ height mesh hw hmesh0 hmeshcap hwm (fun j=>(hwm j).trans hmarkedmesh) hheight hfreq hT hβhi
    hlo₁ hlo₂ hhi₁ hhi₂ ⟨hwlo,hwhi⟩ hcone reflected firstHeight key Ψ χ₀
  have branches:=actual_affine_main_selected_branches (α:=T) M H hH plane W hW hWs hβlo hκbeta g
    ηseed SL dl KL η₀ Q hQM hQ72 Z hl hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂
    height mesh hw hmesh0 hmeshcap hwm hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂
    ⟨hwlo,hwhi⟩ hcone reflected firstHeight key Ψ χ₀ KH SH dh
    (MainHigh.geometryAffineHighTarget g.μ g.δ) highReceipt
  have hamp:=affine_main_amplifier_of_actual_scales plane s Z hZ w (fun _=> rfl)
  rw [hamp] at branches
  have hside : 0≤ geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    (geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)).le
  have common:=affine_main_selected_branches_common_control plane g.δ (g.μ/64) Z amp (g.μ/8)
    firstHeight KL KH _ (MainPhysical.lowTarget (P:=plane) g (Fintype.card T) amp
      (frequencyLoss Z 32 (g.μ/64)+g.μ/8) mesh)
    (amp+MainHigh.geometryAffineHighTarget g.μ g.δ) height dl dh D hZ reflected s p SL SH S key Ψ χ₀
    (internalQ Q η₀) fixedBadMask (MainPhysical.affine_main_low_profile_zero (P:=plane) p 0) (MainPhysical.affine_main_low_profile_zero (P:=plane) p 1)
    hKL hKH hside hheight hSL hSH hdl hdh branches
  exact hp.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone S D hSE hdE Ψ reflected key firstHeight height hheight χ₀ common


/-- Once the shared schedule is fixed, obtain all low constants and join
one literal high estimate for each actual subset. Constants precede the
detector and all moving source data. -/
theorem actual_affine_main_uniform_paid_of_high
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤ plane.incumbent)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hεcap : εaffine≤1/10000000000000000000000000000)
    (hmesh : mesh< Sil.Uneven.MainSource.amplifierMinimum/2)(hmesh0 : 0≤ mesh)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤ N)(B L : ℝ)(hB : 0≤ B)(hL : 0≤ L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤ g.μ/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hmarkedmesh : mesh≤ BootstrapPlain.bootstrapRawMesh*SaturatedPlain.fineRawCore)
    (ηcoarse : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow ηcoarse u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (hhigh : ∀T : Finset α,∃P : HighSourceParameters,P.e=g.e ∧ P.τ=g.τ ∧
      ∃SH : Finset (ℕ×ℕ),∃dh : ℕ,∃KH : ℝ,0≤ KH ∧
      ∀ᶠZ : ℝ in atTop,MainHigh.GeometryAffineMainHighSpec (α:=T) M H hH plane W hW.continuous hWs hβlo
        P g.μ g.δ (MainHigh.geometryAffineHighTarget g.μ g.δ) ηseed SH dh KH η₀ Q hQM hQ72 Z) :
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineMainPaidSpec (plane:=plane) M H hH Sbad W hW.continuous hWs ηseed η₀ mesh g.μ T S D Cm Z := by
  obtain ⟨Cs,dl,SL,hsaved,low⟩:=MainPhysical.actual_affine_main_low_payment (P:=plane) (α:=α) M H hH
    W hW hWs hβlo hκbeta g ηseed ηcoarse u₀ F₀ R₀ hu₀
  obtain ⟨KL,hKL⟩:=low η₀ Q hQM hQ hQt hQ72
  intro T
  obtain ⟨P,he,hτ,SH,dh,KH,hKH,hhighT⟩:=hhigh T
  exact actual_affine_main_complete_payment M H hH T A (dl T) dh hc hs Sbad hbad
    W hW.continuous hWs hβlo hβhi hκbeta ηseed εaffine mesh hε hεcap hmesh hmesh0 g hμ N hN B L
    hB hL hδ hmeshμ hmeshcap hmarkedmesh P he hτ η₀ Q hQM hQ hQt hQ72 (SL T) SH (KL T) KH
    (hKL.down.1 T).le hKH (hKL.down.2.mono (fun _ hz=> hz.2 T)) hhighT

end
end OAI.SevenEighths.MainHigh
end
