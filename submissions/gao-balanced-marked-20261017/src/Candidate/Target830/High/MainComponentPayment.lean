import Candidate.Target830.High.MainPayment
import Candidate.Target830.Source.Reconstruction.GeometryAffineAmplification
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
local instance newMainComponentSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ Target830.Source.LowPhysical.mainLowPhysicalCompleteCost


variable {plane : SourcePlane}
variable {α : Type} [Fintype α] [DecidableEq α]



variable (M : Ideal O) [NeZero M]
local instance mainComponentQuotient : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
theorem actual_affine_main_uniform_component_payment
    (A dl dh : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Source.amplifierMinimum/2)(hmesh0 : 0 ≤ mesh)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤N)(B L : ℝ)(hB : 0≤B)(hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤g.μ/8)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (KL KH : ℝ)(hKL : 0≤KL)(hKH : 0≤KH) :
    ∃Cs : ℝ,1≤Cs ∧ ∃Ksel : ℝ,0<Ksel ∧ ∃Cm : ℝ,0≤Cm ∧
    ∃SE : Finset (ℕ×ℕ),∃dE : ℕ,∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters M H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤ mesh) →
      (81/200:ℝ)≤length Z X₁ → (81/200:ℝ)≤length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      length Z X₁+length Z X₂+plane.lambda*(∑i,w i)≤plane.B →
    ∀(S : Finset (ℕ×ℕ))(D : ℕ),SE⊆S → dE≤D →
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height →
    ∀χ₀ : RayCharacter,
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_main_low_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_main_low_profile_zero p 1
    let beta:=widthCellUpper (∑i,w i)
    let amp:=plane.amp beta
    let P:=CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^amp)
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    let low:=lowTarget (P:=plane) g (Fintype.card T) amp omega mesh
    let high:=amp+(-(1/1000000:ℝ)+4*g.μ-3*g.δ)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    GeometryAffineMainSelectedBranches plane g.δ (g.μ/64) Z amp (g.μ/8) firstHeight
      ((KL*control)*Z^low) ((KH*control)*Z^high) dl dh hZ
      reflected s key Ψ χ₀ Qfix fixedBadMask hz₁ hz₂ →
    (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      ‖balancedMainRetainedSum reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (g.μ/64) q))‖≤
      Cm*control*Z^(-(7/60000000:ℝ)) := by
  obtain ⟨Cs,hCs,Ksel,hKsel,hsource⟩:=actual_affine_main_source_selection (α:=α) M H hH
    W hW hWs g.δ (g.μ/64) g.δ_pos (div_nonneg g.μ_pos.le (by norm_num))
  obtain ⟨Ce,hCe,SE,dE,Co,hCo,hcontract⟩:=actual_affine_main_retained_contraction (plane:=plane) (α:=α)
    M H hH A (max dl dh) (max dl dh) hc hs Sbad hbad W hW hWs ηseed εaffine mesh hε hmesh
    Qfix hQ hQt hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
  obtain ⟨Cb,hCb,hratio⟩:=uniform_actual_affine_main_ratio_payment (plane:=plane) (α:=α) M H hH
    W hW hWs εaffine g.δ hε g.δ_pos
  have hbudget:=Source.Reconstruction.actual_affine_geometry_amplification (plane:=plane) (α:=α) M H hH
    Sbad hbad W hW hWs g.δ mesh (g.μ/64) (g.μ/8) g.δ_pos hmesh (by linarith [g.μ_pos])
    (by linarith [g.μ_cap]) (by linarith [g.μ_pos])
  let Cm:=Ce+Co*(56*4096*Cb*Ksel*(KL+KH))
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
  have hside : 0<geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)
  have hcontrol : 0≤control := by dsimp only [control];positivity
  have hn:=actual_affine_main_normalized_of_selected_low_high Cs g.δ (g.μ/64) Ksel Z
    ((KL*control)*Z^low) ((KH*control)*Z^high) dl dh hZ hKsel.le (by positivity) (by positivity)
    (hz.2 T).1 reflected s p caps amp (g.μ/8) firstHeight key Ψ χ₀ Qfix fixedBadMask
    ballProfile hz₁ hz₂ hbranches
  let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
    firstHeight (Fintype.card T) hZ key hz₁ hz₂
  let datum:=fun j : selected=>geometryLowSecondDatum reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8)
    (9/4) firstHeight (Fintype.card T) hZ key j.val.1 hz₁ hz₂ j.val.2
  let E:=Ksel*Z^g.δ*((KL*control)*Z^low+(KH*control)*Z^high)
  have hE : 0≤E := by dsimp only [E];positivity
  let ratio:=∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A
  have hnorm : SecondNormalizedBound ballProfile (max dl dh) (max dl dh)
      (fun j=>ordinarySecondDatum (datum j) χ₀ Qfix fixedBadMask)
      (fun j=>balancedMainSecondWeight reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (g.μ/64) q)) j.val)
      (fun _=>E) (fun _=>1) := by
    simpa only [geometryMainOrdinaryDatum] using hn
  have hp:=hcZ.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone Ψ reflected key firstHeight
    (fun _=>χ₀) (fun _=>E) (fun _=>1) (fun _ _=>hE) (fun _ _=>by norm_num)
    (by simpa only [datum,selected,s,amp,beta] using hnorm)
  have hratioZ:=hrZ.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
  have hratioPaid : ratio≤Cb*E*Z^g.δ := by
    simpa only [ratio,datum,selected,s,amp,beta] using
      (hratioZ.2.2 reflected key firstHeight).2.1 E hE A
  have hprime:=(hpZ.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi).2.1
  have hcount : Fintype.card T≤N :=
    (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective).trans hN
  have htargets:=affine_main_final_branch_exponents g εaffine hε hμ (Fintype.card T) N hcount
    B L amp omega mesh hB hL hδ hfZ.2.2 hmeshμ
  have hlowcomp:=low_target_le_accepted plane g (Fintype.card T) amp omega mesh hfZ.2.1 hmesh0
  have htargetsLow : low+3*g.δ-amp≤-(7/60000000:ℝ) := by
    dsimp only [low]
    linarith only [hlowcomp,htargets.1]
  have hex : Ce*geometryAffineExceptionalShell reflected Z key*(p.control SE)^2*
      (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ))≤Ce*control*Z^(-(7/60000000:ℝ)) := by
    change Ce*Cycle63InitialMass.geometryAffineExceptionalShell reflected Z key*(p.control SE)^2*
      (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ))≤Ce*control*Z^(-(7/60000000:ℝ))
    rw [geometry_affine_exceptional_shell_eq (Fintype.card T) Z hZ]
    have hprofile:=pow_le_pow_left₀ (p.control_nonneg SE) (Cycle63Physical.profile_control_mono p hSE) 2
    have hbase : (1+‖firstHeight‖)^dE≤(1+|firstHeight|+height)^D := by
      rw [Real.norm_eq_abs]
      exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdE)
    have hpow:=Real.rpow_le_rpow_of_exponent_le hZ.le
      (by norm_num : -(1/100:ℝ)≤-(7/60000000:ℝ))
    have hh : Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control SE)^2*
        (1+‖firstHeight‖)^dE≤Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control S)^2*
        (1+|firstHeight|+height)^D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprofile (mul_nonneg hCe.le hside.le))
        hbase (pow_nonneg (by positivity) _) (by positivity)
    have hm:=mul_le_mul hh hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity)
    convert hm using 1;dsimp only [control];ring
  have hb:=(widthCellUpper_bounds ⟨hwlo,hwhi⟩).1
  have hcoef:=geometry_affine_main_amplifier_bound plane beta hb
  exact geometry_affine_main_contracted_payment Z (P.card:ℝ) amp g.δ low high (-(7/60000000))
    ((amplifierCap 2 0 1+6*amp)/(amp/2)) 4096 Cb Ksel KL KH Ce Co control
    _ _ ratio hZ hprime hcoef.1 hcoef.2 hCb.le hKsel.le hKL hKH hCo.le hcontrol
    (by simpa only [P,s,amp,beta,ratio,datum,selected,mul_assoc] using hp) hex hratioPaid htargetsLow htargets.2

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_affine_main_uniform_component_payment
