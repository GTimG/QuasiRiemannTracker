/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainHighReceipt
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
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

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The paid retained main estimate, uniform in the actual moving source. -/
def GeometryAffineMainPaidSpec
    (Sbad : Finset (Ideal O))
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (ηseed η₀ : Character)(mesh μ : ℝ)(T : Finset α)
    (S : Finset (ℕ×ℕ))(D : ℕ)(Cm Z : ℝ) : Prop :=
    ∀(hZ : 1<Z)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ)
      (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤ mesh) →
      Cycle63.CountAffine.windowBottom≤length Z X₁ → Cycle63.CountAffine.windowBottom≤length Z X₂ →
      length Z X₁≤Cycle63.CountAffine.plainLengthTop → length Z X₂≤Cycle63.CountAffine.plainLengthTop →
      Cycle63.Optimization.slotFloor≤∑i,w i → (∑i,w i)≤Cycle63.Optimization.slotTop →
      length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑i,w i)≤Cycle63.Arithmetic.B →
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),
      0≤height → (∀i,|freq i|≤height) →
    ∀χ₀ : RayCharacter,
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let amp:=Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i)))
    let primes:=CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^amp)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    (56/(primes.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
        firstHeight hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖≤
      Cm*control*Z^(-((Cycle63.Arithmetic.lowReserve/2):ℝ))

/-- Assemble the checked literal low and high estimates with the complete
retained main contraction. The actual subset remains the Fourier carrier;
the ambient cardinality enters only the outside loss ledger. -/
theorem actual_affine_main_complete_payment
    (T : Finset α)(A dl dh : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.Arithmetic.amplifierFloor/2)(hmesh0 : 0≤ mesh)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤N)(B L : ℝ)(hB : 0≤B)(hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤g.μ/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (P : HighSourceParameters)(hPe : P.e=g.e)(hPτ : P.τ=g.τ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (SL SH : Finset (ℕ×ℕ))(KL KH : ℝ)(hKL : 0≤KL)(hKH : 0≤KH)
    (hlow : ∀ᶠZ : ℝ in atTop,GeometryAffineMainLowSpec (α:=T) M H hH W hW hWs hβlo
      g ηseed SL dl KL η₀ Q hQM hQ72 Z)
    (hhigh : ∀ᶠZ : ℝ in atTop,GeometryAffineMainHighSpec (α:=T) M H hH W hW hWs hβlo
      P g.μ g.δ (geometryAffineHighTarget g.μ g.δ) ηseed SH dh KH η₀ Q hQM hQ72 Z) :
    ∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤Cm ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    GeometryAffineMainPaidSpec M H hH Sbad W hW hWs ηseed η₀ mesh g.μ T S D Cm Z := by
  obtain ⟨Cs,hCs,Ksel,hKsel,Cm,hCm,SE,dE,hpaid⟩:=
    actual_affine_main_uniform_component_payment (α:=α) M H hH A dl dh hc hs Sbad hbad
      W hW hWs ηseed εaffine mesh hε hmesh g hμ N hN B L hB hL hδ hmeshμ
      (internalQ Q η₀) hQ hQt hQ72 KL KH hKL hKH
  let S:=(SE∪SL)∪SH
  let D:=max dE (max dl dh)
  have hSE : SE⊆S := fun _ hx=>Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hSL : SL⊆S := fun _ hx=>Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hSH : SH⊆S := fun _ hx=>Finset.mem_union_right _ hx
  have hdE : dE≤D := le_max_left _ _
  have hdl : dl≤D := (le_max_left _ _).trans (le_max_right _ _)
  have hdh : dh≤D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨S,D,Cm,hCm,?_⟩
  filter_upwards [hpaid,hlow,hhigh,(tendsto_rpow_atTop g.τ_pos).eventually
    (eventually_gt_atTop (2:ℝ))] with Z hp hl hh hT
  refine ⟨hp.1,?_⟩
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone Ψ reflected key firstHeight height hheight hfreq χ₀ s amp primes control
  have highReceipt:=actual_affine_main_high_receipt (α:=T) M H hH W hW hWs hβlo g P hPe hPτ
    ηseed SH dh KH (geometryAffineHighTarget g.μ g.δ) η₀ Q hQM hQ72 Z hh hZ θ w σ freq hσ
    bΦ state hη p t X₁ X₂ hX₁ hX₂ height mesh hw hmesh0 hmeshcap hwm (fun j=>(hwm j).trans hmarkedmesh) hheight hfreq hT hβhi
    hlo₁ hlo₂ hhi₁ hhi₂ ⟨hwlo,hwhi⟩ hcone reflected firstHeight key Ψ χ₀
  have branches:=actual_affine_main_selected_branches (α:=T) M H hH W hW hWs hβlo g
    ηseed SL dl KL η₀ Q hQM hQ72 Z hl hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂
    height mesh hw hmesh0 hmeshcap hwm hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂
    ⟨hwlo,hwhi⟩ hcone reflected firstHeight key Ψ χ₀ KH SH dh
    (geometryAffineHighTarget g.μ g.δ) highReceipt
  have hamp:=affine_main_amplifier_of_actual_scales s Z hZ w (fun _=>rfl)
  rw [hamp] at branches
  have hside : 0≤geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    (geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)).le
  have common:=affine_main_selected_branches_common_control g.δ (g.μ/64) Z amp (g.μ/8)
    firstHeight KL KH _ (geometryAffineLowTarget g (Fintype.card T) amp
      (frequencyLoss Z 32 (g.μ/64)+g.μ/8) mesh)
    (amp+geometryAffineHighTarget g.μ g.δ) height dl dh D hZ reflected s p SL SH S key Ψ χ₀
    (internalQ Q η₀) fixedBadMask (affine_main_low_profile_zero p 0) (affine_main_low_profile_zero p 1)
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
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.Arithmetic.amplifierFloor/2)(hmesh0 : 0≤ mesh)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤N)(B L : ℝ)(hB : 0≤B)(hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤g.μ/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (ηcoarse : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow ηcoarse u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hhigh : ∀T : Finset α,∃P : HighSourceParameters,P.e=g.e ∧ P.τ=g.τ ∧
      ∃SH : Finset (ℕ×ℕ),∃dh : ℕ,∃KH : ℝ,0≤KH ∧
      ∀ᶠZ : ℝ in atTop,GeometryAffineMainHighSpec (α:=T) M H hH W hW.continuous hWs hβlo
        P g.μ g.δ (geometryAffineHighTarget g.μ g.δ) ηseed SH dh KH η₀ Q hQM hQ72 Z) :
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤Cm ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineMainPaidSpec M H hH Sbad W hW.continuous hWs ηseed η₀ mesh g.μ T S D Cm Z := by
  obtain ⟨Cs,dl,SL,hsaved,low⟩:=actual_affine_main_low_payment (α:=α) M H hH
    W hW hWs hβlo g ηseed ηcoarse u₀ F₀ R₀ hu₀
  obtain ⟨KL,hKL⟩:=low η₀ Q hQM hQ hQt hQ72
  intro T
  obtain ⟨P,he,hτ,SH,dh,KH,hKH,hhighT⟩:=hhigh T
  exact actual_affine_main_complete_payment M H hH T A (dl T) dh hc hs Sbad hbad
    W hW.continuous hWs hβlo hβhi ηseed εaffine mesh hε hmesh hmesh0 g hμ N hN B L
    hB hL hδ hmeshμ hmeshcap hmarkedmesh P he hτ η₀ Q hQM hQ hQt hQ72 (SL T) SH (KL T) KH
    (hKL.down.1 T).le hKH (hKL.down.2.mono (fun _ hz=>hz.2 T)) hhighT

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_main_complete_payment

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_main_uniform_paid_of_high
