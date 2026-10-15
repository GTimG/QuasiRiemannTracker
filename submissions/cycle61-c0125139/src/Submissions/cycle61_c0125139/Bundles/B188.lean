/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B160
import Submissions.cycle61_c0125139.Bundles.B185
import Submissions.cycle61_c0125139.Bundles.B187

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainHighReceipt; sha256 e3f7e437cb606c5d40a34331e4adaff98e5952ae1e16834d04d9ee3394efddcf -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                             

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentAllocatedRayDictionary CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge Cycle61Moment
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional
open Cycle61InitialSource
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The proved high cost uses precisely the canonical family required by
the retained main contraction. Only selector field equalities and scalar
norm notation are transported; no row, filter, or weight is changed. -/
theorem affine_main_high_receipt_of_selected_cost
    (W : ℝ→ℂ)(hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(P : HighSourceParameters)
    (hPe : P.e=g.e)(hPτ : P.τ=g.τ)(ηseed : Character)(Cs target : ℝ)
    (SH : Finset (ℕ×ℕ))(dh : ℕ)(KH : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (Z : ℝ)(hZ : 1< Z)(s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)(hsη : s.η=ηseed)
    (height mesh : ℝ)(hw : ∀j,0≤ w j)
    (hwL : ∀j,w j≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hwr : ∀j,w j/31≤1)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)(hT : 2< Z^g.τ)
    (hzslot : (17/500:ℝ)≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤1/25)
    (haff : length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
      Cycle61.Arithmetic.B)
    (hvolumeCell : Real.logb Z (volume s)≤ Cycle61.Arithmetic.totalA
      (Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑j,Real.logb Z (s.P j)))))
    (reflected : Bool)(baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ₀ : RayCharacter)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hspec : GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hβlo P g.μ g.δ target
      (fun _ _ _ _ _=>True) ηseed Cs SH dh KH η₀ Q hQM hQ72 Z) :
    let amp:=(1:ℝ)*Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper
      (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    0≤ amp → |amp|≤4 → |omega|≤4 →
    GeometryAffineMainCanonicalHighReceipt M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT
      reflected s p amp baseHeight height key Ψ χ₀ hz₁ hz₂ KH SH dh target := by
  cases P
  cases g
  dsimp only at hPe hPτ
  cases hPe
  cases hPτ
  intro amp omega hamp0 hamp homega second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf firstIndex
    selected raw datum coefficient hP hPN canonical
  have hb:=hspec hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hσ
    hheight hfreq hT hβhi hzslot haff hvolumeCell
    reflected second key baseHeight firstIndex hamp0 hamp homega hf hinj χ₀ fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Ψ t₀ u trivial hP hPN
  convert hb using 1
  rfl

/-- The literal affine high estimate supplies the exact selected branch
used by the main payment, with source admission already discharged. -/
theorem actual_affine_main_high_receipt
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (P : HighSourceParameters)(hPe : P.e=g.e)(hPτ : P.τ=g.τ)
    (ηseed : Character)(SH : Finset (ℕ×ℕ))(dh : ℕ)(KH target : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (Z : ℝ)(hspec : GeometryAffineMainHighSpec (α:=α) M H hH W hW hWs hβlo P
      g.μ g.δ target ηseed SH dh KH η₀ Q hQM hQ72 Z)
    (hZ : 1< Z)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)
    (height mesh : ℝ)(hw : ∀i,0≤ w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwm : ∀i,w i≤ mesh)
    (hheight : 0≤ height)(hfreq : ∀i,|freq i|≤ height)(hT : 2< Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hlo₁ : (41/100:ℝ)≤ length Z X₁)(hlo₂ : (41/100:ℝ)≤ length Z X₂)
    (hhi₁ : length Z X₁≤(44/100:ℝ))(hhi₂ : length Z X₂≤(44/100:ℝ))
    (hslots : (17/500:ℝ)≤∑i,w i ∧ (∑i,w i)≤1/25)
    (hcone : length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑i,w i)≤ Cycle61.Arithmetic.B)
    (reflected : Bool)(baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ₀ : RayCharacter) :
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_main_low_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_main_low_profile_zero p 1
    let amp:=(1:ℝ)*Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper
      (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    GeometryAffineMainCanonicalHighReceipt M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT
      reflected s p amp baseHeight height key Ψ χ₀ hz₁ hz₂ KH SH dh target := by
  cases P
  cases g
  dsimp only at hPe hPτ
  cases hPe
  cases hPτ
  intro s hz₁ hz₂ amp second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf
    firstIndex selected raw datum coefficient hP hPN canonical
  have hb:=hspec hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh
    hw hmesh hmeshcap hwm hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂ hslots hcone
    reflected second key baseHeight firstIndex hf hinj χ₀ fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Ψ t₀ u hP hPN
  convert hb using 1
  rfl

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_main_high_receipt_of_selected_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_main_high_receipt

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainHighReceipt -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainCompletePayment; sha256 6a9fbb7fb52151f710cde449427787bee7555549b0e54fb76cc8c20685386e13 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                 

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle61Moment
open Cycle61Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle61FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle61InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
local notation "O" => HeckeFamily.O

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
    ∀(hZ : 1< Z)(θ : T→ RayQuotient.Characters M H)(w σ freq : T→ℝ)
      (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) →
      (41/100:ℝ)≤ length Z X₁ → (41/100:ℝ)≤ length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑i,w i)≤ Cycle61.Arithmetic.B →
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),
      0≤ height → (∀i,|freq i|≤ height) →
    ∀χ₀ : RayCharacter,
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let amp:=Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑i,w i)))
    let primes:=CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^amp)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    (56/(primes.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
        firstHeight hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖≤
      Cm*control*Z^(-(7/60000000:ℝ))

/-- Assemble the checked literal low and high estimates with the complete
retained main contraction. The actual subset remains the Fourier carrier;
the ambient cardinality enters only the outside loss ledger. -/
theorem actual_affine_main_complete_payment
    (T : Finset α)(A dl dh : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤ N)(B L : ℝ)(hB : 0≤ B)(hL : 0≤ L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤ g.μ/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (P : HighSourceParameters)(hPe : P.e=g.e)(hPτ : P.τ=g.τ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (SL SH : Finset (ℕ×ℕ))(KL KH : ℝ)(hKL : 0≤ KL)(hKH : 0≤ KH)
    (hlow : ∀ᶠZ : ℝ in atTop,GeometryAffineMainLowSpec (α:=T) M H hH W hW hWs hβlo
      g ηseed SL dl KL η₀ Q hQM hQ72 Z)
    (hhigh : ∀ᶠZ : ℝ in atTop,GeometryAffineMainHighSpec (α:=T) M H hH W hW hWs hβlo
      P g.μ g.δ (geometryAffineHighTarget g.μ g.δ) ηseed SH dh KH η₀ Q hQM hQ72 Z) :
    ∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
    ∀ᶠZ : ℝ in atTop,1< Z ∧
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
  have hdE : dE≤ D := le_max_left _ _
  have hdl : dl≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hdh : dh≤ D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨S,D,Cm,hCm,?_⟩
  filter_upwards [hpaid,hlow,hhigh,(tendsto_rpow_atTop g.τ_pos).eventually
    (eventually_gt_atTop (2:ℝ))] with Z hp hl hh hT
  refine ⟨hp.1,?_⟩
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone Ψ reflected key firstHeight height hheight hfreq χ₀ s amp primes control
  have highReceipt:=actual_affine_main_high_receipt (α:=T) M H hH W hW hWs hβlo g P hPe hPτ
    ηseed SH dh KH (geometryAffineHighTarget g.μ g.δ) η₀ Q hQM hQ72 Z hh hZ θ w σ freq hσ
    bΦ state hη p t X₁ X₂ hX₁ hX₂ height mesh hw hmesh0 hmeshcap hwm hheight hfreq hT hβhi
    hlo₁ hlo₂ hhi₁ hhi₂ ⟨hwlo,hwhi⟩ hcone reflected firstHeight key Ψ χ₀
  have branches:=actual_affine_main_selected_branches (α:=T) M H hH W hW hWs hβlo g
    ηseed SL dl KL η₀ Q hQM hQ72 Z hl hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂
    height mesh hw hmesh0 hmeshcap hwm hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂
    ⟨hwlo,hwhi⟩ hcone reflected firstHeight key Ψ χ₀ KH SH dh
    (geometryAffineHighTarget g.μ g.δ) highReceipt
  have hamp:=affine_main_amplifier_of_actual_scales s Z hZ w (fun _=>rfl)
  rw [hamp] at branches
  have hside : 0≤ geometryHighFactor reflected
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
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤ N)(B L : ℝ)(hB : 0≤ B)(hL : 0≤ L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤ g.μ/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (ηcoarse : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow ηcoarse u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (hhigh : ∀T : Finset α,∃P : HighSourceParameters,P.e=g.e ∧ P.τ=g.τ ∧
      ∃SH : Finset (ℕ×ℕ),∃dh : ℕ,∃KH : ℝ,0≤ KH ∧
      ∀ᶠZ : ℝ in atTop,GeometryAffineMainHighSpec (α:=T) M H hH W hW.continuous hWs hβlo
        P g.μ g.δ (geometryAffineHighTarget g.μ g.δ) ηseed SH dh KH η₀ Q hQM hQ72 Z) :
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineMainPaidSpec M H hH Sbad W hW.continuous hWs ηseed η₀ mesh g.μ T S D Cm Z := by
  obtain ⟨Cs,dl,SL,hsaved,low⟩:=actual_affine_main_low_payment (α:=α) M H hH
    W hW hWs hβlo g ηseed ηcoarse u₀ F₀ R₀ hu₀
  obtain ⟨KL,hKL⟩:=low η₀ Q hQM hQ hQt hQ72
  intro T
  obtain ⟨P,he,hτ,SH,dh,KH,hKH,hhighT⟩:=hhigh T
  exact actual_affine_main_complete_payment M H hH T A (dl T) dh hc hs Sbad hbad
    W hW.continuous hWs hβlo hβhi ηseed εaffine mesh hε hmesh hmesh0 g hμ N hN B L
    hB hL hδ hmeshμ hmeshcap P he hτ η₀ Q hQM hQ hQt hQ72 (SL T) SH (KL T) KH
    (hKL.down.1 T).le hKH (hKL.down.2.mono (fun _ hz=>hz.2 T)) hhighT

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_main_complete_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_main_uniform_paid_of_high

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainCompletePayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineFinalWeight; sha256 cd8eea28e8c27121b4ac51baa1d60a0e1c0cae3a6d55adeb99e640fef3dcd809 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                 
                                                      

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput

/-- The shifted first height contributes independent original and Mellin
weights. The second Mellin exponent is rounded up to an even degree. -/
theorem geometry_affine_final_height_weight (J K : ℕ)
    (base height t u : ℝ) (reflected : Bool) (hh : 0≤ height) :
    (1+|base|+height)^J*
      (1+‖base+2*Real.pi*(u-(if reflected then -t else t))‖)^K ≤
    (1+|2*Real.pi|)^K*(1+|base|+height)^(J+K)*
      (1+‖t‖)^K*(1+‖u‖)^(2*K) := by
  have h := geometry_affine_exceptional_mellin_weight K base height t u reflected hh
  have hu : (1+‖u‖)^K≤(1+‖u‖)^(2*K) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg u]) (by omega)
  have hbase : 0≤1+|base|+height := by positivity
  have h₁ := mul_le_mul_of_nonneg_left h (pow_nonneg hbase J)
  have h₂ := mul_le_mul_of_nonneg_left hu
    (show 0≤(1+|2*Real.pi|)^K*(1+|base|+height)^(J+K)*(1+‖t‖)^K by positivity)
  apply h₁.trans
  convert h₂ using 1
  rw [pow_add]
  ring

/-- Convert an actual-slot budget to the ambient budget and the reciprocal
side convention used in the literal affine assembly. The analytic branch
bound remains explicit. -/
theorem geometry_affine_final_budget_weight {α : Type} [Fintype α] [DecidableEq α]
    (T : Finset α) (s : Input T) (Z ξ ε C control height : ℝ) (hZ : 1< Z)
    (J K : ℕ) (Ψ : 𝓢(ℝ,ℂ)) (reflected : Bool) (key : ℤ×(Fin 5→ℤ))
    (t u : ℝ) (hC : 0≤ C) (hc : 0≤ control) (hh : 0≤ height)
    (hbound : geometryLiveBudget reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key
      (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q))
      (Fintype.card T) (9/4) (s.t+2*Real.pi*(u-(if reflected then -t else t))) ≤
      C*geometryHighFactor reflected 64 key*control*(1+|s.t|+height)^J*
        (1+‖s.t+2*Real.pi*(u-(if reflected then -t else t))‖)^K*Z^ε) :
    let E := (9/4:ℝ)^(Fintype.card α)*C*(1+2*(64:ℝ)^2)*(1+|2*Real.pi|)^K*
      control*(1+|s.t|+height)^(J+K)*Z^ε
    geometryLiveBudget reflected s 1 1 Z Z ξ 1 (Real.logb Z (volume s))
      (zero_lt_one.trans hZ) key (fun q=>normPhase (coordinateBlock s 1 1 Ψ Z Z ξ q))
      (Fintype.card α) (9/4) (s.t+2*Real.pi*(u-(if reflected then -t else t))) ≤
      ((if reflected then E/geometryDCompensator key else E*geometryDCompensator key)*
        (1+‖t‖)^K)*(1+‖u‖)^(2*K) := by
  intro E
  have hs : 0≤ geometryHighFactor reflected 64 key :=
    (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  have hz : 0≤ Z^ε := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hw := geometry_affine_final_height_weight J K s.t height t u reflected hh
  have hpaid := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw (mul_nonneg (mul_nonneg hC hs) hc)) hz
  have hactual := hbound.trans (by convert hpaid using 1; ring)
  have hnonneg : 0≤ C*geometryHighFactor reflected 64 key*control*
      ((1+|2*Real.pi|)^K*(1+|s.t|+height)^(J+K)*(1+‖t‖)^K*(1+‖u‖)^(2*K))*Z^ε := by
    positivity
  have hambient := geometry_affine_budget_to_ambient T s Z ξ
    (s.t+2*Real.pi*(u-(if reflected then -t else t))) _ hZ Ψ reflected key hnonneg hactual
  have hside := geometry_physical_side_join reflected 64
    ((9/4:ℝ)^(Fintype.card α)*C) ((1+|2*Real.pi|)^K*control*
      (1+|s.t|+height)^(J+K)*Z^ε*(1+‖t‖)^K*(1+‖u‖)^(2*K)) _ key
      (by positivity) (by positivity) (by convert hambient using 1; ring)
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hside ⊢
  · convert hside using 1
    dsimp only [E]
    ring
  · convert hside using 1
    dsimp only [E]
    ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_final_height_weight
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_final_budget_weight

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineFinalWeight -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePaidBudget; sha256 8e76f76347ee4cc5e6220f5a3f926de9d4a3434af06dc15650e1330afc66a32f -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                           

set_option autoImplicit false
set_option maxHeartbeats 40000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open QuadraticInitialBound CenteredMomentFiniteProfileExceptional Cycle61Physical

private theorem paid_profile_weight_mono
    (p : Profiles (1/4) (9/4)) (S S' : Finset (ℕ×ℕ))
    (C H x y Z e e' : ℝ) (j j' k k' : ℕ)
    (hS : S⊆S') (hC : 0≤ C) (hH : 0≤ H) (hx : 1≤ x) (hy : 1≤ y)
    (hZ : 1< Z) (he : e≤ e') (hj : j≤ j') (hk : k≤ k') :
    C*H*(p.control S)^2*x^j*y^k*Z^e ≤
      C*H*(p.control S')^2*x^j'*y^k'*Z^e' := by
  have hp := profile_control_mono p hS
  have hp0 := p.control_nonneg S
  have hx0 := zero_le_one.trans hx
  have hy0 := zero_le_one.trans hy
  have hxp := pow_le_pow_right₀ hx hj
  have hyp := pow_le_pow_right₀ hy hk
  have hzp := Real.rpow_le_rpow_of_exponent_le hZ.le he
  have hsquare := pow_le_pow_left₀ hp0 hp 2
  gcongr

/-- Join the two already-paid branches with the zero/tail remainder. The
prime average and amplifier coefficient occur only in the supplied paid
branch inequalities; this join introduces no additional prime payment. -/
theorem geometry_affine_paid_branch_budget
    (p : Profiles (1/4) (9/4)) (Sm Se : Finset (ℕ×ℕ))
    (budget main error average coefficient Cr Cm Ce H x y Z em ee e : ℝ)
    (jm je km ke : ℕ)
    (hCr : 0≤ Cr) (hCm : 0≤ Cm) (hCe : 0≤ Ce) (hH : 0≤ H)
    (hx : 1≤ x) (hy : 1≤ y) (hZ : 1< Z)
    (hem : em≤ e) (hee : ee≤ e) (he : 0≤ e)
    (hbudget : budget ≤ Cr*H*(p.control {(0,0)})^2*Z^(-(1/20:ℝ)) +
      average*(coefficient*main+error))
    (hmain : average*coefficient*main ≤ Cm*H*(p.control Sm)^2*x^jm*y^km*Z^em)
    (herror : average*error ≤ Ce*H*(p.control Se)^2*x^je*y^ke*Z^ee) :
    let S := ({(0,0)}∪Sm)∪Se
    budget ≤ (Cr+Cm+Ce)*H*(p.control S)^2*x^(max jm je)*y^(max km ke)*Z^e := by
  intro S
  have hSm : Sm⊆S := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hSe : Se⊆S := Finset.subset_union_right
  have hS0 : {(0,0)}⊆S := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hm := paid_profile_weight_mono p Sm S Cm H x y Z em e jm (max jm je) km (max km ke)
    hSm hCm hH hx hy hZ hem (le_max_left _ _) (le_max_left _ _)
  have herr := paid_profile_weight_mono p Se S Ce H x y Z ee e je (max jm je) ke (max km ke)
    hSe hCe hH hx hy hZ hee (le_max_right _ _) (le_max_right _ _)
  have hr := paid_profile_weight_mono p {(0,0)} S Cr H x y Z (-(1/20:ℝ)) e
    0 (max jm je) 0 (max km ke) hS0 hCr hH hx hy hZ (by linarith)
    (Nat.zero_le _) (Nat.zero_le _)
  simp only [pow_zero, mul_one] at hr
  calc
    budget ≤ Cr*H*(p.control {(0,0)})^2*Z^(-(1/20:ℝ)) +
        average*coefficient*main + average*error := by nlinarith only [hbudget]
    _ ≤ Cr*H*(p.control S)^2*x^(max jm je)*y^(max km ke)*Z^e +
        Cm*H*(p.control S)^2*x^(max jm je)*y^(max km ke)*Z^e +
        Ce*H*(p.control S)^2*x^(max jm je)*y^(max km ke)*Z^e :=
      add_le_add (add_le_add hr (hmain.trans hm)) (herror.trans herr)
    _ = _ := by ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_paid_branch_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePaidBudget -/
