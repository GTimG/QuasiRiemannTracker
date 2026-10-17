/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineRetainedBudget
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePaidBudget
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineUniformBudget
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineBudgetTransport
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
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
attribute [local irreducible] Finset.univ geometryAffineErrorRetainedSum geometryMainRetainedSum geometryLiveBudget

/-- Separate the actual shifted first height from the original source
height. This transport changes only polynomial scalar factors. -/
theorem affine_paid_height_product (t firstHeight height : ℝ)(D : ℕ)(hh : 0≤height) :
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
    (Dm De : ℕ)(hCr : 0≤Cr)(hCm : 0≤Cm)(hCe : 0≤Ce)(hH : 0≤H)
    (hh : 0≤height)(hZ : 1<Z)(hε : 0≤εmass)
    (hbudget : budget≤Cr*(p.control {(0,0)})^2*H*Z^(-(1/20:ℝ))+
      average*(coefficient*main+error))
    (hmain : average*coefficient*main≤Cm*(p.control Sm)^2*H*
      (1+|firstHeight|+height)^Dm*Z^(-((Cycle63.Arithmetic.lowReserve/2):ℝ)))
    (herror : average*error≤Ce*(p.control Se)^2*H*
      (1+|firstHeight|+height)^De*Z^(-((Cycle63.Arithmetic.lowReserve/4):ℝ))) :
    let S:=({(0,0)}∪Sm)∪Se
    budget≤(Cr+Cm+Ce)*H*(p.control S)^2*(1+|t|+height)^(max Dm De)*
      (1+‖firstHeight‖)^(max Dm De)*Z^εmass := by
  intro S
  have hm : average*coefficient*main≤Cm*H*(p.control Sm)^2*
      (1+|t|+height)^Dm*(1+‖firstHeight‖)^Dm*Z^(-((Cycle63.Arithmetic.lowReserve/2):ℝ)) := by
    apply hmain.trans
    have hh:=mul_le_mul_of_nonneg_left (affine_paid_height_product t firstHeight height Dm hh)
      (by positivity : 0≤Cm*(p.control Sm)^2*H)
    have hz:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (zero_lt_one.trans hZ).le (-((Cycle63.Arithmetic.lowReserve/2):ℝ)))
    convert hz using 1;ring
  have he : average*error≤Ce*H*(p.control Se)^2*
      (1+|t|+height)^De*(1+‖firstHeight‖)^De*Z^(-((Cycle63.Arithmetic.lowReserve/4):ℝ)) := by
    apply herror.trans
    have hh:=mul_le_mul_of_nonneg_left (affine_paid_height_product t firstHeight height De hh)
      (by positivity : 0≤Ce*(p.control Se)^2*H)
    have hz:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (zero_lt_one.trans hZ).le (-((Cycle63.Arithmetic.lowReserve/4):ℝ)))
    convert hz using 1;ring
  apply geometry_affine_paid_branch_budget p Sm Se budget main error average coefficient
    Cr Cm Ce H (1+|t|+height) (1+‖firstHeight‖) Z (-((Cycle63.Arithmetic.lowReserve/2))) (-((Cycle63.Arithmetic.lowReserve/4))) εmass
    Dm De Dm De hCr hCm hCe hH (by linarith [abs_nonneg t])
    (by linarith [norm_nonneg firstHeight]) hZ (by linarith [Cycle63.Arithmetic.lowReserve_pos])
    (by linarith [Cycle63.Arithmetic.lowReserve_pos]) hε _ hm he
  convert hbudget using 1;ring

variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance paidAssemblyFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hray : Subgroup (O⧸rayM)ˣ) (hHray : RayOrthogonality.globalUnits rayM≤Hray)

/-- Explicit pending paid components on the literal actual subset source.
The error receipt is universal in the original retained radical witness;
the assembly therefore cannot silently replace that witness. -/
def GeometryAffinePaidSubsetComponents
    (Sbad : Finset (Ideal O))
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh μ τ : ℝ)(Ψ : 𝓢(ℝ,ℂ))(T : Finset α)
    (Sm Se : Finset (ℕ×ℕ))(Dm De : ℕ)(Cm Ce Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(θ : T→RayQuotient.Characters rayM Hray)(w σ freq : T→ℝ)(t height : ℝ),
    (∀i,0≤w i) → (∀i,w i≤mesh) →
  ∀(hσlo : ∀i,(33/50:ℝ)≤σ i)(hσhi : ∀i,σ i≤(33/50:ℝ)),
    0≤height → (∀i,|freq i|≤height) → 1+|t|+height≤Z^τ →
  ∀(Φ : 𝓢(ℝ,ℂ))(hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hpΦ : ∀x,0≤(Φ x).re)(p : Profiles (1/4) (9/4))(X₁ X₂ : ℝ)
    (hX₁ : 0<X₁)(hX₂ : 0<X₂),
    Cycle63.CountAffine.windowBottom≤length Z X₁ → length Z X₁≤Cycle63.CountAffine.plainLengthTop →
    Cycle63.CountAffine.windowBottom≤length Z X₂ → length Z X₂≤Cycle63.CountAffine.plainLengthTop →
    Cycle63.Optimization.slotFloor≤∑i,w i → (∑i,w i)≤Cycle63.Optimization.slotTop →
    length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑i,w i)≤Cycle63.Arithmetic.B →
  let state:=fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
  let s:=affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
    1 t X₁ X₂ hX₁ hX₂
  let amp:=Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i)))
  let P:=CenteredMomentPrimePool.primePool rayM Hray Sbad (1/2) 1 (Z^amp)
  ∀key∈commonGeometryBins s 1 1 Z Z (μ/64),∀(reflected : Bool)(firstHeight : ℝ),
  let side:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key
  let phase:=fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q)
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let First:=GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key
  (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
    ‖geometryMainRetainedSum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight hZ key
      1 (Real.logb Z (volume s)) phase‖≤
    Cm*(p.control Sm)^2*side*(1+|firstHeight|+height)^Dm*Z^(-((Cycle63.Arithmetic.lowReserve/2):ℝ)) ∧
  ∀υ : First→elementPool P→Fin 3→RayCharacter→Character,
    (∀f q i ψ,(υ f q i ψ).modulus.absNorm≤
      radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key f.1.val) ψ)
        fixedBadMask q.val (errorMovingExponent (errorIndex i))) →
    (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z amp (μ/64) (μ/8)
      firstHeight hZ reflected key P υ‖≤
      Ce*(p.control Se)^2*side*(1+|firstHeight|+height)^De*Z^(-((Cycle63.Arithmetic.lowReserve/4):ℝ))

/-- Compose the retained budget with explicit already-paid components.
The common cutoff precedes the detector; subset controls and degrees are
chosen after it and before the moving source. This is conditional on the
component receipts and makes no unconditional endpoint claim. -/
theorem literal_affine_geometry_budget_of_paid_components
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ loss mesh μ εmass τ : ℝ)
    (hloss : 0<loss)(hμ : 0<μ)(hμcap : μ≤1/128)
    (hmesh : mesh<Cycle63.Arithmetic.amplifierFloor/2)(hεmass : 0≤εmass)
    (hcomponents :
      ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
        (∀x,0≤(Ψ x).re) →
      ∀T : Finset α,∃(Sm Se : Finset (ℕ×ℕ))(Dm De : ℕ)(Cm Ce : ℝ),0≤Cm ∧ 0≤Ce ∧
        ∀ᶠZ : ℝ in atTop,GeometryAffinePaidSubsetComponents rayM Hray hHray Sbad W hW hWs
          η η₀ Q bΦ mesh μ τ Ψ T Sm Se Dm De Cm Ce Z) :
    LiteralAffineGeometryBudget (α:=α) rayM Hray hHray W hW hWs
      η η₀ Q bΦ mesh εmass τ (μ/64) := by
  obtain ⟨Cr,hCr,hretained⟩:=actual_affine_geometry_retained_budget (α:=α) rayM Hray hHray
    Sbad hbad W hW hWs loss mesh μ hloss hμ hμcap hmesh
  apply literal_affine_geometry_budget_of_subset_budgets rayM Hray hHray W hW hWs
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
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_paid_height_product
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_paid_budget_of_components
#print axioms OAI.SevenEighths.Cycle63InitialMass.literal_affine_geometry_budget_of_paid_components
