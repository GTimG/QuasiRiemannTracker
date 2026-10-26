import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryMainBudget
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondColumnReindex
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondRetainedContraction
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryCostSelection
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryScalarCompensation
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryExceptionalSplit
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondLiveAllocation
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondLiveWitness
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondLabelDisintegration

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open Cycle61FinalNatural CenteredMomentEnergyState
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondBlockAggregate
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance geometryMainNormalizedPhysicalDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The actual physical weight is paid before the complete live-column sum.
The selected ideal is not made squarefree and the right row remains negated. -/
theorem actual_main_effective_normalized_columns {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ap≤x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ap≤x)
    (reflected : Bool) (t u : ℝ) :
    secondNormalizedSum reflected d
      (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑D∈(d l).block.divisors.filter Squarefree,
          ∑z∈secondLiveColumnRows (d l).block,
            (‖w l‖*((d l).K/lowerFactor N a ap)*
              normalizer (d l).C (d l).D (d l).inactive)*
            (if reflected then
              ‖normalizedColumn (withHeight (d l).input ((d l).τ ψ⁻¹)
                ((d l).input.t+2*Real.pi*(u-(-t))))
                (d l).D (d l).hD (d l).R (d l).seed D (-z.val)‖^2
             else
              ‖normalizedColumn (withHeight (d l).input ((d l).τ χ)
                ((d l).input.t+2*Real.pi*(u-t)))
                (d l).C (d l).hC (d l).R (d l).seed D z.val‖^2) := by
  let cost := fun (r : SecondRow (fun l=>(d l).block)) (D : Ideal O)=>
    if reflected then
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
        ((d r.1).input.t+2*Real.pi*(u-(-t))))
        (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2
    else
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
        ((d r.1).input.t+2*Real.pi*(u-t)))
        (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2
  have hc : ∀r D,0≤cost r D := by
    intro r D
    dsimp only [cost]
    split_ifs <;> exact sq_nonneg _
  calc
    _≤∑r∈secondLiveRows (fun l=>(d l).block),
        ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
          (‖w r.1‖*((d r.1).K/lowerFactor N a ap)*
            normalizer (d r.1).C (d r.1).D (d r.1).inactive)*cost r D := by
      unfold secondNormalizedSum
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      exact mul_le_mul_of_nonneg_right
        (actual_effective_physical_weight N a ap ha hap d w W
          hcard hlower hW₁ hW₂ r) (hc r D)
    _=_ := actual_second_column_reindex (fun l=>(d l).block) _


/-- The ordinary physical filter supplies the literal natural keep mask
for both orientations. The actual radial cutoff majorizes unit row weight. -/
theorem actual_main_ordinary_row_admission {α : Type*} [Fintype α] [DecidableEq α]
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1<Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤Z^Bmask)
    (z : O) (hz : z∈(ordinarySecondDatum d χ₀ Q m).rows) :
    let τ:=if second then d.τ (ψ⁻¹) else d.τ χ
    let row:=if second then -z else z
    let st:=retainedState Z Bmask hZ τ Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    st.radial.keep row ∧
      1≤(st.radial.profile (normValue row/st.radial.scale)).re := by
  have hk := geometry_nonexceptional_reduced_pair d.input.η χ₀ χ ψ Q hQ m hm hml hm2
    d.C d.D d.hC d.hD d.inactive d.τ d.family d.radius z hz
  have hp := actual_partRows_majorized Z Bmask hZ
    (if second then d.τ (ψ⁻¹) else d.τ χ) Q
    (d.R*(if second then d.D else d.C)) hP hPN d.input.η χ₀ m
    d.radius d.C d.D d.inactive z hz
  dsimp only
  constructor
  · rw [retainedState_keep]
    cases second
    · exact hk.1
    · exact hk.2
  · cases second
    · exact hp
    · simpa only [ite_true,normValue,Ideal.span_singleton_neg] using hp

/-- The literal moving-height coefficient has norm at most one. The
first source weight is therefore retained without a label multiplicity. -/
theorem actual_main_block_weight_norm {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) (c : ℝ) (hc : 0≤c) :
    ‖(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ q‖≤c := by
  have hs := commonLabels_supported _ _ _ q.1.val.property
  have hh := common_height_norm_le_one s.η s.t _ _ hs.1.1 hs.2.1
  unfold actualSecondBlockWeight
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  exact mul_le_of_le_one_right hc hh

section PhysicalLow
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The uniform low-column estimate pays the literal source radius and
second normalizer inside the complete column sum. Its allocation is fixed
before every retained frequency; no individual norm bound is an input. -/
theorem actual_main_low_physical_family_columns
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0<margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell)
    (Nweight : ℕ) (slotlo plainlo : ℝ) (hslot : 0<slotlo) (hplain : 0<plainlo) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤Rwidth) → 0≤mesh → (∀j,w j≤mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤21/25 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤Mrow → 0≤omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle61.Arithmetic.B*Mrow →
    ∀(reflected : Bool)(R seed : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t Mprice Aprice : ℝ)
      (sourceWeight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ),
    ∀{Label : Type*}[Fintype Label][DecidableEq Label],
    ∀firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin,
    ∀q : Label→Chain s,
    (∀l,(q l).C₁=geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val) →
    (∀l,(q l).R₁=R) → (∀l,HEq (q l).B₁ (firstIndex l).2) →
    (∀l,(q l).η₁=geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val) →
    (∀l,(q l).t₁=t) →
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀g : (l : Label)→LiveMainGeometry s (q l) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀l,(g l).reflected=reflected) →
    (∀l,(g l).C₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val.1).C) →
    (∀l,(g l).D₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val.1).D) →
    ∀(χ : Label→RayFourExpansion.RayCharacter)(hP : ∀l,(q l).R₂*(q l).E₂≠0)
      (hPN : ∀l,(((q l).R₂*(q l).E₂).absNorm:ℝ)≤Z^Bmask),
    let st := fun l=>retainedState Z Bmask hZ ((g l).datum.τ (χ l)) (internalQ Q η₀)
      ((q l).R₂*(q l).E₂) (hP l) (hPN l) (g l).datum.radius (g l).datum.C (g l).datum.D (g l).datum.inactive
    let src := fun l=>withHeight (q l).first ((g l).datum.τ (χ l)) v
    let nominal := fun l=>secondNominal Mrow Z amp omega (q l).C₁ (g l).D₁
      (g l).datum.C (g l).datum.D (g l).datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀(divisorSeed : Label→Ideal O)(hE₂ : ∀l,Supported (q l).E₂),(∀l,divisorSeed l∣(q l).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀l,∀B₂ : actualAllocations (src l).pools (q l).E₂,
      commonScalar (src l) (q l).E₂ (q l).R₂ B₂≠0 →
      (commonData (src l) (q l).E₂ (q l).R₂ B₂).toSource.allowance Z≤pad) →
    (∀l,∀B₂ : actualAllocations (src l).pools (q l).E₂,
      commonScalar (src l) (q l).E₂ (q l).R₂ B₂≠0 →
      ∀D∈Ds,∀alloc∈(commonData (src l) (q l).E₂ (q l).R₂ B₂).toSource.active D,∀second : Bool,
      finalPlain (commonData (src l) (q l).E₂ (q l).R₂ B₂) second D alloc 0≤Z^L ∧
      finalPlain (commonData (src l) (q l).E₂ (q l).R₂ B₂) second D alloc 1≤Z^L) →
    let low := fun l=>ActualLow M H hH (st l) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Label→Finset O)(weight : Label→O→ℝ),(∀l,∀z∈zs l,0≤weight l z) →
      (∀l,∀z∈zs l,(st l).radial.keep z ∧ low l z) →
      (∀l,∀z∈zs l,weight l z≤((st l).radial.profile (‖eisEmbedding z‖^2/(st l).radial.scale)).re) →
    let c := fun l=>geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin sourceWeight bs t (firstIndex l)*
      ((g l).datum.K/lowerFactor Nweight slotlo plainlo)*
      normalizer (g l).datum.C (g l).datum.D (g l).datum.inactive
    (∑l,c l*(∑D∈Ds,∑z∈zs l,weight l z*
      ‖normalizedColumn (src l) (q l).E₂ (hE₂ l) (q l).R₂ (divisorSeed l) D z‖^2))≤
      Cg*∑l,c l*((src l).toData.profileFactor*(∏j,(src l).M j)^2*
        QuadraticInitialBound.diagonalControl (st l).radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*((q l).E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(nominal l+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh)*Z^pad) := by
  obtain ⟨degree,Sp,hcolumn⟩ := actual_live_main_low_profile_column (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hcolumn η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hzslot haff
    reflected R seed bin t Mprice Aprice sourceWeight Label _ _ firstIndex q hCq hRq hBq hηq htq
    cell amp g hgref hgC hgD χ hP hPN st src nominal δwidth padding divisorSeed hE₂ hseed
    Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps low zs weight hnonneg hkeep hweight c
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  have hh := hz.2 hZ s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
    Mrow omega ξ hMmin hω hξ hMcap' hzslot haff (q l) (g l) (χ l) (hP l) (hPN l)
    (divisorSeed l) (hE₂ l) (hseed l) Ds T pad hT hDs p₀ hp₁ hp₂ (hallow l) (hcaps l)
    (zs l) (weight l) (hnonneg l) (hkeep l) (hweight l)
  have hc : 0≤c l := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg
      (geometry_low_first_weight_nonneg reflected s R seed (Z^Mrow) Z ξ
        Mprice Aprice (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin sourceWeight bs t (firstIndex l))
      (div_nonneg (g l).datum.K_pos.le (lowerFactor_pos Nweight slotlo plainlo hslot hplain).le))
      (normalizer_pos (g l).datum.C (g l).datum.D (g l).datum.hC (g l).datum.inactive).le
  apply (mul_le_mul_of_nonneg_left hh hc).trans_eq
  ring

universe u v
attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum
set_option linter.defProp false in
/-- Literal first and second geometry constructor specialization of the
physical scalar-weighted low kernel. All profile, capacity and detector
gates remain those of the actual retained state. -/
def actual_geometry_main_low_physical_columns {α : Type u} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0<margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell)
    (Nweight : ℕ) (slotlo plainlo : ℝ) (hslot : 0<slotlo) (hplain : 0<plainlo) :=
  let hbase := actual_main_low_physical_family_columns.{u,v} (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell Nweight slotlo plainlo hslot hplain
  let degree := Classical.choose hbase
  let hdegree := Classical.choose_spec hbase
  let Sp := Classical.choose hdegree
  let hcolumn := Classical.choose_spec hdegree
  (degree,Sp,fun η₀ Q hQM hQ0 hQt hQ72=>
    let hc := hcolumn η₀ Q hQM hQ0 hQt hQ72
    let Cg := Classical.choose hc
    let hg := Classical.choose_spec hc
    (Cg,PLift.up (And.intro hg.1 (Filter.Eventually.mono hg.2 (fun Z hz=>
      And.intro hz.1
      (fun (hZ : 1<Z) (s : Input α) (θ : α→RayQuotient.Characters M H)
        (w σ freq : α→ℝ) (heightV height mesh aLow : ℝ) (i : ℕ)
        hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
        hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh (Mrow reserve ξ : ℝ) hMmin hω hξ hMcap'
        hzslot haff (reflected : Bool) (R seed : Ideal O) (bin : ℤ×(Fin 5→ℤ))
        (t Mprice Aprice : ℝ)
        (sourceWeight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
        {Label : Type v} [Fintype Label] [DecidableEq Label]
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
        let cell := Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp := Mrow*Cycle61.Arithmetic.amp cell
        fun (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
        (n : (l : Label)→GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l))=>
        let datum := fun l=>geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l)
        let firstChild := fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        fun (second : Label→Bool)
          (B₂ : (l : Label)→actualAllocations (firstChild l).pools
            (if second l then (datum l).D else (datum l).C))
          (r : (l : Label)→secondLiveRows (fun _:Unit=>(datum l).block))
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hf₂ : ∀l,frozenCoefficient (B₂ l).val
            (if second l then (datum l).D else (datum l).C) (datum l).R
            (firstChild l).ν (firstChild l).W (firstChild l).P≠0)=>
        let q : Label→Chain s := fun l=>geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l)
        let g : (l : Label)→LiveMainGeometry s (q l) Z Mrow amp
          (frequencyLoss Z 32 ξ+reserve) ξ bs (Fintype.card α) := fun l=>geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        let hfields := fun l=>actual_geometry_low_admission_fields reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        hz.2 hZ s θ w σ freq heightV height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
          hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow (frequencyLoss Z 32 ξ+reserve) ξ
          hMmin hω hξ hMcap' hzslot haff reflected R seed bin t Mprice Aprice sourceWeight firstIndex q
          (fun l=>(hfields l).1) (fun l=>(hfields l).2.1) (fun l=>(hfields l).2.2.1)
          (fun l=>(hfields l).2.2.2.1) (fun l=>(hfields l).2.2.2.2.1) g
          (fun l=>(hfields l).2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.2.1)))))))

end PhysicalLow

/-- Original zero blocks and zero source coefficients are removed before
any decomposition into ordinary and exceptional rows. -/
theorem actual_original_nonzero_block_sum {Label : Type*} [Fintype Label]
    (d : Label→SecondBlockSource) (w : Label→ℂ) (live : Label→Prop)
    (hw : ∀l,¬live l→w l=0) (W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(d l).value W)=
      ∑l : Finset.univ.filter (fun l=>live l ∧ (d l).value W≠0),
        w l.val*(d l.val).value W := by
  classical
  rw [Finset.sum_coe_sort (Finset.univ.filter (fun l=>live l ∧ (d l).value W≠0))
    (fun l=>w l*(d l).value W),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  split_ifs with h
  · rfl
  · by_cases hlive : live l
    · have hz : (d l).value W=0 := by
        by_contra hn
        exact h ⟨hlive,hn⟩
      rw [hz,mul_zero]
    · rw [hw l hlive,zero_mul]

section Literal
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance geometryMainNormalizedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))

/-- Every actual first column/allocation and every original second label and
four-coordinate dyadic block remain in the normalized family. -/
abbrev GeometryMainSecondIndex :=
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) ×
  GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key q

variable (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)

/-- Only the inducing branch is removed; all actual second dyads and rows
remain those of the original retained decomposition. -/
def geometryMainOrdinaryDatum (χ : RayCharacter) (Q : Ideal O) (m : O)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    SecondInputDatum α :=
  ordinarySecondDatum
    (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.1 hz₁ hz₂ j.2) χ Q m

/-- The physical first allocation weight is retained inside every literal
second source weight, including canceled and unsupported blocks. -/
def geometryMainSecondWeight (Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) : ℂ :=
  (geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.1:ℂ)*
  actualSecondBlockWeight
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t j.1)
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val)
    j.1.1.val.2.1.val
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val))
    (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val)) Z ξ j.2

/-- Selection takes place on the unrestricted original physical block,
before the ordinary split or any positive column majorant. -/
def geometryMainNonzeroBlocks : Finset
    (GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :=
  Finset.univ.filter (fun j=>
    frozenCoefficient j.1.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val) R s.ν s.W s.P≠0 ∧
    (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.1 hz₁ hz₂ j.2).block.value ballProfile≠0)

set_option linter.defProp false in
/-- Exact original-block selection on the literal main geometry family. -/
def actual_geometry_main_nonzero_sum (Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ) :=
  let datum := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.1 hz₁ hz₂ j.2).block
  let w := geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight
  let live := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    frozenCoefficient j.1.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val) R s.ν s.W s.P≠0
  actual_original_nonzero_block_sum datum w live
    (fun j hf=>by
      simp only [w,geometryMainSecondWeight,geometryLowFirstWeight,geometryAllocationWeight,
        live] at hf ⊢
      simp only [hf,ite_false,zero_div,Complex.ofReal_zero,zero_mul]) ballProfile

/-- The full original block supplies a live second common allocation
once, independently of all subsequent row and shifted-height choices. -/
theorem actual_geometry_main_live_common_allocation
    (j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (second : Bool) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.val.1 hz₁ hz₂ j.val.2
    ∃B₂ : actualAllocations d.input.pools (if second then d.D else d.C),
      frozenCoefficient B₂.val (if second then d.D else d.C) d.R
        d.input.ν d.input.W d.input.P≠0 := by
  intro d
  have hs := actual_geometry_low_column_seed reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    j.val.1 hz₁ hz₂ j.val.2
  have hseed : d.seed∣(if second then d.D else d.C) := by
    cases second
    · exact hs.1
    · exact hs.2
  exact actual_second_input_live_allocation d second hseed ballProfile
    (Finset.mem_filter.mp j.property).2.2

/-- The original nonzero block supplies both a genuine row witness and
a valid canonical inactive partition before the ordinary restriction. -/
theorem actual_geometry_main_original_admission
    (j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.val.1 hz₁ hz₂ j.val.2
    (secondLiveRows (fun _:Unit=>d.block)).Nonempty ∧
      d.inactive∈inactiveSubsets d.C d.D := by
  intro d
  have hn : d.block.value ballProfile≠0 := (Finset.mem_filter.mp j.property).2.2
  exact ⟨actual_second_nonzero_live_row d.block ballProfile hn,
    second_block_nonzero_inactive d.block ballProfile hn⟩

omit [DecidableEq α] in
/-- Original first-source weights bound the literal second block weights;
the radius and second normalizer are paid by the physical low kernel. -/
theorem actual_geometry_main_block_weight_norm
    (Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    ‖geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j‖≤
      geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.1 := by
  exact actual_main_block_weight_norm _ _ _ _ _ Z ξ j.2 _
    (geometry_low_first_weight_nonneg reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.1)

set_option linter.defProp false in
/-- Literal normalized physical columns on original nonzero blocks.
Ordinary blocks may vanish; no positivity enlargement drops those blocks. -/
def actual_geometry_main_normalized_columns
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (Mprice Aprice slotlo plainlo : ℝ) (hslot : 0<slotlo) (hplain : 0<plainlo)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (hcard : Fintype.card α≤N) (hlower : slotlo≤s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→plainlo≤x) (hW₂ : ∀x,s.W₂ x≠0→plainlo≤x)
    (W : 𝓢(ℝ,ℂ)) (second : Bool) (t₀ u : ℝ) :=
  let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
    geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
  let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
    geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val
  actual_main_effective_normalized_columns N slotlo plainlo hslot hplain datum w W hcard
    (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂) second t₀ u

end Literal

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_effective_normalized_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_normalized_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_ordinary_row_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_physical_family_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_low_physical_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_nonzero_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_live_common_allocation

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_original_nonzero_block_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_block_weight_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_original_admission
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_block_weight_norm
