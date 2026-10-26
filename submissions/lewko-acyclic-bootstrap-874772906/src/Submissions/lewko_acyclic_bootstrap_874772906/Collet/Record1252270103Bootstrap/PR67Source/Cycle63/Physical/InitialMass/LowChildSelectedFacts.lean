import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildSelected
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondHighCoordinates
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The facts of the first level that pay the returned HIGH parts of the rows of the selected low frequency columns:
the coordinates of the rows, the first-level payment of the coordinates, the energy scale of the child, the counts of
the rows over one multiplier and the ledger. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
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
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] lowChildSelectedDecidable

set_option linter.unusedVariables false in
/-- The facts of the first level for the rows of the selected low frequency columns of the final daughters of the LOW
children of a step, for the telescope of `LowSelectedBody` up to the presentation `hpres` of the children. The
coordinates of a row `r` are those of the high chain, `X r = actualHighCoordinates reflected left₁ second (first r.1)
(label r) ...`, with the log volume `log s`, the amplifier `amp` and the frequency loss `ξ`, `reserve`. There are
reals `small₁ mfreq A₁ a₁ γ₁` of each row, the first-level data of the reserve of the pair, `κ` and `Lmax` such that:
the missing radical `X r 1` lies in `[0, Bnorm]`; the rows over one multiplier ideal `D` with `X r 1 ≤ cap` number at
most `Capre box.card Z^εA Z^cap` (the prefix count); the first-level payment
`(X0 - σ̄) + X1 + ρ X2 + δ X3 ≤ small₁ - (m₁ (1 - ρ) - δ A₁ - a₁ (5 - 6 ρ)) - γ₁` holds at every bin `δ` of the second
step, with `σ̄ = p + exponent - log N(seed₀)` the side bound of the labels without their first projector `seed₀` and
the saving `γ₁ ≥ 0`; the energy scale of the child, its row width, plus the log norm of the multiplier is at most
`X r 2 + κ`; the reserve data satisfy the bounds of the two-level ledger in the cell; the losses of the second step at
every bin are at most `Lmax`; and the margin of the two-level ledger covers `Lmax`, the count constant `εA`, half of
`εlabels` and the LOW reserve against the error of row 5. -/
def LowReturnedFactsBody [Led : Cycle63.AffineLedger] {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ) (N : ℕ) (Cs supply εv Bnorm εlabels : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (lossFloor gridSlack ampSlack Capre εA : ℝ) (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (Z : ℝ) : Prop :=
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      supply≤ s.lower → Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Lslot) →
      (∀j,w j/d≤Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.AffineLedger.q)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → Adm unit omega ξ → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B*unit →
    ∀{Label : Type}[Fintype Label],∀(reflected second : Bool)
      (first : Label→FirstSourceLabel)
      (_hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
      (_heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
      (Rfirst : Ideal O)
      (alloc : (l : Label)→actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χfirst : Label→ Character)(tfirst : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let childSrc := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χfirst l) (tfirst l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(reserve : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(childSrc l).W₁ 0=0) → (∀l,(childSrc l).W₂ 0=0) →
    (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤Z^Bnorm) →
    ∀(Tfirst p exponent : ℝ),1≤Tfirst → p≤Bnorm →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,seed₀∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val) →
    (∀l,((first l).1.1.absNorm:ℝ)≤Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤Z^Bnorm) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤Z^p) →
    (∀l,labelExp reflected Z (Real.logb Z (volume s)) (first l)≤exponent) →
    (∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (childSrc l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2)
      (box : Finset (Fin 4→ℤ)),
    (∀r∈rows,actualSecondDyad (childSrc r.1) (R r.1) (seed r.1)
      (K r.1) (Tsec r.1) Z ξ r.2∈box) →
    let label := fun r : rows=>actualSecondSupportedLabel (childSrc r.val.1)
      (R r.val.1) (seed r.val.1) (K r.val.1) (Tsec r.val.1) Z ξ r.val.2 (hU r.val r.property)
    let cell := Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀q : rows→ Chain s,
    ∀g : (r : rows)→LiveMainGeometry s (q r) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀r,(q r).C₁=(if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)) →
    (∀r,(g r).D₁=(if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)) →
    (∀r,(g r).datum.C=(label r).1.1) → (∀r,(g r).datum.D=(label r).1.2) →
    (∀r,HEq (g r).datum.inactive (label r).2.val) →
    (∀r,(q r).E₂=(if second then (label r).1.2 else (label r).1.1)) →
    (∀r,(g r).datum.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)) →
    (∀r,(g r).datum.radius=frequencyRadius (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
      (Fintype.card α) (first r.val.1)) Z ξ) →
    omega=frequencyLoss Z 32 ξ+reserve →
    ∀(χ : rows→RayFourExpansion.RayCharacter)(hP : ∀r,(q r).R₂*(q r).E₂≠0)
      (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤Z^Bmask),
    let st := fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
      ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
    let src := fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) v
    ∀(divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂),(∀r,divisorSeed r∣(q r).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      (commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.allowance Z≤pad) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      ∀D∈Ds,∀al∈(commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.active D,∀side : Bool,
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 0≤Z^L ∧
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 1≤Z^L) →
    ∀(left₁ : Bool)(u₀ : O)(unit₁ : FirstSourceLabel→O)(Tz : ℝ),
    left₁=!reflected → u₀≠0 →
    ((∀l,IsUnit (unit₁ l)) ∧ Real.logb Z (normValue u₀)≤ε) →
    let mult := fun r : rows=>firstRowMultiplier first left₁ u₀ unit₁ r.val
    (∀r,∀(W' : ℝ)(hW' : (st r).width≤W'),Presented η₀ Z (widenState (st r) W' hW') (mult r) Tz) →
    ∃(small₁ mfreq A₁ a₁ γ₁ : rows→ℝ)(κ Lmax : ℝ),
    let X := fun r : rows=>actualHighCoordinates reflected left₁ second (first r.val.1) (label r).1.1 (label r).1.2
      (label r).2.val Z Mrow (Real.logb Z (volume s)) amp ξ reserve ε
    (∀r,0≤X r 1 ∧ X r 1≤Bnorm) ∧
    (∀(cap : ℝ)(D : Ideal O),
      (((Finset.univ : Finset rows).filter (fun r=>(X r 1 ≤ cap) ∧ (Ideal.span {mult r} = D))).card:ℝ)≤
        Capre*(box.card:ℝ)*Z^εA*Z^cap) ∧
    (∀r,∀δ,Cycle63.Optimization.secondJunction≤δ → δ≤3/4 →
      (X r 0-(p+exponent-Real.logb Z (seed₀.absNorm:ℝ)))+X r 1+Cycle63.Optimization.density δ*X r 2+δ*X r 3≤
        small₁ r-(mfreq r*(1-Cycle63.Optimization.density δ)-δ*A₁ r-a₁ r*Cycle63.Optimization.amplifierCost δ)-γ₁ r) ∧
    (∀r,0≤γ₁ r) ∧
    (∀r,(st r).rowWidth+Real.logb Z ((Ideal.span {mult r}).absNorm:ℝ)≤X r 2+κ) ∧
    (∀r,1 ≤ mfreq r ∧ A₁ r≤Cycle63.Optimization.twoLevelTotalA cell ∧ a₁ r≤Cycle63.Optimization.firstAmp cell) ∧
    (∀r,∀δ,Cycle63.Optimization.secondJunction≤δ → δ≤3/4 →
      small₁ r+lossFloor+Cycle63.Optimization.density δ*κ+
        δ*(supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z+gridSlack)+Cycle63.AffineLedger.q*mesh+
        (Cycle63.AffineLedger.q-Cycle63.Optimization.firstJunction)*(unit*Cycle63.Optimization.fixedDeletion cell)+
        Cycle63.Optimization.amplifierCost δ*ampSlack≤Lmax) ∧
    Lmax-Cycle63.Optimization.highTwoMargin+εA≤
      εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+
        Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh+εlabels/2 ∧
    (∀r,((Ideal.span {mult r}).absNorm:ℝ)≤Z^(Mcap+5*Bnorm+ε+1))

set_option linter.unusedVariables false in
/-- The facts of the first level for the rows of row 5: for every character `η₀` and ideal `Q` there are constants
`Capre` and `εA` of the prefix count such that, for all large `Z`, the body holds. See `LowReturnedFactsBody`. -/
def LowReturnedFactsStmt [Led : Cycle63.AffineLedger] {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ) (N : ℕ) (Cs supply εv Bnorm εlabels : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (lossFloor gridSlack ampSlack : ℝ) : Prop :=
  ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Capre εA : ℝ, 0<Capre ∧ 0<εA ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
    LowReturnedFactsBody (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell
      N Cs
      supply εv Bnorm εlabels Adm labelExp Presented lossFloor gridSlack ampSlack Capre εA η₀ Q hQM Z

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
