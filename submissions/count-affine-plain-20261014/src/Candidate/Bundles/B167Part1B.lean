/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B090
import Candidate.Bundles.B108
import Candidate.Bundles.B109
import Candidate.Bundles.B135
import Candidate.Bundles.B139
import Candidate.Bundles.B140
import Candidate.Bundles.B149
import Candidate.Bundles.B165
import Candidate.Bundles.B166
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

import Candidate.Bundles.B167Part1A
/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowSelected; sha256 be241fbb522f224b5369ce0bac86646f5ea5951f8b16ac38076337fcfb4385e4 -/
section
                                                            
                                                         
                                                       
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle61FinalNatural Cycle61Moment.LowBranch
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
open Cycle61Moment
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

local notation "O" => HeckeFamily.O
attribute [local instance] geometryMainLowSelectedDecidable

private theorem low_scalar_product_transport
    (coef base diagonal control height norm shell power padding : ℝ)
    (coef' diagonal' norm' power' : ℝ)
    (hc : coef=coef')(hd : diagonal=diagonal')(hn : norm=norm')
    (hp : power*padding=power') :
    coef*(base*diagonal*control*height*norm*shell*power*padding)=
      base*diagonal'*control*height*shell*coef'*norm'*power' := by
  rw [hc,hd,hn]
  calc
    _=(base*diagonal'*control*height*shell*coef'*norm')*(power*padding) := by ring
    _=_ := congrArg (fun x : ℝ=>(base*diagonal'*control*height*shell*coef'*norm')*x) hp

set_option maxHeartbeats 200000 in
/-- Complete selected low frequency columns are paid by the actual finite supported label budget. -/
theorem actual_selected_low_paid_columns {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      supply≤ s.lower → Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤167/200 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀{Label : Type}[Fintype Label],∀(reflected second : Bool)
      (first : Label→ FirstSourceLabel)
      (hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
      (heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
      (Rfirst : Ideal O)
      (alloc : (l : Label)→ actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χfirst : Label→ Character)(tfirst : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let childSrc := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χfirst l) (tfirst l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(reserve : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(childSrc l).W₁ 0=0) → (∀l,(childSrc l).W₂ 0=0) →
    (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤ Z^Bnorm) →
    ∀(Tfirst p exponent : ℝ),1≤ Tfirst → p≤ Bnorm →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,((first l).1.1.absNorm:ℝ)≤ Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤ Z^Bnorm) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤ Z^p) →
    (∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)≤ exponent) →
    (∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (childSrc l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
      (box : Finset (Fin 4→ℤ)),
    (∀r∈rows,actualSecondDyad (childSrc r.1) (R r.1) (seed r.1)
      (K r.1) (Tsec r.1) Z ξ r.2∈box) →
    let label := fun r : rows=>actualSecondSupportedLabel (childSrc r.val.1)
      (R r.val.1) (seed r.val.1) (K r.val.1) (Tsec r.val.1) Z ξ r.val.2 (hU r.val r.property)
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀q : rows→ Chain s,
    ∀g : (r : rows)→ LiveMainGeometry s (q r) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀r,(q r).C₁=(if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)) →
    (∀r,(g r).D₁=(if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)) →
    (∀r,(g r).datum.C=(label r).1.1) → (∀r,(g r).datum.D=(label r).1.2) →
    (∀r,HEq (g r).datum.inactive (label r).2.val) →
    (∀r,(q r).E₂=(if second then (label r).1.2 else (label r).1.1)) →
    (∀r,(g r).datum.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)) →
    omega=frequencyLoss Z 32 ξ+reserve →
    ∀(χ : rows→ RayFourExpansion.RayCharacter)(hP : ∀r,(q r).R₂*(q r).E₂≠0)
      (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
      ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
    let src := fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) v
    ∀(divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂),(∀r,divisorSeed r∣(q r).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤ T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      (commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.allowance Z≤ pad) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      ∀D∈Ds,∀al∈(commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.active D,∀side : Bool,
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 0≤ Z^L ∧
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 1≤ Z^L) →
    let low := fun r=>ActualLow M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : rows→ Finset O)(weight : rows→ O→ℝ),(∀r,∀z∈zs r,0≤ weight r z) →
      (∀r,∀z∈zs r,(st r).radial.keep z ∧ low r z) →
      (∀r,∀z∈zs r,weight r z≤((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re) →
    ∀(mass : Label→ℝ)(physical loss : ℝ),0≤ physical → (∀l,0≤ mass l) →
      (∀l,mass l≤ physical*Z^loss) →
    let c := fun r=>mass r.val.1/volume (childSrc r.val.1)*
      (g r).datum.K*normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
    let error := εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
      (2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad
    (∑r,c r*(∑D∈Ds,∑z∈zs r,weight r z*
      ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2))≤
      Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(2*T)^(3*εshell)*(box.card:ℝ)*physical*
        Z^(loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ) := by
  let hbase := actual_low_fixed_profile_columns (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
  let degree := Classical.choose hbase
  let hdegree := Classical.choose_spec hbase
  let Sp := Classical.choose hdegree
  let hcolumn := Classical.choose_spec hdegree
  let hpbase := eventual_actual_selected_low_second_paid
    N supply εv Bnorm εlabels hsupply hev hBnorm hel
  let K₀ := Classical.choose hpbase
  let hpspec := Classical.choose_spec hpbase
  have hK₀ : 0< K₀ := hpspec.1
  let hpaid := hpspec.2
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hcbase := hcolumn η₀ Q hQM hQ0 hQt hQ72
  let C := Classical.choose hcbase
  let hcspec := Classical.choose_spec hcbase
  have hC : 0< C := hcspec.1
  let hbound := hcspec.2
  refine ⟨C*K₀,mul_pos hC hK₀,?_⟩
  filter_upwards [hbound,hpaid] with Z hz hzpaid
  refine ⟨hzpaid.1,?_⟩
  intro hZ s θ w σ freq v height mesh aLow i hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ
    hMmin hω hξ hMcap' hzslot haff Label _ reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    childSrc R seed K Tsec reserve hseed hw₁ hw₂ hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0
    hinj hfirstseed hfirstnorm hrad hgeom hfirstshell rows hU box hbox label cell amp q g
    hC₁ hD₁ hC₂ hD₂ hU₂ hEeq hKeq hωeq χ hP hPN st src divisorSeed hE₂ hdivisor Ds T pad hT hDs
    p₀ hp₁ hp₂ hallow hcaps low zs weight hnonneg hkeep hweight mass physical loss hphysical hmass0 hmasscap c error
  have hZ0 : 0< Z := zero_lt_one.trans hZ
  let pay := fun r : rows=>Z^(-amp)*
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
    (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
      ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
    Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
      (label r).1.1 (label r).1.2 (label r).2.val+amp+error)
  let fixed := (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*(2*T)^(3*εshell)
  have hfixed : 0≤ fixed := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg ballProfile
    dsimp only [fixed]; positivity
  have hpoint (r : rows) : c r*(∑D∈Ds,∑z∈zs r,weight r z*
      ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)≤
      C*fixed*(physical*Z^(loss+amp))*pay r := by
    have hh := hz.2 hZ s θ w σ freq v height mesh aLow i hcard hmass hm hsη hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ
      hMmin hω hξ hMcap' hzslot haff (q r) (g r) (χ r) (hP r) (hPN r)
      (divisorSeed r) (hE₂ r) (hdivisor r) Ds T pad hT hDs p₀ hp₁ hp₂ (hallow r) (hcaps r)
      (zs r) (weight r) (hnonneg r) (hkeep r) (hweight r)
    have hc : 0≤ c r := by
      dsimp only [c]
      exact mul_nonneg (mul_nonneg (div_nonneg (hmass0 _) (CenteredMomentAmplificationChildInput.volume_pos _).le)
        (g r).datum.K_pos.le) (normalizer_pos _ _ (g r).datum.hC _).le
    have h := mul_le_mul_of_nonneg_left hh hc
    have hcancel : Z^amp*Z^(-amp)=(1:ℝ) := by rw [←Real.rpow_add hZ0]; simp
    have hscale : mass r.val.1*Z^amp≤ physical*Z^(loss+amp) := by
      simpa only [Real.rpow_add hZ0,mul_assoc] using mul_le_mul_of_nonneg_right (hmasscap r.val.1)
        (Real.rpow_nonneg hZ0.le amp)
    have hpay0 : 0≤ pay r := by
      dsimp only [pay]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ0.le _)
        (div_nonneg (first_main_radius_pos _ _ _ _ _ _ _ hZ0 _).le (CenteredMomentAmplificationChildInput.volume_pos _).le))
        (mul_nonneg (normalizer_pos _ _ ((hC₂ r) ▸ (g r).datum.hC) _).le
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (Real.rpow_nonneg hZ0.le _)
    have heq' : c r*(C*(2*b^2*Cs^(4*N))*
      QuadraticInitialBound.diagonalControl (st r).radial.profile*(p₀.control Sp)^2*
      (1+|v|+height)^degree*((q r).E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
      Z^(secondNominal Mrow Z amp omega (q r).C₁ (g r).D₁ (g r).datum.C (g r).datum.D
        (g r).datum.inactive+(εwidth*Mrow+ξ/2)+amp-Mrow*(1/3750000)+εold+
        2*ε*d*(Fintype.card α:ℝ)+(2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh)*Z^pad)=
      C*fixed*(mass r.val.1*Z^amp)*pay r := by
      have hpayeq : (mass r.val.1*Z^amp)*pay r=
          mass r.val.1*
          (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
          (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
            ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
          Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
            (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
            (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
            (label r).1.1 (label r).1.2 (label r).2.val+amp+error) := by
        dsimp only [pay]
        calc
          _=(Z^amp*Z^(-amp))*(mass r.val.1*
              (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
              (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
                ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
              Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
                (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
                (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
                (label r).1.1 (label r).1.2 (label r).2.val+amp+error)) := by ring
          _=_ := by rw [hcancel]; ring
      have hnom : secondNominal Mrow Z amp omega (q r).C₁ (g r).D₁
          (g r).datum.C (g r).datum.D (g r).datum.inactive=
          secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val := by
        have hback:=actual_low_label_nominal Mrow Z amp omega (q r).C₁ (g r).D₁
          (g r).datum.C (g r).datum.D (g r).datum.inactive (label r) (hC₂ r) (hD₂ r) (hU₂ r)
        have hfront:=congrArg₂ (fun C₁ D₁ : Ideal O=>
          secondNominal Mrow Z amp omega C₁ D₁ (label r).1.1 (label r).1.2 (label r).2.val)
          (hC₁ r) (hD₁ r)
        have homega:=congrArg (fun omega : ℝ=>secondNominal Mrow Z amp omega
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val) hωeq
        exact hback.trans (hfront.trans homega)
      have hnormal := actual_low_label_normalizer _ _ _ _ (hC₂ r) (hD₂ r) (hU₂ r)
      have hnorm := congrArg (fun I : Ideal O=>(I.absNorm:ℝ)^(εshell-1)) (hEeq r)
      have hrad : (st r).radial.profile=ballProfile := rfl
      have hexp : secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
        (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
        (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
        (label r).1.1 (label r).1.2 (label r).2.val+(εwidth*Mrow+ξ/2)+amp-Mrow*(1/3750000)+εold+
        2*ε*d*(Fintype.card α:ℝ)+(2*Cycle61.Arithmetic.q0/9)*
        (omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad=
        secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
        (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
        (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
        (label r).1.1 (label r).1.2 (label r).2.val+amp+
        (εwidth*Mrow+ξ/2-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
        (2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh+pad) := by ring
      have hpower := (Real.rpow_add hZ0
        (secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
          (label r).1.1 (label r).1.2 (label r).2.val+(εwidth*Mrow+ξ/2)+amp-Mrow*(1/3750000)+εold+
          2*ε*d*(Fintype.card α:ℝ)+(2*Cycle61.Arithmetic.q0/9)*
          (omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh) pad).symm
      have hpowerExact := hpower.trans (congrArg (fun exponent : ℝ=>Z^exponent) hexp)
      have hnomPower:=congrArg (fun nominal : ℝ=>Z^(nominal+(εwidth*Mrow+ξ/2)+amp-
        Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
        (2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh)) hnom
      have hpowerSource: Z^(secondNominal Mrow Z amp omega (q r).C₁ (g r).D₁
          (g r).datum.C (g r).datum.D (g r).datum.inactive+(εwidth*Mrow+ξ/2)+amp-
          Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh)*Z^pad=
          Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
            (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
            (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
            (label r).1.1 (label r).1.2 (label r).2.val+amp+error) :=
        (congrArg (fun x : ℝ=>x*Z^pad) hnomPower).trans hpowerExact
      have hcoef : c r=mass r.val.1/volume (childSrc r.val.1)*
          firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)*
          normalizer (label r).1.1 (label r).1.2 (label r).2.val :=
        congrArg₂ (fun K normal : ℝ=>mass r.val.1/volume (childSrc r.val.1)*K*normal)
          (hKeq r) hnormal
      have hdiag:=congrArg QuadraticInitialBound.diagonalControl hrad
      have htrans:=low_scalar_product_transport (c r) (C*(2*b^2*Cs^(4*N)))
        (QuadraticInitialBound.diagonalControl (st r).radial.profile) ((p₀.control Sp)^2)
        ((1+|v|+height)^degree) (((q r).E₂.absNorm:ℝ)^(εshell-1)) ((2*T)^(3*εshell))
        (Z^(secondNominal Mrow Z amp omega (q r).C₁ (g r).D₁ (g r).datum.C (g r).datum.D
          (g r).datum.inactive+(εwidth*Mrow+ξ/2)+amp-Mrow*(1/3750000)+εold+
          2*ε*d*(Fintype.card α:ℝ)+(2*Cycle61.Arithmetic.q0/9)*(omega+εpad*Mrow)+Cycle61.Arithmetic.q0*mesh))
        (Z^pad) _ _ _ _ hcoef hdiag hnorm hpowerSource
      calc
        _=_ := htrans
        _=C*fixed*(mass r.val.1*
          (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
          (normalizer (label r).1.1 (label r).1.2 (label r).2.val*
            ((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)^(εshell-1))*
          Z^(secondNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
            (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
            (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
            (label r).1.1 (label r).1.2 (label r).2.val+amp+error)) := by dsimp only [fixed]; ring
        _=_ := (congrArg (fun x : ℝ=>C*fixed*x) hpayeq).symm.trans (by ring)
    have hfull := h.trans_eq heq'
    exact hfull.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (mul_nonneg hC.le hfixed)) hpay0)
  have hpays := hzpaid.2 s hcard hsupply' reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    R seed K Tsec ξ Mrow amp reserve error εshell hseed hw₁ hw₂ heshell.le hsource
    Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hfirstshell
    rows hU box hbox
  calc
    _≤∑r,C*fixed*(physical*Z^(loss+amp))*pay r := Finset.sum_le_sum (fun r _=>hpoint r)
    _=(C*fixed*(physical*Z^(loss+amp)))*(∑r,pay r) := by rw [Finset.mul_sum]
    _≤(C*fixed*(physical*Z^(loss+amp)))*
      ((box.card:ℝ)*(K₀*Z^(p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ))) :=
      mul_le_mul_of_nonneg_left hpays (by positivity)
    _=_ := by
      have hzproduct:=Real.rpow_add hZ0 (loss+amp) (p+exponent+error+εv+Bnorm*εshell+εlabels)
      have headd : (loss+amp)+(p+exponent+error+εv+Bnorm*εshell+εlabels)=
          loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels := by ring
      rw [headd] at hzproduct
      have hscalar:=congrArg (fun x : ℝ=>
        C*fixed*(box.card:ℝ)*physical*K₀*x/(seed₀.absNorm:ℝ)) hzproduct
      calc
        _=C*fixed*(box.card:ℝ)*physical*K₀*
            (Z^(loss+amp)*Z^(p+exponent+error+εv+Bnorm*εshell+εlabels))/(seed₀.absNorm:ℝ) := by ring
        _=C*fixed*(box.card:ℝ)*physical*K₀*
            Z^(loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ) := hscalar.symm
        _=_ := by dsimp only [fixed]; ring


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_selected_low_paid_columns

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowSelected -/
