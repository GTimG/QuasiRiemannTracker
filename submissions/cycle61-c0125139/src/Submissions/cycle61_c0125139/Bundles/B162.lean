/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B154
import Submissions.cycle61_c0125139.Bundles.B156
import Submissions.cycle61_c0125139.Bundles.B161
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputReindex

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalizedPayment; sha256 3c04e815e7ba570a1d3f8f17f5026bb05332240b0bd80abd392902d76afe0199 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                                   
                                                        
                                                              
                                                             

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondRetainedRows
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentEligibleEnergy CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAmplificationErrorEnergy CenteredMomentRestrictedEnergy
open CenteredMomentAllocatedRayDictionary CenteredMomentSlotRatios
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Cycle61FinalNatural Cycle61Moment Cycle61FinalError Cycle61FinalErrorCapacity
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonAllocationSum
open CenteredMomentPrimeElements CenteredMomentRankinRadical
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
local notation "O" => HeckeFamily.O
local instance errorNormalizedPaymentDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _
local instance errorNormalizedPaymentSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Full stored pools survive both genuine restrictions, including entries
whose profile coefficient vanishes. -/
theorem actual_error_extracted_pool_cap {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(q : Chain s)(Y : ℝ)
    (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Y) :
    ∀j I,I∈q.extracted.pools j→(I.absNorm:ℝ)≤ Y :=
  actual_child_pool_cap q.first ((Ideal.span {q.p})^q.k) (q.R₁*q.C₁) q.Bp q.υ q.t₂ Y
    (actual_child_pool_cap s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ Y hpool)

/-- Original cardinality bounds the complete finite extracted source pool;
all stored coefficients remain in the product dictionary. -/
theorem actual_error_extracted_finite_pool_cap {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(q : Chain s)(N : ℕ)(Z U : ℝ)
    (hN : Fintype.card α≤ N)(hZ : 1≤ Z)(hU : 0≤ U)
    (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U) :
    ∀I∈finiteColumns (Fintype.piFinset q.extracted.pools),(I.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) := by
  have hfirst : Fintype.card (liveIndices q.B₁.val)≤ N := by
    apply le_trans _ hN
    simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices q.B₁.val)
  have hextracted : Fintype.card (liveIndices q.Bp.val)≤ N := by
    apply le_trans _ hfirst
    simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices q.Bp.val)
  exact actual_finite_pool_cap q.extracted N Z U hextracted hZ hU
    (actual_error_extracted_pool_cap s q (Z^U) hpool)

/-- A literal extracted physical block inherits the cap through its exact
pool identity; row restrictions and zero coefficients do not change it. -/
theorem actual_error_extracted_projector_cap {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(q : Chain s)(N : ℕ)(Z U : ℝ)
    (hN : Fintype.card α≤ N)(hZ : 1≤ Z)(hU : 0≤ U)
    (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U)
    (b : SecondBlockSource)(hb : b.pool=finiteColumns (Fintype.piFinset q.extracted.pools))
    (L : Ideal O)(hL : L∈b.divisors) :
    L≠0 ∧ (L.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) := by
  apply second_block_projector_norm b _ _ L hL
  rw [hb]
  exact actual_error_extracted_finite_pool_cap s q N Z U hN hZ hU hpool

/-- The exact normalized column coefficient is the extracted scalar paid
by the dependent full-label theorem. Local error cost remains on the
column side; this identity uses the restored removal/moving power. -/
theorem actual_error_normalized_scalar_identity
    (reflected second : Bool)(l v : FirstSourceLabel)(Z M a δ reserve error εcommon V Vextract lf weight : ℝ)
    (P : Finset (Ideal O))(p : O)(i : Fin 3)(hZ : 0< Z) :
    let k := errorIndex i+1
    let K := firstErrorTailRadius reflected l Z M V a δ reserve p k
    let nominal := errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) v.1.1 v.1.2 v.2.val
    ((56/(P.card:ℝ))*weight*(K/lf)*normalizer v.1.1 v.1.2 v.2.val*16*(errorIndex i+2:ℝ)/Vextract)*
      Z^(errorRemoval p Z k-errorMoving p Z k)*
      ((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1)*
      Z^(nominal+error-M*branchReserve k)=
      ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)*
        extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon V Vextract p k := by
  intro k K nominal
  change _= ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)*
    ((K/Vextract)*(normalizer v.1.1 v.1.2 v.2.val*
      ((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
      Z^(nominal+(error-M*branchReserve k)+errorRemoval p Z k-errorMoving p Z k))
  rw [show nominal+(error-M*branchReserve k)+errorRemoval p Z k-errorMoving p Z k=
    (errorRemoval p Z k-errorMoving p Z k)+(nominal+error-M*branchReserve k) by ring,
    Real.rpow_add hZ]
  ring

/-- Both genuine child restrictions pay the four original mass powers;
the fixed ball profile and shared shell scale are independent of labels. -/
theorem actual_error_fixed_shell_factor {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs bp : ℝ)(hCs : 1≤ Cs)(hbp : 1≤ bp)
    (s : Input α)(hcard : Fintype.card α≤ N)(hM : ∀j,s.M j≤ Cs)
    (hb₁ : s.b₁=bp)(hb₂ : s.b₂=bp)(q : Chain s)(η : Character)(v Z T L₂ εshell : ℝ)
    (hZ : 0< Z)(hT : 0≤ T)(hscale : T≤ Z^L₂)(he : 0≤εshell) :
    let src := withHeight q.extracted η v
    src.toData.profileFactor*(∏j,src.M j)^2*
      QuadraticInitialBound.diagonalControl ballProfile*(2*T)^(3*εshell)≤
      (2*bp^2*Cs^(4*N)*(1+QuadraticInitialBound.diagonalControl ballProfile)*(2:ℝ)^(3*εshell))*
        Z^(3*L₂*εshell) := by
  intro src
  have hm := actual_error_fixed_source_factor N Cs bp hCs hbp s hcard hM hb₁ hb₂ q η v
  have hd := QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hs : (2*T)^(3*εshell)≤(2:ℝ)^(3*εshell)*Z^(3*L₂*εshell) := by
    calc
      _≤(2*Z^L₂)^(3*εshell) := Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_left hscale (by norm_num)) (by positivity)
      _=_ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le]
        congr 1
        ring
  calc
    _≤(2*bp^2*Cs^(4*N))*(1+QuadraticInitialBound.diagonalControl ballProfile)*(2*T)^(3*εshell) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      exact mul_le_mul hm (by linarith) hd (by positivity)
    _≤(2*bp^2*Cs^(4*N))*(1+QuadraticInitialBound.diagonalControl ballProfile)*
      ((2:ℝ)^(3*εshell)*Z^(3*L₂*εshell)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _=_ := by ring

/-- Genuine paid columns over the complete supported second-projector
sets. The union of their shells costs one small power before all live
labels, while the source mass and fixed profile cost remain uniform. -/
theorem actual_paid_error_complete_projector_family {α : Type*}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hL : 0≤ L) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hloss : 0< loss) (hmargin : 0< margin) (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (ηseed : Character) (bs J εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤ window) (hpad : 0< pad) (heshell : 0<εshell)
    (hbs : 1≤ bs) (hJ : 0< J) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1≤ Cs)(hL₂ : 0≤ L₂)(heproj : 0<εproj) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(_hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=bp → s.b₂=bp →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^L) →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀{Label : Type*}[Fintype Label],∀q : Label→ Chain s,
    (∀j,(q j).k=1 ∨ (q j).k=6 ∨ (q j).k=7) →
    (∀j,3*amp/4≤ Real.logb Z (normValue (q j).p)) →
    ∀g : (j : Label)→ Geometry s (q j) Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : Label→ RayFourExpansion.RayCharacter)(_hP : ∀j,(q j).R₂*(q j).E₂≠0)
      (_hPN : ∀j,(((q j).R₂*(q j).E₂).absNorm:ℝ)≤ Z^Bmask),
    let src := fun j=>withHeight (q j).extracted ((g j).τ (χ j)) v
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(seed : Label→ Ideal O)(hE₂ : ∀j,Supported (q j).E₂),(∀j,seed j∣(q j).E₂) →
    ∀Ds : Label→ Finset (Ideal O),(∀j D,D∈Ds j→ Squarefree D) →
      (∀j D,D∈Ds j→(D.absNorm:ℝ)≤ Z^L₂) →
    ∀(P : Finset (Ideal O))(weight : Label→ℝ),(∀j,0≤ weight j) →
    let coefficient := fun j=>(56/(P.card:ℝ))*weight j*16*((q j).k+1:ℝ)/volume (src j)
    let rows := fun j=>partRows false (q j).υ (χ j) (internalQ Q η₀)
      fixedBadMask (g j).C (g j).D (g j).U (g j).radius
    (∑j,coefficient j*localErrorCost (q j).p ((q j).k-1)*
      (∑D∈Ds j,∑z∈rows j,‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2))≤
      Cg*(p.control Sp)^2*(1+|v|+height)^degree*Z^(εproj+3*L₂*εshell)*
        ∑j,coefficient j*Z^(errorRemoval (q j).p Z (q j).k-errorMoving (q j).p Z (q j).k)*
          ((q j).E₂.absNorm:ℝ)^(εshell-1)*
          Z^((g j).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (q j).k+
            εold+loss*(Fintype.card α:ℝ)+(omega+εpad*Mrow)/6+(3/4)*mesh+pad) := by
  obtain ⟨degree,Sp,hcolumn⟩ := actual_paid_error_column_family_after_threshold (α:=α) M H hH
    W A B ap bp Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp
    hBmask hL hMcap hεold hloss hmargin hbeta ηseed bs J εwidth εpad Mmin
    window pad εshell hwindow hpad heshell hbs hJ hew hep hmin
  obtain ⟨Csh,hCsh,hshell⟩ := shared_projector_shell_subpower L₂ εproj hL₂ heproj
  let F := 2*bp^2*Cs^(4*N)*(1+QuadraticInitialBound.diagonalControl ballProfile)*(2:ℝ)^(3*εshell)
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hF : 0< F := by dsimp only [F]; positivity
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hcolumn η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg*F*Csh,by positivity,?_⟩
  filter_upwards [hbound,hshell] with Z hz hzs
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh hcard hM hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm
    hσlo hσhi hheight hfreq hOrig hwin Mrow omega ξ hMmin hω hξ hMcap' hslot haff
    cell amp Label _ q hk hprime g χ hP hPN src p hp₁ hp₂ seed hE₂ hseed Ds hDs hcap
    P weight hwgt coefficient rows
  have hzpos : 0< Z := zero_lt_one.trans hZ
  let H := (p.control Sp)^2*(1+|v|+height)^degree
  let scalar := fun j=>coefficient j*
    Z^(errorRemoval (q j).p Z (q j).k-errorMoving (q j).p Z (q j).k)*
    ((q j).E₂.absNorm:ℝ)^(εshell-1)*
    Z^((g j).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (q j).k+
      εold+loss*(Fintype.card α:ℝ)+(omega+εpad*Mrow)/6+(3/4)*mesh+pad)
  have hcoef (j : Label) : 0≤ coefficient j := by
    dsimp only [coefficient]
    have hv := volume_pos (src j)
    have hwj := hwgt j
    have hpc := Nat.cast_nonneg (α:=ℝ) P.card
    positivity
  have hscalar (j : Label) : 0≤ scalar j := by
    have hc := hcoef j
    dsimp only [scalar]
    positivity
  have hH : 0≤ H := by dsimp only [H]; positivity
  have hsum : 0≤∑j,scalar j := Finset.sum_nonneg (fun j _=>hscalar j)
  let shells := selectedShells (sharedProjectors Ds)
  have hpay (n : ℤ)(hn : n∈shells) :
      (∑j,coefficient j*localErrorCost (q j).p ((q j).k-1)*
        (∑D∈sharedLabelProjectorShell Ds j n,∑z∈rows j,
          ‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2))≤
        Cg*F*H*Z^(3*L₂*εshell)*∑j,scalar j := by
    have hscale := shared_projector_shell_scale Ds Z L₂ hcap n hn
    have hgates (j : Label)(D : Ideal O)(hD : D∈sharedLabelProjectorShell Ds j n) :=
      (shared_label_projector_shell_gates Ds j n D hD).2
    have hpaid := hz.2 hZ s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂
      hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow omega ξ hMmin hω hξ
      hMcap' hslot haff q hk hprime g χ hP hPN p hp₁ hp₂ seed hE₂ hseed
      (fun j=>sharedLabelProjectorShell Ds j n) (fun _=>dyadicScale n) (fun _=>hscale.1)
      hgates P weight hwgt
    apply hpaid.trans
    rw [Finset.mul_sum]
    have hterm (j : Label) :
        (src j).toData.profileFactor*(∏a,(src j).M a)^2*
          QuadraticInitialBound.diagonalControl ballProfile*(2*dyadicScale n)^(3*εshell)≤
        F*Z^(3*L₂*εshell) :=
      actual_error_fixed_shell_factor N Cs bp hCs hbp s hcard hM hsb₁ hsb₂ (q j)
        ((g j).τ (χ j)) v Z (dyadicScale n) L₂ εshell hzpos (zero_le_one.trans hscale.1) hscale.2 heshell.le
    calc
      _=∑j,(Cg*scalar j*H)*((src j).toData.profileFactor*(∏a,(src j).M a)^2*
        QuadraticInitialBound.diagonalControl ballProfile*(2*dyadicScale n)^(3*εshell)) := by
        apply Finset.sum_congr rfl
        intro j _
        change Cg*(coefficient j*
          Z^(errorRemoval (q j).p Z (q j).k-errorMoving (q j).p Z (q j).k)*
          ((src j).toData.profileFactor*(∏a,(src j).M a)^2*
            QuadraticInitialBound.diagonalControl ballProfile*(p.control Sp)^2*
            (1+|v|+height)^degree*((q j).E₂.absNorm:ℝ)^(εshell-1)*
            (2*dyadicScale n)^(3*εshell)*
            Z^((g j).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (q j).k+
              εold+loss*(Fintype.card α:ℝ)+(omega+εpad*Mrow)/6+(3/4)*mesh+pad)))=_
        dsimp only [scalar,H]
        ring
      _≤∑j,(Cg*scalar j*H)*(F*Z^(3*L₂*εshell)) :=
        Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hterm j) (mul_nonneg (mul_nonneg hCg.le (hscalar j)) hH))
      _=_ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hrew := shared_label_projector_shell_sum Ds hDs (fun j D=>
    coefficient j*localErrorCost (q j).p ((q j).k-1)*
      (∑z∈rows j,‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2))
  have hrew' :
      (∑j,coefficient j*localErrorCost (q j).p ((q j).k-1)*
        (∑D∈Ds j,∑z∈rows j,‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2))=
      ∑n∈shells,∑j,coefficient j*localErrorCost (q j).p ((q j).k-1)*
        (∑D∈sharedLabelProjectorShell Ds j n,∑z∈rows j,
          ‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2) := by
    simpa only [Finset.mul_sum] using hrew
  rw [hrew']
  calc
    _≤∑_n∈shells,Cg*F*H*Z^(3*L₂*εshell)*∑j,scalar j := Finset.sum_le_sum hpay
    _=(shells.card:ℝ)*(Cg*F*H*Z^(3*L₂*εshell)*∑j,scalar j) := by simp
    _≤(Csh*Z^εproj)*(Cg*F*H*Z^(3*L₂*εshell)*∑j,scalar j) :=
      mul_le_mul_of_nonneg_right (hzs.2 Ds hcap) (by positivity)
    _=_ := by dsimp only [H]; rw [Real.rpow_add hzpos]; ring

/-- The post-column scalar has no common-allocation dependence. Original
nonzero blocks reindex to the full supported arithmetic labels, paying
only the shared four-coordinate dyadic envelope. -/
theorem actual_error_original_block_scalar_subpower {α : Type*}[Fintype α][DecidableEq α]
    (A D₀ B L Cr ε : ℝ)(hA : 0≤ A)(hD₀ : 0≤ D₀)(hB : 0≤ B)(hL : 0≤ L)
    (hCr : 0< Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ ∀ᶠZ : ℝ in atTop,1≤ Z ∧
    ∀(slots : Finset α)(s : Input slots)(R seed : Ideal O)(hseed : Squarefree seed)
      (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(K Tsec ξ : ℝ)(hK : 0< K),
      Z^(-D₀)≤ K → K≤ Z^A → frequencyRadius Tsec Z ξ≤ Cr*Z^L → sourceRadius s≤ Z^B →
    ∀(rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))(W : 𝓢(ℝ,ℂ)),
      ∀hne : ∀n∈rows,(actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK n).block.value W≠0,
    ∀(reflected second : Bool)(first : FirstSourceLabel)(M a δ reserve error εcommon V : ℝ)(p : O)(k : ℕ),
    let hU := actual_second_original_nonzero_supported slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK W rows hne
    (∑n : rows,extractedErrorLabelScalar reflected second first
      (actualSecondSupportedLabel s R seed K Tsec Z ξ n.val (hU n.val n.property))
      Z M a δ reserve error εcommon V (volume s) p k)≤
      C₀*Z^ε*∑v∈actualSecondLabels s R seed,
        extractedErrorLabelScalar reflected second first v Z M a δ reserve error εcommon V (volume s) p k := by
  obtain ⟨C₀,hC₀,hcount⟩ := actual_second_positive_subpower (α:=α) A D₀ B L Cr ε
    hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hz
  refine ⟨hz.1,?_⟩
  intro slots s R seed hseed hz₁ hz₂ K Tsec ξ hK hKlo hKhi hr hs rows W hne
    reflected second first M a δ reserve error εcommon V p k hU
  apply hz.2 slots s R seed hseed hz₁ hz₂ K Tsec ξ hK hKlo hKhi hr hs rows hU
    (fun v=>extractedErrorLabelScalar reflected second first v Z M a δ reserve error εcommon V (volume s) p k)
  intro v hv
  have hg := actual_second_labels_gates s R seed hseed hz₁ hz₂ v hv
  have hn := (normalizer_pos v.1.1 v.1.2 hg.1 v.2.val).le
  have hvol := (volume_pos s).le
  have hrad : 0≤ firstErrorTailRadius reflected first Z M V a δ reserve p k := by
    unfold firstErrorTailRadius errorCommonRadius
    exact Real.rpow_nonneg (zero_le_one.trans hz.1) _
  have hznonneg : 0≤ Z := zero_le_one.trans hz.1
  unfold extractedErrorLabelScalar
  positivity

/-- Genuine dependent full-label payment absorbs its explicit finite
loss into the strict reserve of every extracted-prime branch. -/
theorem eventual_actual_error_dependent_saved_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0< lo) (hev : 0<εv) (hB : 0≤ B) (he : 0<ε)
    (Mmin εaffine : ℝ)(hMmin : 0< Mmin) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
    ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected second : Bool)(T p exponent error εcommon M a δ reserve : ℝ),
      1≤ T → p≤ B → 0≤εcommon → Mmin≤ M →
      error+εv+B*εcommon+ε≤64*geometryLossUnit Mmin εaffine →
    ∀(seed : Ideal O),Squarefree seed → seed≠0 → ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤ Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤ exponent) →
    ∀(Ds : labels→ Finset (Ideal O)),(∀l D,D∈Ds l→ Squarefree D) →
      (∀l D,D∈Ds l→ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : labels)→ Ds l→ actualAllocations s.pools (if reflected then l.val.1.2 else l.val.1.1))
      (χ : (l : labels)→ Ds l→ Character)(t : ℝ),
      (∀l D,frozenCoefficient (alloc l D).val (if reflected then l.val.1.2 else l.val.1.1)
        Rfirst s.ν s.W s.P≠0) →
    let u : (l : labels)→(D : Ds l)→ Input (liveIndices (alloc l D).val) := fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst (alloc l D) (χ l D) t
    ∀(P : Finset (Ideal O)),P.Nonempty → (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀l D,∀q : elementPool P,∀j I,I∈(u l D).slots j→ IsCoprime (Ideal.span {q.val}) I) →
    let Bps := fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    ∀(υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→ RayCharacter→ Bps l D q i→ Character)
      (vheight : ℝ)
      (children : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→ RayCharacter→ Bps l D q i→ Finset FirstSourceLabel),
      (∀l D q i ψ b,∀v∈children l D q i ψ b,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,D.val∣v.1.1 ∧ D.val∣v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (56/(P.card:ℝ))*(∑q : elementPool P,∑i : Fin 3,16*(errorIndex i+2:ℝ)*
        ∑l : labels,∑ψ : RayCharacter,∑D : Ds l,∑Bp : Bps l D q i,∑v∈children l D q i ψ Bp,
          extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
            (volume s) (volume (child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
              (Rfirst*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight))
            q.val (errorIndex i+1))≤
      K*Z^(p+exponent-M*(7/60000000:ℝ))/(seed.absNorm:ℝ) := by
  obtain ⟨K,hK,hpaid⟩ := eventual_actual_error_dependent_full_label_payment N lo εv B ε hlo hev hB he
  refine ⟨1872*K,by positivity,?_⟩
  filter_upwards [hpaid] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon M a δ reserve hT hp hecommon
    hM hloss seed hs hs0 labels hsup heq hseed hnorm hrad hgeom Ds hDs hdyad Rfirst alloc χ t halloc
    u P hne hprime hbad hslot Bps υ vheight children hsup₂ heq₂ hdiv hnorm₂
  have hZ : 0< Z := by linarith [hz.1]
  have hb := hz.2 s hcard hlow reflected second T p exponent error εcommon M a δ reserve
    hT hp hecommon seed hs hs0 labels hsup heq hseed hnorm hrad hgeom Ds hDs hdyad
    Rfirst alloc χ t halloc P hne hprime hbad hslot υ vheight children hsup₂ heq₂ hdiv hnorm₂
  have hn : (0:ℝ)< seed.absNorm := norm_pos seed hs0
  have hsave := geometry_error_branches_saving Z Mmin εaffine M
    (error+εv+B*εcommon+ε) (by linarith [hz.1]) hMmin hM hloss
  apply hb.trans
  calc
    _=(K*Z^(p+exponent)/(seed.absNorm:ℝ))*
      (Z^(error+εv+B*εcommon+ε)*∑i : Fin 3,16*(errorIndex i+2:ℝ)^2*
        Z^(-M*branchReserve (errorIndex i+1))) := by
      rw [show p+exponent+error+εv+B*εcommon+ε=(p+exponent)+(error+εv+B*εcommon+ε) by ring,
        Real.rpow_add hZ]
      ring
    _≤(K*Z^(p+exponent)/(seed.absNorm:ℝ))*(1872*Z^(-M*(7/60000000:ℝ))) :=
      mul_le_mul_of_nonneg_left hsave (by positivity)
    _=_ := by
      rw [show -M*(7/60000000:ℝ)=-(M*(7/60000000:ℝ)) by ring,
        Real.rpow_neg hZ.le,Real.rpow_sub hZ]
      ring


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_extracted_pool_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_extracted_finite_pool_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_extracted_projector_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_normalized_scalar_identity
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_fixed_shell_factor
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_paid_error_complete_projector_family

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_error_dependent_saved_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_original_block_scalar_subpower

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalizedPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalizedClosure; sha256 7615b100d39325257e2d8400bd3451615287fb086e7acb8583174d738e641a89 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                                  
                                                        
                                                              
                                                             

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondRetainedRows
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentEligibleEnergy CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAmplificationErrorEnergy CenteredMomentRestrictedEnergy
open CenteredMomentAllocatedRayDictionary CenteredMomentSlotRatios
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Cycle61FinalNatural Cycle61Moment Cycle61FinalError Cycle61FinalErrorCapacity
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonAllocationSum
open CenteredMomentPrimeElements CenteredMomentRankinRadical
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O
local instance errorNormalizedClosureSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α : Type*} [Fintype α] [DecidableEq α]
section Selected
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (p : O) (i : Fin 3)
variable (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
variable (hne : (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
variable (second : Bool)

/-- The allocation is fixed by the original nonzero physical block, before
its residual projector, either ray, or any external Mellin height. -/
noncomputable def geometryErrorSelectedAllocation :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    actualAllocations d.input.pools (if second then d.D else d.C) :=
  let nz : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ :=
    ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩⟩
  Classical.choose (actual_geometry_error_live_common_allocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ nz second)

theorem geometryErrorSelectedAllocation_nonzero :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    frozenCoefficient (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second).val
      (if second then d.D else d.C) d.R d.input.ν d.input.W d.input.P≠0 :=
  Classical.choose_spec (actual_geometry_error_live_common_allocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂
    ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩⟩ second)


variable (hp : p≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
      IsCoprime (Ideal.span {p}) I)
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

/-- Actual admission uses the live allocation supplied by the original
block; the inducing and full stored-pool coprimality gates stay explicit. -/
noncomputable def geometryErrorSelectedGeometry :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    Geometry s (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then d.D else d.C) d.R (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second))
      Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ b (fixedFactor:ℝ) N :=
  geometryErrorActualGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hp hcop hw₁ hw₂ ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩⟩ second
    (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second) ψ hυ hf₁
    (geometryErrorSelectedAllocation_nonzero reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)

/-- Admission preserves the literal extracted frequency radius in both
first orientations; it does not replace the common source radius. -/
theorem geometryErrorSelectedGeometry_radius :
    (geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁).radius=
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).radius := by
  change errorRadius
    (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).D
       else (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).C)
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).R
      (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second))
    (geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
    (geometryErrorInactive reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
    Z Mrow amp (frequencyLoss Z 32 ξ) reserve ξ b N=
      frequencyRadius (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
  exact actual_geometry_error_radius reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hp hcop _ _ _

/-- The source ledger is independent of the selected common allocation,
both physical rays and the residual projector. -/
theorem geometryErrorSelectedGeometry_nominal :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    (geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁).nominal=
      errorNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
        (errorRemoval p Z (errorIndex i+1)) (errorMoving p Z (errorIndex i+1))
        (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
        (geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
        d.C d.D d.inactive := rfl

/-- Both full physical zero-mode sums equal the columns of the admitted
geometry. The right ray stays inverse and its height shift stays negative. -/
theorem geometryErrorSelectedGeometry_complete_columns
    (Q : Ideal O)(hQ : Q≤ Ideal.span {(72:O)})
    (χ₀ χ ψ₂ : RayCharacter)(L : Ideal O)(tₑ u : ℝ) :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    let chain := geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then d.D else d.C) d.R (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)
    let g := geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
    let hE : Supported chain.E₂ := by
      cases second with
      | false => exact d.hC
      | true => exact d.hD
    (∑z∈partRows false d.input.η χ₀ Q fixedBadMask d.C d.D d.inactive d.radius,
      if second then
        ‖normalizedColumn (withHeight d.input (d.τ ψ₂⁻¹) (d.input.t+2*Real.pi*(u-(-tₑ))))
          d.D d.hD d.R d.seed L (-z)‖^2
      else
        ‖normalizedColumn (withHeight d.input (d.τ χ) (d.input.t+2*Real.pi*(u-tₑ)))
          d.C d.hC d.R d.seed L z‖^2)=
    ∑z∈partRows false chain.υ (if second then ψ₂⁻¹ else χ) Q fixedBadMask
      g.C g.D g.U g.radius,
      ‖normalizedColumn (withHeight chain.extracted (g.τ (if second then ψ₂⁻¹ else χ))
        (chain.extracted.t+2*Real.pi*(u-(if second then -tₑ else tₑ))))
        chain.E₂ hE chain.R₂ d.seed L z‖^2 := by
  intro d chain g hE
  apply (actual_error_complete_column_rows d.input d.τ d.C d.D d.hC d.hD d.inactive
    d.R d.seed L Q d.radius hQ χ₀ χ ψ₂ second tₑ u).trans
  have hr := geometryErrorSelectedGeometry_radius reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
  change _=∑z∈partRows false chain.υ (if second then ψ₂⁻¹ else χ) Q fixedBadMask
    g.C g.D g.U g.radius,_
  rw [show g.radius=d.radius from hr]
  cases second <;> rfl


end Selected

/-- Fixed degree and profile control set of the genuine paid error theorem,
chosen before the original source, its heights, or either block family. -/
def actual_geometry_error_column_parameters {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hL : 0≤ L) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hloss : 0< loss) (hmargin : 0< margin) (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤ window) (hpad : 0< pad) (heshell : 0<εshell)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1≤ Cs)(hL₂ : 0≤ L₂)(heproj : 0<εproj) :=
  let hJ : 0<(fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  let uniform := actual_paid_error_complete_projector_family.{u,v} (α:=α)
    M H hH W A B ap bp Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp
    hBmask hL hMcap hεold hloss hmargin hbeta ηseed bs (fixedFactor:ℝ) εwidth εpad Mmin
    window pad εshell hwindow hpad heshell hbs hJ hew hep hmin N Cs L₂ εproj hCs hL₂ heproj
  PProd.mk (Classical.choose uniform) (Classical.choose (Classical.choose_spec uniform))


set_option linter.defProp false in
/-- Complete ordinary columns for the literal extracted block family.
The original nonzero gate chooses allocations before either ray or projector. -/
def actual_geometry_error_complete_selected_columns {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hL : 0≤ L) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hloss : 0< loss) (hmargin : 0< margin) (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤ window) (hpad : 0< pad) (heshell : 0<εshell)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1≤ Cs)(hL₂ : 0≤ L₂)(heproj : 0<εproj) :=
  let hJ : 0<(fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  let uniform := actual_paid_error_complete_projector_family (α:=α)
    M H hH W A B ap bp Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp
    hBmask hL hMcap hεold hloss hmargin hbeta ηseed bs (fixedFactor:ℝ) εwidth εpad Mmin
    window pad εshell hwindow hpad heshell hbs hJ hew hep hmin N Cs L₂ εproj hCs hL₂ heproj
  let degree := Classical.choose uniform
  let profiles := Classical.choose_spec uniform
  let Sp := Classical.choose profiles
  let hfamily := Classical.choose_spec profiles
  (fun (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
      (hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
      (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})=>
    let receipt := hfamily η₀ Q hQM hQ0 hQt hQ72
    let Cg := Classical.choose receipt
    let bound := Classical.choose_spec receipt
    PProd.mk Cg (And.intro bound.1
      (bound.2.mono (fun Z hz=>And.intro hz.1
        (fun (hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)
          (w σ freq : α→ℝ)(v height mesh : ℝ)
          hcard hM hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin
          (Mrow ξ : ℝ) hMmin hξ hMcap' hslot haff=>
        let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp := Mrow*Cycle61.Arithmetic.amp cell
        fun (reserve : ℝ)(hreserve : 0≤ frequencyLoss Z 32 ξ+reserve)
          (reflected : Bool)(R seed : Ideal O)(t₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
          (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
          (prime : O)(i : Fin 3)(hp : prime≠0)
          (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first).slots j→ IsCoprime (Ideal.span {prime}) I)
          (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first)).pools ((Ideal.span {prime})^(errorIndex i+1)))
          (υ : Character)(v₀ : ℝ)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(ψ : RayCharacter)
          (hυ : υ.modulus.absNorm≤ radicalBound
            (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) ψ)
            fixedBadMask prime (errorMovingExponent (errorIndex i)))
          (hf₁ : frozenCoefficient first.2.val
            (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) R s.ν s.W s.P≠0)
          (hprime : 3*amp/4≤ Real.logb Z (normValue prime))=>
        fun {Label : Type v} [Fintype Label]
          (index : Label→ GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀)=>
        let datum := fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
        fun (hne : ∀n : Label,(datum n).block.value ballProfile≠0)(second : Bool)=>
        let alloc := fun n=>geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second
        let chains := fun n=>geometryErrorChain reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀ hp hcop
          (if second then (datum n).D else (datum n).C) (datum n).R (alloc n)
        let geom := fun n=>geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁
        fun (χ : Label→ RayCharacter) hP hPN (p : Profiles ap bp) hp₁ hp₂
          (Ds : Label→ Finset (Ideal O)) hDs hcap (P : Finset (Ideal O))(weight : Label→ℝ) hwgt=>
        let hk (n : Label) : (chains n).k=1 ∨ (chains n).k=6 ∨ (chains n).k=7 := by
          change errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7
          fin_cases i <;> norm_num [errorIndex]
        let hprime' (n : Label) : 3*amp/4≤ Real.logb Z (normValue (chains n).p) := hprime
        let hE₂ (n : Label) : Supported (chains n).E₂ := by
          cases second with
          | false => exact (datum n).hC
          | true => exact (datum n).hD
        let hs (n : Label) : (datum n).seed∣(chains n).E₂ := by
          have hg := actual_geometry_error_seed_gates reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
          cases second with
          | false => exact hg.1
          | true => exact hg.2
        hz.2 hZ s θ w σ freq v height mesh hcard hM hm hsη hsupper hsb₁ hsb₂
          hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow
          (frequencyLoss Z 32 ξ+reserve) ξ hMmin hreserve hξ hMcap' hslot haff
          chains hk hprime' geom χ hP hPN p hp₁ hp₂ (fun n=>(datum n).seed)
          hE₂ hs Ds hDs hcap P weight hwgt)))))


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorSelectedAllocation
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorSelectedAllocation_nonzero
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorSelectedGeometry
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorSelectedGeometry_radius
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorSelectedGeometry_nominal
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorSelectedGeometry_complete_columns
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_column_parameters
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_complete_selected_columns
set_option pp.universes true in
#check @OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_complete_selected_columns

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalizedClosure -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalizedFullFamily; sha256 a9bcfba56bdf830d0d5b5682a081aae1931d373380919ed2d8496b8159c06ac4 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                                  
                                                        
                                                              
                                                             

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondRetainedRows
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentEligibleEnergy CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAmplificationErrorEnergy CenteredMomentRestrictedEnergy
open CenteredMomentAllocatedRayDictionary CenteredMomentSlotRatios
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Cycle61FinalNatural Cycle61Moment Cycle61FinalError Cycle61FinalErrorCapacity
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonAllocationSum
open CenteredMomentPrimeElements CenteredMomentRankinRadical
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance errorNormalizedFullFamilySumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


/-- Arbitrary finite original block families retain both ray sums, the
complete ordinary zero-mode sets and the exact extracted-prime coefficient. -/
theorem actual_error_indexed_normalized_to_admitted_columns {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0< K)
    (index : Label→ ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0≤ weight) (prime : O) (i : Fin 3)
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (hcard : Fintype.card α≤ N) (hlower : a≤ s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ ap≤ x) (hW₂ : ∀x,s.W₂ x≠0→ ap≤ x)
    (W : 𝓢(ℝ,ℂ)) (χ₀ : Label→ RayCharacter) (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)})
    (second : Bool) (t u : ℝ) :
    let d := fun n=>actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK (index n)
    let datum := fun n=>ordinarySecondDatum (d n) (χ₀ n) Q fixedBadMask
    let c := errorNormalizedCoefficient P weight (volume s) prime i
    let w := fun n=>(c:ℂ)*actualSecondBlockWeight s R seed K Tsec Z ξ (index n)
    secondNormalizedSum second datum
      (secondEffectiveWeight (fun n=>(datum n).block) w W) t u≤
      ∑χ : RayCharacter,∑ψ : RayCharacter,∑n,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if second then
            ∑z∈partRows false s.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D z‖^2
           else
            ∑z∈partRows false s.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
  intro d datum c w
  have hc : 0≤ c := error_normalized_coefficient_nonneg P weight (volume s) hw (volume_pos s) prime i
  have hbase := actual_error_ordinary_normalized_columns N a ap ha hap d w W hcard
    (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂) χ₀ Q second t u
  apply hbase.trans
  calc
    _≤∑n,∑χ : RayCharacter,∑ψ : RayCharacter,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          ∑z∈partRows false s.η (χ₀ n) Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
            (if second then
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D (-z)‖^2
             else
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro χ _
      apply Finset.sum_le_sum
      intro ψ _
      have hn := actual_error_block_weight_norm s R seed K Tsec Z ξ (index n) c hc
      have hf : 0≤ K/lowerFactor N a ap := div_nonneg hK.le (lowerFactor_pos N a ap ha hap).le
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hf)
          (normalizer_pos (d n).C (d n).D (d n).hC (d n).inactive).le
      · exact Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>by split_ifs <;> positivity))
    _=∑n,∑χ : RayCharacter,∑ψ : RayCharacter,
        (c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*
        ∑D∈(d n).block.divisors.filter Squarefree,
          (if second then
            ∑z∈partRows false s.η ψ⁻¹ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t))))
                (d n).D (d n).hD R seed D z‖^2
           else
            ∑z∈partRows false s.η χ Q fixedBadMask (d n).C (d n).D (d n).inactive (d n).radius,
              ‖normalizedColumn (withHeight s ((d n).τ χ) (s.t+2*Real.pi*(u-t)))
                (d n).C (d n).hC R seed D z‖^2) := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ψ _
      apply congrArg (fun r : ℝ=>(c*(K/lowerFactor N a ap)*normalizer (d n).C (d n).D (d n).inactive)*r)
      apply Finset.sum_congr rfl
      intro D _
      exact actual_error_complete_column_rows s (d n).τ (d n).C (d n).D (d n).hC (d n).hD
        (d n).inactive R seed D Q (d n).radius hQ (χ₀ n) χ ψ second t u
    _=_ := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro χ _; rw [Finset.sum_comm]


set_option linter.defProp false in
/-- Literal specialization to the lifted active extracted source. The
inferred result retains every original first key and error-radius parameter. -/
def actual_geometry_error_indexed_admitted_columns
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (index : Label→ GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
    (P : Finset (Ideal O)) (weight : ℝ) (hw : 0≤ weight)
    (Ncap : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap) (hcard : Fintype.card α≤ Ncap)
    (hlower : a≤ s.lower) (hW₁ : ∀x,s.W₁ x≠0→ ap≤ x) (hW₂ : ∀x,s.W₂ x≠0→ ap≤ x)
    (W : 𝓢(ℝ,ℂ))
    (χ₀ : Label→ RayCharacter)
    (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)}) (second : Bool) (θ u : ℝ) :=
  actual_error_indexed_normalized_to_admitted_columns
    (liveIndices (errorActiveAllocation
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val)
    (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)
    ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1))
    q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property)
    hw₁ hw₂ (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
    (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
    index
    P weight hw p i Ncap a ap ha hap
    ((Fintype.card_subtype_le _).trans hcard) hlower hW₁ hW₂ W χ₀ Q hQ second θ u



private theorem error_full_ray_column_transport {Label : Type*}[Fintype Label]
    {Ds : Label→ Finset (Ideal O)} {rawCoefficient paidCoefficient : Label→ℝ}
    {raw paid : RayCharacter→ RayCharacter→ Label→ Ideal O→ℝ} {E : ℝ}
    (hc : ∀n,rawCoefficient n=paidCoefficient n)
    (hcolumn : ∀χ ψ n D,D∈Ds n → raw χ ψ n D=paid χ ψ n D)
    (hpaid : ∀χ ψ,(∑n,paidCoefficient n*∑D∈Ds n,paid χ ψ n D)≤ E) :
    (∑χ : RayCharacter,∑ψ : RayCharacter,∑n,rawCoefficient n*∑D∈Ds n,raw χ ψ n D)≤
      ((Fintype.card RayCharacter:ℝ)^2)*E := by
  calc
    _=(∑χ : RayCharacter,∑ψ : RayCharacter,∑n,paidCoefficient n*∑D∈Ds n,paid χ ψ n D) := by
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ψ _
      apply Finset.sum_congr rfl
      intro n _
      apply congrArg₂ (fun x y : ℝ=>x*y) (hc n)
      exact Finset.sum_congr rfl (fun D hD=>hcolumn χ ψ n D hD)
    _≤∑_χ : RayCharacter,∑_ψ : RayCharacter,E :=
      Finset.sum_le_sum (fun χ _=>Finset.sum_le_sum (fun ψ _=>hpaid χ ψ))
    _=((Fintype.card RayCharacter:ℝ)^2)*E := by simp; ring

set_option linter.defProp false in
/-- Literal ordinary normalized error sums from the genuine paid columns.
The two ray sums pay their fixed finite cardinality, with the first key intact. -/
def actual_geometry_error_paid_normalized_family {α : Type u}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hL : 0≤ L) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hloss : 0< loss) (hmargin : 0< margin) (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤ window) (hpad : 0< pad) (heshell : 0<εshell)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1≤ Cs)(hL₂ : 0≤ L₂)(heproj : 0<εproj) :=
  let hJ : 0<(fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  let uniform := actual_paid_error_complete_projector_family (α:=α)
    M H hH W A B ap bp Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp
    hBmask hL hMcap hεold hloss hmargin hbeta ηseed bs (fixedFactor:ℝ) εwidth εpad Mmin
    window pad εshell hwindow hpad heshell hbs hJ hew hep hmin N Cs L₂ εproj hCs hL₂ heproj
  let degree := Classical.choose uniform
  let profiles := Classical.choose_spec uniform
  let Sp := Classical.choose profiles
  let hfamily := Classical.choose_spec profiles
  (fun (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
      (hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
      (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})=>
    let receipt := hfamily η₀ Q hQM hQ0 hQt hQ72
    let Cg := Classical.choose receipt
    let bound := Classical.choose_spec receipt
    PProd.mk Cg (And.intro bound.1
      (bound.2.mono (fun Z hz=>And.intro hz.1
        (fun (hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)
          (w σ freq : α→ℝ)(height mesh : ℝ)
          hcard hM hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin
          (Mrow ξ : ℝ) hMmin hξ hMcap' hslot haff=>
        let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp := Mrow*Cycle61.Arithmetic.amp cell
        fun (reserve : ℝ)(hreserve : 0≤ frequencyLoss Z 32 ξ+reserve)
          (reflected : Bool)(R seed : Ideal O)(t₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
          (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
          (prime : O)(i : Fin 3)(hp : prime≠0)
          (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first).slots j→ IsCoprime (Ideal.span {prime}) I)
          (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first)).pools ((Ideal.span {prime})^(errorIndex i+1)))
          (υ : Character)(v₀ : ℝ)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(ψ : RayCharacter)
          (hυ : υ.modulus.absNorm≤ radicalBound
            (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) ψ)
            fixedBadMask prime (errorMovingExponent (errorIndex i)))
          (hf₁ : frozenCoefficient first.2.val
            (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) R s.ν s.W s.P≠0)
          (hprime : 3*amp/4≤ Real.logb Z (normValue prime))=>
        fun {Label : Type v} [Fintype Label]
          (index : Label→ GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀)=>
        let datum := fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
        fun (hne : ∀n : Label,(datum n).block.value ballProfile≠0)(second : Bool)=>
        let alloc := fun n=>geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second
        let chains := fun n=>geometryErrorChain reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀ hp hcop
          (if second then (datum n).D else (datum n).C) (datum n).R (alloc n)
        let geom := fun n=>geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁

        fun (hP : ∀n,(chains n).R₂*(chains n).E₂≠0)
          (hPN : ∀n,(((chains n).R₂*(chains n).E₂).absNorm:ℝ)≤ Z^Bmask)
          (p : Profiles ap bp)(hp₁ : s.W₁=p.profile 0)(hp₂ : s.W₂=p.profile 1)
          (a : ℝ)(ha : 0< a)(hlower : a≤ s.lower)
          (hW₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hW₂ : ∀x,s.W₂ x≠0→ ap≤ x)
          (windowProfile : 𝓢(ℝ,ℂ))(χ₀ : Label→ RayCharacter)
          (P : Finset (Ideal O))(weight : ℝ)(hwgt : 0≤ weight)
          (hcap : ∀n D,D∈(datum n).block.divisors.filter Squarefree→(D.absNorm:ℝ)≤ Z^L₂)
          (tₑ u : ℝ)=>
        let analyticv := v₀+2*Real.pi*(u-(if second then -tₑ else tₑ))
        let Ds := fun n=>(datum n).block.divisors.filter Squarefree
        let hDs : ∀n D,D∈Ds n→ Squarefree D := fun _ _ hD=>(Finset.mem_filter.mp hD).2
        let hk (n : Label) : (chains n).k=1 ∨ (chains n).k=6 ∨ (chains n).k=7 := by
          change errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7
          fin_cases i <;> norm_num [errorIndex]
        let hprime' (n : Label) : 3*amp/4≤ Real.logb Z (normValue (chains n).p) := hprime
        let hE₂ (n : Label) : Supported (chains n).E₂ := by
          cases second with
          | false => exact (datum n).hC
          | true => exact (datum n).hD
        let hs (n : Label) : (datum n).seed∣(chains n).E₂ := by
          have hg := actual_geometry_error_seed_gates reflected s R seed Z Mrow amp ξ reserve bs t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
          cases second with
          | false => exact hg.1
          | true => exact hg.2
        let source := geometryErrorChild reflected s R seed Z Mrow ξ t₀ hZ bin first prime i Bp υ v₀
        let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i
        let columnWeight : Label→ℝ := fun n=>weight*(K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive
        let hcolumnWeight : ∀n,0≤ columnWeight n := by
          intro n
          have hK := actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin first prime i
          have hlf := lowerFactor_pos N a ap ha hap
          have hn := normalizer_pos (datum n).C (datum n).D (datum n).hC (datum n).inactive
          dsimp only [columnWeight]
          positivity
        let coefficient : Label→ℝ := fun n=>(56/(P.card:ℝ))*columnWeight n*16*((chains n).k+1:ℝ)/volume (chains n).extracted
        let scalar : Label→ℝ := fun n=>coefficient n*
          Z^(errorRemoval (chains n).p Z (chains n).k-errorMoving (chains n).p Z (chains n).k)*
          ((chains n).E₂.absNorm:ℝ)^(εshell-1)*
          Z^((geom n).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (chains n).k+
            εold+loss*(Fintype.card α:ℝ)+
            (frequencyLoss Z 32 ξ+reserve+εpad*Mrow)/6+(3/4)*mesh+pad)
        let E : ℝ := Cg*(p.control Sp)^2*(1+|analyticv|+height)^degree*Z^(εproj+3*L₂*εshell)*∑n,scalar n
        let rayCost : RayCharacter→ RayCharacter→ℝ := fun χ ψ₂=>(∑n,coefficient n*localErrorCost (chains n).p ((chains n).k-1)*
              ∑D∈Ds n,∑z∈partRows false (chains n).υ (if second then ψ₂⁻¹ else χ)
                (internalQ Q η₀) fixedBadMask (geom n).C (geom n).D (geom n).U (geom n).radius,
                ‖normalizedColumn (withHeight (chains n).extracted ((geom n).τ (if second then ψ₂⁻¹ else χ)) analyticv)
                  (chains n).E₂ (hE₂ n) (chains n).R₂ (datum n).seed D z‖^2)
        let hpay (χ ψ₂ : RayCharacter) : rayCost χ ψ₂≤ E := by
          exact hz.2 hZ s θ w σ freq analyticv height mesh hcard hM hm hsη hsupper hsb₁ hsb₂
            hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow
            (frequencyLoss Z 32 ξ+reserve) ξ hMmin hreserve hξ hMcap' hslot haff
            chains hk hprime' geom (fun _=>if second then ψ₂⁻¹ else χ) hP hPN p hp₁ hp₂
            (fun n=>(datum n).seed) hE₂ hs Ds hDs hcap P columnWeight hcolumnWeight
        let hnorm := actual_geometry_error_indexed_admitted_columns reflected s R seed Z Mrow amp ξ reserve bs t₀
          (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ index P weight hwgt
          N a ap ha hap hcard hlower hW₁ hW₂ windowProfile χ₀
          (internalQ Q η₀) hQ72 second tₑ u
        let hc (n : Label) :
            errorNormalizedCoefficient P weight (volume source) prime i*
              (K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive=
              coefficient n*localErrorCost (chains n).p ((chains n).k-1) := by
          change errorNormalizedCoefficient P weight (volume source) prime i*
            (K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive=
            (56/(P.card:ℝ))*(weight*(K/lowerFactor N a ap)*normalizer (datum n).C (datum n).D (datum n).inactive)*
              16*((errorIndex i+1:ℕ)+1:ℝ)/volume source*localErrorCost prime ((errorIndex i+1)-1)
          simp only [Nat.add_sub_cancel]
          unfold errorNormalizedCoefficient
          push_cast
          ring
        let hcolumn := fun (χ ψ₂ : RayCharacter)(n : Label)(D : Ideal O)=>
          let hcolumns := geometryErrorSelectedGeometry_complete_columns reflected s R seed Z Mrow amp ξ reserve bs t₀
            (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁
            (internalQ Q η₀) hQ72 (if second then ψ₂⁻¹ else χ) χ ψ₂ D tₑ u
          let hrows := actual_error_complete_column_rows (datum n).input (datum n).τ
            (datum n).C (datum n).D (datum n).hC (datum n).hD (datum n).inactive
            (datum n).R (datum n).seed D (internalQ Q η₀) (datum n).radius hQ72
            (if second then ψ₂⁻¹ else χ) χ ψ₂ second tₑ u
          let ht : (chains n).extracted.t=v₀ := rfl
          let hheight := congrArg (fun v : ℝ=>
            ∑z∈partRows false (chains n).υ (if second then ψ₂⁻¹ else χ)
              (internalQ Q η₀) fixedBadMask (geom n).C (geom n).D (geom n).U (geom n).radius,
              ‖normalizedColumn (withHeight (chains n).extracted ((geom n).τ (if second then ψ₂⁻¹ else χ))
                (v+2*Real.pi*(u-(if second then -tₑ else tₑ))))
                (chains n).E₂ (hE₂ n) (chains n).R₂ (datum n).seed D z‖^2) ht
          (hrows.symm.trans hcolumns).trans hheight
        hnorm.trans (error_full_ray_column_transport (Ds:=Ds) hc
          (fun χ ψ₂ n D _=>hcolumn χ ψ₂ n D) hpay))))))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_indexed_normalized_to_admitted_columns
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_indexed_admitted_columns
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_paid_normalized_family

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorNormalizedFullFamily -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondDatumReindex; sha256 a77ce69e6d56bdfcfb4576320e6da8df016758f377ffc8555006c11de5337987 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                             

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearSource CenteredMomentCommonHeightEnvelope
open CenteredMomentSourceInputReindex CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceMass
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstAmplificationChoice RayFourExpansion
open CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
local instance secondDatumReindexDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Renaming original slots leaves the literal source column unchanged. -/
theorem source_column_reindex (e : α ≃ β) (s : Input α)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O) (z : O) :
    sourceColumn (reindex e s) C hC R seed L z = sourceColumn s C hC R seed L z := by
  unfold sourceColumn
  change (let Q := residualPool C hC.1 (original (reindex e s) R seed).columns
          let b := (original (reindex e s) R seed).beta
          rowPolynomial Finset.univ (sourceGenerator Q)
            (fun I : supportedColumns Q =>
              (if IsCoprime C (I : Ideal O) ∧ L ∣ (I : Ideal O)
               then b (C * I) else 0) * heightCoeff s.η s.t I) z) = _
  rw [columns_map, coefficient_map]
  rfl

/-- The physical volume normalization is invariant under slot equivalence. -/
theorem normalized_column_reindex (e : α ≃ β) (s : Input α)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O) (z : O) :
    normalizedColumn (reindex e s) C hC R seed L z =
      normalizedColumn s C hC R seed L z := by
  unfold normalizedColumn
  change (Real.sqrt (CenteredMomentAmplificationChildInput.volume (reindex e s)) : ℂ)⁻¹ *
    sourceColumn (reindex e s) C hC R seed L z = _
  rw [volume_map, source_column_reindex]
  rfl

/-- Height shifts commute with reindexing; no Mellin parameter is changed. -/
theorem normalized_column_reindex_height (e : α ≃ β) (s : Input α)
    (η : Character) (t : ℝ) (C : Ideal O) (hC : Supported C)
    (R seed L : Ideal O) (z : O) :
    normalizedColumn (withHeight (reindex e s) η t) C hC R seed L z =
      normalizedColumn (withHeight s η t) C hC R seed L z :=
  normalized_column_reindex e (withHeight s η t) C hC R seed L z

/-- Place each varying slot subset in one fixed original ambient type. -/
def SecondInputDatum.image (e : α ↪ β) (d : SecondInputDatum α) : SecondInputDatum β where
  slots := d.slots.map e
  input := imageInput e d.slots d.input
  R := d.R
  seed := d.seed
  C := d.C
  D := d.D
  hC := d.hC
  hD := d.hD
  sameSupport := d.sameSupport
  inactive := d.inactive
  radius := d.radius
  rows := d.rows
  rows_ne := d.rows_ne
  K := d.K
  K_pos := d.K_pos
  dyad := d.dyad
  τ := d.τ
  family := d.family
  rowBudget := d.rowBudget

/-- The entire physical block is unchanged by the ambient embedding. -/
@[simp] theorem second_datum_image_block (e : α ↪ β) (d : SecondInputDatum α) :
    (d.image e).block = d.block := by
  have hc := columns_map (Finset.equivMap e d.slots) d.input d.R d.seed
  have hb := coefficient_map (Finset.equivMap e d.slots) d.input d.R d.seed
  dsimp only [CenteredMomentFirstAmplificationChoice.OriginalData.columns, original] at hc
  dsimp only [CenteredMomentFirstAmplificationChoice.OriginalData.beta,
    CenteredMomentFirstAmplificationChoice.OriginalData.profile, original] at hb
  unfold SecondInputDatum.block
  dsimp only [SecondInputDatum.image, imageInput]
  unfold originalSecondBlock
  rw [hc, hb]
  rfl

@[simp] theorem second_datum_image_volume (e : α ↪ β) (d : SecondInputDatum α) :
    CenteredMomentExceptionalAmplitudePair.volume (d.image e).input.toData =
      CenteredMomentExceptionalAmplitudePair.volume d.input.toData :=
  volume_map (Finset.equivMap e d.slots) d.input

/-- Exact columns on both original and reflected rows, at arbitrary shifted height. -/
theorem second_datum_image_column (e : α ↪ β) (d : SecondInputDatum α)
    (η : Character) (t : ℝ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (z : O) :
    normalizedColumn (withHeight (d.image e).input η t) C hC (d.image e).R (d.image e).seed L z =
      normalizedColumn (withHeight d.input η t) C hC d.R d.seed L z :=
  normalized_column_reindex_height (Finset.equivMap e d.slots) d.input η t C hC d.R d.seed L z

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.source_column_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.normalized_column_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.normalized_column_reindex_height
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_datum_image_block
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_datum_image_volume
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_datum_image_column

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondDatumReindex -/
