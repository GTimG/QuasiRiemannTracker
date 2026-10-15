/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryErrorNormalizedAssembly
import Candidate.Cycle62.Physical.InitialMass.SecondProjectorShell
import Candidate.Cycle62.Physical.InitialMass.GeometryAmplifiedRemainder
import Candidate.Cycle62.Physical.InitialMass.SecondLabelDisintegration

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle62InitialMass
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
open Cycle62FinalNatural Cycle62Moment Cycle62FinalError Cycle62FinalErrorCapacity
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
    (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Y) :
    ∀j I,I∈q.extracted.pools j→(I.absNorm:ℝ)≤Y :=
  actual_child_pool_cap q.first ((Ideal.span {q.p})^q.k) (q.R₁*q.C₁) q.Bp q.υ q.t₂ Y
    (actual_child_pool_cap s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ Y hpool)

/-- Original cardinality bounds the complete finite extracted source pool;
all stored coefficients remain in the product dictionary. -/
theorem actual_error_extracted_finite_pool_cap {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(q : Chain s)(N : ℕ)(Z U : ℝ)
    (hN : Fintype.card α≤N)(hZ : 1≤Z)(hU : 0≤U)
    (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U) :
    ∀I∈finiteColumns (Fintype.piFinset q.extracted.pools),(I.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) := by
  have hfirst : Fintype.card (liveIndices q.B₁.val)≤N := by
    apply le_trans _ hN
    simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices q.B₁.val)
  have hextracted : Fintype.card (liveIndices q.Bp.val)≤N := by
    apply le_trans _ hfirst
    simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices q.Bp.val)
  exact actual_finite_pool_cap q.extracted N Z U hextracted hZ hU
    (actual_error_extracted_pool_cap s q (Z^U) hpool)

/-- A literal extracted physical block inherits the cap through its exact
pool identity; row restrictions and zero coefficients do not change it. -/
theorem actual_error_extracted_projector_cap {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(q : Chain s)(N : ℕ)(Z U : ℝ)
    (hN : Fintype.card α≤N)(hZ : 1≤Z)(hU : 0≤U)
    (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U)
    (b : SecondBlockSource)(hb : b.pool=finiteColumns (Fintype.piFinset q.extracted.pools))
    (L : Ideal O)(hL : L∈b.divisors) :
    L≠0 ∧ (L.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) := by
  apply second_block_projector_norm b _ _ L hL
  rw [hb]
  exact actual_error_extracted_finite_pool_cap s q N Z U hN hZ hU hpool

/-- The exact normalized column coefficient is the extracted scalar paid
by the dependent full-label theorem. Local error cost remains on the
column side; this identity uses the restored removal/moving power. -/
theorem actual_error_normalized_scalar_identity
    (reflected second : Bool)(l v : FirstSourceLabel)(Z M a δ reserve error εcommon V Vextract lf weight : ℝ)
    (P : Finset (Ideal O))(p : O)(i : Fin 3)(hZ : 0<Z) :
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
    (N : ℕ)(Cs bp : ℝ)(hCs : 1≤Cs)(hbp : 1≤bp)
    (s : Input α)(hcard : Fintype.card α≤N)(hM : ∀j,s.M j≤Cs)
    (hb₁ : s.b₁=bp)(hb₂ : s.b₂=bp)(q : Chain s)(η : Character)(v Z T L₂ εshell : ℝ)
    (hZ : 0<Z)(hT : 0≤T)(hscale : T≤Z^L₂)(he : 0≤εshell) :
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
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hL : 0≤L) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hloss : 0<loss) (hmargin : 0<margin) (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (ηseed : Character) (bs J εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤window) (hpad : 0<pad) (heshell : 0<εshell)
    (hbs : 1≤bs) (hJ : 0<J) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (N : ℕ)(Cs L₂ εproj : ℝ)(hCs : 1≤Cs)(hL₂ : 0≤L₂)(heproj : 0<εproj) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(_hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤bs → s.b₁=bp → s.b₂=bp →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤mesh → (∀j,w j≤mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) →
      (∀second j,Cycle62.Physical.sourcePlainScales s.toData.toSource second j≤Z^L) →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
    ∀(Mrow omega ξ : ℝ),Mmin≤Mrow → 0≤omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle62.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle62.Arithmetic.B*Mrow →
    let cell := Cycle62.Arithmetic.cellUpper (Cycle62.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle62.Arithmetic.amp cell
    ∀{Label : Type*}[Fintype Label],∀q : Label→Chain s,
    (∀j,(q j).k=1 ∨ (q j).k=6 ∨ (q j).k=7) →
    (∀j,3*amp/4≤Real.logb Z (normValue (q j).p)) →
    ∀g : (j : Label)→Geometry s (q j) Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : Label→RayFourExpansion.RayCharacter)(_hP : ∀j,(q j).R₂*(q j).E₂≠0)
      (_hPN : ∀j,(((q j).R₂*(q j).E₂).absNorm:ℝ)≤Z^Bmask),
    let src := fun j=>withHeight (q j).extracted ((g j).τ (χ j)) v
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(seed : Label→Ideal O)(hE₂ : ∀j,Supported (q j).E₂),(∀j,seed j∣(q j).E₂) →
    ∀Ds : Label→Finset (Ideal O),(∀j D,D∈Ds j→Squarefree D) →
      (∀j D,D∈Ds j→(D.absNorm:ℝ)≤Z^L₂) →
    ∀(P : Finset (Ideal O))(weight : Label→ℝ),(∀j,0≤weight j) →
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
  have hF : 0<F := by dsimp only [F]; positivity
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
  have hzpos : 0<Z := zero_lt_one.trans hZ
  let H := (p.control Sp)^2*(1+|v|+height)^degree
  let scalar := fun j=>coefficient j*
    Z^(errorRemoval (q j).p Z (q j).k-errorMoving (q j).p Z (q j).k)*
    ((q j).E₂.absNorm:ℝ)^(εshell-1)*
    Z^((g j).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (q j).k+
      εold+loss*(Fintype.card α:ℝ)+(omega+εpad*Mrow)/6+(3/4)*mesh+pad)
  have hcoef (j : Label) : 0≤coefficient j := by
    dsimp only [coefficient]
    have hv := volume_pos (src j)
    have hwj := hwgt j
    have hpc := Nat.cast_nonneg (α:=ℝ) P.card
    positivity
  have hscalar (j : Label) : 0≤scalar j := by
    have hc := hcoef j
    dsimp only [scalar]
    positivity
  have hH : 0≤H := by dsimp only [H]; positivity
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
    (A D₀ B L Cr ε : ℝ)(hA : 0≤A)(hD₀ : 0≤D₀)(hB : 0≤B)(hL : 0≤L)
    (hCr : 0<Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ : ℝ in atTop,1≤Z ∧
    ∀(slots : Finset α)(s : Input slots)(R seed : Ideal O)(hseed : Squarefree seed)
      (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(K Tsec ξ : ℝ)(hK : 0<K),
      Z^(-D₀)≤K → K≤Z^A → frequencyRadius Tsec Z ξ≤Cr*Z^L → sourceRadius s≤Z^B →
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
  have hrad : 0≤firstErrorTailRadius reflected first Z M V a δ reserve p k := by
    unfold firstErrorTailRadius errorCommonRadius
    exact Real.rpow_nonneg (zero_le_one.trans hz.1) _
  have hznonneg : 0≤Z := zero_le_one.trans hz.1
  unfold extractedErrorLabelScalar
  positivity

/-- Genuine dependent full-label payment absorbs its explicit finite
loss into the strict reserve of every extracted-prime branch. -/
theorem eventual_actual_error_dependent_saved_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0<lo) (hev : 0<εv) (hB : 0≤B) (he : 0<ε)
    (Mmin εaffine : ℝ)(hMmin : 0<Mmin) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
    ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤N → lo≤s.lower →
    ∀(reflected second : Bool)(T p exponent error εcommon M a δ reserve : ℝ),
      1≤T → p≤B → 0≤εcommon → Mmin≤M →
      error+εv+B*εcommon+ε≤64*geometryLossUnit Mmin εaffine →
    ∀(seed : Ideal O),Squarefree seed → seed≠0 → ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤exponent) →
    ∀(Ds : labels→Finset (Ideal O)),(∀l D,D∈Ds l→Squarefree D) →
      (∀l D,D∈Ds l→T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : labels)→Ds l→actualAllocations s.pools (if reflected then l.val.1.2 else l.val.1.1))
      (χ : (l : labels)→Ds l→Character)(t : ℝ),
      (∀l D,frozenCoefficient (alloc l D).val (if reflected then l.val.1.2 else l.val.1.1)
        Rfirst s.ν s.W s.P≠0) →
    let u : (l : labels)→(D : Ds l)→Input (liveIndices (alloc l D).val) := fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst (alloc l D) (χ l D) t
    ∀(P : Finset (Ideal O)),P.Nonempty → (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀l D,∀q : elementPool P,∀j I,I∈(u l D).slots j→IsCoprime (Ideal.span {q.val}) I) →
    let Bps := fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    ∀(υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→RayCharacter→Bps l D q i→Character)
      (vheight : ℝ)
      (children : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→RayCharacter→Bps l D q i→Finset FirstSourceLabel),
      (∀l D q i ψ b,∀v∈children l D q i ψ b,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,D.val∣v.1.1 ∧ D.val∣v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
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
  have hZ : 0<Z := by linarith [hz.1]
  have hb := hz.2 s hcard hlow reflected second T p exponent error εcommon M a δ reserve
    hT hp hecommon seed hs hs0 labels hsup heq hseed hnorm hrad hgeom Ds hDs hdyad
    Rfirst alloc χ t halloc P hne hprime hbad hslot υ vheight children hsup₂ heq₂ hdiv hnorm₂
  have hn : (0:ℝ)<seed.absNorm := norm_pos seed hs0
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
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_extracted_pool_cap
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_extracted_finite_pool_cap
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_extracted_projector_cap
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_normalized_scalar_identity
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_fixed_shell_factor
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_paid_error_complete_projector_family

#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_actual_error_dependent_saved_payment

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_original_block_scalar_subpower
