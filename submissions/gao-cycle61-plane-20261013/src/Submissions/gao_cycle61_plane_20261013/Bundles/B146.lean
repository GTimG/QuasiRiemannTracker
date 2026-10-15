/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B109
import Submissions.gao_cycle61_plane_20261013.Bundles.B113
import Submissions.gao_cycle61_plane_20261013.Bundles.B119
import Submissions.gao_cycle61_plane_20261013.Bundles.B123
import Submissions.gao_cycle61_plane_20261013.Bundles.B126
import Submissions.gao_cycle61_plane_20261013.Bundles.B137
import Submissions.gao_cycle61_plane_20261013.Bundles.B140
import Submissions.gao_cycle61_plane_20261013.Bundles.B142
import Submissions.gao_cycle61_plane_20261013.Bundles.B144
import Submissions.gao_cycle61_plane_20261013.Bundles.B145
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeElements

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorColumn; sha256 099259aab90d36bae25ec04e4ec3f17be3e9d6f9e1057dc2e27e393b60f22196 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                       
                                                    
                                     
                                                   
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
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
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment Cycle61FinalError
open CenteredMomentAmplificationErrorEnergy CenteredMomentSlotRatios
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]


open CenteredMomentCommonPairedSource
/-- The complete row sum precedes both supported allocation payments. -/
theorem error_common_column_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀(s : Input ι),s.upper≤ b → ∀C R seed : Ideal O,
      ∀hC : Supported C,seed∣C →
      ∀(Ds : Finset (Ideal O))(zs : Finset O)(weight : O→ℝ)(T Z pad E : ℝ),
      1≤ T → 1< Z → 0≤ E →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      ∀(keep : O→ Prop)(Φ : 𝓢(ℝ,ℂ))(rad : ℝ),0< rad →
      (∀z : O,keep z → 0≤(Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀z∈zs,0≤ weight z) → (∀z∈zs,keep z) →
      (∀z∈zs,weight z≤(Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        (commonData s C R B).toSource.allowance Z≤ pad) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        ∀D∈Ds,∀a∈(commonData s C R B).toSource.active D,∀second : Bool,
          finalPositiveEnergy (commonData s C R B) second D a keep Φ rad≤ E) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn s C hC R seed D z‖^2)≤
        K*s.toData.profileFactor*(∏i,s.M i)^2*E*(C.absNorm:ℝ)^(ε-1)*
          (2*T)^(3*ε)*Z^pad := by
  obtain ⟨Kc,hKc,hcommon⟩ := actual_common_low_energy (ι:=ι) b ε hε
  obtain ⟨Ke,hKe,hpoint⟩ := actual_common_column_extraction (ι:=ι) ε hε
  refine ⟨Ke*Kc,by positivity,?_⟩
  intro s hb C R seed hC hseed Ds zs weight T Z pad E hT hZ hE hDs keep Φ rad hrad hΦ
    hn hk hw hallow henergy
  have hh := hcommon s hb C R hC.1 Ds zs weight T Z pad E hT hZ hE hDs
    keep Φ rad hrad hΦ hk hw hallow henergy
  have hT0 : 0<2*T := by linarith
  have hmajor : (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn s C hC R seed D z‖^2)≤
      Ke*(2*T)^ε*(∑D∈Ds,∑z∈zs,weight z*commonRetainedCost s C R D z) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro D hD
    apply Finset.sum_le_sum
    intro z hz
    have hp := mul_le_mul_of_nonneg_left (hpoint s C hC R seed D hseed (hDs D hD).1 z) (hn z hz)
    apply hp.trans
    have hd := Real.rpow_le_rpow (Nat.cast_nonneg D.absNorm) (hDs D hD).2.2.le hε.le
    have hc := common_retained_cost_nonneg s C R D z
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hKe.le)
      (mul_nonneg (hn z hz) hc) using 1; ring_nf
  apply hmajor.trans
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤ Ke*(2*T)^ε)).trans_eq
  rw [show 3*ε=ε+2*ε by ring_nf,Real.rpow_add hT0 ε (2*ε)]
  ring_nf

theorem uniform_error_common_column_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀S : Finset ι,∀(s : Input S),s.upper≤ b → ∀C R seed : Ideal O,
      ∀hC : Supported C,seed∣C →
      ∀(Ds : Finset (Ideal O))(zs : Finset O)(weight : O→ℝ)(T Z pad E : ℝ),
      1≤ T → 1< Z → 0≤ E →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      ∀(keep : O→ Prop)(Φ : 𝓢(ℝ,ℂ))(rad : ℝ),0< rad →
      (∀z : O,keep z → 0≤(Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀z∈zs,0≤ weight z) → (∀z∈zs,keep z) →
      (∀z∈zs,weight z≤(Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        (commonData s C R B).toSource.allowance Z≤ pad) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        ∀D∈Ds,∀a∈(commonData s C R B).toSource.active D,∀second : Bool,
          finalPositiveEnergy (commonData s C R B) second D a keep Φ rad≤ E) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn s C hC R seed D z‖^2)≤
        K*s.toData.profileFactor*(∏i,s.M i)^2*E*(C.absNorm:ℝ)^(ε-1)*
          (2*T)^(3*ε)*Z^pad := by
  choose K hK hc using fun S : Finset ι=>error_common_column_energy (ι:=S) b ε hε
  let Kall := 1+∑S : Finset ι,K S
  have hpos : 0< Kall := by
    have hn : 0≤∑S : Finset ι,K S := Finset.sum_nonneg (fun S _=>(hK S).le)
    dsimp [Kall]; linarith
  refine ⟨Kall,hpos,?_⟩
  intro S s hb C R seed hC hseed Ds zs weight T Z pad E hT hZ hE hDs keep Φ rad hrad hΦ
    hn hk hw hallow henergy
  have hle : K S≤ Kall := by
    have hh := Finset.single_le_sum (fun S (_ : S∈Finset.univ)=>(hK S).le) (Finset.mem_univ S)
    dsimp [Kall]; linarith
  apply (hc S s hb C R seed hC hseed Ds zs weight T Z pad E hT hZ hE hDs
    keep Φ rad hrad hΦ hn hk hw hallow henergy).trans
  have hp := s.toData.profile_nonneg
  gcongr

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Actual extracted normalized columns with prime payment retained outside the complete frequency sum. -/
theorem actual_paid_error_column_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hL : 0≤ L) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hloss : 0< loss) (hmargin : 0< margin) (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (ηseed : Character) (bs J εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤ window) (hpad : 0< pad) (heshell : 0<εshell)
    (hbs : 1≤ bs) (hJ : 0< J) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=bp → s.b₂=bp →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^L) →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    q.k=1 ∨ q.k=6 ∨ q.k=7 → 3*amp/4≤ Real.logb Z (normValue q.p) →
    ∀g : Geometry s q Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask)
,
    let st := retainedState Z Bmask hZ (g.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    let src := withHeight q.extracted (g.τ χ) v
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(seed : Ideal O)(hE₂ : Supported q.E₂),seed∣q.E₂ →
    ∀(Ds : Finset (Ideal O))(T : ℝ),1≤ T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀(zs : Finset O)(weight : O→ℝ),(∀z∈zs,0≤ weight z) →
      (∀z∈zs,st.radial.keep z) →
      (∀z∈zs,weight z≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
    localErrorCost q.p (q.k-1)*Z^(-errorRemoval q.p Z q.k+errorMoving q.p Z q.k)*
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2)≤
      Cg*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(g.nominal+δwidth-Mrow*branchReserve q.k+εold+loss*(Fintype.card α:ℝ)+
          padding/6+(3/4)*mesh+pad) := by
  obtain ⟨degree,Sp,hprofiles⟩ := actual_paid_error_uniform (α:=α) M H hH W A B ap bp Bmask L lo hi
    Mcap εold loss margin hA hWs hW hB hap hap' hbp hBmask hL hMcap hεold hloss hmargin hbeta
    ηseed bs J εwidth εpad Mmin hbs hJ hew hep hmin
  choose Kss hKss hcolumns using fun S : Finset α=>
    uniform_error_common_column_energy (ι:=S) bs εshell heshell
  let Kall := 1+∑S : Finset α,Kss S
  have hKall : 0< Kall := by
    have hn : 0≤∑S : Finset α,Kss S := Finset.sum_nonneg (fun S _=>(hKss S).le)
    dsimp [Kall]; linarith
  have hKle (S : Finset α) : Kss S≤ Kall := by
    have hh := Finset.single_le_sum (fun S (_ : S∈Finset.univ)=>(hKss S).le) (Finset.mem_univ S)
    dsimp [Kall]; linarith
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hprofiles η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kall*C,by positivity,?_⟩
  filter_upwards [hbound,Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (((Fintype.card α:ℝ)*window+2*Real.log bp)/pad))] with Z hZ hallow
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm
    hσlo hσhi hheight hfreq hOrig hwin Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp hk hprime g χ hP hPN st src δwidth padding p hp₁ hp₂ seed hE₂ hseed
    Ds T hT hDs zs weight hnonneg hkeep hweight
  let exponent := g.nominal+δwidth-Mrow*branchReserve q.k+εold+loss*(Fintype.card α:ℝ)+
    padding/6+(3/4)*mesh
  let E := C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
    (1+|v|+height)^degree*Z^(exponent+errorRemoval q.p Z q.k)
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hE : 0≤ E := by dsimp [E]; positivity
  have henergy (B₂ : actualAllocations src.pools q.E₂)(hn : commonScalar src q.E₂ q.R₂ B₂≠0)
      (D : Ideal O)(hD : D∈Ds)
      (alloc : Allocation D (Finset.univ : Finset (liveIndices B₂.val⊕Fin 2)))
      (_halloc : alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D)(second : Bool) :
      finalPositiveEnergy (commonData src q.E₂ q.R₂ B₂) second D alloc
        st.radial.keep st.radial.profile st.radial.scale≤ E := by
    let q' : Chain s := { q with B₂:=B₂ }
    have hB₂ : frozenCoefficient B₂.val q.E₂ q.R₂ q.extracted.ν q.extracted.W q.extracted.P≠0 :=
      right_ne_zero_of_mul hn
    let g' : Geometry s q' Z Mrow amp omega ξ bs J (Fintype.card α) :=
      { g with second_nonzero:=hB₂ }
    have he := (hZ.2 hZone s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂
      hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig Mrow omega ξ hMmin hω hξ hMcap'
      hz haff q' hk hprime g' χ hP hPN second D alloc p hp₁ hp₂).1
    change finalPositiveEnergy (commonData src q.E₂ q.R₂ B₂) second D alloc
      st.radial.keep st.radial.profile st.radial.scale≤
      C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
        (1+|v|+height)^degree*Z^(g.nominal+δwidth+errorRemoval q.p Z q.k-
          Mrow*branchReserve q.k+εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh) at he
    apply he.trans_eq
    dsimp only [E,exponent]
    congr 1
    ring_nf
  have hallowance (B₂ : actualAllocations src.pools q.E₂)
      (_hn : commonScalar src q.E₂ q.R₂ B₂≠0) :
      (commonData src q.E₂ q.R₂ B₂).toSource.allowance Z≤ pad := by
    have hh := fixed_source_allowance (Fintype.card α) window bp hwindow hbp
      (commonData src q.E₂ q.R₂ B₂)
      ((live_card_le B₂.val).trans ((live_card_le q.Bp.val).trans (live_card_le q.B₁.val)))
      (fun j=>hwin j.val.val.val) hsb₁.le hsb₂.le Z hZone
    have hfixed : ((Fintype.card α:ℝ)*window+2*Real.log bp)/Real.log Z≤ pad :=
      (div_le_iff₀ (Real.log_pos hZone)).mpr
        (by nlinarith [(div_le_iff₀ hpad).mp hallow])
    have hpaid := hh.trans hfixed
    have hp : 0≤ Cycle61.Physical.plainClipAllowance Z
        ![(commonData src q.E₂ q.R₂ B₂).b₁,(commonData src q.E₂ q.R₂ B₂).b₂] := by
      unfold Cycle61.Physical.plainClipAllowance
      exact Finset.sum_nonneg (fun j _=>Real.logb_nonneg hZone (le_max_left _ _))
    linarith
  have hcolumn := hcolumns (liveIndices q.B₁.val) (liveIndices q.Bp.val) src hsupper
    q.E₂ q.R₂ seed hE₂ hseed Ds zs weight T Z pad E hT hZone hE hDs
    st.radial.keep st.radial.profile st.radial.scale st.radial.scale_pos
    (fun z _=>st.radial.nonneg z) hnonneg hkeep hweight hallowance henergy
  have hlarge : (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2)≤
      (Kall*C*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell))*
          Z^((exponent+pad)+errorRemoval q.p Z q.k) := by
    apply hcolumn.trans
    calc
      _ ≤ Kall*src.toData.profileFactor*(∏j,src.M j)^2*E*
          (q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*Z^pad := by
        have hp := src.toData.profile_nonneg
        gcongr
        exact hKle _
      _ = _ := by
        have hpow : Z^(exponent+errorRemoval q.p Z q.k)*Z^pad=
            Z^((exponent+pad)+errorRemoval q.p Z q.k) := by
          rw [←Real.rpow_add (zero_lt_one.trans hZone)]
          congr 1
          ring_nf
        dsimp only [E]
        linear_combination Kall*src.toData.profileFactor*(∏j,src.M j)^2*C*
          QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
          (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*hpow
  exact normalize_error_energy q.p q.hp Z hZone q.k hk _ _ _
    (by have hp:=src.toData.profile_nonneg; positivity) hlarge

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_common_column_energy
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_error_common_column_energy
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_paid_error_column_uniform

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorColumn -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorColumnFamily; sha256 1ba624b244314b045945737f0a53bcc7217f51885aaaf6454771f9b0f324e17e -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                       
                                                            
                                                          
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentPrimeElements
open CenteredMomentCommonPairedSource Cycle61FinalError Cycle61FinalNatural
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentRestrictedEnergy
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment Cycle61FinalError
open CenteredMomentAmplificationErrorEnergy CenteredMomentSlotRatios
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstMixedRightTransport
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondCanonical CenteredMomentCompleteCommon
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentChildRows CenteredMomentAmplificationRadicalFamily RayFourExpansion
open CenteredMomentCommonRawScale CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildSourceCaps CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance errorColumnFamilyDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The entire nonexceptional frequency set supplies its own keep and
unit radial majorant; no row energy or majorization input is required. -/
theorem actual_error_complete_row_admission (s : Input α) (q : Chain s)
    (Z Mrow amp omega ξ b J : ℝ)
    (g : Geometry s q Z Mrow amp omega ξ b J (Fintype.card α))
    (Bmask : ℝ) (hZ : 1< Z) (χ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hP : q.R₂*q.E₂≠0) (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask)
    (z : O) (hz : z∈partRows false q.υ χ Q fixedBadMask g.C g.D g.U g.radius) :
    let st := retainedState Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    st.radial.keep z ∧ 1≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re := by
  refine ⟨?_,?_⟩
  · have hne : nonexceptional q.υ χ Q fixedBadMask
        (commonFrequencyGenerator g.C g.D*nonunitFrequencyGenerator g.C g.D g.U) z := by
      exact (Finset.mem_filter.mp hz).2
    exact (actual_nonexceptional_keep g.family g.radius Z Bmask hZ χ Q (q.R₂*q.E₂) hP hPN
      fixedBadMask z fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hne
  · rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact actual_partRows_majorized Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN
      q.υ χ fixedBadMask g.radius g.C g.D g.U z hz

/-- Removing the paid-row normalization keeps its exact compensating
prime power inside the source-normalized family. -/
theorem error_column_paid_weight_cancel (p : O) (k : ℕ) (Z V c energy : ℝ)
    (hZ : 0< Z) :
    (c*localErrorCost p (k-1)/V)*energy=
      (c/V*Z^(errorRemoval p Z k-errorMoving p Z k))*
        (localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*energy) := by
  have hp : Z^(errorRemoval p Z k-errorMoving p Z k)*
      Z^(-errorRemoval p Z k+errorMoving p Z k)=1 := by
    rw [←Real.rpow_add hZ]
    simp only [show errorRemoval p Z k-errorMoving p Z k+
      (-errorRemoval p Z k+errorMoving p Z k)=0 by ring,Real.rpow_zero]
  linear_combination -(c/V*localErrorCost p (k-1)*energy)*hp

/-- Exact prime averaging retains the three separate reserves. Its
cardinality cancels against the original amplifier denominator. -/
theorem actual_error_reserve_average (P : Finset (Ideal O)) (hne : P.Nonempty)
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes) (Z M : ℝ) :
    (56/(P.card:ℝ))*(∑_p : elementPool P,∑i : Fin 3,
      16*(errorIndex i+2:ℝ)*Z^(-M*branchReserve (errorIndex i+1)))=
      56*∑i : Fin 3,16*(errorIndex i+2:ℝ)*Z^(-M*branchReserve (errorIndex i+1)) := by
  have hn : (0:ℝ)< P.card := by exact_mod_cast hne.card_pos
  have hc : Fintype.card (elementPool P)=P.card := by
    rw [Fintype.card_coe,elementPool_card P hp hbad]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc]
  field_simp

/-- Exact restoration of the original extracted weight. -/
theorem error_column_paid_restore (p : O) (k : ℕ) (Z coefficient energy C envelope : ℝ)
    (hZ : 0< Z) (hc : 0≤ coefficient)
    (hpaid : localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*energy≤ C*envelope) :
    coefficient*localErrorCost p (k-1)*energy≤
      C*(coefficient*Z^(errorRemoval p Z k-errorMoving p Z k)*envelope) := by
  have hinv : Z^(errorRemoval p Z k-errorMoving p Z k)*
      Z^(-errorRemoval p Z k+errorMoving p Z k)=1 := by
    rw [←Real.rpow_add hZ]
    simp only [show errorRemoval p Z k-errorMoving p Z k+
      (-errorRemoval p Z k+errorMoving p Z k)=0 by ring,Real.rpow_zero]
  calc
    _ = (coefficient*Z^(errorRemoval p Z k-errorMoving p Z k))*
        (localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*energy) := by
      linear_combination -(coefficient*localErrorCost p (k-1)*energy)*hinv
    _ ≤ (coefficient*Z^(errorRemoval p Z k-errorMoving p Z k))*(C*envelope) :=
      mul_le_mul_of_nonneg_left hpaid (mul_nonneg hc (Real.rpow_nonneg hZ.le _))
    _ = _ := by ring

/-- A complete finite column family, with its literal source volume and
amplifier denominator still present. The energies come from the genuine
paid error theorem rather than an additional family estimate. -/
theorem actual_paid_error_column_family_uniform {Label : Type*} [Fintype Label]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (hap : 0< ap) (hap' : ap≤1/4) (hbp : 1≤ bp)
    (hBmask : 0≤ Bmask) (hL : 0≤ L) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hloss : 0< loss) (hmargin : 0< margin) (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (ηseed : Character) (bs J εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤ window) (hpad : 0< pad) (heshell : 0<εshell)
    (hbs : 1≤ bs) (hJ : 0< J) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
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
    ∀q : Label→ Chain s,
    (∀j,(q j).k=1 ∨ (q j).k=6 ∨ (q j).k=7) →
    (∀j,3*amp/4≤ Real.logb Z (normValue (q j).p)) →
    ∀g : (j : Label)→ Geometry s (q j) Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : Label→ RayFourExpansion.RayCharacter)(hP : ∀j,(q j).R₂*(q j).E₂≠0)
      (hPN : ∀j,(((q j).R₂*(q j).E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := fun j=>retainedState Z Bmask hZ ((g j).τ (χ j)) (internalQ Q η₀)
      ((q j).R₂*(q j).E₂) (hP j) (hPN j) (g j).radius (g j).C (g j).D (g j).U
    let src := fun j=>withHeight (q j).extracted ((g j).τ (χ j)) v
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(seed : Label→ Ideal O)(hE₂ : ∀j,Supported (q j).E₂),(∀j,seed j∣(q j).E₂) →
    ∀(Ds : Label→ Finset (Ideal O))(T : Label→ℝ),(∀j,1≤ T j) →
      (∀j,∀D∈Ds j,Squarefree D ∧ T j≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T j) →
    ∀(P : Finset (Ideal O))(weight : Label→ℝ),(∀j,0≤ weight j) →
    let coefficient := fun j=>(56/(P.card:ℝ))*weight j*16*((q j).k+1:ℝ)/volume (src j)
    let rows := fun j=>partRows false (q j).υ (χ j) (internalQ Q η₀)
      fixedBadMask (g j).C (g j).D (g j).U (g j).radius
    (∑j,coefficient j*localErrorCost (q j).p ((q j).k-1)*
      (∑D∈Ds j,∑z∈rows j,‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2))≤
      Cg*∑j,coefficient j*Z^(errorRemoval (q j).p Z (q j).k-errorMoving (q j).p Z (q j).k)*
        ((src j).toData.profileFactor*(∏a,(src j).M a)^2*
          QuadraticInitialBound.diagonalControl (st j).radial.profile*(p.control Sp)^2*
          (1+|v|+height)^degree*((q j).E₂.absNorm:ℝ)^(εshell-1)*(2*T j)^(3*εshell)*
          Z^((g j).nominal+εwidth*Mrow+ξ/2-Mrow*branchReserve (q j).k+
            εold+loss*(Fintype.card α:ℝ)+(omega+εpad*Mrow)/6+(3/4)*mesh+pad)) := by
  obtain ⟨degree,Sp,hbound⟩ := actual_paid_error_column_uniform (α:=α) M H hH W A B ap bp
    Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp hBmask hL hMcap
    hεold hloss hmargin hbeta ηseed bs J εwidth εpad Mmin window pad εshell
    hwindow hpad heshell hbs hJ hew hep hmin
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hZs⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hZs] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm
    hσlo hσhi hheight hfreq hOrig hwin Mrow omega ξ hMmin hω hξ hMcap' hslot haff
    cell amp q hk hprime g χ hP hPN st src p hp₁ hp₂ seed hE₂ hseed Ds T hT hDs P weight
    hwgt coefficient rows
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hrow (z : O) (hz : z∈rows j) := actual_error_complete_row_admission s (q j)
    Z Mrow amp omega ξ bs J (g j) Bmask hZ (χ j) (internalQ Q η₀) (hP j) (hPN j) z hz
  have hcol := hz.2 hZ s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂ hw hwL
    hmesh hwm hσlo hσhi hheight hfreq hOrig hwin Mrow omega ξ hMmin hω hξ hMcap'
    hslot haff (q j) (hk j) (hprime j) (g j) (χ j) (hP j) (hPN j) p hp₁ hp₂
    (seed j) (hE₂ j) (hseed j) (Ds j) (T j) (hT j) (hDs j) (rows j) (fun _=>1)
    (fun _ _=>zero_le_one) (fun z hz=>(hrow z hz).1) (fun z hz=>(hrow z hz).2)
  simp only [one_mul] at hcol
  have hc : 0≤ coefficient j := by
    dsimp only [coefficient]
    have hv := volume_pos (src j)
    have hn : 0≤(P.card:ℝ) := Nat.cast_nonneg _
    have hwj := hwgt j
    positivity
  apply error_column_paid_restore (q j).p (q j).k Z (coefficient j) _ Cg _
    (zero_lt_one.trans hZ) hc
  convert hcol using 1
  dsimp only [src,st]
  ring_nf

/-- Every actual nonzero extracted block supplies the supported label and
complete-row gates for the family theorem, in either first orientation. -/
theorem actual_geometry_error_column_gates (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂) (second : Bool)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C))
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ) fixedBadMask p
      (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C) ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).R ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).ν ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).W ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).P≠0) :
    let chain := geometryErrorActualChain reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hp hcop hw₁ hw₂ n second B₂
    let g := geometryErrorActualGeometry reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hp hcop hw₁ hw₂ n second B₂ ψ hυ hf₁ hf₂
    Supported chain.E₂ ∧ (chain.k=1 ∨ chain.k=6 ∨ chain.k=7) ∧
    ∀(Bmask : ℝ)(χ : RayFourExpansion.RayCharacter)(Q : Ideal O)
      (hP : chain.R₂*chain.E₂≠0)(hPN : ((chain.R₂*chain.E₂).absNorm:ℝ)≤ Z^Bmask)
      (z : O), z∈partRows false chain.υ χ Q fixedBadMask g.C g.D g.U g.radius →
    let st := retainedState Z Bmask hZ (g.τ χ) Q (chain.R₂*chain.E₂) hP hPN g.radius g.C g.D g.U
    st.radial.keep z ∧ 1≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re := by
  dsimp only
  let chain := geometryErrorActualChain reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hp hcop hw₁ hw₂ n second B₂
  let g := geometryErrorActualGeometry reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hp hcop hw₁ hw₂ n second B₂ ψ hυ hf₁ hf₂
  refine ⟨?_,?_,?_⟩
  · rcases g.label with hl|hr
    · exact hl.symm ▸ g.hC
    · exact hr.symm ▸ g.hD
  · change errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7
    rcases errorIndex_cases i with hi|hi|hi <;> simp [hi]
  · intro Bmask χ Q hP hPN z hz
    exact actual_error_complete_row_admission s chain Z Mrow amp (frequencyLoss Z 32 ξ+reserve)
      ξ b (fixedFactor:ℝ) g Bmask hZ χ Q hP hPN z hz

/-- The literal extracted retained datum supplies both projector divisibilities. -/
theorem actual_geometry_error_seed_gates (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v) :
    let datum := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    datum.seed∣datum.C ∧ datum.seed∣datum.D := by
  have hg := actual_retained_block_gates (liveIndices (errorActiveAllocation (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp).val)
    (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v) ((R*(geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))*(Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) bin)
      (fun _=>logAnnulus) q.1.val q.1.property) hw₁ hw₂ (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z Mrow amp ξ reserve hZ bin q p i) n
  exact ⟨hg.1,hg.2.1⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_complete_row_admission
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_column_paid_weight_cancel
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_reserve_average

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_paid_error_column_family_uniform

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_column_gates

#print axioms OAI.SevenEighths.Cycle61InitialMass.error_column_paid_restore

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_seed_gates

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorColumnFamily -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorTail; sha256 2e935142079b9d056d435101b7fbdb7b29e0eae580790a39ed2e552b5ebef74b -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                     
                                                            
                                                       
                                                                      
                                                                          

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentSupportedTailAggregate CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationErrorEnergy
open CenteredMomentPrimeElements RayFourExpansion ConcretePrimeRowBridge CenteredMomentFirstAnnularInput
local notation "O" => HeckeFamily.O
local instance errorTailDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- Constants are chosen over the finite original slot dictionary before
both allocations, both characters, and both independent heights. -/
theorem actual_twice_child_second_tail {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi B ξ saving : ℝ)(hCs : 1≤ Cs)(hb : 0≤ b)
    (hlo : 0< lo)(hhi : 0≤ hi)(hB : 0≤ B)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(s : Input α),Fintype.card α≤ N → (∀i,s.M i≤ Cs) → (∀i,s.hi i≤ b) →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(C R seed : Ideal O)(B₁ : actualAllocations s.pools C)(χ : Character)(t : ℝ)
      (Q : Ideal O)(k : ℕ)
      (Bp : actualAllocations (child s C R B₁ χ t).pools (Q^k))
      (υ : Character)(v : ℝ)(Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),0< K →
    let u := twiceChild s C R B₁ χ t Q k Bp υ v
    volume u≤ Z^B → Tsec≤ Z^B → (volume u)^2/K≤ Tsec →
    ‖secondDiscardedEnergy u.η u.t (original u ((R*C)*(Q^k)) seed).columns
      (original u ((R*C)*(Q^k)) seed).beta Φ K Tsec Z ξ‖/volume u≤
      Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  have hex (J : Finset α) := actual_common_child_second_tail (α:=J)
    N Cs b lo hi B ξ saving hCs hb hlo hhi hB hξ
  choose F D hD hbound using hex
  let F₀ := Finset.univ.biUnion F
  let C₀ := ∑J : Finset α,D J
  refine ⟨F₀,C₀,Finset.sum_pos (fun J _=>hD J) Finset.univ_nonempty,?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
  refine ⟨(hz ∅).1,?_⟩
  intro s hn hm hs p hp₁ hp₂ C R seed B₁ χ t Q k Bp υ v Φ K Tsec hK u hV hT hnom
  have hh := (hz (liveIndices B₁.val)).2 (child s C R B₁ χ t)
    ((live_card_le B₁.val).trans hn) (fun i=>hm i.val) (fun i=>hs i.val) p hp₁ hp₂
    (Q^k) (R*C) seed Bp υ v Φ K Tsec hK hV hT hnom
  have hCJ : D (liveIndices B₁.val)≤ C₀ := Finset.single_le_sum
    (fun J _=>(hD J).le) (Finset.mem_univ _)
  have hF := (Finset.sup_mono
    (Finset.subset_biUnion_of_mem F (Finset.mem_univ (liveIndices B₁.val))) :
    (F (liveIndices B₁.val)).sup (schwartzSeminormFamily ℝ ℝ ℂ)≤ F₀.sup (schwartzSeminormFamily ℝ ℝ ℂ)) Φ
  have hzpos : 0< Z := zero_lt_one.trans (hz ∅).1
  have hC₀ : 0< C₀ := Finset.sum_pos (fun J _=>hD J) Finset.univ_nonempty
  apply hh.trans
  gcongr

/-- The literal error radius stays in a polynomial box. The hypothesis
on the prime is only its genuine nonzero ideal norm. -/
theorem actual_error_radius_box (reflected : Bool)(C D E : Ideal O)
    (hC : C≠0)(hD : D≠0)(hE : E≠0)
    (heq : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (Z M V a δ reserve B : ℝ)(hZ : 1< Z)(hV : 0< V)(hB : 0≤ B)
    (hM : 0≤ M)(hMB : M≤ B)(ha : 0≤ a)(haB : a≤ B)(hδ : 0≤δ)(hr : 0≤ reserve)
    (hω : δ+reserve≤ B)(hA : |Real.logb Z V|≤ B)
    (hc : Real.logb Z (C.absNorm:ℝ)≤ B)(hd : Real.logb Z (D.absNorm:ℝ)≤ B)
    (he : Real.logb Z (E.absNorm:ℝ)≤ B)
    (hactive : Real.logb Z (Ideal.span {activeConductor C D}).absNorm≤ B)
    (q : O)(hq : q≠0)(k : ℕ)(hk : 1≤ k) :
    Z^(-5*B)≤ errorCommonRadius Z (Real.logb Z ((if reflected then C else D).absNorm:ℝ))
      (nominalLog C D E (Z^M) V Z) (Real.logb Z ((if reflected then D else C).absNorm:ℝ))
      (3*a) δ reserve q k ∧
    errorCommonRadius Z (Real.logb Z ((if reflected then C else D).absNorm:ℝ))
      (nominalLog C D E (Z^M) V Z) (Real.logb Z ((if reflected then D else C).absNorm:ℝ))
      (3*a) δ reserve q k≤ Z^(12*B) := by
  have hz : 0< Z := zero_lt_one.trans hZ
  have hc0 := Real.logb_nonneg hZ (norm_ge_one C hC)
  have hd0 := Real.logb_nonneg hZ (norm_ge_one D hD)
  have he0 := Real.logb_nonneg hZ (norm_ge_one E hE)
  have hr0 : 0≤ Real.logb Z (Ideal.span {activeConductor C D}).absNorm :=
    Real.logb_nonneg hZ (norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr
      (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have hNc := norm_pos C hC
  have hNd := norm_pos D hD
  have hNe := norm_pos E hE
  have hNr := active_norm_pos C D
  have hn : nominalLog C D E (Z^M) V Z=
      Real.logb Z (E.absNorm:ℝ)+Real.logb Z (Ideal.span {activeConductor C D}).absNorm+
      2*Real.logb Z V-M-Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ) := by
    unfold nominalLog
    rw [nominal_equal_support C D E hC hD heq]
    simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow,
      Real.logb_rpow hz hZ.ne']
    ring
  have hq0 : 0≤ Real.logb Z (normValue q) := by
    apply Real.logb_nonneg hZ
    exact norm_ge_one (Ideal.span {q}) (Ideal.span_singleton_eq_bot.not.mpr hq)
  have hmove : errorMoving q Z k≤2*errorRemoval q Z k := by
    have hkR : (1:ℝ)≤ k := by exact_mod_cast hk
    unfold errorMoving errorRemoval
    split_ifs <;> nlinarith
  have hnomlo : -5*B≤ nominalLog C D E (Z^M) V Z := by rw [hn];linarith [(abs_le.mp hA).1]
  have hnomhi : nominalLog C D E (Z^M) V Z≤4*B := by rw [hn];linarith [(abs_le.mp hA).2]
  unfold errorCommonRadius
  constructor <;> apply Real.rpow_le_rpow_of_exponent_le hZ.le
  · linarith [le_max_right
      (Real.logb Z ((if reflected then C else D).absNorm:ℝ)-
        Real.logb Z ((if reflected then D else C).absNorm:ℝ)-2*errorRemoval q Z k+errorMoving q Z k) 0]
  · have hmax : max (Real.logb Z ((if reflected then C else D).absNorm:ℝ)-
        Real.logb Z ((if reflected then D else C).absNorm:ℝ)-2*errorRemoval q Z k+errorMoving q Z k) 0≤ B := by
      apply max_le _ hB
      cases reflected <;> simp only [Bool.false_eq_true,ite_true,ite_false] <;> linarith
    linarith

/-- The literal twice-child Fourier scale, including the actual extracted
prime power. This scale admits the true source without an energy premise. -/
def firstErrorTailFourier (N : ℕ)(b V : ℝ)(C : Ideal O)(q : O)(k : ℕ)(radius : ℝ) : ℝ :=
  (b^N*V/(C.absNorm:ℝ)/((Ideal.span {q}).absNorm:ℝ)^k)^2/radius


/-- True twice-child volume and admissibility, using the retained first
coefficient and coprimality of the extracted prime with the surviving slots. -/
theorem actual_error_tail_scale_caps {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(b Z B rad : ℝ)(hb : 1≤ b)(hZ : 1< Z)(hB : 0≤ B)
    (hbZ : b^N≤ Z)(hr : Z^(-5*B)≤ rad)
    (s : Input α)(hn : Fintype.card α≤ N)(hs : s.upper≤ b)(hV : volume s≤ Z^B)
    (C R : Ideal O)(B₁ : actualAllocations s.pools C)(χ : Character)(t : ℝ)
    (hne : frozenCoefficient B₁.val C R s.ν s.W s.P≠0)
    (q : O)(hq : q≠0)(k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B₁ χ t).slots i,IsCoprime (Ideal.span {q}) I)
    (Bp : actualAllocations (child s C R B₁ χ t).pools ((Ideal.span {q})^k))
    (υ : Character)(v : ℝ) :
    let u := twiceChild s C R B₁ χ t (Ideal.span {q}) k Bp υ v
    volume u≤ Z^(7*B+2) ∧
      firstErrorTailFourier N b (volume s) C q k rad≤ Z^(7*B+2) ∧
      (volume u)^2/rad≤ firstErrorTailFourier N b (volume s) C q k rad := by
  intro u
  have hz : 0< Z := zero_lt_one.trans hZ
  have hqN : (1:ℝ)≤(Ideal.span {q}).absNorm :=
    norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hq)
  have hqpow := one_le_pow₀ (n:=k) hqN
  have hC := norm_ge_one C (allocation_ne s C B₁)
  have hh := common_volume_le N b hb s hn hs C R B₁ χ t hne
  have hv : volume u≤ b^N*volume s/(C.absNorm:ℝ)/((Ideal.span {q}).absNorm:ℝ)^k := by
    change volume (child (child s C R B₁ χ t) ((Ideal.span {q})^k) (R*C) Bp υ v)≤ _
    rw [child_volume _ _ (Ideal.span_singleton_eq_bot.not.mpr hq) k hslot]
    exact div_le_div_of_nonneg_right hh (by positivity)
  have hnum : 0≤ b^N*volume s/(C.absNorm:ℝ)/((Ideal.span {q}).absNorm:ℝ)^k :=
    div_nonneg (div_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le)
      (zero_le_one.trans hC)) (by positivity)
  have hnum₁ : 0≤ b^N*volume s/(C.absNorm:ℝ) :=
    div_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le) (zero_le_one.trans hC)
  have hfactor : b^N*volume s/(C.absNorm:ℝ)/((Ideal.span {q}).absNorm:ℝ)^k≤ Z^(B+1) := by
    calc
      _≤ b^N*volume s/(C.absNorm:ℝ) := div_le_self hnum₁ hqpow
      _≤ b^N*volume s := div_le_self (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (volume_pos s).le) hC
      _≤ Z*Z^B := mul_le_mul hbZ hV (volume_pos s).le hz.le
      _=Z^(B+1) := by rw [Real.rpow_add hz,Real.rpow_one];ring
  have hrad : 0< rad := (Real.rpow_pos_of_pos hz _).trans_le hr
  refine ⟨(hv.trans hfactor).trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)),?_,?_⟩
  · unfold firstErrorTailFourier
    calc
      _≤(Z^(B+1))^2/Z^(-5*B) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ hnum hfactor 2)
          (Real.rpow_pos_of_pos hz _) hr
      _=Z^(7*B+2) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1;ring
  · unfold firstErrorTailFourier
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (volume_pos u).le hv 2) hrad.le

/-- Literal extracted-prime discarded source with arbitrary saving.
The input is an actual first label with its genuine geometric norm caps;
there is no tail, source-energy, or Fourier-admissibility premise. -/
theorem eventual_actual_first_label_error_tail {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi B ξ saving : ℝ)(hCs : 1≤ Cs)(hb : 1≤ b)
    (hlo : 0< lo)(hhi : 0≤ hi)(hB : 0≤ B)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(s : Input α)(R seed : Ideal O),Fintype.card α≤ N → (∀i,s.M i≤ Cs) → s.upper≤ b →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(M a δ reserve t : ℝ)(hZ : 1< Z),0≤ M → M≤ B → 0≤ a → a≤ B → 0≤δ → 0≤ reserve →
      δ+reserve≤ B → |Real.logb Z (volume s)|≤ B →
    ∀(reflected : Bool)(l : FirstSourceLabel),Supported l.1.1 → Supported l.1.2 →
      CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2 →
      Real.logb Z (l.1.1.absNorm:ℝ)≤ B → Real.logb Z (l.1.2.absNorm:ℝ)≤ B →
      Real.logb Z (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm≤ B →
      Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm≤ B →
    let C := if reflected then l.1.2 else l.1.1
    ∀(B₁ : actualAllocations s.pools C)(χ : Character),
      frozenCoefficient B₁.val C R s.ν s.W s.P≠0 →
    ∀(q : O),q≠0 → ∀k : ℕ,1≤ k →
      (∀i,∀I∈(child s C R B₁ χ t).slots i,IsCoprime (Ideal.span {q}) I) →
    ∀(Bp : actualAllocations (child s C R B₁ χ t).pools ((Ideal.span {q})^k))
      (υ : Character)(v : ℝ)(Φ : 𝓢(ℝ,ℂ)),
    let u := twiceChild s C R B₁ χ t (Ideal.span {q}) k Bp υ v
    let rad := errorCommonRadius Z (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
      (nominalLog l.1.1 l.1.2 (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val}) (Z^M) (volume s) Z)
      (Real.logb Z (C.absNorm:ℝ)) (3*a) δ reserve q k
    let Tsec := firstErrorTailFourier N b (volume s) C q k rad
    ‖secondDiscardedEnergy u.η u.t (original u ((R*C)*(Ideal.span {q})^k) seed).columns
      (original u ((R*C)*(Ideal.span {q})^k) seed).beta Φ rad Tsec Z ξ‖/volume u≤
      Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨F,Ct,hCt,hbound⟩ := actual_twice_child_second_tail (α:=α) N Cs b lo hi (7*B+2) ξ
    (saving+12*B) hCs (zero_le_one.trans hb) hlo hhi (by positivity) hξ
  refine ⟨F,Ct,hCt,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (b^N)] with Z hz hbZ
  refine ⟨hz.1,?_⟩
  intro s R seed hn hm hs p hp₁ hp₂ M a δ reserve t hZ hM hMB ha haB hδ hreserve hω hA
    reflected l hC hD heq hc hd he hactive C B₁ χ hne q hq k hk hslot Bp υ v Φ u rad Tsec
  have hbox := actual_error_radius_box reflected l.1.1 l.1.2
    (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val})
    hC.1 hD.1 (subsetGenerator_supported l.1.1 l.1.2 hC l.2.val).1 heq
    Z M (volume s) a δ reserve B hZ (volume_pos s) hB hM hMB ha haB hδ hreserve hω hA
    hc hd he hactive q hq k hk
  change Z^(-5*B)≤ rad ∧ rad≤ Z^(12*B) at hbox
  have hrhi := hbox.2
  have hvol : volume s≤ Z^B := (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (abs_le.mp hA).2
  have hcaps := actual_error_tail_scale_caps N b Z B rad hb hZ hB hbZ hbox.1 s hn hs hvol C R B₁ χ t hne
    q hq k hslot Bp υ v
  have hrad : 0< rad := (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).trans_le hbox.1
  have hh := hz.2 s hn hm (fun i=>(s.upper_ge i).trans hs) p hp₁ hp₂ C R seed B₁ χ t
    (Ideal.span {q}) k Bp υ v Φ rad Tsec hrad hcaps.1 hcaps.2.1 hcaps.2.2
  apply hh.trans
  calc
    _≤ Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(12*B)*Z^(-(saving+12*B)) := by gcongr
    _=_ := by rw [mul_assoc,←Real.rpow_add (zero_lt_one.trans hZ),show 12*B+(-(saving+12*B))=-saving by ring]

/-- Source support alone supplies all four actual first-label norm gates.
These are uniform in the selected column and orientation. -/
theorem actual_geometry_error_tail_label_caps {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(R seed : Ideal O)(M Z ξ B : ℝ)(hZ : 1< Z)(hK : 0< Z^M)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)) :
    let l := geometryFirstLabel s R seed (Z^M) Z ξ hK key j
    Real.logb Z (l.1.1.absNorm:ℝ)≤ B ∧ Real.logb Z (l.1.2.absNorm:ℝ)≤ B ∧
      Real.logb Z (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm≤ B ∧
      Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm≤ B := by
  intro l
  have hlog (i : Fin 5) : geometryExponents s R seed (Z^M) Z ξ j.1.val i≤ B := by
    have hh := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val i
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hh.1)).mpr hh.2
  exact ⟨hlog 0,hlog 1,hlog 4,hlog 3⟩

def firstErrorTailRadius (reflected : Bool)(l : FirstSourceLabel)
    (Z M V a δ reserve : ℝ)(q : O)(k : ℕ) : ℝ :=
  errorCommonRadius Z (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
    (nominalLog l.1.1 l.1.2 (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
      (fun P:CommonIndex l.1.1 l.1.2=>P.val) l.2.val}) (Z^M) V Z)
    (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) (3*a) δ reserve q k

/-- The radius used by the literal error split is exactly the physical
first-label radius used by the twice-child tail theorem. -/
theorem actual_geometry_error_tail_radius {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(R seed : Ideal O)(Z M ξ a δ reserve : ℝ)(hK : 0< Z^M)
    (reflected : Bool)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key))(q : O)(k : ℕ) :
    let g := geometryBranch reflected s R seed (Z^M) Z ξ hK key j
    errorCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z) g.cLog (3*a) δ reserve q k=
      firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
        Z M (volume s) a δ reserve q k := by
  rfl

lemma actual_local_error_cost_le_one (q : O)(hq : q≠0)(n : ℕ) : localErrorCost q n≤1 := by
  have hN : (1:ℝ)≤(Ideal.span {q}).absNorm := norm_ge_one _ (Ideal.span_singleton_eq_bot.not.mpr hq)
  have hi : ((Ideal.span {q}).absNorm:ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ hN
  have hi0 : 0≤((Ideal.span {q}).absNorm:ℝ)⁻¹ := inv_nonneg.mpr (zero_le_one.trans hN)
  unfold localErrorCost
  split_ifs <;> nlinarith

/-- Genuine active extracted-allocation counting, with the literal slots
and the three actual extraction indices. -/
theorem actual_error_tail_active_card {α : Type*}[Fintype α]
    (u : Input α)(q : O)(hq : Prime (Ideal.span {q}))
    (hslot : ∀i,∀I∈u.slots i,IsCoprime (Ideal.span {q}) I)(i : Fin 3) :
    (Fintype.card (actualAllocations (activeInput u).pools ((Ideal.span {q})^(errorIndex i+1))):ℝ)≤8 := by
  have hh := actual_error_allocations_card (activeInput u).pools (Ideal.span {q}) hq
    (errorIndex i+1) (error_extracted_index_cases i) (by
      intro j I hI
      have hI' := error_active_pools_subset u (Sum.inl j) hI
      exact ⟨u.pools_ne (Sum.inl j) I hI',hslot j I hI'⟩)
  simp only [Fintype.card_coe]
  exact_mod_cast hh

/-- Genuine prime-ideal counting supplies the coarse polynomial cutoff
needed to absorb the full extracted-prime multiplicity by arbitrary saving. -/
theorem actual_error_tail_prime_card (P : Finset (Ideal O))(Z U : ℝ)(hZ : 1≤ Z)(hU : 0≤ U)
    (hp : ∀Q∈P,Prime Q)(hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hcap : ∀Q∈P,(Q.absNorm:ℝ)≤ Z^U) :
    (Fintype.card (elementPool P):ℝ)≤128*Z^U := by
  rw [Fintype.card_coe,elementPool_card P hp hbad]
  exact DescentFiberCost.finite_ideal_count_real P (Z^U) (Real.one_le_rpow hZ hU)
    (fun Q hQ=>(hp Q hQ).ne_zero) hcap

def extractedTailSum {α : Type*}[Fintype α]
    (u : Input α)(R seed : Ideal O)(Φ : 𝓢(ℝ,ℂ))(Z ξ : ℝ)(P : Finset (Ideal O))
    (radius Fourier : elementPool P→ Fin 3→ℝ)
    (υ : elementPool P→ Fin 3→ RayCharacter→ Character) : ℝ :=
  let Label := (q : elementPool P) × (i : Fin 3) × (_ψ : RayCharacter) ×
    actualAllocations (activeInput u).pools ((Ideal.span {q.val})^(errorIndex i+1))
  let E := fun l : Label=>(Ideal.span {l.1.val})^(errorIndex l.2.1+1)
  let source := fun l : Label=>child u (E l) R
    (errorActiveAllocation u (E l) l.2.2.2) (υ l.1 l.2.1 l.2.2.1) u.t
  ∑l : Label,(16*(errorIndex l.2.1+2:ℝ)*localErrorCost l.1.val (errorIndex l.2.1)/volume (source l))*
    ‖secondDiscardedEnergy (source l).η (source l).t
      (original (source l) (R*E l) seed).columns (original (source l) (R*E l) seed).beta
      Φ (radius l.1 l.2.1) (Fourier l.1 l.2.1) Z ξ‖

lemma extracted_tail_sum_eq {α : Type*}[Fintype α]
    (u : Input α)(R seed : Ideal O)(Φ : 𝓢(ℝ,ℂ))(Z ξ : ℝ)(P : Finset (Ideal O))
    (radius Fourier : elementPool P→ Fin 3→ℝ)
    (υ : elementPool P→ Fin 3→ RayCharacter→ Character) :
    extractedTailSum u R seed Φ Z ξ P radius Fourier υ=
      ∑q : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
        ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {q.val})^(errorIndex i+1)),
          let v := child u ((Ideal.span {q.val})^(errorIndex i+1)) R
            (errorActiveAllocation u ((Ideal.span {q.val})^(errorIndex i+1)) Bp) (υ q i ψ) u.t
          16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i)*
            (‖secondDiscardedEnergy v.η v.t (original v (R*(Ideal.span {q.val})^(errorIndex i+1)) seed).columns
              (original v (R*(Ideal.span {q.val})^(errorIndex i+1)) seed).beta
              Φ (radius q i) (Fourier q i) Z ξ‖/volume v) := by
  unfold extractedTailSum
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro ψ _
  apply Finset.sum_congr rfl
  intro Bp _
  ring

def firstExtractedTailSum {α : Type*}[Fintype α]
    (N : ℕ)(b : ℝ)(s : Input α)(reflected : Bool)(l : FirstSourceLabel)(R seed : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(Φ : 𝓢(ℝ,ℂ))(Z M a δ reserve ξ : ℝ)
    (P : Finset (Ideal O))(υ : elementPool P→ Fin 3→ RayCharacter→ Character) : ℝ :=
  let C := if reflected then l.1.2 else l.1.1
  let radius := fun (q : elementPool P)(i : Fin 3)=>
    firstErrorTailRadius reflected l Z M (volume s) a δ reserve q.val (errorIndex i+1)
  let Fourier := fun (q : elementPool P)(i : Fin 3)=>
    firstErrorTailFourier N b (volume s) C q.val (errorIndex i+1) (radius q i)
  extractedTailSum (child s C R B₁ χ t) (R*C) seed Φ Z ξ P radius Fourier υ

/-- All literal extracted-prime labels are counted; constants precede
both allocations, source profiles, primes, rays and independent heights. -/
theorem eventual_actual_first_label_error_tail_sum {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi B U ξ saving : ℝ)(hCs : 1≤ Cs)(hb : 1≤ b)
    (hlo : 0< lo)(hhi : 0≤ hi)(hB : 0≤ B)(hU : 0≤ U)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(s : Input α)(R seed : Ideal O),Fintype.card α≤ N → (∀i,s.M i≤ Cs) → s.upper≤ b →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(M a δ reserve t : ℝ)(hZ : 1< Z),0≤ M → M≤ B → 0≤ a → a≤ B → 0≤δ → 0≤ reserve →
      δ+reserve≤ B → |Real.logb Z (volume s)|≤ B →
    ∀(reflected : Bool)(l : FirstSourceLabel),Supported l.1.1 → Supported l.1.2 →
      CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2 →
      Real.logb Z (l.1.1.absNorm:ℝ)≤ B → Real.logb Z (l.1.2.absNorm:ℝ)≤ B →
      Real.logb Z (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun Q:CommonIndex l.1.1 l.1.2=>Q.val) l.2.val}).absNorm≤ B →
      Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm≤ B →
    ∀(B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))(χ : Character),
      frozenCoefficient B₁.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0 →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤ Z^U) →
      (∀q : elementPool P,∀i,∀I∈(child s (if reflected then l.1.2 else l.1.1) R B₁ χ t).slots i,
        IsCoprime (Ideal.span {q.val}) I) →
    ∀υ : elementPool P→ Fin 3→ RayCharacter→ Character,∀Φ : 𝓢(ℝ,ℂ),
      firstExtractedTailSum N b s reflected l R seed B₁ χ t Φ Z M a δ reserve ξ P υ≤
        Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(U-saving) := by
  obtain ⟨F,Ct,hCt,hbound⟩ := eventual_actual_first_label_error_tail (α:=α)
    N Cs b lo hi B ξ saving hCs hb hlo hhi hB hξ
  have hRay : 0<(Fintype.card RayCharacter:ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨F,393216*(Fintype.card RayCharacter:ℝ)*Ct,by positivity,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed hn hm hs p hp₁ hp₂ M a δ reserve t hZ hM hMB ha haB hδ hr hω hA
    reflected l hC hD heq hc hd he hactive B₁ χ hne P hp hbad hpool hslot υ Φ
  let C := if reflected then l.1.2 else l.1.1
  let first := child s C R B₁ χ t
  let Fval : ℝ := Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving)
  have hFval : 0≤ Fval := by dsimp only [Fval];positivity
  have hcountP := actual_error_tail_prime_card P Z U hZ.le hU hp hbad hpool
  have hpoint (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)
      (Bp : actualAllocations (activeInput first).pools ((Ideal.span {q.val})^(errorIndex i+1))) :
      let u := child first ((Ideal.span {q.val})^(errorIndex i+1)) (R*C)
        (errorActiveAllocation first ((Ideal.span {q.val})^(errorIndex i+1)) Bp) (υ q i ψ) first.t
      let rad := firstErrorTailRadius reflected l Z M (volume s) a δ reserve q.val (errorIndex i+1)
      16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i)*
        (‖secondDiscardedEnergy u.η u.t (original u ((R*C)*(Ideal.span {q.val})^(errorIndex i+1)) seed).columns
          (original u ((R*C)*(Ideal.span {q.val})^(errorIndex i+1)) seed).beta Φ rad
          (firstErrorTailFourier N b (volume s) C q.val (errorIndex i+1) rad) Z ξ‖/volume u)≤128*Fval := by
    have hdq := elementPool_data P hp hbad q.val q.property
    have hq : q.val≠0 := hdq.1.ne_zero
    have hh := hz.2 s R seed hn hm hs p hp₁ hp₂ M a δ reserve t hZ hM hMB ha haB hδ hr hω hA
      reflected l hC hD heq hc hd he hactive B₁ χ hne q.val hq (errorIndex i+1) (by omega)
      (hslot q) (errorActiveAllocation first ((Ideal.span {q.val})^(errorIndex i+1)) Bp) (υ q i ψ) t Φ
    have hcoeff : 0≤16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i) ∧
        16*(errorIndex i+2:ℝ)*localErrorCost q.val (errorIndex i)≤128 := by
      have hcost := actual_local_error_cost_le_one q.val hq (errorIndex i)
      have hcost0 := localErrorCost_nonneg q.val (errorIndex i)
      rcases errorIndex_cases i with hi|hi|hi <;> rw [hi] at hcost hcost0 ⊢ <;>
        norm_num only [Nat.cast_ofNat] <;> constructor <;> nlinarith only [hcost,hcost0]
    exact (mul_le_mul_of_nonneg_left hh hcoeff.1).trans
      (mul_le_mul_of_nonneg_right hcoeff.2 hFval)
  have hcountB (q : elementPool P)(i : Fin 3) := actual_error_tail_active_card first q.val
    (hp _ (elementPool_data P hp hbad q.val q.property).2.1) (hslot q) i
  unfold firstExtractedTailSum
  rw [extracted_tail_sum_eq]
  calc
    _≤∑q : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
        ∑_Bp : actualAllocations (activeInput first).pools ((Ideal.span {q.val})^(errorIndex i+1)),128*Fval :=
      Finset.sum_le_sum (fun q _=>Finset.sum_le_sum (fun i _=>Finset.sum_le_sum
        (fun ψ _=>Finset.sum_le_sum (fun Bp _=>hpoint q i ψ Bp))))
    _≤∑q : elementPool P,∑i : Fin 3,(Fintype.card RayCharacter:ℝ)*8*(128*Fval) := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro i _
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hcountB q i) (by positivity : 0≤128*Fval))
        (show 0≤(Fintype.card RayCharacter:ℝ) from Nat.cast_nonneg _)
    _=(Fintype.card (elementPool P):ℝ)*(3*((Fintype.card RayCharacter:ℝ)*8*(128*Fval))) := by simp
    _≤(128*Z^U)*(3*((Fintype.card RayCharacter:ℝ)*8*(128*Fval))) :=
      mul_le_mul_of_nonneg_right hcountP (by positivity)
    _=_ := by
      dsimp only [Fval]
      rw [Real.rpow_sub (zero_lt_one.trans hZ),Real.rpow_neg (zero_lt_one.trans hZ).le]
      ring


/-- Exact single heterogeneous Label sum of the second error split.
The physical first weight remains inside its literal coefficient. -/
lemma weighted_extracted_tail_sum_eq {First : Type*}[Fintype First]
    (α : First→ Type*)[∀q,Fintype (α q)](s : (q : First)→ Input (α q))
    (R seed : First→ Ideal O)(weight : First→ℝ)(Φ : 𝓢(ℝ,ℂ))(Z ξ : ℝ)
    (P : Finset (Ideal O))(radius Fourier : First→ elementPool P→ Fin 3→ℝ)
    (υ : First→ elementPool P→ Fin 3→ RayCharacter→ Character) :
    (∑q : First,weight q*extractedTailSum (s q) (R q) (seed q) Φ Z ξ P
      (radius q) (Fourier q) (υ q))=
    let Label := (q : First) × (p : elementPool P) × (i : Fin 3) ×
      (_ψ : RayCharacter) × actualAllocations (activeInput (s q)).pools
        ((Ideal.span {p.val})^(errorIndex i+1))
    let E := fun l : Label=>(Ideal.span {l.2.1.val})^(errorIndex l.2.2.1+1)
    let source := fun l : Label=>child (s l.1) (E l) (R l.1)
      (errorActiveAllocation (s l.1) _ l.2.2.2.2)
      (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) (s l.1).t
    ∑l : Label,((weight l.1*(16*(errorIndex l.2.2.1+2:ℝ)*
      localErrorCost l.2.1.val (errorIndex l.2.2.1)))/volume (source l))*
      ‖secondDiscardedEnergy (source l).η (source l).t
        (original (source l) (R l.1*E l) (seed l.1)).columns
        (original (source l) (R l.1*E l) (seed l.1)).beta Φ
        (radius l.1 l.2.1 l.2.2.1) (Fourier l.1 l.2.1 l.2.2.1) Z ξ‖ := by
  unfold extractedTailSum
  simp only [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro ψ _
  apply Finset.sum_congr rfl
  intro Bp _
  ring

/-- Complete literal extracted-prime discarded-source payment. The genuine
prime and allocation multiplicities are paid by arbitrarily strong tail
saving; the physical-D factor and original seed remain visible. -/
theorem eventual_actual_geometry_error_tail {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi slotlo B Uslot Uprime ξ εmass εcount saving : ℝ)
    (hCs : 1≤ Cs)(hb : 1≤ b)(hlo : 0< lo)(hhi : 0≤ hi)(hslotlo : 0< slotlo)
    (hB : 0≤ B)(hUs : 0≤ Uslot)(hUp : 0≤ Uprime)(hξ : 0<ξ)
    (hem : 0<εmass)(hec : 0<εcount) :
    ∃F : Finset (ℕ×ℕ),∃Ctail : ℝ,0< Ctail ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(s : Input α)(R seed : Ideal O)(W Φ : 𝓢(ℝ,ℂ)),
      Fintype.card α≤ N → (∀i,s.M i≤ Cs) → s.upper≤ b → slotlo≤ s.lower →
    ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(M a reserve t : ℝ)(hZ : 1< Z),0≤ M → M≤ B → 0≤ a → a≤ B → 0≤ reserve →
      frequencyLoss Z 32 ξ+reserve≤ B → Squarefree seed → seed≠0 →
      0< sourceRadius s → sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^Uslot) →
    ∀P : Finset (Ideal O),(∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤ Z^Uprime) →
      (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let A := Real.logb Z (volume s)
    let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus)
    let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let weight := fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    ∀υ : (j : rows)→ actualAllocations s.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character,
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*
        firstExtractedTailSum N b s reflected
          (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val) R j.val.2.1.val alloc
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t Φ
          Z M a (frequencyLoss Z 32 ξ) reserve ξ P (υ j alloc))≤
      Ctail*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*
        geometryHighFactor reflected (geometrySupportConstant N slotlo lo lo) key*
          Z^(-saving)/(seed.absNorm:ℝ) := by
  let L : ℝ := ((N:ℝ)+2)*Uslot
  let requested : ℝ := saving+B*εmass+6*B+L+3*εcount+Uprime
  obtain ⟨F,Ct,hCt,htail⟩ := eventual_actual_first_label_error_tail_sum (α:=α)
    N Cs b lo hi B Uprime ξ requested hCs hb hlo hhi hB hUp hξ
  obtain ⟨Cw,hCw,hpayment⟩ := eventual_actual_geometry_tail_allocation_payment (ι:=α)
    N Cs b slotlo lo B Uslot ξ εmass εcount hCs hslotlo hlo hB hUs hξ.le hem hec
  refine ⟨F,Ct*Cw,mul_pos hCt hCw,?_⟩
  filter_upwards [htail,hpayment] with Z ht hw
  refine ⟨ht.1,?_⟩
  intro s R seed W Φ hn hm hs hl p hp₁ hp₂ M a reserve t hZ hM hMB ha haB hr hω
    hseed hseed0 hsource hcap hA hpool P hp hbad hpcap hslot reflected key hK A rows C weight υ
  have hs₁ : ∀x,s.W₁ x≠0→ lo≤ x := by
    intro x hx;rw [hp₁] at hx;exact (p.support 0 hx).1
  have hs₂ : ∀x,s.W₂ x≠0→ lo≤ x := by
    intro x hx;rw [hp₂] at hx;exact (p.support 1 hx).1
  have hz₁ : s.W₁ 0=0 := by by_contra h;have hh:=hs₁ 0 h;linarith
  have hz₂ : s.W₂ 0=0 := by by_contra h;have hh:=hs₂ 0 h;linarith
  let T : ℝ := Uprime-requested
  let factor : ℝ := Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hterm (j : rows)(alloc : actualAllocations s.pools (C j)) :
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*
        firstExtractedTailSum N b s reflected
          (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val) R j.val.2.1.val alloc
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t Φ
          Z M a (frequencyLoss Z 32 ξ) reserve ξ P (υ j alloc)≤
        factor*(geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*Z^T) := by
    by_cases hne : frozenCoefficient alloc.val (C j) R s.ν s.W s.P≠0
    · let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1
      have hc := actual_geometry_error_tail_label_caps s R seed M Z ξ B hZ hK
        hseed hz₁ hz₂ hcap key j.val
      have hh := ht.2 s R j.val.2.1.val hn hm hs p hp₁ hp₂ M a (frequencyLoss Z 32 ξ)
        reserve t hZ hM hMB ha haB
        (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ.le) hr hω hA
        reflected (geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val)
        src.hC src.hD src.sameSupport hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 alloc
        (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) hne P hp hbad hpcap
        (fun q i I hI=>hslot q i.val I hI) (υ j alloc) Φ
      apply (mul_le_mul_of_nonneg_left hh
        (geometryAllocationWeight_nonneg reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc)).trans_eq
      dsimp only [factor,T]
      ring
    · have hw0 : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc=0 := by
        simp only [geometryAllocationWeight,C,hne,ite_false]
      rw [hw0,zero_mul,zero_mul,mul_zero]
  have hpaid := hw.2 s R seed W M T hZ hn hm hl hseed hseed0 hz₁ hz₂ hsource hcap hA hM
    hs₁ hs₂ hpool reflected key
  have he : B*εmass+T+6*B+((N:ℝ)+2)*Uslot+3*εcount=-saving := by
    dsimp only [T,requested,L];ring
  rw [he] at hpaid
  calc
    _≤∑j : rows,∑alloc : actualAllocations s.pools (C j),
      factor*(geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*Z^T) :=
      Finset.sum_le_sum (fun j _=>Finset.sum_le_sum (fun alloc _=>hterm j alloc))
    _=factor*(∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N b j.val alloc*Z^T) := by
      simp only [Finset.mul_sum]
    _≤ factor*_ := mul_le_mul_of_nonneg_left hpaid (by dsimp only [factor];positivity)
    _=_ := by dsimp only [factor];ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_twice_child_second_tail
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_radius_box
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_tail_scale_caps
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_first_label_error_tail
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_tail_label_caps
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_tail_radius
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_local_error_cost_le_one
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_tail_active_card
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_tail_prime_card
#print axioms OAI.SevenEighths.Cycle61InitialMass.extracted_tail_sum_eq
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_first_label_error_tail_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_tail

#print axioms OAI.SevenEighths.Cycle61InitialMass.weighted_extracted_tail_sum_eq

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorTail -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowPayment; sha256 eb2ce956c51de6ce86a999af894bc5fede637f4a2f04d6abfa91675f4da99db2 -/
section
                                                     
                                           

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61Moment Cycle61FinalCapacity
local notation "O" => HeckeFamily.O

/-- The low-branch nominal energy cancels the actual second normalizer
and the amplified main-radius cost, leaving the first geometry weight.
No count of first labels or residual projectors is hidden in this identity. -/
theorem actual_low_scalar_payment (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve error : ℝ)(hZ : 1< Z) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let nominal := secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstMainRadius reflected (Z^M) (Z^A) Z ξ (3*a) reserve l/Z^(A-c))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(nominal+a+error)=Z^(A-c+R+E-b₂+error) := by
  dsimp only
  rw [actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hZ,
    actual_second_normalizer_power C₂ D₂ hC₂ U Z hZ]
  unfold secondNominal
  have hz := zero_lt_one.trans hZ
  simp only [←Real.rpow_sub hz,←Real.rpow_add hz]
  congr 1
  have hm (c d : ℝ) : c-d+max (d-c) 0=max (c-d) 0 := by
    by_cases h : c≤ d
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  have hh := hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_scalar_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowPayment -/
