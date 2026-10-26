import Candidate.Target836.SourceProvider.ErrorMain
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Cycle63.Physical.FinalError.Main
import Candidate.Cycle63.Physical.InitialMass.SecondExtraction
import Candidate.Cycle63.Physical.FinalProfiles
import Candidate.Cycle63.Physical.InitialMass.SecondLowCommon
import Candidate.Cycle63.Physical.InitialMass.SecondSourceControls

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Target836ErrorPayment
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
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
open Cycle63Moment Cycle63FinalError
open CenteredMomentAmplificationErrorEnergy CenteredMomentSlotRatios
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]


open CenteredMomentCommonPairedSource
/-- The complete row sum precedes both supported allocation payments. -/
theorem error_common_column_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b ε : ℝ) (hε : 0 < ε) :
    ∃K : ℝ,0 < K ∧ ∀(s : Input ι),s.upper ≤ b → ∀C R seed : Ideal O,
      ∀hC : Supported C,seed∣C →
      ∀(Ds : Finset (Ideal O))(zs : Finset O)(weight : O→ℝ)(T Z pad E : ℝ),
      1 ≤ T → 1 < Z → 0 ≤ E →
      (∀D∈Ds,Squarefree D ∧ T ≤ (D.absNorm:ℝ) ∧ (D.absNorm:ℝ) < 2*T) →
      ∀(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(rad : ℝ),0 < rad →
      (∀z : O,keep z → 0 ≤ (Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀z∈zs,0 ≤ weight z) → (∀z∈zs,keep z) →
      (∀z∈zs,weight z ≤ (Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        (commonData s C R B).toSource.allowance Z ≤ pad) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        ∀D∈Ds,∀a∈(commonData s C R B).toSource.active D,∀second : Bool,
          finalPositiveEnergy (commonData s C R B) second D a keep Φ rad ≤ E) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn s C hC R seed D z‖^2) ≤ 
        K*s.toData.profileFactor*(∏i,s.M i)^2*E*(C.absNorm:ℝ)^(ε-1)*
          (2*T)^(3*ε)*Z^pad := by
  obtain ⟨Kc,hKc,hcommon⟩ := actual_common_low_energy (ι:=ι) b ε hε
  obtain ⟨Ke,hKe,hpoint⟩ := actual_common_column_extraction (ι:=ι) ε hε
  refine ⟨Ke*Kc,by positivity,?_⟩
  intro s hb C R seed hC hseed Ds zs weight T Z pad E hT hZ hE hDs keep Φ rad hrad hΦ
    hn hk hw hallow henergy
  have hh := hcommon s hb C R hC.1 Ds zs weight T Z pad E hT hZ hE hDs
    keep Φ rad hrad hΦ hk hw hallow henergy
  have hT0 : 0 < 2*T := by linarith
  have hmajor : (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn s C hC R seed D z‖^2) ≤ 
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
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ Ke*(2*T)^ε)).trans_eq
  rw [show 3*ε=ε+2*ε by ring_nf,Real.rpow_add hT0 ε (2*ε)]
  ring_nf

theorem uniform_error_common_column_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b ε : ℝ) (hε : 0 < ε) :
    ∃K : ℝ,0 < K ∧ ∀S : Finset ι,∀(s : Input S),s.upper ≤ b → ∀C R seed : Ideal O,
      ∀hC : Supported C,seed∣C →
      ∀(Ds : Finset (Ideal O))(zs : Finset O)(weight : O→ℝ)(T Z pad E : ℝ),
      1 ≤ T → 1 < Z → 0 ≤ E →
      (∀D∈Ds,Squarefree D ∧ T ≤ (D.absNorm:ℝ) ∧ (D.absNorm:ℝ) < 2*T) →
      ∀(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(rad : ℝ),0 < rad →
      (∀z : O,keep z → 0 ≤ (Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀z∈zs,0 ≤ weight z) → (∀z∈zs,keep z) →
      (∀z∈zs,weight z ≤ (Φ (‖eisEmbedding z‖^2/rad)).re) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        (commonData s C R B).toSource.allowance Z ≤ pad) →
      (∀B : actualAllocations s.pools C,commonScalar s C R B≠0 →
        ∀D∈Ds,∀a∈(commonData s C R B).toSource.active D,∀second : Bool,
          finalPositiveEnergy (commonData s C R B) second D a keep Φ rad ≤ E) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn s C hC R seed D z‖^2) ≤ 
        K*s.toData.profileFactor*(∏i,s.M i)^2*E*(C.absNorm:ℝ)^(ε-1)*
          (2*T)^(3*ε)*Z^pad := by
  choose K hK hc using fun S : Finset ι=>error_common_column_energy (ι:=S) b ε hε
  let Kall := 1+∑S : Finset ι,K S
  have hpos : 0 < Kall := by
    have hn : 0 ≤ ∑S : Finset ι,K S := Finset.sum_nonneg (fun S _=>(hK S).le)
    dsimp [Kall]; linarith
  refine ⟨Kall,hpos,?_⟩
  intro S s hb C R seed hC hseed Ds zs weight T Z pad E hT hZ hE hDs keep Φ rad hrad hΦ
    hn hk hw hallow henergy
  have hle : K S ≤ Kall := by
    have hh := Finset.single_le_sum (fun S (_ : S∈Finset.univ)=>(hK S).le) (Finset.mem_univ S)
    dsimp [Kall]; linarith
  apply (hc S s hb C R seed hC hseed Ds zs weight T Z pad E hT hZ hE hDs
    keep Φ rad hrad hΦ hn hk hw hallow henergy).trans
  have hp := s.toData.profile_nonneg
  gcongr

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Actual extracted normalized columns with prime payment retained outside the complete frequency sum. -/
theorem actual_paid_error_column_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hBmask : 0 ≤ Bmask) (hL : 0 ≤ L) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hloss : 0 < loss) (hmargin : 0 < margin) (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (ηseed : Character) (bs J εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0 ≤ window) (hpad : 0 < pad) (heshell : 0 < εshell)
    (hbs : 1 ≤ bs) (hJ : 0 < J) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q ≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0 < Cg ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀(hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper ≤ bs → s.b₁=bp → s.b₂=bp →
      (∀j,0 ≤ w j) → (∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0 ≤ mesh → (∀j,w j ≤ mesh) → (∀j,lo ≤ σ j) → (∀j,σ j ≤ hi) →
      0 ≤ height → (∀j,|freq j| ≤ height) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^L) →
      (∀j,logWindow (s.lo j) (s.hi j) ≤ window) →
    ∀(Mrow omega ξ : ℝ),Mmin ≤ Mrow → 0 ≤ omega → 0 ≤ ξ → Mrow+εwidth*Mrow+ξ/2 ≤ Mcap →
      ((17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Named.lam*(∑j,Real.logb Z (s.P j)) ≤ Named.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Named.amp cell
    q.k=1 ∨ q.k=6 ∨ q.k=7 → 3*amp/4 ≤ Real.logb Z (normValue q.p) →
    ∀g : Geometry s q Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ) ≤ Z^Bmask)
,
    let st := retainedState Z Bmask hZ (g.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    let src := withHeight q.extracted (g.τ χ) v
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(seed : Ideal O)(hE₂ : Supported q.E₂),seed∣q.E₂ →
    ∀(Ds : Finset (Ideal O))(T : ℝ),1 ≤ T →
      (∀D∈Ds,Squarefree D ∧ T ≤ (D.absNorm:ℝ) ∧ (D.absNorm:ℝ) < 2*T) →
    ∀(zs : Finset O)(weight : O→ℝ),(∀z∈zs,0 ≤ weight z) →
      (∀z∈zs,st.radial.keep z) →
      (∀z∈zs,weight z ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
    localErrorCost q.p (q.k-1)*Z^(-errorRemoval q.p Z q.k+errorMoving q.p Z q.k)*
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2) ≤ 
      Cg*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(g.nominal+δwidth-Mrow*Target874836.SourceProvider.ErrorPhysical.branchReserve q.k+εold+loss*(Fintype.card α:ℝ)+
          padding/6+(3/4)*mesh+pad) := by
  obtain ⟨degree,Sp,hprofiles⟩ := Target874836.SourceProvider.ErrorPhysical.actual_paid_error_uniform (α:=α) M H hH W A B ap bp Bmask L lo hi
    Mcap εold loss margin hA hWs hW hB hap hap' hbp hBmask hL hMcap hεold hloss hmargin hbeta
    ηseed bs J εwidth εpad Mmin hbs hJ hew hep hmin
  choose Kss hKss hcolumns using fun S : Finset α=>
    uniform_error_common_column_energy (ι:=S) bs εshell heshell
  let Kall := 1+∑S : Finset α,Kss S
  have hKall : 0 < Kall := by
    have hn : 0 ≤ ∑S : Finset α,Kss S := Finset.sum_nonneg (fun S _=>(hKss S).le)
    dsimp [Kall]; linarith
  have hKle (S : Finset α) : Kss S ≤ Kall := by
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
  let exponent := g.nominal+δwidth-Mrow*Target874836.SourceProvider.ErrorPhysical.branchReserve q.k+εold+loss*(Fintype.card α:ℝ)+
    padding/6+(3/4)*mesh
  let E := C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
    (1+|v|+height)^degree*Z^(exponent+errorRemoval q.p Z q.k)
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have henergy (B₂ : actualAllocations src.pools q.E₂)(hn : commonScalar src q.E₂ q.R₂ B₂≠0)
      (D : Ideal O)(hD : D∈Ds)
      (alloc : Allocation D (Finset.univ : Finset (liveIndices B₂.val⊕Fin 2)))
      (_halloc : alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D)(second : Bool) :
      finalPositiveEnergy (commonData src q.E₂ q.R₂ B₂) second D alloc
        st.radial.keep st.radial.profile st.radial.scale ≤ E := by
    let q' : Chain s := { q with B₂:=B₂ }
    have hB₂ : frozenCoefficient B₂.val q.E₂ q.R₂ q.extracted.ν q.extracted.W q.extracted.P≠0 :=
      right_ne_zero_of_mul hn
    let g' : Geometry s q' Z Mrow amp omega ξ bs J (Fintype.card α) :=
      { g with second_nonzero:=hB₂ }
    have he := (hZ.2 hZone s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂
      hw hwL hmesh hwm hσlo hσhi hheight hfreq hOrig Mrow omega ξ hMmin hω hξ hMcap'
      hz haff q' hk hprime g' χ hP hPN second D alloc p hp₁ hp₂).1
    change finalPositiveEnergy (commonData src q.E₂ q.R₂ B₂) second D alloc
      st.radial.keep st.radial.profile st.radial.scale ≤ 
      C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
        (1+|v|+height)^degree*Z^(g.nominal+δwidth+errorRemoval q.p Z q.k-
          Mrow*Target874836.SourceProvider.ErrorPhysical.branchReserve q.k+εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh) at he
    apply he.trans_eq
    dsimp only [E,exponent]
    congr 1
    ring_nf
  have hallowance (B₂ : actualAllocations src.pools q.E₂)
      (_hn : commonScalar src q.E₂ q.R₂ B₂≠0) :
      (commonData src q.E₂ q.R₂ B₂).toSource.allowance Z ≤ pad := by
    have hh := fixed_source_allowance (Fintype.card α) window bp hwindow hbp
      (commonData src q.E₂ q.R₂ B₂)
      ((live_card_le B₂.val).trans ((live_card_le q.Bp.val).trans (live_card_le q.B₁.val)))
      (fun j=>hwin j.val.val.val) hsb₁.le hsb₂.le Z hZone
    have hfixed : ((Fintype.card α:ℝ)*window+2*Real.log bp)/Real.log Z ≤ pad :=
      (div_le_iff₀ (Real.log_pos hZone)).mpr
        (by nlinarith [(div_le_iff₀ hpad).mp hallow])
    have hpaid := hh.trans hfixed
    have hp : 0 ≤ Cycle63.Physical.plainClipAllowance Z
        ![(commonData src q.E₂ q.R₂ B₂).b₁,(commonData src q.E₂ q.R₂ B₂).b₂] := by
      unfold Cycle63.Physical.plainClipAllowance
      exact Finset.sum_nonneg (fun j _=>Real.logb_nonneg hZone (le_max_left _ _))
    linarith
  have hcolumn := hcolumns (liveIndices q.B₁.val) (liveIndices q.Bp.val) src hsupper
    q.E₂ q.R₂ seed hE₂ hseed Ds zs weight T Z pad E hT hZone hE hDs
    st.radial.keep st.radial.profile st.radial.scale st.radial.scale_pos
    (fun z _=>st.radial.nonneg z) hnonneg hkeep hweight hallowance henergy
  have hlarge : (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2) ≤ 
      (Kall*C*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell))*
          Z^((exponent+pad)+errorRemoval q.p Z q.k) := by
    apply hcolumn.trans
    calc
      _  ≤  Kall*src.toData.profileFactor*(∏j,src.M j)^2*E*
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
end OAI.SevenEighths.Target836ErrorPayment
#print axioms OAI.SevenEighths.Target836ErrorPayment.error_common_column_energy
#print axioms OAI.SevenEighths.Target836ErrorPayment.uniform_error_common_column_energy
#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_paid_error_column_uniform
