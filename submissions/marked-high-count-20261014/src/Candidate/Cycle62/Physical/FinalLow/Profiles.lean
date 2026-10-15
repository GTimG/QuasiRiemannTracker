import Candidate.Cycle62.Physical.FinalLow.Main
import Candidate.Cycle62.Physical.FinalProfiles

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle62FinalLow
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
open Cycle62Moment.LowBranch Cycle62FinalNatural Cycle62FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle62FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Literal retained plain quotients, before clipping. -/
def profileScales {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (j : Fin 2) : ℝ :=
  Cycle62.Physical.sourcePlainScales src.toSource second j/(selectedPlain L₂ alloc j).absNorm

theorem profile_scales_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (j : Fin 2) : 0<profileScales src second L₂ alloc j := by
  apply div_pos (source_plain_positive src second j)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero L₂ Finset.univ alloc (Sum.inr j)))

/-- An actual surviving row forces both retained support tests. -/
theorem profile_scales_survive {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O) (hne : Cycle62.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0) :
    1≤profileScales src second L₂ alloc 0*src.b₁ ∧
      1≤profileScales src second L₂ alloc 1*src.b₂ := by
  exact allocated_survives src L₂ alloc z _ _ (source_plain_positive src second 0)
    (source_plain_positive src second 1) hne

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Actual low bound controlled by the original plain profiles. The uniform
control and all constants precede the moving retained scales. -/
theorem actual_main_low_profiles
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
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin) :
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
      length Z s.X₁+length Z s.X₂+Cycle62.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle62.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle62.Arithmetic.cellUpper (Cycle62.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle62.Arithmetic.amp cell
    ∀g : MainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    let src := q.final (g.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.C g.D g.U
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      finalPlain src second L₂ alloc 0≤Z^L → finalPlain src second L₂ alloc 1≤Z^L →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    finalPositiveEnergy src second L₂ alloc (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*(1+|v|+height)^degree*
        Z^(nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle62.Arithmetic.q0/9)*padding+Cycle62.Arithmetic.q0*mesh) := by
  have haClip : 0<a/max 1 b := div_pos ha (by positivity)
  have haClip' : a/max 1 b≤1/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<max 1 b)).mpr
    exact ha'.trans (by nlinarith [le_max_left (1:ℝ) b])
  obtain ⟨degree,S,hmain⟩ := actual_main_low_uniform (α:=α) M H hH W A B (a/max 1 b) b Bmask L lo hi Mcap εold
    hA hWs hW hB haClip haClip' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs b b εwidth εpad Mmin hbs hew hep hmin
  obtain ⟨Sp,Cp,hCp,hcontrol⟩ := clipped_pair_control a b ha S
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C*Cp^2,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p₀ hp₁ hp₂ hXcap₁ hXcap₂
  dsimp only
  let U := profileScales src second L₂ alloc
  have hU : ∀j,0<U j := profile_scales_pos src second L₂ alloc
  by_cases hret : ∀j,1≤U j*b
  · let p := retainedPair a b ha p₀ U hU 0
    have hp (j : Fin 2) : (p.profile j : ℝ→ℂ)=dilated (p₀.profile j) (clipDilation (U j)) :=
      actual_clipped_pair a b ha p₀ U hU hret j
    have henergy := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
      Mrow omega ξ hMmin hω hξ hMcap' hz haff q g χ hP hPN second L₂ alloc p
      (by rw [hp 0,←hp₁]; rfl) (by rw [hp 1,←hp₂]; rfl) hXcap₁ hXcap₂
    have hc := hcontrol p₀ U hU
    have hc2 : (p.control S)^2≤Cp^2*(p₀.control Sp)^2 := by
      calc (p.control S)^2≤(Cp*p₀.control Sp)^2 := pow_le_pow_left₀ (Profiles.control_nonneg p S) hc 2
           _=Cp^2*(p₀.control Sp)^2 := by ring
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    let exponent : ℝ := nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
      (2*Cycle62.Arithmetic.q0/9)*padding+Cycle62.Arithmetic.q0*mesh
    apply henergy.trans
    change C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
      (1+|v|+height)^degree*Z^exponent≤_
    calc C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
          (1+|v|+height)^degree*Z^exponent≤
        C*QuadraticInitialBound.diagonalControl st.radial.profile*(Cp^2*(p₀.control Sp)^2)*
          (1+|v|+height)^degree*Z^exponent := by gcongr
         _=_ := by ring
  · have hzrow : ∀z,Cycle62.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      intro z
      by_contra hne
      have hh := profile_scales_survive src second L₂ alloc z hne
      have hb₁ : src.b₁=b := hsb₁
      have hb₂ : src.b₂=b := hsb₂
      rw [hb₁,hb₂] at hh
      apply hret
      intro j; fin_cases j
      · exact hh.1
      · exact hh.2
    rw [zero_low_energy src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

#print axioms profile_scales_survive
#print axioms actual_main_low_profiles
end
end OAI.SevenEighths.Cycle62FinalLow
