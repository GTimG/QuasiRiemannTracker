/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B091
import Candidate.Bundles.B123
import Candidate.Bundles.B142
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.InductionEnergy

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondLowProfiles; sha256 baad3987a5413bf6f5fb7c6dc4975c58f4f7064aa4d6dd5177404284cfc061b2 -/
section
                                                    
                                     

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
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Literal retained plain quotients, before clipping. -/
def profileScales {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (j : Fin 2) : ℝ :=
  Cycle61.Physical.sourcePlainScales src.toSource second j/(selectedPlain L₂ alloc j).absNorm

theorem profile_scales_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (j : Fin 2) : 0< profileScales src second L₂ alloc j := by
  apply div_pos (source_plain_positive src second j)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero L₂ Finset.univ alloc (Sum.inr j)))

/-- An actual surviving row forces both retained support tests. -/
theorem profile_scales_survive {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O) (hne : Cycle61.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0) :
    1≤ profileScales src second L₂ alloc 0*src.b₁ ∧
      1≤ profileScales src second L₂ alloc 1*src.b₂ := by
  exact allocated_survives src L₂ alloc z _ _ (source_plain_positive src second 0)
    (source_plain_positive src second 1) hne

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Actual low bound controlled by the original plain profiles. The uniform
control and all constants precede the moving retained scales. -/
theorem actual_live_main_low_profiles
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
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤167/200 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤ Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := q.final (g.datum.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      finalPlain src second L₂ alloc 0≤ Z^L → finalPlain src second L₂ alloc 1≤ Z^L →
    let hQM' : st.fixedModulus≤ M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    finalPositiveEnergy src second L₂ alloc (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*(1+|v|+height)^degree*
        Z^(nominal+δwidth+amp-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh) := by
  have haClip : 0< a/max 1 b := div_pos ha (by positivity)
  have haClip' : a/max 1 b≤1/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)< max 1 b)).mpr
    exact ha'.trans (by nlinarith [le_max_left (1:ℝ) b])
  obtain ⟨degree,S,hmain⟩ := actual_live_main_low_uniform (α:=α) M H hH W A B (a/max 1 b) b Bmask L lo hi Mcap εold
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
  have hU : ∀j,0< U j := profile_scales_pos src second L₂ alloc
  by_cases hret : ∀j,1≤ U j*b
  · let p := retainedPair a b ha p₀ U hU 0
    have hp (j : Fin 2) : (p.profile j : ℝ→ℂ)=dilated (p₀.profile j) (clipDilation (U j)) :=
      actual_clipped_pair a b ha p₀ U hU hret j
    have henergy := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
      Mrow omega ξ hMmin hω hξ hMcap' hz haff q g χ hP hPN second L₂ alloc p
      (by rw [hp 0,←hp₁]; rfl) (by rw [hp 1,←hp₂]; rfl) hXcap₁ hXcap₂
    have hc := hcontrol p₀ U hU
    have hc2 : (p.control S)^2≤ Cp^2*(p₀.control Sp)^2 := by
      calc (p.control S)^2≤(Cp*p₀.control Sp)^2 := pow_le_pow_left₀ (Profiles.control_nonneg p S) hc 2
           _=Cp^2*(p₀.control Sp)^2 := by ring
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    let exponent : ℝ := nominal+δwidth+amp-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
      (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh
    apply henergy.trans
    change C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
      (1+|v|+height)^degree*Z^exponent≤ _
    calc C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
          (1+|v|+height)^degree*Z^exponent≤
        C*QuadraticInitialBound.diagonalControl st.radial.profile*(Cp^2*(p₀.control Sp)^2)*
          (1+|v|+height)^degree*Z^exponent := by gcongr
         _=_ := by ring
  · have hzrow : ∀z,Cycle61.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
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

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_live_main_low_profiles
end
end OAI.SevenEighths.Cycle61InitialMass

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondLowProfiles -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryLow; sha256 2d397c986cdc4766e76fb82c550439a89f603c37520c133d7a26f6358a9a0c3b -/
section
                                                     
                                                 

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open Cycle61FinalLow
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Build the low-estimate geometry from the actual first geometric
column and any actual live second row. The selected allocations remain
literal; no moment estimate or whole-block nonvanishing is supplied. -/
def actualGeometryLow (reflected : Bool)(s : Input α)(q : Chain s)
    (R seed : Ideal O)(Z Mrow amp ξ reserve b : ℝ)(N : ℕ)(hZ : 1< Z)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin))
    (hC : q.C₁=geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j)
    (hη : q.η₁=geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j)
    (d : SecondInputDatum α)(r : secondLiveRows (fun _:Unit=>d.block))
    (hparent : d.input.η=q.η₁)
    (hradius : d.radius=frequencyRadius
      (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j)) Z ξ)
    (hlabel : q.E₂=d.C ∨ q.E₂=d.D)
    (hf₁ : frozenCoefficient q.B₁.val q.C₁ q.R₁ s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient q.B₂.val q.E₂ q.R₂ q.first.ν q.first.W q.first.P≠0) :
    LiveMainGeometry s q Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ b N :=
  let src := geometryFirstSource s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j.1
  { reflected:=reflected,C₀:=src.C,D₀:=src.D,hC₀:=src.hC,hD₀:=src.hD,
    heq₀:=src.sameSupport,selected:=hC,E₀:=src.inactive,
    hmod:=by
      rw [hη]
      exact actual_geometry_column_modulus reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin j,
    δ:=frequencyLoss Z 32 ξ,reserve:=reserve,homega:=rfl,
    datum:=d,parent:=hparent,row:=r,radius_eq:=hradius,label:=hlabel,
    first_nonzero:=hf₁,second_nonzero:=hf₂ }

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actualGeometryLow

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryLow -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseRows; sha256 5d4ba64f774c801b8ff6f470e76a2e608f54bf9a700ca01a07141c3b0ea2c03f -/
section
                                           
                                                          

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
open CenteredMomentDivisorRetained CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentInductionEnergy Cycle61Moment
local notation "O" => HeckeFamily.O
variable {ι : Type*}[Fintype ι][DecidableEq ι]

/-- Clipping cannot enlarge the right endpoint of a nonnegative support
interval. This elementary bound does not need a surviving row. -/
lemma coarse_dilated_support (W : ℝ→ℂ)(b c : ℝ)(hb : 0≤ b)(hc : 1≤ c)
    (hs : Function.support W⊆Set.Iic b) : Function.support (dilated W c)⊆Set.Iic b := by
  intro x hx
  change x≤ b
  have hh : c*x≤ b := hs hx
  by_cases hneg : x≤0
  · exact hneg.trans hb
  · have hmul := mul_le_mul_of_nonneg_right hc (le_of_not_ge hneg)
    linarith

/-- An absolute bound for each actual positive allocated row, independent
of height, character and frequency. The fixed profile suprema and the literal
remaining scales are retained explicitly for the Mellin tail estimate. -/
theorem actual_second_positive_absolute (s : Data ι)(second : Bool)
    (D : Ideal O)(alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O)(B₁ B₂ : ℝ)(hB₁ : 0≤ B₁)(hB₂ : 0≤ B₂)
    (hW₁ : ∀x,‖s.W₁ x‖≤ B₁)(hW₂ : ∀x,‖s.W₂ x‖≤ B₂) :
    let U := fun j=>Cycle61.Physical.sourcePlainScales s.toSource second j/(selectedPlain D alloc j).absNorm
    ‖Cycle61.Physical.sourcePositiveRow s.toSource second D alloc z‖^2≤
      ((128*max 1 s.b₁*B₁)*(128*max 1 s.b₂*B₂)*
        (∏i : liveIndices D alloc,128*max 1 (s.hi i)*s.M i))^2*
        (clippedScale (U 0)*clippedScale (U 1)*∏i : liveIndices D alloc,s.P i) := by
  intro U
  have hU (j : Fin 2) : 0< U j := by
    apply div_pos
    · cases second <;> fin_cases j
      · exact s.X₁_pos
      · exact s.X₂_pos
      · exact s.Y₁_pos
      · exact s.Y₂_pos
    · exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (selectedDivisor_ne_zero D Finset.univ alloc (Sum.inr j)))
  apply positive_squared_absolute (ι:=↥(liveIndices D alloc)) s.η s.m s.A z s.t
    (dilated s.W₁ (clipDilation (U 0))) (dilated s.W₂ (clipDilation (U 1)))
    (max 1 s.b₁) (max 1 s.b₂) B₁ B₂ (clippedScale (U 0)) (clippedScale (U 1))
    (by positivity) (by positivity) hB₁ hB₂
    (zero_lt_one.trans_le (clippedScale_ge_one _)) (zero_lt_one.trans_le (clippedScale_ge_one _))
    (coarse_dilated_support _ _ _ (by positivity) (clipDilation_ge_one _ (hU 0))
      (fun x hx=>show x≤ max 1 s.b₁ from (s.support₁ hx).trans (le_max_right _ _)))
    (coarse_dilated_support _ _ _ (by positivity) (clipDilation_ge_one _ (hU 1))
      (fun x hx=>show x≤ max 1 s.b₂ from (s.support₂ hx).trans (le_max_right _ _)))
    (fun x=>hW₁ _) (fun x=>hW₂ _) (fun i=>s.slots i)
    (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) (fun i=>s.P i)
    (fun i=>max 1 (s.hi i)) (fun i=>s.M i) (fun i=>s.P_pos i)
    (fun _=>by positivity) (fun i=>zero_le_one.trans (s.M_ge_one i))
    (fun i=>s.coefficient_bound i)
  intro i I hI hne
  have hs := (s.support i (right_ne_zero_of_mul hne)).2
  have hh := (div_le_iff₀ (s.P_pos i)).mp hs
  exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (s.P_pos i).le)

/-- A height-independent majorant for all allocated positive rows of one
source. It retains the two profile suprema as explicit homogeneous factors. -/
def coarseRowControl (s : Data ι)(B₁ B₂ : ℝ) : ℝ :=
  (128*max 1 s.b₁*B₁)*(128*max 1 s.b₂*B₂)*∏i,128*max 1 (s.hi i)*s.M i

def coarseRowSize (s : Data ι)(second : Bool) : ℝ :=
  max 1 (Cycle61.Physical.sourcePlainScales s.toSource second 0)*
    max 1 (Cycle61.Physical.sourcePlainScales s.toSource second 1)*∏i,max 1 (s.P i)

lemma coarse_row_size_nonneg (s : Data ι)(second : Bool) : 0≤ coarseRowSize s second := by
  unfold coarseRowSize
  positivity

theorem actual_second_positive_coarse (s : Data ι)(second : Bool)
    (D : Ideal O)(alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O)(B₁ B₂ : ℝ)(hB₁ : 0≤ B₁)(hB₂ : 0≤ B₂)
    (hW₁ : ∀x,‖s.W₁ x‖≤ B₁)(hW₂ : ∀x,‖s.W₂ x‖≤ B₂) :
    ‖Cycle61.Physical.sourcePositiveRow s.toSource second D alloc z‖^2≤
      (coarseRowControl s B₁ B₂)^2*coarseRowSize s second := by
  have hh := actual_second_positive_absolute s second D alloc z B₁ B₂ hB₁ hB₂ hW₁ hW₂
  dsimp only at hh
  have hfac (i : ι) : 1≤128*max 1 (s.hi i)*s.M i := by
    have hi := le_max_left (1:ℝ) (s.hi i)
    have hm := s.M_ge_one i
    nlinarith [mul_le_mul hi hm (by norm_num : (0:ℝ)≤1) (by linarith : 0≤ max 1 (s.hi i))]
  have hprod : (∏i : liveIndices D alloc,128*max 1 (s.hi i)*s.M i)≤
      ∏i,128*max 1 (s.hi i)*s.M i := by
    rw [Finset.prod_coe_sort (liveIndices D alloc) (fun i:ι=>128*max 1 (s.hi i)*s.M i)]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (hfac i)) (fun i _ _=>hfac i)
  have hcoeff : 0≤(128*max 1 s.b₁*B₁)*(128*max 1 s.b₂*B₂) := by positivity
  have hc := mul_le_mul_of_nonneg_left hprod hcoeff
  have hscale (j : Fin 2) :
      clippedScale (Cycle61.Physical.sourcePlainScales s.toSource second j/(selectedPlain D alloc j).absNorm)≤
        max 1 (Cycle61.Physical.sourcePlainScales s.toSource second j) := by
    have hx : 0< Cycle61.Physical.sourcePlainScales s.toSource second j := by
      cases second <;> fin_cases j
      · exact s.X₁_pos
      · exact s.X₂_pos
      · exact s.Y₁_pos
      · exact s.Y₂_pos
    have hn : (1:ℝ)≤(selectedPlain D alloc j).absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (selectedDivisor_ne_zero D Finset.univ alloc (Sum.inr j)))
    exact max_le (le_max_left _ _) ((div_le_self hx.le hn).trans (le_max_right _ _))
  have hp : (∏i : liveIndices D alloc,s.P i)≤∏i,max 1 (s.P i) := by
    calc
      _≤∏i : liveIndices D alloc,max 1 (s.P i) :=
        Finset.prod_le_prod₀ (fun i _=>(s.P_pos i).le) (fun i _=>le_max_right _ _)
      _≤ _ := by
        rw [Finset.prod_coe_sort (liveIndices D alloc) (fun i:ι=>max 1 (s.P i))]
        exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>by positivity) (fun i _ _=>le_max_left _ _)
  have hfp : 0≤∏i : liveIndices D alloc,128*max 1 (s.hi i)*s.M i :=
    Finset.prod_nonneg (fun i _=>zero_le_one.trans (hfac i))
  have hpp : 0≤∏i : liveIndices D alloc,s.P i := Finset.prod_nonneg (fun i _=>(s.P_pos i).le)
  apply hh.trans
  apply mul_le_mul (pow_le_pow_left₀ (mul_nonneg hcoeff hfp) hc 2)
  · exact mul_le_mul (mul_le_mul (hscale 0) (hscale 1) (by unfold clippedScale; positivity)
      (by positivity)) hp (by positivity) (by positivity)
  · unfold clippedScale; positivity
  · exact sq_nonneg _

/-- The absolute tail bound keeps the extraction divisor in the denominator.
It is uniform over both positive rectangles and all heights. -/
theorem actual_second_allocation_coarse (s : Data ι)
    (D : Ideal O)(alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O)(B₁ B₂ : ℝ)(hB₁ : 0≤ B₁)(hB₂ : 0≤ B₂)
    (hW₁ : ∀x,‖s.W₁ x‖≤ B₁)(hW₂ : ∀x,‖s.W₂ x‖≤ B₂) :
    retainedAllocationCost s D alloc z≤
      ((2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*(coarseRowControl s B₁ B₂)^2*
        (coarseRowSize s false+coarseRowSize s true))/formalReductionFactor D alloc s.P := by
  have hprod : (∏i∈frozenIndices D alloc,s.M i)≤∏i,s.M i :=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  have hrows := add_le_add
    (actual_second_positive_coarse s false D alloc z B₁ B₂ hB₁ hB₂ hW₁ hW₂)
    (actual_second_positive_coarse s true D alloc z B₁ B₂ hB₁ hB₂ hW₁ hW₂)
  have hfp : 0≤∏i∈frozenIndices D alloc,s.M i :=
    Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
  have hden := (s.reduction_pos D alloc).le
  unfold retainedAllocationCost
  apply (mul_le_mul
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hfp hprod 2) (by positivity)) (s.reduction_pos D alloc).le)
    hrows (by positivity) (by positivity)).trans_eq
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.coarse_dilated_support
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_positive_absolute
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_positive_coarse
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_allocation_coarse

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseRows -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseShell; sha256 4d6d81bb3dd0795fe7f77643c0d84760bd8aec9d6a517c3c7bdab07fc15cb23d -/
section
                                                    

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw Cycle61Moment
local notation "O" => HeckeFamily.O
variable {ι : Type*}[Fintype ι][DecidableEq ι]

def coarseAllocationControl (s : Data ι)(B₁ B₂ : ℝ) : ℝ :=
  (2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2*(coarseRowControl s B₁ B₂)^2*
    (coarseRowSize s false+coarseRowSize s true)

lemma coarse_allocation_control_nonneg (s : Data ι)(B₁ B₂ : ℝ) :
    0≤ coarseAllocationControl s B₁ B₂ := by
  unfold coarseAllocationControl
  exact mul_nonneg (by positivity)
    (add_nonneg (coarse_row_size_nonneg s false) (coarse_row_size_nonneg s true))

/-- The diagonal extraction sum is dominated by the already proved paired
projector sum. This costs no assertion that the projector divides a row. -/
theorem actual_reciprocal_diagonal (s : Data ι)(Ds : Finset (Ideal O)) :
    (∑D∈Ds,∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)≤
      ∑D∈Ds,∑a∈s.toSource.active D,∑b∈s.toSource.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b s.P) := by
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro a ha
  have hh := Finset.single_le_sum (s:=s.toSource.active D)
    (f:=fun b=>1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b s.P))
    (fun b _=>by positivity) ha
  simpa only [←pow_two,Real.sqrt_sq (s.reduction_pos D a).le] using hh

/-- All-height coarse energy of the literal residual-projector shell.
The fixed factor precedes source data; the bound retains the original
support allowance and coefficient/profile controls. -/
theorem actual_second_coarse_shell (N : ℕ)(hι : Fintype.card ι≤ N)(ε : ℝ)(hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀(s : Data ι)(Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z : ℝ,1≤ T → 1< Z →
      (∀D∈Ds,T≤(D.absNorm:ℝ)) → (∀D∈Ds,(D.absNorm:ℝ)<2*T) →
      ∀(z : (D : Ideal O)→ Allocation D (Finset.univ : Finset (ι⊕Fin 2))→ O)
        (B₁ B₂ : ℝ),0≤ B₁ → 0≤ B₂ → (∀x,‖s.W₁ x‖≤ B₁) → (∀x,‖s.W₂ x‖≤ B₂) →
      (∑D∈Ds,∑a∈s.toSource.active D,retainedAllocationCost s D a (z D a))≤
        coarseAllocationControl s B₁ B₂*C*(2*T)^(2*ε)*Z^(s.toSource.allowance Z) := by
  obtain ⟨C,hC,hshell⟩ := paired_all_active_shell (ι:=ι) (κ:=ι) N hι hι ε hε
  refine ⟨C,hC,?_⟩
  intro s Ds hDs T Z hT hZ hlo hhi z B₁ B₂ hB₁ hB₂ hW₁ hW₂
  have hs := (actual_reciprocal_diagonal s Ds).trans (hshell s.toSource s.toSource Ds hDs T Z hT hZ hlo hhi)
  have hcost := coarse_allocation_control_nonneg s B₁ B₂
  calc
    _≤∑D∈Ds,∑a∈s.toSource.active D,coarseAllocationControl s B₁ B₂/formalReductionFactor D a s.P :=
      Finset.sum_le_sum (fun D _=>Finset.sum_le_sum (fun a _=>
        actual_second_allocation_coarse s D a (z D a) B₁ B₂ hB₁ hB₂ hW₁ hW₂))
    _=coarseAllocationControl s B₁ B₂*(∑D∈Ds,∑a∈s.toSource.active D,1/formalReductionFactor D a s.P) := by
      simp only [Finset.mul_sum,mul_one_div]
    _≤ coarseAllocationControl s B₁ B₂*(C*(2*T)^(2*ε)*Z^((s.toSource.allowance Z+s.toSource.allowance Z)/2)) :=
      mul_le_mul_of_nonneg_left hs hcost
    _=_ := by rw [show (s.toSource.allowance Z+s.toSource.allowance Z)/2=s.toSource.allowance Z by ring]; ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_reciprocal_diagonal
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_coarse_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseShell -/
