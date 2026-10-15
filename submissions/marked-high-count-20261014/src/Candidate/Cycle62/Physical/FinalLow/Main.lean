import Candidate.Cycle62.Physical.FinalLow.Geometry
import Candidate.Cycle62.Moment.LowBranch.PaidMain

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
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Actual main second low energy. Constants are chosen on the original
 ambient labels before either common allocation, all rows and all heights. -/
theorem actual_main_low_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0<margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (ηseed : Character) (bs bp₁ bp₂ εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤bs → s.b₁=bp₁ → s.b₂=bp₂ →
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
    ∀p : Profiles ap bp,
      dilated s.W₁ (clipDilation (Cycle62.Physical.sourcePlainScales src.toSource second 0/
        (Ideal.absNorm (selectedPlain L₂ alloc 0):ℝ)))=p.profile 0 →
      dilated s.W₂ (clipDilation (Cycle62.Physical.sourcePlainScales src.toSource second 1/
        (Ideal.absNorm (selectedPlain L₂ alloc 1):ℝ)))=p.profile 1 →
      finalPlain src second L₂ alloc 0≤Z^L → finalPlain src second L₂ alloc 1≤Z^L →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    finalPositiveEnergy src second L₂ alloc (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(nominal+δwidth+amp-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle62.Arithmetic.q0/9)*padding+Cycle62.Arithmetic.q0*mesh) := by
  obtain ⟨degree,Sp,hmain⟩ := actual_paid_low_main (α:=α) M H hH W A B ap bp 2 Bmask L lo hi Mcap εold
    hA hWs hW hB hap hap' hbp (by norm_num) hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C^(Fintype.card α)*(C₀+C₁),by positivity,?_⟩
  filter_upwards [hbound,Cycle62FinalRadius.fixed_final_width_loss_uniform (fun _:Unit=>ηseed)
    (Fintype.card α) bs 1 εwidth Mmin (zero_lt_one.trans_le hbs) (by norm_num) hew hmin,
    support_padding_eventually_mass (Fintype.card α) bs bp₁ bp₂ εpad Mmin (zero_lt_one.trans_le hbs) hep hmin]
    with Z hZ hwidthLoss hpadLoss
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p hp₁ hp₂ hXcap₁ hXcap₂
  dsimp only
  have hM : 0<Mrow := hmin.trans_le hMmin
  obtain ⟨hc₁,hc₂,_,_⟩ := Cycle62.Moment.originalCell_mem
    (show (17/500:ℝ)≤(∑j,Real.logb Z (s.P j))/Mrow ∧ (∑j,Real.logb Z (s.P j))/Mrow≤1/25 from
      ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩)
  have hcell := Cycle62.Arithmetic.cellUpper_bounds hc₁ hc₂
  have hamp := (mul_pos hM (Cycle62.Arithmetic.amp_pos hcell)).le
  have hshift := CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.C g.D g.hC g.U Z hZone
  have hnmax : 0≤max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0 := le_max_right _ _
  have hnominal : nominal≤Mrow := by unfold nominal secondNominal; linarith
  have hwidth : st.width-nominal≤δwidth := by
    have ht := main_state_width g Bmask hZone (zero_lt_one.trans_le hbs) χ (internalQ Q η₀) hP hPN
    have hl := hwidthLoss.2 () Mrow hMmin
    rw [←hsη] at hl
    norm_num only [Real.logb_one] at hl
    change st.width≤nominal+_ at ht
    dsimp [δwidth]; linarith
  have hδ : 0≤δwidth := by dsimp [δwidth]; positivity
  have hpadding : 0≤padding := by dsimp [padding]; positivity
  have hs : st.width≤Mcap := by dsimp only [δwidth] at hwidth; linarith
  by_cases live : ∃z,Cycle62.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0
  · obtain ⟨z,hzrow⟩ := live
    have htotal := main_source_capacity g hbs hsupper hZone hM
      (fun j=>by rw [hm.scale j]; exact Real.one_le_rpow hZone.le (hw j)) hz haff (g.τ χ) v second L₂ alloc z hzrow
    rw [original_slot_sum s q (g.τ χ) v Z hZone w hm.scale L₂ alloc] at htotal
    have hpadd := hpadLoss.2 Mrow hMmin
    rw [←hsb₁,←hsb₂] at hpadd
    have htotal' : length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
        (9/2)*(∑j∈q.indices L₂ alloc,w j)-nominal≤Mrow*Cycle62.Arithmetic.g cell+6*amp+padding := by
      change _≤_ at htotal; dsimp [padding]; linarith
    obtain ⟨R,hR,hpaid,henergy⟩ := hZ.2 (q.indices L₂ alloc) θ w σ freq v height mesh aLow i hw hwL
      (fun j _=>hwr j) hmesh (fun j _=>hwm j) hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh
      st rfl hs p _ _ (zero_lt_one.trans_le (clippedScale_ge_one _))
      (zero_lt_one.trans_le (clippedScale_ge_one _)) hXcap₁ hXcap₂ cell Mrow nominal δwidth padding
      hcell hM.le hwidth hδ hpadding htotal'
    rw [original_low_energy M H hH s η₀ θ w σ freq W B Z Bmask hZone hm q (g.τ χ) v
      (internalQ Q η₀) hP hPN g.radius g.C g.D g.U second L₂ alloc _,hp₁,hp₂]
    exact henergy.trans_eq (by ring)
  · have hzrow : ∀z,Cycle62.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      simpa only [not_exists,not_not] using live
    rw [zero_low_energy src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

#print axioms actual_main_low_uniform
end
end OAI.SevenEighths.Cycle62FinalLow
