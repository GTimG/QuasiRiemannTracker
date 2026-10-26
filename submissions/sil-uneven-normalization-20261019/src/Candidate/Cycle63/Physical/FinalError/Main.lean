import Candidate.Cycle63.Physical.FinalError.Payment

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63FinalError
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
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale CenteredMomentAllocatedChildCapacity
open CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAmplificationErrorEnergy
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity Cycle63FinalErrorCapacity
open Cycle63Physical.ExtractedBranches
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The genuine extracted retained positive energy, with both common
 allocations and prime extraction paid in the original ambient family.
 Profiles and all moment constants precede the moving physical labels. -/
theorem actual_paid_error_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hL : 0≤L) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hloss : 0<loss) (hmargin : 0<margin) (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (ηseed : Character) (bs J εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hJ : 0<J) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤bs → s.b₁=bp → s.b₂=bp →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤mesh → (∀j,w j≤mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^L) →
    ∀(Mrow omega ξ : ℝ),Mmin≤Mrow → 0≤omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle63.Arithmetic.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle63.Arithmetic.amp cell
    q.k=1 ∨ q.k=6 ∨ q.k=7 → 3*amp/4≤Real.logb Z (normValue q.p) →
    ∀g : Geometry s q Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    let src := q.final (g.τ χ) v
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    finalPositiveEnergy src second L₂ alloc st.radial.keep st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
          εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh) ∧
    localErrorCost q.p (q.k-1)*Z^(-errorRemoval q.p Z q.k+errorMoving q.p Z q.k)*
      finalPositiveEnergy src second L₂ alloc st.radial.keep st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(g.nominal+δwidth-Mrow*branchReserve q.k+εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh) := by
  have hapret : 0<ap/max 1 bp := div_pos hap (by positivity)
  have hapret' : ap/max 1 bp≤1/4 := (div_le_self hap.le (le_max_left _ _)).trans hap'
  obtain ⟨degree,S,hmain⟩ := actual_global_main_uniform (α:=α) M H hH W A B (ap/max 1 bp) bp
    2 Bmask L lo hi Mcap εold loss margin hA hWs hW hB hapret hapret' hbp (by norm_num)
    hBmask hMcap hεold hloss hmargin hbeta
  obtain ⟨Sp,Cp,hCp,hcontrol⟩ := Cycle63FinalProfiles.clipped_pair_control ap bp hap S
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg*Cp^2,by positivity,?_⟩
  filter_upwards [hbound,Cycle63FinalRadius.fixed_final_width_loss_uniform (fun _:Unit=>ηseed)
    (Fintype.card α) bs J εwidth Mmin (zero_lt_one.trans_le hbs) hJ hew hmin,
    support_padding_eventually_mass (Fintype.card α) bs bp bp εpad Mmin (zero_lt_one.trans_le hbs) hep hmin]
    with Z hZ hwidthLoss hpadLoss
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh hm hsη hsupper hsb₁ hsb₂ hw hwL hmesh hwm
    hσlo hσhi hheight hfreq hOrig Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp hk hprime g χ hP hPN second L₂ alloc st src δwidth padding p hp₁ hp₂
  dsimp only
  suffices henergy : finalPositiveEnergy src second L₂ alloc st.radial.keep st.radial.profile st.radial.scale≤
      (Cg*Cp^2)*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
          εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh) by
    refine ⟨henergy,?_⟩
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    apply normalize_error_energy q.p q.hp Z hZone q.k hk _ _ _ (by positivity)
    have hExp : (g.nominal+δwidth-Mrow*branchReserve q.k+εold+
        loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh)+errorRemoval q.p Z q.k =
      g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
        εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh := by ring
    simpa only [hExp] using henergy
  have hM : 0<Mrow := hmin.trans_le hMmin
  obtain ⟨hc₁,hc₂,_,_⟩ := Cycle63.Moment.originalCell_mem
    (show (17/500:ℝ)≤(∑j,Real.logb Z (s.P j))/Mrow ∧ (∑j,Real.logb Z (s.P j))/Mrow≤1/25 from
      ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩)
  have hcell := Cycle63.Arithmetic.cellUpper_bounds hc₁ hc₂
  have hamp := (mul_pos hM (Cycle63.Arithmetic.amp_pos hcell)).le
  have hshift := CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.C g.D g.hC g.U Z hZone
  have hnominal : g.nominal≤Mrow := by
    have hm0 := le_max_right (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)+
      2*errorRemoval q.p Z q.k-errorMoving q.p Z q.k) (0:ℝ)
    unfold Geometry.nominal errorNominal
    linarith
  have hwidth : st.width-g.nominal≤δwidth := by
    have ht := error_state_width g Bmask hZone (zero_lt_one.trans_le hbs) hJ χ (internalQ Q η₀) hP hPN
    have hl := hwidthLoss.2 () Mrow hMmin
    rw [←hsη] at hl
    dsimp [δwidth]; linarith
  have hδ : 0≤δwidth := by dsimp [δwidth]; positivity
  have hpadding : 0≤padding := by dsimp [padding]; positivity
  have hs : st.width≤Mcap := by dsimp [δwidth] at hwidth; linarith
  by_cases live : ∃z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0
  · obtain ⟨z,hzrow⟩ := live
    let X := Cycle63.Physical.sourcePlainScales src.toSource second
    let U := fun j : Fin 2=>X j/(Ideal.absNorm (selectedPlain L₂ alloc j):ℝ)
    have hU : ∀j,0<U j := fun j=> div_pos (source_plain_positive src second j)
      (zero_lt_one.trans_le (CenteredMomentAmplificationChildSourceCaps.norm_ge_one _
        (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero L₂ Finset.univ alloc (Sum.inr j))))
    have hsurv := allocated_survives src L₂ alloc z (X 0) (X 1)
      (source_plain_positive src second 0) (source_plain_positive src second 1) hzrow
    have hret : ∀j,1≤U j*bp := by
      intro j; fin_cases j
      · change 1≤_/ _*bp
        have hs0 := hsurv.1
        change 1≤_/ _*s.b₁ at hs0
        rw [hsb₁] at hs0
        exact hs0
      · change 1≤_/ _*bp
        have hs1 := hsurv.2
        change 1≤_/ _*s.b₂ at hs1
        rw [hsb₂] at hs1
        exact hs1
    let pret := retainedPair ap bp hap p U hU 0
    have hprofile (j : Fin 2) := Cycle63FinalProfiles.actual_clipped_pair ap bp hap p U hU hret j
    have hp0 : dilated s.W₁ (clipDilation (U 0))=pret.profile 0 := by rw [hp₁]; exact (hprofile 0).symm
    have hp1 : dilated s.W₂ (clipDilation (U 1))=pret.profile 1 := by rw [hp₂]; exact (hprofile 1).symm
    have hXcap₁ := final_plain_cap s q (g.τ χ) v Z L hZone hL hOrig second L₂ alloc 0
    have hXcap₂ := final_plain_cap s q (g.τ χ) v Z L hZone hL hOrig second L₂ alloc 1
    have htotal := error_source_capacity g hbs hsupper hZone hM
      (fun j=>by rw [hm.scale j]; exact Real.one_le_rpow hZone.le (hw j)) hz haff (g.τ χ) v second L₂ alloc z hzrow
    rw [original_slot_sum s q (g.τ χ) v Z hZone w hm.scale L₂ alloc] at htotal
    have hpadd := hpadLoss.2 Mrow hMmin
    rw [hsb₁,hsb₂] at htotal
    have hcap : length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
        (9/2)*(∑j∈q.indices L₂ alloc,w j)-g.nominal≤Mrow*Cycle63.Arithmetic.g cell+3*amp+
        ((q.k:ℝ)*Real.logb Z (normValue q.p)-(if q.k=6 then 0 else Real.logb Z (normValue q.p)))+padding := by
      change _≤_ at htotal
      dsimp [padding]; unfold errorRemoval errorMoving at htotal; linarith
    have hpaid := paid_branch_exponent q.k hk hcell hM.le hwidth hδ hprime hpadding hcap
    have he := hZ.2 (q.indices L₂ alloc) θ w σ freq v height mesh hw hwL hmesh (fun j _=>hwm j)
      hσlo hσhi hheight hfreq st rfl hs pret _ _
      (zero_lt_one.trans_le (clippedScale_ge_one _)) (zero_lt_one.trans_le (clippedScale_ge_one _)) hXcap₁ hXcap₂
    have hcoef := hcontrol p U hU
    have hpn := Profiles.control_nonneg p Sp
    have hpretn := Profiles.control_nonneg pret S
    have hsq : (pret.control S)^2≤Cp^2*(p.control Sp)^2 := by nlinarith
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    rw [original_positive_energy M H hH s η₀ θ w σ freq W B Z Bmask hZone hm q (g.τ χ) v
      (internalQ Q η₀) hP hPN g.radius g.C g.D g.U second L₂ alloc,hp0,hp1]
    apply he.trans
    have hpow := Real.rpow_le_rpow_of_exponent_le hZone.le
      (show st.width+εold+loss*(Fintype.card α:ℝ)+(1/6)*max
        (length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
          (9/2)*(∑j∈q.indices L₂ alloc,w j)-st.width) 0+(3/4)*mesh ≤
          g.nominal+δwidth+errorRemoval q.p Z q.k-Mrow*branchReserve q.k+
            εold+loss*(Fintype.card α:ℝ)+padding/6+(3/4)*mesh by
        unfold errorRemoval; linarith)
    calc
      _ ≤ Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(Cp^2*(p.control Sp)^2)*
        (1+|v|+height)^degree*Z^_ := mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity))
          hpow (Real.rpow_nonneg (zero_le_one.trans hZone.le) _) (by positivity)
      _ = _ := by ring
  · have hzrow : ∀z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      simpa only [not_exists,not_not] using live
    rw [no_surviving_row_energy_zero src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

#print axioms actual_paid_error_uniform
end
end OAI.SevenEighths.Cycle63FinalError
