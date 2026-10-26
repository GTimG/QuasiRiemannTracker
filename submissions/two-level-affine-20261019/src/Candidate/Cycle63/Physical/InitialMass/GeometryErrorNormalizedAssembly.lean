/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorNormalized
import Candidate.Cycle25.Energy.Endpoint

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
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
open Cycle63FinalNatural Cycle63Moment Cycle63FinalError
local instance errorNormalizedAssemblyDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- The genuine ordinary filter admits either ray of the full physical
pair. Its complete row set is independent of which ray names the filter. -/
theorem actual_error_ordinary_rows_eq (η : Character) (χ ψ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) :
    partRows false η χ Q fixedBadMask C D U R=
      partRows false η ψ Q fixedBadMask C D U R := by
  ext z
  exact (actual_error_ordinary_rows_neg η χ 1 Q hQ C D U R z).symm.trans
    (actual_error_ordinary_rows_neg η ψ 1 Q hQ C D U R z)

/-- Right columns sum over the literal negated physical row. Reindexing
this entire set occurs before either common allocation or residual ideal. -/
theorem actual_error_complete_right_rows (η : Character) (χ ψ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (f : O→ℝ) :
    (∑z∈partRows false η χ Q fixedBadMask C D U R,f (-z))=
      ∑z∈partRows false η ψ Q fixedBadMask C D U R,f z := by
  apply Finset.sum_bij (fun z _=>-z)
  · intro z hz
    exact (actual_error_ordinary_rows_neg η χ ψ Q hQ C D U R z).mpr hz
  · intro z hz z' hz' heq
    exact neg_inj.mp heq
  · intro z hz
    refine ⟨-z,(actual_error_ordinary_rows_neg η ψ χ Q hQ C D U R z).mpr hz,?_⟩
    exact neg_neg z
  · intro z hz
    rfl

/-- Complete actual columns use the admitted ray-specific ordinary sets,
with the right inverse ray at its original negative height shift. -/
theorem actual_error_complete_column_rows {ι : Type*}[Fintype ι]
    (s : Input ι)(τ : RayCharacter→ Character)
    (C D : Ideal O)(hC : Supported C)(hD : Supported D)
    (U : Finset (CommonIndex C D))(R seed L Q : Ideal O)(radius : ℝ)
    (hQ : Q≤Ideal.span {(72:O)})(χ₀ χ ψ : RayCharacter)(second : Bool)(t u : ℝ) :
    (∑z∈partRows false s.η χ₀ Q fixedBadMask C D U radius,
      if second then
        ‖normalizedColumn (withHeight s (τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t)))) D hD R seed L (-z)‖^2
      else
        ‖normalizedColumn (withHeight s (τ χ) (s.t+2*Real.pi*(u-t))) C hC R seed L z‖^2)=
    if second then
      ∑z∈partRows false s.η ψ⁻¹ Q fixedBadMask C D U radius,
        ‖normalizedColumn (withHeight s (τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t)))) D hD R seed L z‖^2
    else
      ∑z∈partRows false s.η χ Q fixedBadMask C D U radius,
        ‖normalizedColumn (withHeight s (τ χ) (s.t+2*Real.pi*(u-t))) C hC R seed L z‖^2 := by
  cases second
  · simp only [Bool.false_eq_true,ite_false]
    rw [actual_error_ordinary_rows_eq s.η χ₀ χ Q hQ C D U radius]
  · simp only [ite_true]
    exact actual_error_complete_right_rows s.η χ₀ ψ⁻¹ Q hQ C D U radius
      (fun z=>‖normalizedColumn (withHeight s (τ ψ⁻¹) (s.t+2*Real.pi*(u-(-t)))) D hD R seed L z‖^2)

variable [Cycle63.AffineLedger] in
/-- The degree, profile control and threshold precede the moving finite
block family. Each column comes from the genuine paid error estimate. -/
theorem actual_paid_error_column_family_after_threshold {α : Type*}[Fintype α][DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold loss margin : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hL : 0≤L) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hloss : 0<loss) (hmargin : 0< margin) (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (bs J εwidth εpad Mmin : ℝ)
    (window pad εshell : ℝ) (hwindow : 0≤window) (hpad : 0<pad) (heshell : 0<εshell)
    (hbs : 1≤bs) (hJ : 0<J) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀_hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh : ℝ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=bp → s.b₂=bp →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^L) →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B*unit →
    let cell := Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀{Label : Type*}[Fintype Label],∀q : Label→ Chain s,
    (∀j,(q j).k=1 ∨ (q j).k=6 ∨ (q j).k=7) →
    (∀j,Cycle63.AffineLedger.primeFraction*amp≤Real.logb Z (normValue (q j).p)) →
    ∀g : (j : Label)→Geometry s (q j) Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : Label→RayFourExpansion.RayCharacter)(hP : ∀j,(q j).R₂*(q j).E₂≠0)
      (hPN : ∀j,(((q j).R₂*(q j).E₂).absNorm:ℝ)≤Z^Bmask),
    let st := fun j=>retainedState Z Bmask hZ ((g j).τ (χ j)) (internalQ Q η₀)
      ((q j).R₂*(q j).E₂) (hP j) (hPN j) (g j).radius (g j).C (g j).D (g j).U
    let src := fun j=>withHeight (q j).extracted ((g j).τ (χ j)) v
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(seed : Label→ Ideal O)(hE₂ : ∀j,Supported (q j).E₂),(∀j,seed j∣(q j).E₂) →
    ∀(Ds : Label→Finset (Ideal O))(T : Label→ℝ),(∀j,1≤T j) →
      (∀j,∀D∈Ds j,Squarefree D ∧ T j≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T j) →
    ∀(P : Finset (Ideal O))(weight : Label→ℝ),(∀j,0≤weight j) →
    let coefficient := fun j=>(56/(P.card:ℝ))*weight j*16*((q j).k+1:ℝ)/volume (src j)
    let rows := fun j=>partRows false (q j).υ (χ j) (internalQ Q η₀)
      fixedBadMask (g j).C (g j).D (g j).U (g j).radius
    (∑j,coefficient j*localErrorCost (q j).p ((q j).k-1)*
      (∑D∈Ds j,∑z∈rows j,‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2))≤
      Cg*∑j,coefficient j*Z^(errorRemoval (q j).p Z (q j).k-errorMoving (q j).p Z (q j).k)*
        ((src j).toData.profileFactor*(∏a,(src j).M a)^2*
          QuadraticInitialBound.diagonalControl (st j).radial.profile*(p.control Sp)^2*
          (1+|v|+height)^degree*((q j).E₂.absNorm:ℝ)^(εshell-1)*(2*T j)^(3*εshell)*
          Z^((g j).nominal unit+εwidth*unit+ξ/2-unit*branchReserve (q j).k+
            εold+loss*(Fintype.card α:ℝ)+(omega+εpad*unit)/6+Cycle63.Optimization.slotPrice*mesh+pad)) := by
  have hbound := actual_paid_error_column_uniform (α:=α) M H hH W A B ap bp
    Bmask L lo hi Mcap εold loss margin hA hWs hW hB hap hap' hbp hBmask hL hMcap
    hεold hloss hmargin hbeta bs J εwidth εpad Mmin window pad εshell
    hwindow hpad heshell hbs hJ hew hep hmin
  obtain ⟨degree,Sp,hbound⟩ := hbound
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hZs⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hZs] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh hm hsupper hsb₁ hsb₂ hw hwL hmesh hwm
    hσlo hσhi hheight hfreq hOrig hwin unit Mrow omega ξ hMmin hω hξ hMcap' hfit hslot haff
    cell amp Label _ q hk hprime g χ hP hPN st src p hp₁ hp₂ seed hE₂ hseed Ds T hT hDs P weight
    hwgt coefficient rows
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hrow (z : O) (hz : z∈rows j) := actual_error_complete_row_admission s (q j)
    Z Mrow amp omega ξ bs J (g j) Bmask hZ (χ j) (internalQ Q η₀) (hP j) (hPN j) z hz
  have hcol := hz.2 hZ s θ w σ freq v height mesh hm hsupper hsb₁ hsb₂ hw hwL
    hmesh hwm hσlo hσhi hheight hfreq hOrig hwin unit Mrow omega ξ hMmin hω hξ hMcap' hfit
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

end
end OAI.SevenEighths.Cycle63InitialMass
