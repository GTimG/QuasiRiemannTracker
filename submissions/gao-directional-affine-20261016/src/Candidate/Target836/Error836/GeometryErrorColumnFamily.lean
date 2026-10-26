import Candidate.Target836.SourceProvider.ErrorMain
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Target836.Error836.GeometryErrorColumn
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorActiveInput
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeElements

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Target836ErrorPayment
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentPrimeElements
open CenteredMomentCommonPairedSource Cycle63FinalError Cycle63FinalNatural
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
open Cycle63Moment Cycle63FinalError
open CenteredMomentAmplificationErrorEnergy CenteredMomentSlotRatios
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
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
    (Bmask : ℝ) (hZ : 1 < Z) (χ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hP : q.R₂*q.E₂≠0) (hPN : ((q.R₂*q.E₂).absNorm:ℝ) ≤ Z^Bmask)
    (z : O) (hz : z∈partRows false q.υ χ Q fixedBadMask g.C g.D g.U g.radius) :
    let st := retainedState Z Bmask hZ (g.τ χ) Q (q.R₂*q.E₂) hP hPN g.radius g.C g.D g.U
    st.radial.keep z ∧ 1 ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re := by
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
    (hZ : 0 < Z) :
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
      16*(errorIndex i+2:ℝ)*Z^(-M*Target874836.SourceProvider.ErrorPhysical.branchReserve (errorIndex i+1)))=
      56*∑i : Fin 3,16*(errorIndex i+2:ℝ)*Z^(-M*Target874836.SourceProvider.ErrorPhysical.branchReserve (errorIndex i+1)) := by
  have hn : (0:ℝ) < P.card := by exact_mod_cast hne.card_pos
  have hc : Fintype.card (elementPool P)=P.card := by
    rw [Fintype.card_coe,elementPool_card P hp hbad]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc]
  field_simp

/-- Exact restoration of the original extracted weight. -/
theorem error_column_paid_restore (p : O) (k : ℕ) (Z coefficient energy C envelope : ℝ)
    (hZ : 0 < Z) (hc : 0 ≤ coefficient)
    (hpaid : localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*energy ≤ C*envelope) :
    coefficient*localErrorCost p (k-1)*energy ≤ 
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
    _  ≤  (coefficient*Z^(errorRemoval p Z k-errorMoving p Z k))*(C*envelope) :=
      mul_le_mul_of_nonneg_left hpaid (mul_nonneg hc (Real.rpow_nonneg hZ.le _))
    _ = _ := by ring

/-- A complete finite column family, with its literal source volume and
amplifier denominator still present. The energies come from the genuine
paid error theorem rather than an additional family estimate. -/
theorem actual_paid_error_column_family_uniform {Label : Type*} [Fintype Label]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
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
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Named.amp cell
    ∀q : Label→Chain s,
    (∀j,(q j).k=1 ∨ (q j).k=6 ∨ (q j).k=7) →
    (∀j,3*amp/4 ≤ Real.logb Z (normValue (q j).p)) →
    ∀g : (j : Label)→Geometry s (q j) Z Mrow amp omega ξ bs J (Fintype.card α),
    ∀(χ : Label→RayFourExpansion.RayCharacter)(hP : ∀j,(q j).R₂*(q j).E₂≠0)
      (hPN : ∀j,(((q j).R₂*(q j).E₂).absNorm:ℝ) ≤ Z^Bmask),
    let st := fun j=>retainedState Z Bmask hZ ((g j).τ (χ j)) (internalQ Q η₀)
      ((q j).R₂*(q j).E₂) (hP j) (hPN j) (g j).radius (g j).C (g j).D (g j).U
    let src := fun j=>withHeight (q j).extracted ((g j).τ (χ j)) v
    ∀p : Profiles ap bp,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(seed : Label→Ideal O)(hE₂ : ∀j,Supported (q j).E₂),(∀j,seed j∣(q j).E₂) →
    ∀(Ds : Label→Finset (Ideal O))(T : Label→ℝ),(∀j,1 ≤ T j) →
      (∀j,∀D∈Ds j,Squarefree D ∧ T j ≤ (D.absNorm:ℝ) ∧ (D.absNorm:ℝ) < 2*T j) →
    ∀(P : Finset (Ideal O))(weight : Label→ℝ),(∀j,0 ≤ weight j) →
    let coefficient := fun j=>(56/(P.card:ℝ))*weight j*16*((q j).k+1:ℝ)/volume (src j)
    let rows := fun j=>partRows false (q j).υ (χ j) (internalQ Q η₀)
      fixedBadMask (g j).C (g j).D (g j).U (g j).radius
    (∑j,coefficient j*localErrorCost (q j).p ((q j).k-1)*
      (∑D∈Ds j,∑z∈rows j,‖normalizedColumn (src j) (q j).E₂ (hE₂ j) (q j).R₂ (seed j) D z‖^2)) ≤ 
      Cg*∑j,coefficient j*Z^(errorRemoval (q j).p Z (q j).k-errorMoving (q j).p Z (q j).k)*
        ((src j).toData.profileFactor*(∏a,(src j).M a)^2*
          QuadraticInitialBound.diagonalControl (st j).radial.profile*(p.control Sp)^2*
          (1+|v|+height)^degree*((q j).E₂.absNorm:ℝ)^(εshell-1)*(2*T j)^(3*εshell)*
          Z^((g j).nominal+εwidth*Mrow+ξ/2-Mrow*Target874836.SourceProvider.ErrorPhysical.branchReserve (q j).k+
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
  have hc : 0 ≤ coefficient j := by
    dsimp only [coefficient]
    have hv := volume_pos (src j)
    have hn : 0 ≤ (P.card:ℝ) := Nat.cast_nonneg _
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
    (Z Mrow amp ξ reserve b t : ℝ) (hZ : 1 < Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hp : p≠0) (hcop : ∀j I,I∈
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→IsCoprime (Ideal.span {p}) I)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂) (second : Bool)
    (B₂ : actualAllocations ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).pools (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C))
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm ≤ radicalBound (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ) fixedBadMask p
      (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val (if second then ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).D else ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).C) ((geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n.val)).R ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).ν ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).W ((geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)).P≠0) :
    let chain := geometryErrorActualChain reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hp hcop hw₁ hw₂ n second B₂
    let g := geometryErrorActualGeometry reflected s R seed Z Mrow amp ξ reserve b t (Fintype.card α) hZ bin q p i Bp υ v hp hcop hw₁ hw₂ n second B₂ ψ hυ hf₁ hf₂
    Supported chain.E₂ ∧ (chain.k=1 ∨ chain.k=6 ∨ chain.k=7) ∧
    ∀(Bmask : ℝ)(χ : RayFourExpansion.RayCharacter)(Q : Ideal O)
      (hP : chain.R₂*chain.E₂≠0)(hPN : ((chain.R₂*chain.E₂).absNorm:ℝ) ≤ Z^Bmask)
      (z : O), z∈partRows false chain.υ χ Q fixedBadMask g.C g.D g.U g.radius →
    let st := retainedState Z Bmask hZ (g.τ χ) Q (chain.R₂*chain.E₂) hP hPN g.radius g.C g.D g.U
    st.radial.keep z ∧ 1 ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re := by
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
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1 < Z) (bin : ℤ×(Fin 5→ℤ))
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
end OAI.SevenEighths.Target836ErrorPayment
#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_error_complete_row_admission
#print axioms OAI.SevenEighths.Target836ErrorPayment.error_column_paid_weight_cancel
#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_error_reserve_average

#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_paid_error_column_family_uniform

#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_geometry_error_column_gates

#print axioms OAI.SevenEighths.Target836ErrorPayment.error_column_paid_restore

#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_geometry_error_seed_gates
