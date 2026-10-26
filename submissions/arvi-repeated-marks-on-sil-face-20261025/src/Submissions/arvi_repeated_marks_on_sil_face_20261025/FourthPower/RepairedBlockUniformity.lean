/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform actual nonexceptional block over a fixed finite indexed slot family.
The global degree/control/constant are chosen before every moving live type,
first common ideal/allocation, supplier assignment and physical row.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshNonexceptionalBlock
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstOuterUniformity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedBlockUniformity
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentSourceRow CenteredMomentSectorLocalization CenteredMomentFirstPhysicalSource
open CenteredMomentSecondHeightFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondDyadicRowSupport CenteredMomentSecondChildRadialWidth
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentFirstSectors
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentLogDyadic
open CenteredMomentSecondWindowBudget
open CenteredMomentFiniteProfileExceptional CenteredMomentUncenteredTerminal CenteredExceptionalProfile
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedLiveNormalization
open MixedFirstSeededEnergy MixedFirstSourceWindow MixedFirstSourceMoment
open MixedFirstProfileEnvelope MixedFirstUniformLossBudget MixedFirstChosenEnergy
open MixedFirstActualNonexceptional MixedFirstLiveSource MixedInnerExceptionalBlock
open MixedSupplierFourthRow MixedSupplierPositive MixedSupplierSource MixedSupplierOuterActive
open MixedSupplierOriginalFrequency MixedCanonicalSource ReferencePrimeEnclosure
open OuterFreshSource OuterFreshSelectedWindow OuterFreshConsumer OuterFreshDeclaredRadius
open OuterFreshWindowPair OuterFreshRows OuterFreshNonexceptionalFamily OuterFreshStructure
open OuterFreshAllocatedWindow OuterFreshRootAdmission OuterFreshPairedAllocatedWindow
open OuterFreshAllocationMass OuterFreshActualAllocationPair OuterFreshArtificialSum
open OuterFreshFixedWindows OuterFreshWeightedKernel OuterFreshSelectedKernel OuterFreshNonexceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _

theorem profileMoment_mono {j J : ℕ} (h : j≤J) :
    CenteredMomentSecondWindowBudget.profileMoment j≤
      CenteredMomentSecondWindowBudget.profileMoment J := by
  unfold CenteredMomentSecondWindowBudget.profileMoment
  apply integral_mono (columnDensity_moments logAnnulus logAnnulus_compact logAnnulus_smooth j)
    (columnDensity_moments logAnnulus logAnnulus_compact logAnnulus_smooth J)
  intro w
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg w)) h) (norm_nonneg _)

theorem heightEnvelope_one_le (t : ℝ) : 1≤heightEnvelope t := by
  unfold heightEnvelope
  apply one_le_mul_of_one_le_of_one_le
  · linarith [norm_nonneg t,Real.pi_pos]
  · linarith [Real.pi_pos]

/-- The precise nonlinear envelope is monotone in its checked constants,
degree and control set; the Fourier moment is not discarded or assumed. -/
theorem angleEnvelope_mono {κ : Type u} [Fintype κ] {a b : ℝ}
    (r : Source κ a b) (C C' Kslot : ℝ) (N j J : ℕ)
    (S U : Finset (ℕ×ℕ)) (t₀ tp V Z Rdecl ε : ℝ)
    (hC : 0≤C) (hCC : C≤C') (hK : 0≤Kslot) (hV : 0≤V) (hZ : 0≤Z)
    (hj : j≤J) (hS : S⊆U) :
    angleEnvelope r C Kslot N j S t₀ tp V Z Rdecl ε≤
      angleEnvelope r C' Kslot N J U t₀ tp V Z Rdecl ε := by
  have hC' := hC.trans hCC
  have hp : sourceControl S r.W₁*sourceControl S r.W₂≤sourceControl U r.W₁*sourceControl U r.W₂ :=
    mul_le_mul (MixedPrincipalPositivePart.control_mono hS r.W₁)
      (MixedPrincipalPositivePart.control_mono hS r.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hp0 : 0≤sourceControl S r.W₁*sourceControl S r.W₂ :=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hpSq := pow_le_pow_left₀ hp0 hp 2
  have hh : 1≤height t₀ V r.t₁ r.t₂ := by
    unfold height
    linarith [abs_nonneg t₀,norm_nonneg r.t₁,norm_nonneg r.t₂]
  have hhPow := pow_le_pow_right₀ hh hj
  have hm := profileMoment_mono hj
  have hmSq := pow_le_pow_left₀ (profileMoment_nonneg j) hm 2
  have htPow := pow_le_pow_right₀ (heightEnvelope_one_le tp) (Nat.mul_le_mul_left 2 hj)
  have hslot := pow_nonneg hK (2*N)
  have hc := mul_le_mul_of_nonneg_right hCC hslot
  have hcp := mul_le_mul hc hpSq (sq_nonneg _) (mul_nonneg hC' hslot)
  have hcph := mul_le_mul hcp hhPow (pow_nonneg (zero_le_one.trans hh) _)
    (mul_nonneg (mul_nonneg hC' hslot) (sq_nonneg _))
  have hcphm := mul_le_mul hcph hmSq (sq_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg hC' hslot) (sq_nonneg _))
      (pow_nonneg (zero_le_one.trans hh) _))
  have hscale := div_nonneg (Real.rpow_nonneg hZ Rdecl) fixedPresentationCost_pos.le
  have hbase := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcphm hscale) (Real.rpow_nonneg hZ ε)
  have hfinal := mul_le_mul hbase htPow (pow_nonneg (heightEnvelope_pos tp).le _)
    (profileBase_nonneg r C' Kslot N J U t₀ V Z Rdecl ε hC' hK hV hZ)
  simpa only [angleEnvelope,profileBase] using hfinal

/-- A single dominating constant may occupy the four original constant
positions. Genuine common norms, rootFactor and every scale remain literal. -/
theorem blockBudget_mono {κ : Type u} [Fintype κ] {a b : ℝ}
    (r : Source κ a b) (G E : Id) (Cg Ca Ckernel Cw C Kslot : ℝ)
    (N j J : ℕ) (S U : Finset (ℕ×ℕ))
    (t₀ tp V Z Rdecl ε δ epsilonArt : ℝ)
    (hCg : 0≤Cg) (hCa : 0≤Ca) (hCkernel : 0≤Ckernel) (hCw : 0≤Cw)
    (hC : 0≤C) (hCgC : Cg≤C) (hCaC : Ca≤C) (hCkernelC : Ckernel≤C) (hCwC : Cw≤C)
    (hK : 0≤Kslot) (hV : 0≤V) (hZ : 0≤Z) (hj : j≤J) (hS : S⊆U) :
    Ckernel*((Ca*Z^epsilonArt)*
      Real.sqrt ((Cg*(G.absNorm:ℝ)^δ*(rootFactor r/(G.absNorm:ℝ)))*
        (Cg*(E.absNorm:ℝ)^δ*(rootFactor r/(E.absNorm:ℝ))))*
      angleEnvelope r Cw Kslot N j S t₀ tp V Z Rdecl ε) ≤
    C*((C*Z^epsilonArt)*
      Real.sqrt ((C*(G.absNorm:ℝ)^δ*(rootFactor r/(G.absNorm:ℝ)))*
        (C*(E.absNorm:ℝ)^δ*(rootFactor r/(E.absNorm:ℝ))))*
      angleEnvelope r C Kslot N J U t₀ tp V Z Rdecl ε) := by
  have hrG := div_nonneg (rootFactor_nonneg r) (Nat.cast_nonneg G.absNorm)
  have hrE := div_nonneg (rootFactor_nonneg r) (Nat.cast_nonneg E.absNorm)
  have hNG := Real.rpow_nonneg (Nat.cast_nonneg G.absNorm) δ
  have hNE := Real.rpow_nonneg (Nat.cast_nonneg E.absNorm) δ
  have hG := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCgC hNG) hrG
  have hE := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCgC hNE) hrE
  have hcommon := Real.sqrt_le_sqrt (mul_le_mul hG hE
    (mul_nonneg (mul_nonneg hCg hNE) hrE) (mul_nonneg (mul_nonneg hC hNG) hrG))
  have ha := angleEnvelope_mono r Cw C Kslot N j J S U t₀ tp V Z Rdecl ε
    hCw hCwC hK hV hZ hj hS
  have ha0 := angleEnvelope_nonneg r Cw Kslot N j S t₀ tp V Z Rdecl ε hCw hK hV hZ
  have hp := mul_le_mul (mul_le_mul_of_nonneg_right hCaC (Real.rpow_nonneg hZ epsilonArt)) hcommon
    (Real.sqrt_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hZ epsilonArt))
  have hB := mul_le_mul hp ha ha0
    (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hZ _)) (Real.sqrt_nonneg _))
  exact mul_le_mul hCkernelC hB
    (mul_nonneg (mul_nonneg (mul_nonneg hCa (Real.rpow_nonneg hZ _)) (Real.sqrt_nonneg _)) ha0) hC

/-- Original subset, restoration-surviving subset and actual first-allocation
live subset. This finite family covers the full three-level caller nesting. -/
abbrev ThreeStage (α : Type u) [Fintype α] :=
  Σ T : Finset α, Σ R : Finset T, Finset R

abbrev ThreeStageSlot {α : Type u} [Fintype α] (shape : ThreeStage α) := ↥shape.2.2

theorem three_stage_card {α : Type u} [Fintype α] (shape : ThreeStage α) :
    Fintype.card (ThreeStageSlot shape)≤Fintype.card α := by
  exact (Fintype.card_le_of_injective (fun i : ThreeStageSlot shape=>i.val) Subtype.val_injective).trans
    ((Fintype.card_le_of_injective (fun i : shape.2.1=>i.val) Subtype.val_injective).trans
      (Fintype.card_le_of_injective (fun i : shape.1=>i.val) Subtype.val_injective))

/-- Only fixed constants are consolidated. Every moving norm, source
normalization, root profile multiplier and physical scale remains explicit. -/
theorem blockBudget_single_constant {κ : Type u} [Fintype κ] {a b : ℝ}
    (r : Source κ a b) (G E : Id) (C Kslot : ℝ) (N J : ℕ)
    (control : Finset (ℕ×ℕ)) (t₀ tp V Z Rdecl ε δ epsilonArt : ℝ) (hC : 0≤C) :
    C*((C*Z^epsilonArt)*
      Real.sqrt ((C*(G.absNorm:ℝ)^δ*(rootFactor r/(G.absNorm:ℝ)))*
        (C*(E.absNorm:ℝ)^δ*(rootFactor r/(E.absNorm:ℝ))))*
      angleEnvelope r C Kslot N J control t₀ tp V Z Rdecl ε) =
    C^4*(Z^epsilonArt*
      Real.sqrt (((G.absNorm:ℝ)^δ*(rootFactor r/(G.absNorm:ℝ)))*
        ((E.absNorm:ℝ)^δ*(rootFactor r/(E.absNorm:ℝ))))*
      angleEnvelope r 1 Kslot N J control t₀ tp V Z Rdecl ε) := by
  have hroot : Real.sqrt ((C*(G.absNorm:ℝ)^δ*(rootFactor r/(G.absNorm:ℝ)))*
        (C*(E.absNorm:ℝ)^δ*(rootFactor r/(E.absNorm:ℝ)))) =
      C*Real.sqrt (((G.absNorm:ℝ)^δ*(rootFactor r/(G.absNorm:ℝ)))*
        ((E.absNorm:ℝ)^δ*(rootFactor r/(E.absNorm:ℝ)))) := by
    rw [show (C*(G.absNorm:ℝ)^δ*(rootFactor r/(G.absNorm:ℝ)))*
        (C*(E.absNorm:ℝ)^δ*(rootFactor r/(E.absNorm:ℝ))) =
      C^2*(((G.absNorm:ℝ)^δ*(rootFactor r/(G.absNorm:ℝ)))*
        ((E.absNorm:ℝ)^δ*(rootFactor r/(E.absNorm:ℝ)))) by ring,
      Real.sqrt_mul (sq_nonneg C),Real.sqrt_sq hC]
  rw [hroot]
  unfold angleEnvelope profileBase
  ring

-- BEGIN FINITE FAMILY CONSUMER
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- One dominating degree, control and leading constant for every type in
the finite family. The original N bound is retained. In particular Index may
be ThreeStage ambient, so every moving first-allocation live type is chosen
AFTER these constants and the common event. No analytic estimate is assumed.
-/
theorem uniform_actual_block_family
    (Index : Type v) [Fintype Index] (Slot : Index→Type u) [∀k,Fintype (Slot k)]
    (N Holes : ℕ) (hcard : ∀k,Fintype.card (Slot k)≤N) (Wslot : ℝ→ℂ)
    (a b Lorig Bwindow Lslot Lcap Cap BR0 BH Bdecl lo hi Kslot Bseed ε rho δ epsilonArt : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤Bwindow)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : Bwindow≤Lcap)
    (hslots : (N:ℝ)*Lslot+1≤Bwindow) (hCap : 2≤Cap)
    (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBdecl : 0≤Bdecl)
    (hdeclWindow : Bdecl+1≤Bwindow)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hseedExp : commonExponent Lorig (N:ℝ) Lslot≤Bseed)
    (hε : 0<ε) (hrho : 0<rho) (hδ : 0<δ) (hArt : 0<epsilonArt)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step:=budgetStep Bwindow Bseed ε rho
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),
    ∀(Φ:𝓢(ℝ,ℂ))(decay:ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀k : Index,
    ∀(θ : (Slot k)→RayQuotient.Characters M Hray)(w σ freq : (Slot k)→ℝ)
      (t₀ tp V : ℝ)(R₀ : (Slot k)→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source (Slot k) a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s→
      (∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i,∀P∈s.H,P.val∈R₀ i)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀cover : OriginalEnclosure s,∀u : Id,∀L : Finset (Slot k),∀J : Finset {i // i∉Lᶜ},
    let q:=supplierData s ha u L J
    ∀x : Frozen q,MixedSupplierFourthRow.frozenWeight q x≠0→
    ∀seed : Id,Squarefree seed→u=frozenProduct q x*seed→
    ∀p : FixedLabel (fixedPool q x (residualSource s ha cover u L J x) seed),
    ∀(hC : Supported p.val.1)(hE : Supported p.val.2),
    ∀(τ : Character)(ξ χ₀ : RayCharacter)(U : Finset (CommonIndex p.val.1 p.val.2))
      (ψ : RayCharacter→Character),
      SharpFamily τ (frozenProduct q x) ξ p.val.1 p.val.2 hC hE U ψ→
    ∀(Rfreq K:ℝ),0<K→∀n : Fin 4→ℤ,
    ∀Rdecl : ℝ,physicalWidth τ (frozenProduct q x) p.val.1 p.val.2 U Rfreq Z≤Rdecl→
      Rdecl≤Bdecl→
    let r:=unavoidedResidual s ha cover u L J x
    let ra:=residualSource s ha cover u L J x
    let d:=Real.logb Z (MixedSelectedVolume.volume q)
    (∀G : Id,G=p.val.1 ∨ G=p.val.2→∀B : actualAllocations (tuplePools r) G,
      frozenCoefficient B.val G r.R r.ν r.Wslot r.P≠0→
      Real.logb Z (s.T/pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))+
        2*(∑i : liveIndices B.val,w i.val.val.val)+4*d≤Rdecl-rho ∧
        (3/4:ℝ)*(∑i : liveIndices B.val,w i.val.val.val)<d)→
    let H:=heightCoeff τ tp p.val.1*star (heightCoeff τ tp p.val.2)
    let B:= Z^epsilonArt*
      Real.sqrt (((p.val.1.absNorm:ℝ)^δ*(rootFactor r/(p.val.1.absNorm:ℝ)))*
        ((p.val.2.absNorm:ℝ)^δ*(rootFactor r/(p.val.2.absNorm:ℝ))))*
      angleEnvelope r 1 Kslot N degree control t₀ tp V Z Rdecl ε
    Z^step*‖normalization (r.X₁*r.X₂) r.P‖^2*(1+kernelScale n)^decay*
      ‖H*physicalAverage q x ra seed τ ξ χ₀ Q p.val.1 p.val.2 hC hE U tp Rfreq Φ K n‖≤
      C*(outerScalar p.val.1 p.val.2 K n*normalizer p.val.1 p.val.2 U)*(‖H‖*B) := by
  dsimp only
  choose degreeT controlT CgT CaT hCgT hCaT hsource using fun k : Index =>
    uniform_actual_nonexceptional_block (ι:=Slot k) M Hray hHray
      N Holes (hcard k) Wslot a b Lorig Bwindow Lslot Lcap Cap BR0 BH Bdecl lo hi Kslot Bseed ε rho δ epsilonArt
      hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc hBR0 hBH hBdecl
      hdeclWindow hβ hKslot hBseed hseedExp hε hrho hδ hArt Q hQt hQ72 hQM
  let J : ℕ := ∑k,degreeT k
  let control := (Finset.univ : Finset Index).biUnion controlT
  have hdegree (k : Index) : degreeT k≤J :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
  have hcontrol (k : Index) : controlT k⊆control :=
    Finset.subset_biUnion_of_mem controlT (Finset.mem_univ k)
  refine ⟨J,control,?_⟩
  intro Φ decay η₀ hη₀
  choose CkernelT hCkernelT heta using fun k : Index => hsource k Φ decay
  choose CwT hCwT hbound using fun k : Index => heta k η₀ hη₀
  let Cmax : ℝ := 1+∑k : Index,(CgT k+CaT k+CkernelT k+CwT k)
  have hterm (k : Index) : 0≤CgT k+CaT k+CkernelT k+CwT k := by
    have hg:=hCgT k
    have ha:=hCaT k
    have hk:=hCkernelT k
    have hw:=hCwT k
    linarith
  have hCmax : 0<Cmax := by
    have hs:=Finset.sum_nonneg (fun k (_ : k∈(Finset.univ : Finset Index))=>hterm k)
    dsimp only [Cmax]
    linarith
  have hdom (k : Index) : CgT k≤Cmax ∧ CaT k≤Cmax ∧ CkernelT k≤Cmax ∧ CwT k≤Cmax := by
    have hs:=Finset.single_le_sum (s:=Finset.univ)
      (f:=fun k=>CgT k+CaT k+CkernelT k+CwT k) (fun k _=>hterm k) (Finset.mem_univ k)
    have hg:=hCgT k
    have ha:=hCaT k
    have hk:=hCkernelT k
    have hw:=hCwT k
    dsimp only [Cmax]
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  refine ⟨Cmax^4,pow_pos hCmax _,?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound,eventually_gt_atTop (1:ℝ)] with Z hfamily hZ
  refine ⟨hZ,?_⟩
  intro k θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L T x hx seed hseed hu p
    hC hE τ ξ χ₀ U ψ hψ Rfreq K hK n Rdecl hpaid hcap hgates
  have he := (hfamily k).2 θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L T x hx seed hseed hu p
    hC hE τ ξ χ₀ U ψ hψ Rfreq K hK n Rdecl hpaid hcap hgates
  let q:=supplierData s ha u L T
  let r:=unavoidedResidual s ha cover u L T x
  let H:=heightCoeff τ tp p.val.1*star (heightCoeff τ tp p.val.2)
  have hc:=hdom k
  have hb := blockBudget_mono r p.val.1 p.val.2 (CgT k) (CaT k) (CkernelT k) (CwT k)
    Cmax Kslot N (degreeT k) J (controlT k) control t₀ tp V Z Rdecl ε δ epsilonArt
    (hCgT k).le (hCaT k).le (hCkernelT k) (hCwT k).le hCmax.le
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 (zero_le_one.trans hKslot) hV
    (zero_lt_one.trans hZ).le (hdegree k) (hcontrol k)
  rw [blockBudget_single_constant r p.val.1 p.val.2 Cmax Kslot N J control
    t₀ tp V Z Rdecl ε δ epsilonArt hCmax.le] at hb
  have houter : 0≤outerScalar p.val.1 p.val.2 K n := by unfold outerScalar;positivity
  have hnorm : 0≤normalizer p.val.1 p.val.2 U := (normalizer_pos _ _ hC U).le
  have hp := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (norm_nonneg H))
    (mul_nonneg houter hnorm)
  apply he.trans
  convert hp using 1 <;> ring

end
end Candidate.FourthPower.RepairedBlockUniformity

