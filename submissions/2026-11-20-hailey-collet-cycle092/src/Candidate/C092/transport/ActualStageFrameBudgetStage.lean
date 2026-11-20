/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual CenteredAt target reduced to true averaged physical prices on
its compensated native children. No energy front or reference Box is assumed. -/
import Candidate.C092.transport.OrderedPairActualRestoredBounds
import Candidate.C092.transport.ActualStageFrameBudgetFamily
import Candidate.C092.transport.OrderedPairPhaseTerminal
import Candidate.C092.transport.OrderedPairActualRestoredModulus
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentLattice
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.SilDensitySplit.CubeFree.FP
open QRH.Cycle092.NativeStrip QRH.Cycle092.WholeSlot
open QRH.Cycle092.OrderedPairPhase QRH.Cycle092.ReferenceShortP3
open QRH.Cycle090
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.FixedFramePacking
open QRH.Cycle092.TwistedRawBallRootProducer QRH.Cycle092.PairedRetainedBudget
open RepairedSourceSideSupply MixedInnerExceptionalBlock MixedPrincipalPair
open CenteredMomentActiveSource CenteredMomentSourceRow
open QRH.Cycle092.CofactorOrdinary QRH.Cycle092.FixedRayPair
open Candidate.FourthPower.KernelCollisionEnergy
open QRH.SilDensitySplit.CubeFree.FP.RestorationFamily
open QRH.SilDensitySplit.CubeFree.FP.RestorationCollisionEnergy
open RestoredInitialSource RestoredRootDictionary MixedCanonicalSource NativeMaskedEnergy
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open CenteredMomentDetectorPlainFiberSource
local notation "O"=>HeckeFamily.O
variable {Slot:Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM:Ideal O) [NeZero rayM] (Hr:Subgroup (O⧸rayM)ˣ)
variable (hHr:RayOrthogonality.globalUnits rayM ≤ Hr)

def CenteredFramesAt (N Y l : ℝ) (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (_bΦ mesh _ε Z : ℝ) (hZ : 1<Z) (hmesh : mesh ≤ 1/6)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (J : ℕ) (cRad ξ κ loss ξsecond : ℝ)
    (Cz Ct : RepairedSourceSideSupply.RootShape Slot→ℝ) (Qprice : Ideal O)(Cfee δ:ℝ) : Prop :=
  ∀ (T : Finset Slot) (θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr) (w σ₁ σ₂ v₁ v₂ : Slot→ℝ)
    (t₁ t₂ height : ℝ),
    (hw : ∀ i,0 ≤ w i) → (hwm : ∀ i,w i ≤ mesh) →
    (∀ i,(33/50:ℝ) ≤ σ₁ i) → (∀ i,σ₁ i ≤ (33/50:ℝ)) →
    (∀ i,(33/50:ℝ) ≤ σ₂ i) → (∀ i,σ₂ i ≤ (33/50:ℝ)) →
    0 ≤ height → (∀ i,|v₁ i| ≤ height) → (∀ i,|v₂ i| ≤ height) → (∑ i∈T,w i) ≤ l →
  ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
    length Z X₁ ≤ N → length Z X₂ ≤ Y →
  ∀ (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
    (∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
    (∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
    (∀ u∈s,rowNorm u ≤ Z) →
    (∀ u∈s,∀ i∈T,‖mark i u‖=
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀₁ θ₁ W Z w σ₁ v₁ i) t₁ (Z^(w i))‖) →
    (∀ u∈s,∀ i∈T,‖mark i u‖=
      ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀₂ θ₂ W Z w σ₂ v₂ i) t₂ (Z^(w i))‖) →
    Z^shortWidth < X₁ → Z^shortWidth < X₂ →
    FrameRestoredFamilyAt T rayM Hr hHr Z hZ W hW hWs η₀₁ η₁ η₂
      (fun i=>θ₁ i.val) (fun i=>w i.val) (fun i=>v₁ i.val)
      (fun i=>hw i.val) (fun i=>(hwm i.val).trans hmesh)
      t₁ t₁ t₂ p X₁ X₂ (Z^shortWidth) (X₁*X₂/Z^shortWidth)
      (max X₁ (Z^shortWidth)) (max X₂ (X₁*X₂/Z^shortWidth))
      height cRad ξ κ loss ξsecond controls degree J Cz Ct 1 Qprice fixedBadMask Cfee δ mesh (sourceWidth N Y)


def NativeFramesStageSupply (N Y l mesh ε cRad ξ κ loss ξsecond δ:ℝ)
    (hmesh:mesh ≤ 1/6) : Prop :=
  ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
  ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM  ≤  Hr),
  ∀ W : ℝ→ℂ, ∀hW:ContDiff ℝ ∞ W, ∀hWs:Function.support W⊆Set.Icc (1:ℝ) 2,
  ∀ bΦ : ℝ, 2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
  ∀ (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O),
    Q₁ ≤ rayM → internalQ Q₁ η₀₁ ≠ 0 → internalQ Q₁ η₀₁ ≠ ⊤ →
    internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)} →
    Q₂ ≤ rayM → internalQ Q₂ η₀₂ ≠ 0 → internalQ Q₂ η₀₂ ≠ ⊤ →
    internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)} →
    let base:=η₀₁.product η₁.inverse
    let q:=stageQ Q₁ η₀₁ base η₁ η₂
    q≠0 → q≠⊤ → q ≤ rayM → q ≤ Ideal.span {(72:O)} → q ≤ base.modulus →
    q ≤ η₁.modulus → q ≤ η₂.modulus → internalQ q base=q →
    internalQ q (base.product η₁)=q → internalQ q (base.product η₂)=q →
    ∃ J degree : ℕ, ∃ controls : Finset (ℕ×ℕ), (0,0)∈controls ∧
    ∀ Cz Ct : RepairedSourceSideSupply.RootShape Slot→ℝ, (∀k,0<Cz k ∧ 0<Ct k) →
    ∃Cfee:ℝ,0 ≤ Cfee ∧ ∀ᶠZ:ℝ in atTop, ∀hZ:1<Z,
      CenteredFramesAt rayM Hr hHr N Y l W hW.continuous hWs bΦ mesh ε Z hZ hmesh
        η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls J cRad ξ κ loss ξsecond Cz Ct q Cfee δ

/-- Actual global stage integration. The mesh and analytic degrees precede
all positive root fees. The sole analytic supplier prices literal physical
classes on the actual restoration/inverse family; retained energies are
not inputs to this theorem. -/
theorem native_averaged_of_frames (N Y l mesh ε cRad κ loss ξsecond δ:ℝ)
    (hy0:sourceY0 ≤ Y)(hy1:Y ≤ sourceY)(hn:N ≤ sourceRatio*Y)
    (hl:l ≤ sourceWidth N Y)(hwidth:l+mesh ≤ sourceWidth N Y)
    (hmesh0:0 ≤ mesh)(hmesh:mesh ≤ 1/6)(hcRad:1 ≤ cRad)
    (hκ:κ ≤ 1/1500)(hδ:0<δ)(hgap:3*δ<loss)(hloss:0 ≤ loss)
    (supply:NativeFramesStageSupply N Y l mesh ε cRad κ κ loss ξsecond δ hmesh) :
    NativeAveragedStageSupply N Y l mesh ε cRad κ κ loss ξsecond hmesh := by
  intro Slot instS instD rayM instM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  dsimp only
  intro hq0 hqt hqray hq72 hqbase hqη₁ hqη₂ hqB hqBη₁ hqBη₂
  obtain ⟨J,degree,controls,h00,hprice⟩:=supply Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
    hq0 hqt hqray hq72 hqbase hqη₁ hqη₂ hqB hqBη₁ hqBη₂
  refine ⟨J,degree,controls,h00,?_⟩
  intro Cz Ct hconstants
  obtain ⟨Cfee,hCfee,hframe⟩:=hprice Cz Ct hconstants
  let K:=RestoredRootSource.slotBound W hW.continuous hWs
  have hK:1 ≤ K:=(RestoredRootSource.slotBound_spec W hW.continuous hWs).1
  have hev (k:RootShape Slot):=retained_of_native_frames (ι:=RootSlot k)
    (Fintype.card Slot) J degree K Cfee δ loss mesh N Y l κ hK hCfee hδ hgap hloss
    hmesh0 hy1 hn hκ hwidth controls h00 (Cz k) (Ct k) (hconstants k).1.le (hconstants k).2.le
  have hall:=Filter.eventually_all.mpr hev
  filter_upwards [hframe,hall,restored_caps (Fintype.card Slot)] with Z hf hr hc
  intro hZ T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hheight hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hxn hxy rows mark hk₁ hk₂ hrad hm₁ hm₂ hlong₁ hlong₂
  have hz:0<Z:=zero_lt_one.trans hZ
  have hN1:N ≤ 1:=by norm_num [sourceRatio,sourceY] at hn hy1;linarith
  have hY1:Y ≤ 1:=by norm_num [sourceY] at hy1;linarith
  have hNY:N+Y ≤ 1+shortWidth:=by norm_num [sourceRatio,sourceY,shortWidth] at hn hy1 ⊢;linarith
  have hxcap:X₁ ≤ Z:=by
    simpa only [Real.rpow_one] using (scale_le_of_length hZ hxn).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hN1)
  have hycap:X₂ ≤ Z:=by
    simpa only [Real.rpow_one] using (scale_le_of_length hZ hxy).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hY1)
  let q:=Z^shortWidth
  let Y₂:=X₁*X₂/q
  have hq:0<q:=Real.rpow_pos_of_pos hz _
  have hqcap:q ≤ Z:=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le
      (show shortWidth ≤ (1:ℝ) by norm_num [shortWidth])
  have hprodCap:X₁*X₂ ≤ Z^(N+Y):=by
    calc
      _ ≤ Z^N*Z^Y:=mul_le_mul (scale_le_of_length hZ hxn) (scale_le_of_length hZ hxy)
        hX₂.le (Real.rpow_nonneg hz.le _)
      _=Z^(N+Y):=(Real.rpow_add hz _ _).symm
  have hY₂cap:Y₂ ≤ Z:=by
    calc
      _ ≤ Z^(N+Y)/Z^shortWidth:=div_le_div_of_nonneg_right hprodCap hq.le
      _=Z^(N+Y-shortWidth):=(Real.rpow_sub hz _ _).symm
      _ ≤ Z:=by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : N+Y-shortWidth ≤ 1)
  have hqY₂:q ≤ Y₂:=by
    apply (le_div_iff₀ hq).mpr
    exact mul_le_mul hlong₁.le hlong₂.le hq.le hX₁.le
  have hsumT:(∑i:T,w i.val) ≤ l:=by simpa only [Finset.sum_coe_sort] using hsum
  have hfamily:=hf hZ T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hheight hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hxn hxy rows mark hk₁ hk₂ hrad hm₁ hm₂ hlong₁ hlong₂
  intro r tc A ti hinj d hd g
  dsimp only
  let data:=restoredMarksData rayM Hr Z hZ W hW.continuous hWs η₀₁ η₁
    (fun i:T=>θ₁ i.val) (fun i:T=>w i.val) (fun i:T=>v₁ i.val)
    (fun i=>hw i.val) (fun i=>(hwm i.val).trans hmesh) t₁ p r tc A ti
  let s:=dividedCanonicalSource rayM Hr hHr data X₁ X₂ q Y₂ t₁ t₂ d g
  let cover:=canonicalPairSource_original_enclosure rayM Hr hHr data _ _ _ _ t₁ t₂
    g.x₁ g.x₂ g.y₁ g.y₂ g.product g.capx₁ g.capx₂ g.capy₁ g.capy₂
  let k:RootShape Slot:=⟨T,remainingSet r A⟩
  have hNroot:Fintype.card (remainingSet r A) ≤ Fintype.card Slot:=root_slot_card k
  have hM:∀i,s.M i ≤ K:=fun i=>le_rfl
  have hP:∀i,s.P i=Z^(data.w i):=fun i=>rfl
  have hwr:(∑i:remainingSet r A,data.w i) ≤ l:=
    (actual_survivor_width r A (fun i:T=>w i.val) (fun i=>hw i.val)).trans hsumT
  have caps:=hc.2 (remainingSet r A) s (primeEnclosure Z) d X₁ X₂ q Y₂
    (max X₁ q) (max X₂ Y₂) N Y l data.w hNroot data.hw hP hy0 hy1 hn hxn hxy hwr hl
    (by convert hlong₁.le using 1 <;> norm_num [shortWidth])
    (by convert hlong₂.le using 1 <;> norm_num [shortWidth])
    (by change Z^(115/1000:ℝ) ≤ Z^shortWidth;norm_num [shortWidth])
    (by convert hqY₂ using 1 <;> norm_num [q,shortWidth])
    (le_max_left _ _) (le_max_right _ _) (le_max_left _ _) (le_max_right _ _)
    (max_le hxcap hqcap) (max_le hycap hY₂cap) hd rfl rfl rfl rfl rfl
  have hactive:∀I∈RootColoredSeed.active s (by norm_num) (idealCoeff η₁) (idealCoeff η₂),
      (I.absNorm:ℝ) ≤ Z^(8:ℝ):=by
    intro I hI
    have hhI:TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1 I≠0:=by
      change I∈activeSource _ _ at hI
      rw [mem_activeSource] at hI
      exact hI.2
    exact (TwistedRawSource.sourceColumn_cap s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1 I hhI).2.trans caps.norm
  have hfc:=hfamily r tc A ti hinj d hd g
  have hAmp:=actual_divided_amplitude rayM Hr hHr data X₁ X₂ q Y₂ t₁ t₂ d g height degree controls
  change amplitude s 0 height degree controls 1=(p.control controls)^2*(1+|t₁|+|t₂|+height)^degree at hAmp
  rw [←hAmp] at hfc ⊢
  exact (hr k).2 s hNroot hM cover data.w data.hw (fun i=>hwm i.val.val) hP hwr η₁ η₂
    ColoredRootRestore.bareBase 1 (stageQ Q₁ η₀₁ (η₀₁.product η₁.inverse) η₁ η₂) fixedBadMask
    (cRad*Z) (Z^(8:ℝ)) ξsecond height
    (by nlinarith) hheight hactive (by simpa only [Real.rpow_two] using caps.invVolume) hfc

#print axioms native_averaged_of_frames
end
end QRH.Cycle092.ActualStageFrameBudget
