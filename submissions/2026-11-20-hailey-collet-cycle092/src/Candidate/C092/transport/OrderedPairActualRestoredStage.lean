/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual CenteredAt target reduced to true averaged physical prices on
its compensated native children. No energy front or reference Box is assumed. -/
import Candidate.C092.transport.OrderedPairActualRestoredBounds
import Candidate.C092.transport.OrderedPairPhaseTerminal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairActualRestored
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
local notation "O"=>HeckeFamily.O
variable {Slot:Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM:Ideal O) [NeZero rayM] (Hr:Subgroup (O⧸rayM)ˣ)
variable (hHr:RayOrthogonality.globalUnits rayM ≤ Hr)

def CenteredAveragedAt (N Y l : ℝ) (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (_bΦ mesh _ε Z : ℝ) (hZ : 1<Z) (hmesh : mesh ≤ 1/6)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (J : ℕ) (cRad ξ κ loss ξsecond : ℝ)
    (Cz Ct : RepairedSourceSideSupply.RootShape Slot→ℝ) (Qprice : Ideal O) : Prop :=
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
    AveragedRestoredFamilyAt T rayM Hr hHr Z hZ W hW hWs η₀₁ η₁ η₂
      (fun i=>θ₁ i.val) (fun i=>w i.val) (fun i=>v₁ i.val)
      (fun i=>hw i.val) (fun i=>(hwm i.val).trans hmesh)
      t₁ t₁ t₂ p X₁ X₂ (Z^shortWidth) (X₁*X₂/Z^shortWidth)
      (max X₁ (Z^shortWidth)) (max X₂ (X₁*X₂/Z^shortWidth))
      height cRad ξ κ loss ξsecond controls degree J Cz Ct 1 Qprice fixedBadMask


/-- Literal original CenteredAt, with only actual averaged physical children
left to price. Constants and the finite child fees precede all live arrays. -/
theorem centered_at_of_averaged (N Y l mesh ε:ℝ)
    (hy0:sourceY0 ≤ Y)(hy1:Y ≤ sourceY)(hn:N ≤ sourceRatio*Y)
    (hl:l ≤ sourceWidth N Y)(hmesh:mesh ≤ 1/6)(hε:0<ε)
    (J degree:ℕ)(W:ℝ→ℂ)(hW:Continuous W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (controls:Finset (ℕ×ℕ))(h00:(0,0)∈controls)
    (cRad ξ κ ξsecond εmass loss:ℝ)(hcRad:1 ≤ cRad)(hξ:0<ξ)(hκ:0<κ)
    (hξsecond:0<ξsecond)(hsmall:ξ/2+κ ≤ 22)(hεmass:0<εmass)(hloss:loss+εmass ≤ ε/2) :
    ∃C:ℝ,∃Cz Ct:RepairedSourceSideSupply.RootShape Slot→ℝ,
      0<C ∧ (∀k,0<Cz k ∧ 0<Ct k) ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(hZ:1<Z)(bΦ:ℝ)(η₁ η₂ η₀₁ η₀₂:Character)(Q₁ Q₂ Qprice:Ideal O),
      CenteredAveragedAt rayM Hr hHr N Y l W hW hWs bΦ mesh ε Z hZ hmesh
        η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls J cRad ξ κ loss ξsecond Cz Ct Qprice →
      CenteredAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z
        η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls C := by
  obtain ⟨C,Cz,Ct,hC,hconstants,hbound⟩:=actual_aligned_of_averaged_family_final Slot J degree W hW hWs
    controls h00 cRad ξ κ ξsecond εmass ε hcRad hξ hκ hξsecond hsmall hεmass hε
  refine ⟨C,Cz,Ct,hC,hconstants,?_⟩
  filter_upwards [hbound] with Z hb
  refine ⟨hb.1,?_⟩
  intro hZ bΦ η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ Qprice hsupply
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
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
  have hparentprod:X₁*X₂=q*Y₂:=by dsimp [Y₂];field_simp
  have hsumT:(∑i:T,w i.val) ≤ l:=by simpa only [Finset.sum_coe_sort] using hsum
  have hfamily:=hsupply T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hheight hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hxn hxy rows mark hk₁ hk₂ hrad hm₁ hm₂ hlong₁ hlong₂
  have hσ₁:σ₁=fun _=>(33/50:ℝ):=funext (fun i=>le_antisymm (hσ₁hi i) (hσ₁lo i))
  have hmark:∀u∈rows,∀i:T,‖mark i.val u‖=‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
    (CenteredMomentPrimeSlot.primePool rayM Hr 2 (Z^(w i.val)))
    (fun I=>idealCoeff (relativeCharacter rayM Hr hHr η₀₁ (θ₁ i.val)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i.val)) (33/50) (v₁ i.val) I) t₁ (Z^(w i.val))‖:=by
    intro u hu i
    have hm:=hm₁ u hu i.val i.property
    dsimp only [QRH.Cycle092.WholeSlot.originalPools,QRH.Cycle092.WholeSlot.originalCoefficients] at hm
    rw [hσ₁] at hm
    exact hm
  have hsw:(115/1000:ℝ)=shortWidth:=by norm_num [shortWidth]
  have hh:=hb.2 hZ T rayM Hr hHr η₀₁ η₁ η₂ (fun i=>θ₁ i.val) (fun i=>w i.val) (fun i=>v₁ i.val)
    (fun i=>hw i.val) (fun i=>(hwm i.val).trans hmesh) t₁ t₁ t₂ p
    X₁ X₂ q Y₂ (max X₁ q) (max X₂ Y₂) N Y l height loss
    hy0 hy1 hn hxn hxy hsumT hl (by simpa only [hsw] using hlong₁.le)
    (by simpa only [hsw] using hlong₂.le) (by simp only [hsw];rfl)
    (by simpa only [hsw] using hqY₂) hparentprod
    (le_max_left _ _) (le_max_right _ _) (le_max_left _ _) (le_max_right _ _)
    (max_le hxcap hqcap) (max_le hycap hY₂cap) hheight hloss
    1 Qprice fixedBadMask hfamily rows mark hrad hmark
  have hA:0 ≤ C*(p.control controls)^2*(1+|t₁|+|t₂|+height)^degree*Z^(1+ε):=by positivity
  have hd:=mul_le_mul_of_nonneg_right radial_diagonal_ge_one hA
  exact hh.trans (by convert hd using 1 <;> ring)

#print axioms centered_at_of_averaged
end
end QRH.Cycle092.OrderedPairActualRestored
