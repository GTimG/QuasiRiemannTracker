/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Every actual small-radius regular row has the genuine global prime ceiling.
The independent native pair source is invoked on those same original rows.
-/
import Candidate.C092.transport.StrongPairSmallAll
import Candidate.C092.transport.StrongPairPhysical
import Candidate.C092.transport.TerminalActualRowState
import Candidate.C092.transport.OriginalGlobalResponse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy CenteredMomentEnergyBands
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafSmallActual_bf65bde799804d20_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- No low-row bound is an input. The established global boundary supplies
it on each sparse original row, including every zero-width whole slot. -/
theorem terminal_actual_small_radii {n y : ℝ}
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃ buffer : ℝ,0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ (W : ℝ → ℂ),ContDiff ℝ ∞ W  →  Function.support W⊆Icc (1:ℝ) 2  → 
    ∀ bΦ : ℝ,2 ≤ bΦ  →  Function.support (radialMajorant:ℝ → ℂ)⊆Iic bΦ  → 
    ∀ (old base η₁ η₂ η₀₁ η₀₂ : Character) (Qold Q₁ Q₂ : Ideal O),
      Qold ≤ rayM  →  Qold ≤ base.modulus  → 
      Q₁ ≤ rayM  →  internalQ Q₁ η₀₁≠0  →  internalQ Q₁ η₀₁≠⊤  →  internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)}  → 
      Q₂ ≤ rayM  →  internalQ Q₂ η₀₂≠0  →  internalQ Q₂ η₀₂≠⊤  →  internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)}  → 
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀ V : ℝ,0 ≤ V  →  V ≤ 98/100  → 
    ∀ (J : Finset Slot) (θ θ₁ θ₂ : Slot → RayQuotient.Characters rayM Hr)
      (w σ σ₁ σ₂ v v₁ v₂ : Slot → ℝ) (tOld t₁ t₂ heightOld height : ℝ),
      (∀i,0 ≤ w i)  →  (∀i,w i ≤ mesh)  → 
      (∀i,σ i=33/50)  → 
      (∀i,(33/50:ℝ) ≤ σ₁ i)  →  (∀i,σ₁ i ≤ (33/50:ℝ))  → 
      (∀i,(33/50:ℝ) ≤ σ₂ i)  →  (∀i,σ₂ i ≤ (33/50:ℝ))  → 
      (∀i,|v i| ≤ heightOld)  →  |tOld|+heightOld ≤ U^(1/2:ℝ)  → 
      0 ≤ height  →  (∀i,|v₁ i| ≤ height)  →  (∀i,|v₂ i| ≤ height)  → 
      (∑i ∈ J,w i) ≤ sourceWidth n y-(u:ℝ)  → 
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁  →  0 < X₂  → 
      length U X₁ ≤ n  →  length U X₂ ≤ y  → 
    ∀ rows : Finset FreeRow,
      (∀z ∈ rows,initialKeep old Qold z.val)  → 
      (∀z ∈ rows,initialKeep η₁ (internalQ Q₁ η₀₁) z.val)  → 
      (∀z ∈ rows,initialKeep η₂ (internalQ Q₂ η₀₂) z.val)  → 
      (∀z ∈ rows,rowNorm z ≤ U^V)  → 
      (∀z ∈ rows,∀i ∈ J,‖originalMark rayM Hr hHr old base θ W U w σ v tOld i z‖=
        ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 z.val
          (originalPools rayM Hr 2 U w i)
          (originalCoefficients rayM Hr hHr η₀₁ θ₁ W U w σ₁ v₁ i) t₁ (U^(w i))‖)  → 
      (∀z ∈ rows,∀i ∈ J,‖originalMark rayM Hr hHr old base θ W U w σ v tOld i z‖=
        ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 z.val
          (originalPools rayM Hr 2 U w i)
          (originalCoefficients rayM Hr hHr η₀₂ θ₂ W U w σ₂ v₂ i) t₂ (U^(w i))‖)  → 
      finiteEnergyOn J rows η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
        (originalMark rayM Hr hHr old base θ W U w σ v tOld) ≤ 
        C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
          (1+|t₁|+|t₂|+height)^degree*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  obtain ⟨mesh,hm,hsource⟩:=independent_all_small_radii hβ hy0 hy1 hn0 hn1
    (by norm_num : (0:ℝ) ≤ 3/4) (le_rfl : (3/4:ℝ) ≤ 3/4)
  refine ⟨min mesh 1,lt_min hm zero_lt_one,?_⟩
  intro Slot _ _
  obtain ⟨buffer,hbuffer,hsource⟩:=hsource Slot
  refine ⟨buffer,hbuffer,?_⟩
  intro rayM _ Hr hHr W hW hWs bΦ hbΦ hΦ old base η₁ η₂ η₀₁ η₀₂ Qold Q₁ Q₂
    hQoldM hQoldBase hQ₁M hQ₁0 hQ₁t hQ₁72 hQ₂M hQ₂0 hQ₂t hQ₂72
  obtain ⟨Cg,hCg,hglobal⟩:=GlobalResponse.all_regular_low (Slot:=Slot) hβ rayM Hr hHr W hWs hW
    buffer bΦ hbuffer (by linarith)
  obtain ⟨degree,controls,C,hC,hsource⟩:=hsource rayM Hr hHr W hW hWs bΦ hbΦ hΦ
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁M hQ₁0 hQ₁t hQ₁72 hQ₂M hQ₂0 hQ₂t hQ₂72 Cg hCg.le
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hsource,hglobal base,TerminalActualRow.fixed_character_conductor old (by norm_num : (0:ℝ) < 1/100)] with U hsource hglobal hmod
  refine ⟨hmod.1,?_⟩
  intro V hV0 hV1 J θ θ₁ θ₂ w σ σ₁ σ₂ v v₁ v₂ tOld t₁ t₂ heightOld height
    hw hwm hσ hσ₁lo hσ₁hi hσ₂lo hσ₂hi hv ht hh hv₁ hv₂ hwidth p X₁ X₂ hX₁ hX₂ hXN hXY
    rows hkOld hk₁ hk₂ hy hm₁ hm₂
  let state:=TerminalActualRow.state old Qold bΦ U V (1/100) hmod.1.le hV0 (by norm_num) hΦ hmod.2
  have hstate : state.width ≤ 2 := by change V+1/100 ≤ 2;linarith
  have hslot (z : FreeRow) (hz : z ∈ rows) :
      QRH.Cycle092.WholeSlot.LowRows Finset.univ old (fixedBadMask*idealGenerator 1) 1
      tOld U (3/4) (Cg*U^buffer) w (originalPools rayM Hr 2 U w)
      (originalCoefficients rayM Hr hHr base θ W U w σ v) (fun i=>U^(w i)) z.val := by
    have hrows:=TerminalActualRow.state_row_support old Qold bΦ U V (1/100) hmod.1.le hV0 (by norm_num)
      hΦ hmod.2 z (hkOld z hz) (hy z hz)
    exact hglobal.2 state hstate hQoldM hQoldBase θ w σ v tOld heightOld hw
      (fun i=>(hwm i).trans (min_le_right _ _)) hσ hv ht z.val hrows.1 (by rw [hrows.2];norm_num)
  exact hsource V hV0 hV1 J θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw
    (fun i=>(hwm i).trans (min_le_left _ _)) hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidth
    p X₁ X₂ hX₁ hX₂ hXN hXY rows (originalMark rayM Hr hHr old base θ W U w σ v tOld)
    hk₁ hk₂ hy (fun z hz i hi=>hslot z hz i (Finset.mem_univ _)) hm₁ hm₂

#print axioms terminal_actual_small_radii
end
end QRH.Cycle092.RegularColoredForward
