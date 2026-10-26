import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialSourceReduction
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.ComparisonEnergy
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Incumbent
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.WidenedState
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.AffineLedger
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional ConcretePrimeRowBridge
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open Cycle63InitialSource Cycle63Moment Cycle63Moment.LowBranch

variable [Cycle63.AffineLedger] in
/-- The plain lengths and the slots of a window of the ledger, whose overshoot over the unit with the slots priced at
`slotPrice` is at most `7/1000`, satisfy the facts that the old moment needs for the comparison of the ledger at the
width one, with the margin `7/1000` and the slack `1/1000`. -/
theorem affine_comparison_old_facts {x₁ x₂ z : ℝ} (hz : 0≤z)
    (hwin : Cycle63.AffineLedger.PlainWindow x₁ x₂ z)
    (hover : x₁+x₂+6*Cycle63.Optimization.slotPrice*z≤1+7/1000) :
    let Lc:=Cycle63.AffineLedger.comparisonLength x₁ x₂ z
    0<x₁ ∧ 0<x₂ ∧ x₁+x₂≤1 ∧ 0≤Lc ∧ Lc≤1/4 ∧ 0≤x₁+x₂-Lc ∧
      Lc+(x₁+x₂-Lc)+6*Cycle63.Optimization.slotPrice*z≤1+7/1000 ∧
      max 0 (1-(x₁+x₂-Lc)+1/1000)+Lc+6*Cycle63.Optimization.slotPrice*z+7/1000≤1 := by
  intro Lc
  have hvol:=hwin.volume_le hz
  have h1:=Cycle63.AffineLedger.comparisonLength_nonneg x₁ x₂ z hwin
  have h2:=Cycle63.AffineLedger.comparisonLength_le x₁ x₂ z hwin
  have h3:=Cycle63.AffineLedger.long_factor x₁ x₂ z hwin
  have h4:=Cycle63.AffineLedger.daughter_fits x₁ x₂ z hwin
  have hb:=Cycle63.AffineLedger.windowBottom_pos
  have hκ:=Cycle63.Optimization.slotPrice_mem
  have hκz : 6*Cycle63.Optimization.slotPrice*z≤(9/2)*z := by nlinarith [hκ.2]
  refine ⟨lt_of_lt_of_le hb hwin.left_ge,lt_of_lt_of_le hb hwin.right_ge,by linarith,h1,h2,by linarith,
    by linarith,?_⟩
  rcases le_total 0 (1-(x₁+x₂-Lc)+1/1000) with h|h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance affineStateComparisonFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
/-- The energy of the comparison daughter of the literal affine input of a natural state of width at most one, for plain
lengths in the window of the ledger whose overshoot is at most `7/1000`, is at most the old moment at the loss `ε` in the
unit of the ledger. The slot widths are at most `mesh`, which is below the common mesh of the mask of the state at the
loss `ε/2`. -/
theorem affine_state_comparison_energy
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta) (bΦ Bmask ε mesh : ℝ) (hbΦ : 0<bΦ) (hBmask : 0≤Bmask) (hε : 0<ε)
    (hmeshY : mesh≤Cycle25.Energy.commonMesh 1 Bmask 1 (ε/2))
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) :
    ∃(Cy : ℝ)(Jy : ℕ)(Uy : Finset (ℕ×ℕ)),0<Cy ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(T : Finset α)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ)
      (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))(t height : ℝ),
      (∀i,0≤w i) → (∀i,w i≤ mesh) → 0≤height → (∀i,|freq i|≤height) →
    ∀(state : NaturalState Z Bmask bΦ),state.fixedModulus=internalQ Q η₀ → state.width≤1 →
    ∀(p : Profiles (1/4) (9/4))(X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
      length Z X₁+length Z X₂+6*Cycle63.Optimization.slotPrice*(∑i,w i)≤1+7/1000 →
    let s:=affineInput M H hH η₀ θ W hW.continuous 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num)
      (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    energy s.η (fixedBadMask*idealGenerator state.puncture) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂
      state.radial.keep state.radial.profile state.radial.scale≤
      Cy*diagonalControl state.radial.profile*(p.control Uy)^2*(1+|t|+height)^Jy*Z^(1+ε) := by
  obtain ⟨degreeI,SI,hincumbent⟩:=original_incumbent (α:=α) M H hH W 1 2 (1/4) (9/4) bΦ Bmask 1 (33/50) (33/50) 1 (ε/2)
    (by norm_num) hWs hW (by norm_num) (by norm_num) le_rfl (by norm_num) hbΦ hBmask (by norm_num)
    (by positivity) hbeta
  obtain ⟨C₀,C₁,hC₀,hC₁,hpositive⟩:=hincumbent η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cr,Jexp,U,hCr,hcomparison⟩:=punctured_comparison_energy_of_fits (α:=α) M H hH W 1 2 (1/4) (9/4) bΦ Bmask 1
    (Cycle25.Energy.commonMesh 1 Bmask 1 (ε/2)) (33/50) (33/50) 1 (ε/2) (7/1000) (1/1000) (ε/2) degreeI SI
    (by norm_num) hWs hW.continuous (by norm_num) le_rfl (by norm_num) hbΦ hBmask (by norm_num)
    (by positivity) (by norm_num) (by norm_num) (by positivity)
  refine ⟨Cr*(C₁+1),Jexp,U,by positivity,?_⟩
  filter_upwards [hpositive,hcomparison] with Z hpos hcmp
  refine ⟨hcmp.1,?_⟩
  intro T θ w σ freq hσ t height hw hwm hheight hfreq state hfix hwidth p X₁ X₂ hX₁ hX₂ hwin hover s
  have hz : 0≤∑i,w i := Finset.sum_nonneg (fun i _=>hw i)
  obtain ⟨hx₁,hx₂,hsum,hLc0,hLc4,hal0,hover',hrefl⟩:=affine_comparison_old_facts hz hwin hover
  have hmesh0 : 0≤Cycle25.Energy.commonMesh 1 Bmask 1 (ε/2) :=
    (Cycle25.Energy.commonMesh_pos 1 Bmask 1 (ε/2) zero_le_one hBmask (by positivity)).le
  let we:=slotExtend T w 0
  let se:=slotExtend T σ (33/50)
  let ve:=slotExtend T freq 0
  have hew (i : α) : 0≤we i := by
    dsimp only [we,slotExtend]
    split_ifs with h
    · exact hw ⟨i,h⟩
    · exact le_rfl
  have hewm (i : α) : we i≤Cycle25.Energy.commonMesh 1 Bmask 1 (ε/2) := by
    dsimp only [we,slotExtend]
    split_ifs with h
    · exact (hwm ⟨i,h⟩).trans hmeshY
    · exact hmesh0
  have heslo (i : α) : (33/50:ℝ) ≤ se i := by
    dsimp only [se,slotExtend]
    split_ifs with h
    · exact (hσ ⟨i,h⟩).1
    · exact le_rfl
  have heshi (i : α) : se i ≤ (33/50:ℝ) := by
    dsimp only [se,slotExtend]
    split_ifs with h
    · exact (hσ ⟨i,h⟩).2
    · exact le_rfl
  have hev (i : α) : |ve i|≤height := by
    dsimp only [ve,slotExtend]
    split_ifs with h
    · exact hfreq ⟨i,h⟩
    · simpa only [abs_zero] using hheight
  have hzJ : (∑i∈T,we i)=∑i,w i := by
    rw [←Finset.sum_coe_sort T we]
    simp only [we,slotExtend_coe]
  have hwidth1 := LowBranch.widenState_width state 1 hwidth
  have hY:=hcmp.2 η₀ Q C₁ hC₁.le hpos.2.2 T (slotExtend T θ 1) we se ve t height hew hewm heslo heshi hheight hev
    (LowBranch.widenState state 1 hwidth) hfix (by rw [hwidth1]) (by rw [hwidth1]) (p.profile 0) (p.profile 1)
    (p.support 0) (p.support 1) X₁ X₂ hX₁ hX₂ (length Z X₁) (length Z X₂) (∑i,w i) 1
    (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) rfl rfl hzJ.symm hwidth1.symm
    hx₁ hx₂ hsum hLc0 hLc4 hal0 hover' hrefl
  rw [hwidth1] at hY
  simp only [we,se,ve,slotExtend_coe] at hY
  have hexp : Z^(1+ε/2+ε/2)=Z^(1+ε) := by
    congr 1
    ring
  rw [hexp] at hY
  exact hY

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
