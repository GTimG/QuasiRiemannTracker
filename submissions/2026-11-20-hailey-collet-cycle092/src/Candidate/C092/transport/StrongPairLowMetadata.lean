/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Early mesh and finite metadata for actual independent-pair source calls. -/
import Candidate.C092.transport.StrongPairLowP3
import Candidate.C092.transport.LowActualBankUniform

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

theorem pairAt_mesh_mono {N Y l bΦ small large ε Z C : ℝ} {W : ℝ→ℂ}
    {η₁ η₂ η₀₁ η₀₂ : Character} {Q₁ Q₂ : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hm : small ≤ large)
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ large ε Z η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls C) :
    PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ small ε Z η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls C := by
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm
  exact hsrc T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw (fun i=>(hwm i).trans hm)

theorem pairUnit_mesh_mono {N Y l small large ε : ℝ}
    (hm : small ≤ large) (hsrc : PairUnitBox N Y l large ε) : PairUnitBox N Y l small ε := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨d,S,C,hC,h⟩ := hsrc Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  exact ⟨d,S,C,hC,h.mono (fun _ h=>pairAt_mesh_mono rayM Hr hHr hm h)⟩

theorem pairAt_metadata_mono {N Y l bΦ mesh ε Z C C' : ℝ} {W : ℝ→ℂ}
    {η₁ η₂ η₀₁ η₀₂ : Character} {Q₁ Q₂ : Ideal O} {d d' : ℕ} {S S' : Finset (ℕ×ℕ)}
    (hZ : 0 ≤ Z) (hC0 : 0 ≤ C) (hC : C ≤ C') (hd : d ≤ d') (hS : S ⊆ S')
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ d S C) :
    PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ d' S' C' := by
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hsum
    p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hm₁ hm₂
  have hb := hsrc T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hsum
    p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hm₁ hm₂
  have hc : p.control S ≤ p.control S' := by
    unfold Profiles.control
    exact mul_le_mul
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 0))
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hp0 := p.control_nonneg S
  have hp1 := p.control_nonneg S'
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hheight : 1 ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hp := pow_le_pow_right₀ hheight hd
  have hC0' : 0 ≤ C' := hC0.trans hC
  have hpow := Real.rpow_nonneg hZ (1+ε)
  exact hb.trans (by gcongr)

/-- One true source threshold works at every later live radius above Vmin. -/
theorem pair_radius_metadata {N Y l mesh ε Vmin : ℝ}
    (hsrc : PairUnitBox N Y l mesh ε) (hVmin : 0 < Vmin)
    (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (hΦs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (hQ₁ray : Q₁ ≤ rayM) (hQ₁0 : internalQ Q₁ η₀₁ ≠ 0) (hQ₁top : internalQ Q₁ η₀₁ ≠ ⊤)
    (hQ₁72 : internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)})
    (hQ₂ray : Q₂ ≤ rayM) (hQ₂0 : internalQ Q₂ η₀₂ ≠ 0) (hQ₂top : internalQ Q₂ η₀₂ ≠ ⊤)
    (hQ₂72 : internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ,∃ S : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,Vmin ≤ V →
      PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε (U^V) η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ d S C := by
  obtain ⟨d,S,C,hC,h⟩ := hsrc Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨d,S,C,hC,?_⟩
  have hlarge := (tendsto_rpow_atTop hVmin).eventually (eventually_ge_atTop Z₀)
  filter_upwards [hlarge,eventually_ge_atTop (1:ℝ)] with U hlarge hU
  intro V hV
  exact hZ₀ (U^V) (hlarge.trans (Real.rpow_le_rpow_of_exponent_le hU hV))

/-- A finite family of genuine pair sources has one early mesh. -/
theorem pair_finite_bank_mesh {Index : Type*} [DecidableEq Index]
    (bank : Finset Index) (N Y l : Index→ℝ)
    (hsrc : ∀ i∈bank,PairUniformBox (N i) (Y i) (l i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ mesh : ℝ,0 < mesh ∧ ∀ i∈bank,PairUnitBox (N i) (Y i) (l i) mesh ε := by
  induction bank using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | insert i bank hi ih =>
    obtain ⟨a,ha,hsource⟩ := hsrc i (Finset.mem_insert_self _ _) ε hε
    obtain ⟨b,hb,hbank⟩ := ih (fun j hj=>hsrc j (Finset.mem_insert_of_mem hj))
    refine ⟨min a b,lt_min ha hb,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact pairUnit_mesh_mono (min_le_left _ _) hsource
    · exact pairUnit_mesh_mono (min_le_right _ _) (hbank j hj)

#print axioms pair_radius_metadata
#print axioms pair_finite_bank_mesh
end
end QRH.Cycle092.StrongPair
