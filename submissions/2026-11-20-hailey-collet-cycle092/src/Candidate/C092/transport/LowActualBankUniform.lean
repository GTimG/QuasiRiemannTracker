/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Common actual source constants and controls over a finite moving-cap bank. -/
import Candidate.C092.transport.LowActualBankSuppliers

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open QRH.Cycle092.NativeStrip QRH.Cycle092.WholeSlot
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

/-- Genuine seminorm controls and the height degree can be enlarged uniformly. -/
theorem labelledAt_mono_metadata {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    {N Y l bslot a b bΦ mesh σlo σhi Mmin Mmax ε U C C' : ℝ}
    {W : ℝ → ℂ} {η η₀ : Character} {Q : Ideal O} {degree degree' : ℕ}
    {controls controls' : Finset (ℕ×ℕ)}
    (hU : 0 ≤ U) (hC0 : 0 ≤ C) (hC : C ≤ C') (hd : degree ≤ degree') (hS : controls ⊆ controls')
    (hsrc : LabelledAt (α := Slot) rayM Hr hHr N Y l W bslot a b bΦ mesh
      σlo σhi Mmin Mmax ε U η η₀ Q degree controls C) :
    LabelledAt (α := Slot) rayM Hr hHr N Y l W bslot a b bΦ mesh
      σlo σhi Mmin Mmax ε U η η₀ Q degree' controls' C' := by
  intro T θ w σ v t height hw hwm hlo hhi hh hv M hM hM' Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox
  have hb := hsrc T θ w σ v t height hw hwm hlo hhi hh hv M hM hM' Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox
  have hc0 := p.control_nonneg controls
  have hc1 := p.control_nonneg controls'
  have hc : p.control controls ≤ p.control controls' := by
    unfold Profiles.control
    exact mul_le_mul
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 0))
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 1))
      (sourceControl_nonneg _ _) 
      (sourceControl_nonneg _ _)
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hheight : 1 ≤ 1+|t|+height := by linarith [abs_nonneg t]
  have hp := pow_le_pow_right₀ hheight hd
  have hC0' : 0 ≤ C' := hC0.trans hC
  have hpowU := Real.rpow_nonneg hU (M+ε)
  apply hb.trans
  gcongr

/-- The unchanged mesh of an actual UnitBox works at every radius with a
fixed positive lower bound, before all live heights and source calls. -/
theorem radiusUnitBox_of_unitBox {N Y l mesh ε Vmin : ℝ}
    (hsrc : UnitBox N Y l mesh ε) (hVmin : 0 < Vmin) : RadiusUnitBox N Y l mesh ε Vmin := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,h⟩ := hsrc Slot rayM Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨degree,controls,C,hC,?_⟩
  have hlarge := (tendsto_rpow_atTop hVmin).eventually (eventually_ge_atTop Z₀)
  filter_upwards [hlarge,eventually_ge_atTop (1 : ℝ)] with U hUmin hU
  intro V hV
  exact hZ₀ (U^V) (hUmin.trans (Real.rpow_le_rpow_of_exponent_le hU hV))

/-- Common genuine controls, degree and constant for the entire finite cap
bank. This makes all choices before the live radius V and its bank index. -/
theorem finite_bank_metadata {Index : Type*} [DecidableEq Index]
    (bank : Finset Index) (N Y l : Index → ℝ) {mesh ε Vmin : ℝ}
    (hsource : ∀ i ∈ bank, UnitBox (N i) (Y i) (l i) mesh ε) (hVmin : 0 < Vmin)
    (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (η η₀ : Character) (Q : Ideal O)
    (hQray : Q ≤ rayM) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, ∀ V : ℝ, Vmin ≤ V → ∀ i ∈ bank,
        LabelledAt (α := Slot) rayM Hr hHr (N i) (Y i) (l i) W 2 (1/4) (9/4) bΦ mesh
          (33/50) (33/50) 1 1 ε (U^V) η η₀ Q degree controls C := by
  induction bank using Finset.induction_on with
  | empty => exact ⟨0,∅,1,by norm_num,Filter.Eventually.of_forall (by simp)⟩
  | insert i bank hi ih =>
    obtain ⟨di,Si,Ci,hCi,hiU⟩ := radiusUnitBox_of_unitBox
      (hsource i (Finset.mem_insert_self _ _)) hVmin
      Slot rayM Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
    obtain ⟨db,Sb,Cb,hCb,hbU⟩ := ih (fun j hj => hsource j (Finset.mem_insert_of_mem hj))
    refine ⟨max di db,Si∪Sb,Ci+Cb,add_pos hCi hCb,?_⟩
    filter_upwards [hiU,hbU,eventually_ge_atTop (1 : ℝ)] with U hiU hbU hU
    intro V hV j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact labelledAt_mono_metadata rayM Hr hHr (Real.rpow_nonneg (zero_le_one.trans hU) _) hCi.le (by linarith)
        (le_max_left _ _) Finset.subset_union_left (hiU V hV)
    · exact labelledAt_mono_metadata rayM Hr hHr (Real.rpow_nonneg (zero_le_one.trans hU) _) hCb.le (by linarith)
        (le_max_right _ _) Finset.subset_union_right (hbU V hV j hj)

end
end QRH.Cycle092.LowActual
