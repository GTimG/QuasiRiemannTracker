/- Copyright (c) 2026 Hailey Collet; additive source assembly (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowFinalPayment
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle153LowPhysical
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonHeightEnvelope
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstAmplificationChoice

/-- Assemble ONLY the OLD contribution across actual first-projector shells.
The native structural source count is proved uniformly before the moving
source. Returned forests are not partitioned or multiplied by this count. -/
theorem eventual_actual_old_first_shell_sum
    (N : ℕ) (U epsFirst : ℝ) (hU : 0≤ U) (heps : 0< epsFirst) :
    ∃Cfirst : ℝ,0< Cfirst ∧ ∀ᶠ Z : ℝ in atTop,1< Z ∧
    ∀{alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
      (s : Input alpha),(Fintype.card alpha≤ N) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
    ∀(reflected : Bool)(R seed : Ideal O)(Mrow amp xi reserve b t : ℝ)(Nrow : ℕ)
      (hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))
      (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
      (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp xi reserve b t
        Nrow hZ key firstIndex l)) (cost : rows→ℝ) (oldBound : ℝ),
    0≤ oldBound →
    (∀n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
      (∑q : mainLowShellRows reflected s R seed Z Mrow amp xi reserve b t Nrow hZ key firstIndex rows n,
        cost (mainLowShellRowOriginal reflected s R seed Z Mrow amp xi reserve b t Nrow hZ key
          firstIndex rows n q))≤ oldBound) →
    (∑r : rows,cost r)≤ Cfirst*Z^epsFirst*oldBound := by
  obtain ⟨Cfirst,hCfirst,hcount⟩:=eventual_actual_geometry_selected_first_shell_subpower.{0,0} N U epsFirst hU heps
  refine ⟨Cfirst,hCfirst,?_⟩
  filter_upwards [hcount] with Z hz
  refine ⟨hz.1,?_⟩
  intro alpha Label _ _ _ s hN hpool reflected R seed Mrow amp xi reserve b t Nrow hZ key firstIndex
    rows cost oldBound hold hlocal
  let column:=fun l=>(firstIndex l).1.val
  have hsquare : ∀l,Squarefree (column l).2.1.val:=
    fun l=>actual_first_live_squarefree _ _ _ (firstIndex l).1.property
  have hc:=hz.2 s hN hpool R seed (Z^Mrow) xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key column
  rw [main_low_shell_complete_subtype_sum reflected s R seed Z Mrow amp xi reserve b t Nrow hZ key
    firstIndex rows hsquare cost]
  calc
    _≤∑_n∈selectedShells (selectedFirstProjectors column),oldBound:=Finset.sum_le_sum hlocal
    _=((selectedShells (selectedFirstProjectors column)).card:ℝ)*oldBound:=by simp
    _≤_:=mul_le_mul_of_nonneg_right hc hold
end
end OAI.SevenEighths.Cycle153LowPhysical
#print axioms OAI.SevenEighths.Cycle153LowPhysical.eventual_actual_old_first_shell_sum
