import Candidate.Cycle62.Physical.InitialMass.SecondCommonSelection

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve Cycle62Moment
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentCommonHeightEnvelope CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
local instance secondShellDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- A selected joint residual-shell estimate controls the actual window
columns, including common allocation mass and the extraction divisor cost.
All constants precede the moving sources, scales, rows and shells. -/
theorem actual_second_selected_shell_windows {α : Type*} [Fintype α] [DecidableEq α]
    (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→Finset α)
      (s : (k : κ)→Input (slots k)) (C R seed : κ→Ideal O)
      (hC : ∀k,Supported (C k)) (Ds : κ→Finset (Ideal O))
      (η : κ→Character) (t θ X : κ→ℝ) (hX : ∀k,0<X k)
      (z : κ→O) (scalar : κ→ℂ)
      (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
      (J : ℕ) (G E T : ℝ),0≤G → 0≤E → 1≤T →
      (∀k∈rows,seed k∣C k) → (∀k∈rows,(s k).upper≤b) →
      (∀k∈rows,C k≠0) →
      (∀k∈rows,‖scalar k‖^2*(∏j,(s k).M j)^2*((C k).absNorm:ℝ)^(ε-1)≤G) →
      (∀k∈rows,∀L∈Ds k,Squarefree L ∧ (L.absNorm:ℝ)≤2*T) →
      (∀u : ℝ,∀S : Finset rows,
        ∀pick : (k : S)→actualAllocations (s k.val.val).pools (C k.val.val),
        (∀k,frozenCoefficient (pick k).val (C k.val.val) (R k.val.val)
          (s k.val.val).ν (s k.val.val).W (s k.val.val).P≠0) →
        (∑k : S,∑L∈Ds k.val.val,
          ∑a∈(commonData (withHeight (s k.val.val) (η k.val.val)
              (t k.val.val+2*Real.pi*(u-θ k.val.val))) (C k.val.val) (R k.val.val)
                (pick k)).toSource.active L,
            retainedAllocationCost (commonData (withHeight (s k.val.val) (η k.val.val)
              (t k.val.val+2*Real.pi*(u-θ k.val.val))) (C k.val.val) (R k.val.val)
                (pick k)) L a (z k.val.val))≤E*(1+‖u‖)^(2*J)) →
      (∑k∈rows,∑L∈Ds k,‖scalar k*windowColumn (s k) (C k) (hC k)
        (R k) (seed k) L (η k) (t k) (θ k) (X k) V (z k)‖^2)≤
        (K*G*E*(2*T)^ε)*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  obtain ⟨K₁,hK₁,hwindow⟩ := actual_second_allocation_window_energy (α:=α) ε hε
  obtain ⟨K₂,hK₂,hcommon⟩ := actual_second_common_mass_selection (α:=α) b ε hε
  refine ⟨K₁*K₂,mul_pos hK₁ hK₂,?_⟩
  intro κ rows slots s C R seed hC Ds η t θ X hX z scalar V hc hs J G E T
    hG hE hT hseed hupper hCne hscalar hDs hjoint
  let pairs := rows.sigma Ds
  have hbudget (u : ℝ) :
      (∑q∈pairs,‖scalar q.1‖^2*((q.2.absNorm:ℝ)^ε)*
        commonRetainedCost (withHeight (s q.1) (η q.1) (t q.1+2*Real.pi*(u-θ q.1)))
          (C q.1) (R q.1) q.2 (z q.1))≤
        ((K₂*G)*E*(2*T)^ε)*(1+‖u‖)^(2*J) := by
    have hh := hcommon rows slots
      (fun k=>withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
      C R Ds z scalar G (E*(1+‖u‖)^(2*J)) hG hupper hCne hscalar
      (fun S pick hne=>hjoint u S pick (fun k=>right_ne_zero_of_mul (hne k)))
    calc
      _≤∑q∈pairs,‖scalar q.1‖^2*(2*T)^ε*
          commonRetainedCost (withHeight (s q.1) (η q.1) (t q.1+2*Real.pi*(u-θ q.1)))
            (C q.1) (R q.1) q.2 (z q.1) := by
        apply Finset.sum_le_sum
        intro q hq
        have hmem := Finset.mem_sigma.mp hq
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg _) (hDs q.1 hmem.1 q.2 hmem.2).2 hε.le)
            (sq_nonneg _)) (common_retained_cost_nonneg _ _ _ _ _)
      _=(2*T)^ε*(∑k∈rows,‖scalar k‖^2*∑L∈Ds k,
          commonRetainedCost (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
            (C k) (R k) L (z k)) := by
        simp only [pairs,Finset.sum_sigma,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro L hL
        ring
      _≤(2*T)^ε*((K₂*G)*(E*(1+‖u‖)^(2*J))) :=
        mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by linarith) _)
      _=_ := by ring
  have hw := hwindow pairs (fun q=>slots q.1) (fun q=>s q.1)
    (fun q=>C q.1) (fun q=>R q.1) (fun q=>seed q.1) (fun q=>q.2)
    (fun q=>hC q.1) (fun q=>η q.1) (fun q=>t q.1) (fun q=>θ q.1)
    (fun q=>X q.1) (fun q=>hX q.1) (fun q=>z q.1) (fun q=>scalar q.1)
    V hc hs J ((K₂*G)*E*(2*T)^ε) (by positivity)
    (fun q hq=>hseed q.1 (Finset.mem_sigma.mp hq).1)
    (fun q hq=>(hDs q.1 (Finset.mem_sigma.mp hq).1 q.2 (Finset.mem_sigma.mp hq).2).1)
    hbudget
  simp only [pairs,Finset.sum_sigma] at hw
  convert hw using 1 <;> ring

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_selected_shell_windows
