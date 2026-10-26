import Candidate.Cycle63.Physical.InitialMass.SecondInput
import Candidate.Cycle63.Moment.JointColumnExtraction

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource Cycle63Moment
open CenteredMomentCommonWindowColumn CenteredMomentCommonHeightEnvelope
open CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
local instance secondExtractionDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- One extraction constant for every surviving subset of the original
finite slot dictionary, chosen before all moving source data. -/
theorem actual_uniform_second_column_extraction {α : Type*} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀ S : Finset α,∀s : Input S,∀C : Ideal O,∀hC : Supported C,
      ∀R seed L : Ideal O,seed∣C → Squarefree L → ∀z : O,
      ‖normalizedColumn s C hC R seed L z‖^2≤
        K*(L.absNorm:ℝ)^ε*commonRetainedCost s C R L z := by
  have he (S : Finset α) := actual_common_column_extraction (ι:=S) ε hε
  choose K hK hb using he
  let Ksum := 1+∑S : Finset α,K S
  have hs : 0≤∑S : Finset α,K S := Finset.sum_nonneg (fun S _=>(hK S).le)
  refine ⟨Ksum,by dsimp [Ksum]; linarith,?_⟩
  intro S s C hC R seed L hseed hL z
  have hle : K S≤Ksum := by
    have hh := Finset.single_le_sum (fun S _=>(hK S).le) (Finset.mem_univ S)
    dsimp [Ksum]
    linarith
  exact (hb S s C hC R seed L hseed hL z).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (common_retained_cost_nonneg _ _ _ _ _))

/-- Both common and residual allocations are expanded inside the joint
Hilbert sum; there is no per-source maximum or source-label count. -/
theorem actual_heterogeneous_second_extraction {α : Type*} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→Finset α)
      (s : (k : κ)→Input (slots k)) (C R seed L : κ→Ideal O)
      (hC : ∀k,Supported (C k)) (z : κ→O) (scalar : κ→ℂ),
      (∀k∈rows,seed k∣C k) → (∀k∈rows,Squarefree (L k)) →
      (∑k∈rows,‖scalar k*normalizedColumn (s k) (C k) (hC k) (R k) (seed k) (L k) (z k)‖^2)≤
        K*∑k∈rows,‖scalar k‖^2*(L k).absNorm^ε*commonRetainedCost (s k) (C k) (R k) (L k) (z k) := by
  obtain ⟨K,hK,hbound⟩ := actual_uniform_second_column_extraction (α:=α) ε hε
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R seed L hC z scalar hseed hL
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul,mul_pow]
  calc
    _≤‖scalar k‖^2*(K*((L k).absNorm:ℝ)^ε*commonRetainedCost (s k) (C k) (R k) (L k) (z k)) :=
      mul_le_mul_of_nonneg_left
        (hbound (slots k) (s k) (C k) (hC k) (R k) (seed k) (L k) (hseed k hk) (hL k hk) (z k))
        (sq_nonneg _)
    _=_ := by ring

/-- The actual joint allocation budget passes through the second Mellin
window with one uniform extraction constant. -/
theorem actual_second_allocation_window_energy {α : Type*} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→Finset α)
      (s : (k : κ)→Input (slots k)) (C R seed L : κ→Ideal O)
      (hC : ∀k,Supported (C k)) (η : κ→Character)
      (t θ X : κ→ℝ) (hX : ∀k,0<X k) (z : κ→O) (scalar : κ→ℂ)
      (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
      (J : ℕ) (E : ℝ),0≤E →
      (∀k∈rows,seed k∣C k) → (∀k∈rows,Squarefree (L k)) →
      (∀u : ℝ,(∑k∈rows,‖scalar k‖^2*((L k).absNorm:ℝ)^ε*
        commonRetainedCost (withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
          (C k) (R k) (L k) (z k))≤E*(1+‖u‖)^(2*J)) →
      (∑k∈rows,‖scalar k*windowColumn (s k) (C k) (hC k) (R k) (seed k) (L k)
        (η k) (t k) (θ k) (X k) V (z k)‖^2)≤
          (K*E)*(∫u : ℝ,(1+‖u‖)^J*‖columnDensity V hc hs u‖)^2 := by
  obtain ⟨K,hK,hbound⟩ := actual_heterogeneous_second_extraction (α:=α) ε hε
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R seed L hC η t θ X hX z scalar V hc hs J E hE hseed hL hbudget
  apply actual_heterogeneous_joint_window_energy rows slots s C R seed L hC η t θ X hX
    z scalar V hc hs J (K*E) (mul_nonneg hK.le hE)
  intro u
  have hh := hbound rows slots
    (fun k=>withHeight (s k) (η k) (t k+2*Real.pi*(u-θ k)))
    C R seed L hC z scalar hseed hL
  exact hh.trans ((mul_le_mul_of_nonneg_left (hbudget u) hK.le).trans_eq (by ring))

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_uniform_second_column_extraction
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_heterogeneous_second_extraction
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_allocation_window_energy
