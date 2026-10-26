import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.JointBlock
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSmooth CenteredMomentCauchy Cycle63Moment CenteredMomentLogDyadic

def firstActiveSectors {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (V : Fin 4→ℝ→ℂ) : Finset (FirstSector s) :=
  Finset.univ.filter (fun q=>V 0 (firstRho s q)≠0 ∧ V 1 (firstX s q)≠0 ∧ Squarefree q.2.1.val)

/-- Vanishing row windows are removed before the Hilbert norm is taken. -/
theorem actual_first_active_expression {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (weight : Label→ℂ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) :
    (∑l,weight l*(s l).value W V)=
      ∑q∈firstActiveSectors s V,firstJointWeight s q*
        (∑i : (s q.1).LeftIndex,∑j : (s q.1).RightIndex,
          (firstJointLeft s weight q i*star (firstJointRight s q j))*
            wholeKernel W V (s q.1).ratio (firstRho s q) (firstX s q)
              (firstLeftLog (s q.1) i) (firstRightLog (s q.1) j)) := by
  rw [actual_first_block_joint_expression,firstActiveSectors,Finset.sum_filter]
  refine Finset.sum_congr rfl fun q hq => ?_
  by_cases h₀ : V 0 (firstRho s q)=0
  · simp [h₀,wholeKernel]
  · by_cases h₁ : V 1 (firstX s q)=0
    · simp [h₁,wholeKernel]
    · by_cases hL : Squarefree q.2.1.val
      · simp [h₀,h₁,hL]
      · simp [h₀,h₁,hL,firstJointWeight,
          ]

def firstActiveEnergyPair {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (weight : Label→ℂ) (V : Fin 4→ℝ→ℂ) (t : ℝ) : ℝ :=
  Real.sqrt (∑q∈firstActiveSectors s V,
    ‖leftColumn Finset.univ (firstJointLeft s weight q) (V 2) (firstLeftLog (s q.1)) t‖^2)*
  Real.sqrt (∑q∈firstActiveSectors s V,
    ‖rightColumn Finset.univ (firstJointRight s q) (V 3) (firstRightLog (s q.1)) t‖^2)

/-- Localized joint contraction, retaining the dyadic Fourier-row window. -/
theorem actual_first_active_contraction (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ)
    (M : Fin 4→ℝ) (hM : ∀i,0≤M i)
    (hV : ∀i y,V i y≠0 → |y|≤M i) (A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label][DecidableEq Label]
      (s : Label→FirstBlockSource) (weight : Label→ℂ) (R : ℝ),
      0<R → (∀l,(s l).ratio=R) →
      (∀q : FirstSector s,‖V 0 (firstRho s q)‖≤1) →
      (∀q : FirstSector s,‖V 1 (firstX s q)‖≤1) →
      ∀E : ℝ,0≤E → (∀t : ℝ,firstActiveEnergyPair s weight V t≤E*(1+‖t‖)^J) →
        (1+R)^A*‖∑l,weight l*(s l).value W V‖≤C*E := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_dependent_row_estimate W V M hM hV A J
  refine ⟨C,hC,?_⟩
  intro Label _ _ s weight R hR hr h₀ h₁ E hE he
  rw [actual_first_active_expression]
  simp_rw [hr]
  exact hbound R hR (Label:=Label) (κ:=FirstSector s)
    (α:=fun l=>(s l).LeftIndex) (β:=fun l=>(s l).RightIndex)
    (firstActiveSectors s V) (fun q=>q.1)
    (firstJointLeft s weight) (firstJointRight s) (fun l=>firstLeftLog (s l))
    (fun l=>firstRightLog (s l)) (firstRho s) (firstX s) (firstJointWeight s)
    (fun q _=>first_joint_weight_norm s q) (fun q _=>h₀ q) (fun q _=>h₁ q) E hE he

/-- Every retained first-sector row lies in its actual annulus. -/
theorem actual_first_active_annulus {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (q : FirstSector s)
    (hq : q∈firstActiveSectors s (fun _=>logAnnulus)) :
    (s q.1).H0/4≤‖ConcreteTraceCRT.eisEmbedding q.2.2.2.2.val‖^2 ∧
      ‖ConcreteTraceCRT.eisEmbedding q.2.2.2.2.val‖^2≤(s q.1).H0 := by
  have hx := logAnnulus_support (Finset.mem_filter.mp hq).2.2.1
  have hz : 0<‖ConcreteTraceCRT.eisEmbedding q.2.2.2.2.val‖^2 := by
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero
      ((s q.1).rows_ne _ q.2.2.2.2.property))
  have hratio := div_pos hz (s q.1).H0_pos
  have hlo := Real.exp_le_exp.mpr hx.1
  have hhi := Real.exp_le_exp.mpr hx.2
  dsimp [firstX] at hlo hhi
  rw [Real.exp_log hratio,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<4)] at hlo
  rw [Real.exp_log hratio,Real.exp_zero] at hhi
  constructor
  · have hh := (le_div_iff₀ (s q.1).H0_pos).mp hlo
    linarith
  · exact (div_le_one (s q.1).H0_pos).mp hhi

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
