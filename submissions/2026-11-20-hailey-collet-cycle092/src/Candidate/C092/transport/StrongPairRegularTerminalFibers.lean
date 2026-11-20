/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
An exact weighted partition of the same actual supported witness family. -/
import Candidate.C092.transport.StrongPairRegularTerminalWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorWitnessRows

/-- A finite function partitions arbitrary weighted original rows exactly;
no positivity or count estimate is used for this identity. -/
theorem terminal_sum_fibers {Row Key : Type*} [Fintype Row] [Fintype Key] [DecidableEq Key]
    (key : Row→Key) (value : Row→ℝ) :
    (∑ u,value u) = ∑ k : Key,∑ u∈Finset.univ.filter (fun u=>key u=k),value u := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp

/-- Dyad fibers use the actual witness's integer left/right labels.
The real inverse and ordinary lengths are derived from the same witness;
no new zero, frequency, family or coefficient dictionary is selected. -/
theorem terminal_supported_fibers {Row Label : Type*} [Fintype Row] [Fintype Label] [DecidableEq Label]
    {χ : Row→Label→Character} {Z a ε cutoff T allowance : ℝ} {i : ℕ}
    (ws : ∀ u,SupportedWitness (χ u) Z a ε cutoff T allowance i) (hZ : 1 < Z)
    (value : Row→ℝ) :
    let key := fun u=>((ws u).label,(ws u).left,(ws u).right)
    (∑ u,value u) = ∑ k : Label×Fin (dyadicLength Z)×Fin (dyadicLength Z),
      ∑ u∈Finset.univ.filter (fun u=>key u=k),value u ∧
    (∀ (k : Label×Fin (dyadicLength Z)×Fin (dyadicLength Z)) u,
      u∈Finset.univ.filter (fun u=>key u=k) →
      (ws u).label=k.1 ∧
      (ws u).r=Real.logb Z ((2:ℝ)^k.2.1.val) ∧
      (ws u).m=Real.logb Z ((2:ℝ)^k.2.2.val)) := by
  dsimp only
  refine ⟨terminal_sum_fibers _ value,?_⟩
  intro k u hu
  have h := (Finset.mem_filter.mp hu).2
  have hl := congrArg (fun p : Label×Fin (dyadicLength Z)×Fin (dyadicLength Z)=>p.1) h
  have hj := congrArg (fun p : Label×Fin (dyadicLength Z)×Fin (dyadicLength Z)=>p.2.1) h
  have hk := congrArg (fun p : Label×Fin (dyadicLength Z)×Fin (dyadicLength Z)=>p.2.2) h
  dsimp only at hl hj hk
  exact ⟨hl,(ws u).toWitness.left_exponent hZ |>.trans (by rw [hj]),
    (ws u).toWitness.right_exponent hZ |>.trans (by rw [hk])⟩

/-- The genuine inverse/ordinary event is split after fixing the same
family. Every row is counted once, including r=r0 in the inverse branch. -/
theorem terminal_inverse_ordinary_partition {Row Label : Type*} [Fintype Row]
    {χ : Row→Label→Character} {Z a ε cutoff T allowance r0 : ℝ} {i : ℕ}
    (ws : ∀ u,SupportedWitness (χ u) Z a ε cutoff T allowance i) (value : Row→ℝ) :
    (∑ u,value u) =
      (∑ u∈Finset.univ.filter (fun u=>(ws u).r<r0),value u)+
      (∑ u∈Finset.univ.filter (fun u=>r0≤(ws u).r),value u) := by
  have h := Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (p:=fun u=>(ws u).r<r0) (f:=value)
  simpa only [not_lt] using h.symm

/-- The actual two-dyad class cost is uniform for every later enlarged
conductor exponent in a fixed compact positive interval. -/
theorem terminal_dyad_budget {dmin dmax loss : ℝ}
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hloss : 0 < loss) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ᶠ U : ℝ in atTop,1 < U ∧
      ∀ d : ℝ,dmin ≤ d → d ≤ dmax → (dyadicLength (U^d):ℝ)^2 ≤ K*U^loss := by
  have hdmax0 : 0 < dmax := hdmin.trans_le hdmax
  obtain ⟨K,hK,hcost⟩ := HeckeDetectorClassBudget.dyadic_cost_eventually (loss/dmax) (div_pos hloss hdmax0)
  obtain ⟨Z0,hZ0⟩ := Filter.eventually_atTop.mp hcost
  have hUlarge := (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop Z0)
  refine ⟨K,hK,?_⟩
  filter_upwards [hUlarge,eventually_gt_atTop (1:ℝ)] with U hlarge hU
  refine ⟨hU,?_⟩
  intro d hd hd'
  have hbase : Z0 ≤ U^d := hlarge.trans (Real.rpow_le_rpow_of_exponent_le hU.le hd)
  have h := hZ0 (U^d) hbase
  rw [←Real.rpow_mul (zero_le_one.trans hU.le)] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply Real.rpow_le_rpow_of_exponent_le hU.le
  have heq : d*(loss/dmax) ≤ loss := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hdmax0).2
    nlinarith
  exact heq

#print axioms terminal_supported_fibers
#print axioms terminal_inverse_ordinary_partition
#print axioms terminal_dyad_budget
end
end QRH.Cycle092.StrongPair
