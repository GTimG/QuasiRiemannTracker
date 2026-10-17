/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B110
import Candidate.Bundles.B113

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondRows; sha256 70a5b82dd66fdae562251eebc79fcdb0aa0016442345edee8f093a863c3ab21c -/
section
                                                         

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

/-- Row labels before choosing the residual second projector. -/
abbrev SecondRow {Label : Type*} (s : Label→ SecondBlockSource) :=
  (l : Label) × RayCharacter × RayCharacter × ↥(s l).rows

def secondRowSector {Label : Type*} (s : Label→ SecondBlockSource)
    (r : SecondRow s) (L : (s r.1).divisors) : SecondSector s :=
  ⟨r.1,⟨L,r.2⟩⟩

def secondLiveRows {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) : Finset (SecondRow s) :=
  Finset.univ.filter (fun r=>logAnnulus (s r.1).rho≠0 ∧
    logAnnulus ((s r.1).x r.2.2.2.val)≠0 ∧ (s r.1).rowWeight r.2.2.2.val≠0)

def secondSquarefreeProjectors {Label : Type*} (s : Label→ SecondBlockSource)
    (r : SecondRow s) : Finset (s r.1).divisors :=
  Finset.univ.filter (fun L=>Squarefree L.val)

/-- The full active sum is regrouped by its physical row before summing
the second projectors. This is the order required by the residual-shell bound. -/
theorem actual_second_rows_regroup {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (f : SecondSector s→ℝ) :
    (∑q∈secondActiveSectors s,f q)=
      ∑r∈secondLiveRows s,∑L∈secondSquarefreeProjectors s r,f (secondRowSector s r L) := by
  simp only [secondActiveSectors,secondLiveRows,secondSquarefreeProjectors,
    Finset.sum_filter,Fintype.sum_sigma,Fintype.sum_prod_type,secondRowSector]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs with hrow
  · apply Finset.sum_congr rfl
    intro L hL
    simp only [hrow.1,hrow.2.1,hrow.2.2,ne_eq,not_false_eq_true,and_true,true_and]
  · apply Finset.sum_eq_zero
    intro L hL
    have hn : ¬(logAnnulus (s l).rho≠0 ∧ logAnnulus ((s l).x z.val)≠0 ∧
        Squarefree L.val ∧ (s l).rowWeight z.val≠0) := by
      intro h
      exact hrow ⟨h.1,h.2.1,h.2.2.2⟩
    simp only [hn,ite_false]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_rows_regroup

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondRows -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondEncoding; sha256 5d9f7b309e0d0281be48737ce67bdf259f34a092da6710675edb62912c2e8860 -/
section
                                              
                                           

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem actual_second_live_partition {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (r : SecondRow s) (hr : r∈secondLiveRows s) :
    canonicalPartition (s r.1).C (s r.1).D (s r.1).inactive
      (nonunitFrequencyGenerator (s r.1).C (s r.1).D (s r.1).inactive*r.2.2.2.val) := by
  have hw := (Finset.mem_filter.mp hr).2.2.2
  by_contra hn
  exact hw (by simp [SecondBlockSource.rowWeight,retainedScalar,canonicalPartitionScalar,hn])

theorem actual_second_live_retained_weight {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (r : SecondRow s) (hr : r∈secondLiveRows s) :
    retainedWeight (s r.1).radius (normValue ((s r.1).frequency*r.2.2.2.val))≠0 := by
  have hw := (Finset.mem_filter.mp hr).2.2.2
  have hs := (mul_ne_zero_iff.mp hw).1
  change retainedScalar (s r.1).C (s r.1).D (s r.1).inactive
    (s r.1).radius r.2.2.2.val≠0 at hs
  have he := (mul_ne_zero_iff.mp hs).2
  exact Complex.ofReal_ne_zero.mp he

/-- A physical row is encoded only after the residual projector has been
separated from the row coordinate. Its canonical partition is proved from
the literal retained scalar. -/
def secondEncodedRow {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (first : Label→ FirstSourceLabel)
    (r : secondLiveRows s) : JointSourceLabel :=
  ⟨first r.val.1,((s r.val.1).C,(s r.val.1).D),
    ⟨((s r.val.1).inactive,r.val.2.2.2.val),actual_second_live_partition s r.val r.property⟩⟩

theorem actual_second_encoded_row_factorization {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (first : Label→ FirstSourceLabel)
    (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O) :
    jointSourceRow left u₀ unit (secondEncodedRow s first r)=
      jointFirstFrequency left u₀ unit (secondEncodedRow s first r)*
        ((s r.val.1).frequency*r.val.2.2.2.val) :=
  joint_source_row_factorization left u₀ unit (secondEncodedRow s first r)

theorem actual_second_encoded_row_ne_zero {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (first : Label→ FirstSourceLabel)
    (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (hf : jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0) :
    jointSourceRow left u₀ unit (secondEncodedRow s first r)≠0 := by
  rw [actual_second_encoded_row_factorization]
  apply mul_ne_zero hf
  apply mul_ne_zero _ ((s r.val.1).rows_ne _ r.val.2.2.2.property)
  exact mul_ne_zero (commonFrequencyGenerator_ne_zero _ _ (s r.val.1).hC)
    (nonunitFrequencyGenerator_ne_zero _ _ (s r.val.1).hC _)

def secondEncodedNonzeroRow {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (first : Label→ FirstSourceLabel)
    (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (hf : jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0) :
    NonzeroJointSourceLabel left u₀ unit :=
  ⟨secondEncodedRow s first r,actual_second_encoded_row_ne_zero s first r left u₀ unit hf⟩

theorem actual_second_encoded_first_projector {Label : Type*} [Fintype Label]
    (s : Label→ SecondBlockSource) (first : Label→ FirstSourceLabel)
    (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (L : Ideal O) (hL : Squarefree L) (hLC : L∣(s r.val.1).C) (hLD : L∣(s r.val.1).D) :
    L∣Ideal.span {jointSourceRow left u₀ unit (secondEncodedRow s first r)} :=
  actual_first_projector_dvd_joint_row left u₀ unit (secondEncodedRow s first r)
    L hL (s r.val.1).hC (s r.val.1).hD.1 hLC hLD

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_partition
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_live_retained_weight
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_encoded_row_factorization
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_encoded_row_ne_zero
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_encoded_first_projector

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondEncoding -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondShellWindows; sha256 11c82f39c972030cf5722cfb02c2a555435f1996082be35898a30d7e26239373 -/
section
                                                         

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory HeckeFamily CanonicalQuadraticSieve Cycle61Moment
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
    ∃K : ℝ,0< K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→ Finset α)
      (s : (k : κ)→ Input (slots k)) (C R seed : κ→ Ideal O)
      (hC : ∀k,Supported (C k)) (Ds : κ→ Finset (Ideal O))
      (η : κ→ Character) (t θ X : κ→ℝ) (hX : ∀k,0< X k)
      (z : κ→ O) (scalar : κ→ℂ)
      (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
      (J : ℕ) (G E T : ℝ),0≤ G → 0≤ E → 1≤ T →
      (∀k∈rows,seed k∣C k) → (∀k∈rows,(s k).upper≤ b) →
      (∀k∈rows,C k≠0) →
      (∀k∈rows,‖scalar k‖^2*(∏j,(s k).M j)^2*((C k).absNorm:ℝ)^(ε-1)≤ G) →
      (∀k∈rows,∀L∈Ds k,Squarefree L ∧ (L.absNorm:ℝ)≤2*T) →
      (∀u : ℝ,∀S : Finset rows,
        ∀pick : (k : S)→ actualAllocations (s k.val.val).pools (C k.val.val),
        (∀k,frozenCoefficient (pick k).val (C k.val.val) (R k.val.val)
          (s k.val.val).ν (s k.val.val).W (s k.val.val).P≠0) →
        (∑k : S,∑L∈Ds k.val.val,
          ∑a∈(commonData (withHeight (s k.val.val) (η k.val.val)
              (t k.val.val+2*Real.pi*(u-θ k.val.val))) (C k.val.val) (R k.val.val)
                (pick k)).toSource.active L,
            retainedAllocationCost (commonData (withHeight (s k.val.val) (η k.val.val)
              (t k.val.val+2*Real.pi*(u-θ k.val.val))) (C k.val.val) (R k.val.val)
                (pick k)) L a (z k.val.val))≤ E*(1+‖u‖)^(2*J)) →
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_selected_shell_windows

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondShellWindows -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondPhysicalWindows; sha256 5d4e8ce8c64b56863a5f56a544f3e2b74007a9bccf929d0e3ebe1c593f3241e0 -/
section
                                              
                                                      

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentCommonWindowColumn CenteredMomentSectorLocalization CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance secondPhysicalWindowsDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Actual residual projectors at a physical row, with the subtype removed
so the allocation and shell estimates apply directly. -/
def secondResidualIdeals {Label : Type*} (s : Label→ SecondBlockSource)
    (r : SecondRow s) : Finset (Ideal O) :=
  (secondSquarefreeProjectors s r).image Subtype.val

theorem mem_second_residual_ideals {Label : Type*} (s : Label→ SecondBlockSource)
    (r : SecondRow s) (L : Ideal O) :
    L∈secondResidualIdeals s r ↔ L∈(s r.1).divisors ∧ Squarefree L := by
  simp only [secondResidualIdeals,secondSquarefreeProjectors,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨L',hs,rfl⟩
    exact ⟨L'.property,hs⟩
  · rintro ⟨hL,hs⟩
    exact ⟨⟨L,hL⟩,hs,rfl⟩

theorem actual_second_residual_sum {Label : Type*} (s : Label→ SecondBlockSource)
    (r : SecondRow s) (f : Ideal O→ℝ) :
    (∑L∈secondSquarefreeProjectors s r,f L.val)=∑L∈secondResidualIdeals s r,f L := by
  rw [secondResidualIdeals,Finset.sum_image]
  intro a ha b hb hab
  exact Subtype.ext hab

variable {α : Type*} [Fintype α] [DecidableEq α]

def secondRowLeftScalar {Label : Type*} (d : Label→ SecondInputDatum α) (w : Label→ℂ)
    (r : SecondRow (fun l=>(d l).block)) : ℂ :=
  w r.1*(d r.1).block.outside*(Real.sqrt (volume (d r.1).input.toData):ℂ)
def secondRowRightScalar {Label : Type*} (d : Label→ SecondInputDatum α)
    (r : SecondRow (fun l=>(d l).block)) : ℂ :=
  Real.sqrt (volume (d r.1).input.toData)

def secondRowLeftWindow {Label : Type*} (d : Label→ SecondInputDatum α) (w : Label→ℂ)
    (t : ℝ) (r : SecondRow (fun l=>(d l).block)) (L : Ideal O) : ℂ :=
  secondRowLeftScalar d w r*windowColumn (d r.1).input (d r.1).C (d r.1).hC
    (d r.1).R (d r.1).seed L ((d r.1).τ r.2.1) (d r.1).input.t t
    (dyadicScale ((d r.1).dyad 2)) logAnnulus r.2.2.2.val

def secondRowRightWindow {Label : Type*} (d : Label→ SecondInputDatum α)
    (t : ℝ) (r : SecondRow (fun l=>(d l).block)) (L : Ideal O) : ℂ :=
  secondRowRightScalar d r*windowColumn (d r.1).input (d r.1).D (d r.1).hD
    (d r.1).R (d r.1).seed L ((d r.1).τ r.2.2.1⁻¹) (d r.1).input.t (-t)
    (dyadicScale ((d r.1).dyad 3)) (fun x=>star (logAnnulus x)) (-r.2.2.2.val)

/-- The literal physical energy is the product of the two joint shell
energies. This equality retains every live row and every actual projector. -/
theorem actual_second_family_row_energy {Label : Type*} [Fintype Label]
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (t : ℝ) :
    secondActiveEnergyPair (fun l=>(d l).block) w t=
      Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
        ∑L∈secondResidualIdeals (fun l=>(d l).block) r,‖secondRowLeftWindow d w t r L‖^2)*
      Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
        ∑L∈secondResidualIdeals (fun l=>(d l).block) r,‖secondRowRightWindow d t r L‖^2) := by
  rw [actual_second_family_energy]
  congr 1 <;> congr 1
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    exact actual_second_residual_sum (fun l=>(d l).block) r
      (fun L=>‖secondRowLeftWindow d w t r L‖^2)
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    exact actual_second_residual_sum (fun l=>(d l).block) r
      (fun L=>‖secondRowRightWindow d t r L‖^2)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.mem_second_residual_ideals
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_residual_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_family_row_energy

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondPhysicalWindows -/
