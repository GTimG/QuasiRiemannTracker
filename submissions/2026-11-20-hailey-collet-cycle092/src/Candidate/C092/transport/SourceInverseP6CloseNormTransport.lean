/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
PairAt's exact common-mark norm presentation preserves the measured response,
attaining subclasses and actual paid energies at the short anchor. -/
import Candidate.C092.transport.SourceInverseP6CloseUniformPaid
import Candidate.C092.transport.SourceInverseP6CloseUniformPaidUnmarked
import Candidate.C092.transport.StrongPairFinite

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ConcretePrimeRowBridge
open CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily
open QRH.Cycle092.WholeSlot
open CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot]

/-- Apply with Slot equal to the actual surviving Finset subtype. -/
theorem response_norm_congr (Z pay : ℝ) (w : Slot→ℝ) (mark₁ mark₂ : Slot→ℂ)
    (h : ∀ j,‖mark₁ j‖=‖mark₂ j‖) :
    response Z pay w (fun j=>‖mark₁ j‖^2)=response Z pay w (fun j=>‖mark₂ j‖^2) := by
  congr 1
  funext j
  rw [h j]

theorem original_product_energy_norm_congr (rows : Finset FreeRow)
    (A B : FreeRow→ℂ) (mark₁ mark₂ : Slot→FreeRow→ℂ)
    (h : ∀ u∈rows,∀ j,‖mark₁ j u‖=‖mark₂ j u‖) :
    (∑ u∈rows,‖A u*B u*(∏ j,mark₁ j u)‖^2)=
      ∑ u∈rows,‖A u*B u*(∏ j,mark₂ j u)‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  simp only [norm_mul,norm_prod]
  congr 2
  exact Finset.prod_congr rfl (fun j _=>h u hu j)

theorem finiteEnergyOn_norm_congr [DecidableEq Slot]
    (T : Finset Slot) (rows : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark₁ mark₂ : Slot→FreeRow→ℂ)
    (h : ∀ u∈rows,∀ j∈T,‖mark₁ j u‖=‖mark₂ j u‖) :
    finiteEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark₁=
      finiteEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark₂ := by
  unfold finiteEnergyOn
  apply Finset.sum_congr rfl
  intro u hu
  have hp := Finset.prod_congr (s₁:=T) (s₂:=T) rfl (fun j hj=>congrArg (fun x:ℝ=>x^2) (h u hu j hj))
  rw [hp]

def physicalAttainingRows (rows : Finset FreeRow) (Z pay b : ℝ) (w : Slot→ℝ)
    (mark : Slot→FreeRow→ℂ) (j : Slot) : Finset FreeRow :=
  rows.filter (fun u=>b<w j ∧ ‖mark j u‖^2=
    pay*Z^(response Z pay w (fun k=>‖mark k u‖^2)*w j))

variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6CloseNormTransport_68cb864186235773_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M≤H)

/-- Literal PairAt short-anchor presentation, including its unit puncture. -/
theorem descriptor_short_anchor (η η₀ : Character) (W : ℝ→ℂ) (Z : ℝ)
    (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ) (t : ℝ)
    (u : FreeRow) (j : Slot) (hσ : σ j=33/50) :
    descriptor M H hH η η₀ W Z θ w v t u j=
      normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools M H 2 Z w j) (originalCoefficients M H hH η₀ θ W Z w σ v j) t (Z^(w j)) := by
  rw [unit_mask_slot η u]
  unfold descriptor annularMark originalPools QRH.Cycle092.WholeSlot.originalCoefficients
  rw [hσ]

theorem physical_attaining_rows_eq (rows : Finset FreeRow) (η η₀ : Character)
    (W : ℝ→ℂ) (Z pay b : ℝ) (θ : Slot→RayQuotient.Characters M H)
    (w v : Slot→ℝ) (t : ℝ) (mark : Slot→FreeRow→ℂ)
    (h : ∀ u∈rows,∀ j,‖mark j u‖=‖descriptor M H hH η η₀ W Z θ w v t u j‖) (jd : Slot) :
    physicalAttainingRows rows Z pay b w mark jd=
      descriptorRows M H hH rows η η₀ W Z pay b θ w v t jd := by
  unfold physicalAttainingRows descriptorRows
  apply Finset.filter_congr
  intro u hu
  rw [h u hu jd,response_norm_congr Z pay w (fun j=>mark j u)
    (descriptor M H hH η η₀ W Z θ w v t u) (h u hu)]
  rfl

/-- Exact transport of the two paid leaves, including their measured windows
and actual attaining rows, to PairAt's original physical common mark. -/
theorem paid_window_energy_eq (rows : Finset FreeRow) (η η₀ : Character)
    (W : ℝ→ℂ) (Z pay b : ℝ) (θ : Slot→RayQuotient.Characters M H)
    (w v : Slot→ℝ) (t : ℝ) (mark : Slot→FreeRow→ℂ) (A B : FreeRow→ℂ)
    (h : ∀ u∈rows,∀ j,‖mark j u‖=‖descriptor M H hH η η₀ W Z θ w v t u j‖) (jd : Slot) :
    (∑ u∈physicalAttainingRows rows Z pay b w mark jd,‖A u*B u*(∏ j,mark j u)‖^2)=
      ∑ u∈descriptorRows M H hH rows η η₀ W Z pay b θ w v t jd,
        ‖A u*B u*(∏ j,descriptor M H hH η η₀ W Z θ w v t u j)‖^2 := by
  rw [physical_attaining_rows_eq M H hH rows η η₀ W Z pay b θ w v t mark h jd]
  exact original_product_energy_norm_congr _ A B mark
    (fun j u=>descriptor M H hH η η₀ W Z θ w v t u j)
    (fun u hu=>h u (Finset.mem_filter.mp hu).1)

#print axioms response_norm_congr
#print axioms finiteEnergyOn_norm_congr
#print axioms paid_window_energy_eq
end
end QRH.Cycle092.SourceInverseP6
