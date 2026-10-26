/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual LOW erasure with the selected-subset row restrictions preserved.
The source admission is imposed on these exact fibers. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.LowErasure.Slots
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalLowErasurePartition
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredNewtonPositive
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open Cycle61Moment.LowBranch QRH.Record1252270103Source.LowErasure
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open ConcretePrimeRowBridge Record1252270103Second
local notation "O" => HeckeFamily.O

variable (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
variable (M : Ideal O) [NeZero M]
local instance actualLowErasureQuotientFinite : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hq0 hq1

theorem actual_restricted_erasure_supplier
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ Cslot : ℝ, 1≤Cslot ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀ {Row Slot : Type*} (rows : Finset Row) (T : Finset Slot)
      (weight : Row→ℝ) (D : Row→ℂ) (st : Row→NaturalState Z Bmask bΦ)
      (hQM : ∀r,(st r).fixedModulus≤M) (hQη : ∀r,(st r).fixedModulus≤η₀.modulus)
      (z : Row→O) (t a : Row→ℝ) (i : Row→ℕ) (parentR extraR : Row→Ideal O)
      (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ),
    (∀r∈rows,0≤weight r) →
    (∀r∈rows,(st r).width≤Mcap) →
    (∀r∈rows,(st r).puncture=parentR r*extraR r) →
    (∀r∈rows,51/100≤a r) → (∀r∈rows,a r≤(1+q)/2) →
    (∀j∈T,0≤w j) → (∀j∈T,w j/d≤Rwidth) →
    (∀j∈T,σmin≤σ j) → (∀j∈T,σ j≤σmax) →
    (∀r∈rows,∀j∈T,|t r+v j|+Z^τ/2≤(3*i r+2:ℕ)*Z^τ) →
    (∀r∈rows,(3+(3*i r+2:ℕ)*Z^τ)^2≤(Z^d)^η) →
    (∀r∈rows,∀j∈T,∀I∈primePool M H B (Z^(w j)),IsCoprime I (extraR r)) →
    (∀r∈rows,weight r≠0 → (st r).radial.keep (z r)) →
    (∀r∈rows,weight r≠0 → ActualLow M H hH (st r) η₀ (hQM r) (hQη r) (a r) e
      (3*(i r+1:ℕ)*Z^τ) (z r)) →
    let slot := fun r j => normalizedSlot (st r).character (fixedBadMask*idealGenerator (parentR r))
      1 (z r) (primePool M H B (Z^(w j)))
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I) (t r) (Z^(w j))
    let pay := Cslot*Z^(2*ε*d)
    (∀ F : Finset Slot, F⊆T → retainedNorm rows weight D slot T≤
      erasurePayment Z q pay w T F*retainedNorm rows weight D slot F) ∧
    (∀ select : Row→Finset Slot, (∀r∈rows,select r⊆T) →
      retainedNorm rows weight D slot T≤
        ∑F∈T.powerset,erasurePayment Z q pay w T F*retainedNorm (rows.filter (fun r=>select r=F)) weight D slot F) := by
  obtain ⟨C,hC,hslots⟩ := actual_low_slots_parent_mask q hq0 hq1 M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro η₀
  filter_upwards [hslots η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Row Slot rows T weight D st hQM hQη z t a i parentR extraR θ w σ v
    hweight hwidth hpuncture ha ha' hw hwr hσ hσ' hfreq hheight havoid hkeep hlow slot pay
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hp : 0≤pay := by dsimp only [pay]; positivity
  have hslot : ∀r∈rows,weight r≠0 → ∀j∈T,‖slot r j‖^2≤pay*Z^(q*w j) := by
    intro r hr hn j hj
    have hh := hZ.2 (st r) (hwidth r hr) (hQM r) (hQη r) (a r) (i r) (ha r hr) (ha' r hr)
      (w j) (σ j) (t r) (v j) (hw j hj) (hwr j hj) (hσ j hj) (hσ' j hj)
      (hfreq r hr j hj) (hheight r hr) (z r) (hkeep r hr hn) (hlow r hr hn) (θ j)
      (parentR r) (extraR r) (hpuncture r hr) (havoid r hr j hj)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg hZ0.le _))
      (Real.rpow_nonneg hZ0.le _))
  constructor
  · intro F hF
    exact fixed_retained_norm rows weight D slot T F hF hweight Z q pay w hZ0
      (fun r hr hn j hj=>hslot r hr hn j (Finset.mem_sdiff.mp hj).1)
  · intro select hs
    exact restricted_varying_retained_norm rows weight D slot T select hs hweight Z q pay w hZ0
      (fun r hr hn j hj=>hslot r hr hn j (Finset.mem_sdiff.mp hj).1)
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_restricted_erasure_supplier
