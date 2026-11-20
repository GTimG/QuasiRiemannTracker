/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine rectangular inverse moments for the actual arbitrary-ray union,
with original marks, including independent rowwise common heights. -/
import Candidate.C092.transport.SourceInverseP6Dictionary

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion HeckeDetectorRowwisePolynomial
open HeckeDetectorInverseFiberCount Qrh.MarkedAnchor.Interface
open QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6Union_3fa497121c1845f8_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def originalSlot (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η η₀ : Character) (W : ℝ→ℂ)
    {Slot : Type} (U : ℝ) (θ : Slot→RayQuotient.Characters M H) (wr σ v : Slot→ℝ)
    (t : FreeRow→ℝ) (u : FreeRow) (slot : Slot) : ℂ :=
  normalizedSlot η fixedBadMask 1 u.val (primePool M H 2 (U^(wr slot)))
    (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ slot)) I*
      HeckePrimeAnnular.annularWeight W (U^(wr slot)) (σ slot) (v slot) I)
    (t u) (U^(wr slot))

theorem actual_union_inverse_of_rect {ρ : Contract.AnchorRect} {mesh εm : ℝ}
    (hs : Contract.InverseRectSource Contract.canonicalFamily ρ mesh εm)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ : Character) (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (wrmin : ℝ) (hwrmin : 0 < wrmin) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (Z B bΦ : ℝ) (s : NaturalState Z B bΦ),s.character=η → s.puncture=1 →
    ∀ F : ∀ u : FreeRow,NaturalRow s.character u.val,
    ∀ (label : Option (RayQuotient.Characters M H × RayQuotient.Characters M H))
      (rows : Finset FreeRow), (∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
    ∀ (selected : Finset Slot) (θ : Slot→RayQuotient.Characters M H) (wr σ v : Slot→ℝ)
      (t : FreeRow→ℝ) (height : ℝ),
      (∀ j∈selected,wrmin ≤ wr j) → (∀ j∈selected,wr j ≤ mesh) →
      (∀ j∈selected,σ j=33/50) → 0 ≤ height → (∀ u∈rows,|t u| ≤ height) →
      (∀ j∈selected,|v j| ≤ height) →
    ∀ r : ℝ,ρ.Admissible r (∑ j∈selected,wr j) 1 →
    ∀ (cutoff : ℝ) (n : ℕ),n≤2 → ∀ σ'∈Icc (0:ℝ) 1,∀ freq∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (family M H hH s η₀ (F u) label) true
        ((logProfile^[n]) (inverseTest U cutoff r)) (U^r) σ' freq *
        (∏ j∈selected,originalSlot M H hH η η₀ W U θ wr σ v t u j)‖^2 ≤
      C*(1+height)^J*U^(1+εm) := by
  let Label := Option (RayQuotient.Characters M H × RayQuotient.Characters M H)
  obtain ⟨J,C,hC,hev⟩ := source_inverse_of_rect hs M H hH W hWs hW η η₀
    Label (witnessBase M H hH η η₀) Slot wrmin hwrmin
  have hbig : ∀ᶠ U : ℝ in atTop,
      ((Record12518109Natural.wholeAnchorMask M H hH η₀).absNorm : ℝ) < U^wrmin :=
    (tendsto_rpow_atTop hwrmin).eventually (eventually_gt_atTop _)
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hev,hbig] with U hU hlarge
  refine ⟨hU.1,?_⟩
  intro Z B bΦ s hη hpuncture F label rows hrows selected θ wr σ v t height
    hwmin hmesh hσ hh ht hv r hadm cutoff n hn σ' hσ' freq hfreq
  have hm := hU.2 label rows hrows selected θ wr σ v t height hwmin hmesh hσ hh ht hv
    r hadm cutoff n hn σ' hσ' freq hfreq
  refine (le_of_eq ?_).trans hm
  apply Finset.sum_congr rfl
  intro u hu
  have hc := HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff _ _
    (union_coefficients M H hH s η η₀ hη hpuncture u (F u) label) true
    ((logProfile^[n]) (inverseTest U cutoff r)) (U^r) σ' freq
  rw [hc]
  simp only [norm_mul,norm_prod]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  exact (original_slot_norm M H hH η η₀ W hWs U θ wr σ v t u j
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _)
    (hlarge.trans_le (Real.rpow_le_rpow_of_exponent_le hU.1.le (hwmin j hj)))).symm

#print axioms actual_union_inverse_of_rect
end
end QRH.Cycle092.SourceInverseP6
