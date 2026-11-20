/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual canonical prime mark at each independent ordinary anchor. The
native dictionary identity retains all coefficient zeros and annular phases. -/
import Candidate.C092.transport.SourceWindowCompactLive
import Candidate.C092.transport.MixedMiddleReturnPresentation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
set_option autoImplicit false
namespace QRH.Cycle092.SourceWindowCompact
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge CanonicalRowCompletion
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckeDyadic ProbePhysical
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyBands
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentDetectorPlainRelativeClass
open QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
local notation "O" => ActualEisensteinCubic.O

/-- Every fixed ordinary character has left the live prime annuli after one
threshold, uniformly before the later radius, width or dictionary label. -/
theorem finite_label_annuli_eventually {Label : Type*} [Fintype Label]
    (eta1 eta2 : Label→Character) {Vmin wmin : ℝ}
    (hVmin : 0 < Vmin) (hwmin : 0 < wmin) :
    ∀ᶠ U : ℝ in atTop,1 < U ∧ ∀ (V w : ℝ),Vmin≤V → wmin≤w → ∀ j : Label,
      ((eta1 j).modulus.absNorm:ℝ) < (U^V)^w ∧
      ((eta2 j).modulus.absNorm:ℝ) < (U^V)^w := by
  have hlarge (j : Label) : ∀ᶠ U : ℝ in atTop,
      ((eta1 j).modulus.absNorm:ℝ) < U^(Vmin*wmin) ∧
      ((eta2 j).modulus.absNorm:ℝ) < U^(Vmin*wmin) := by
    filter_upwards [(tendsto_rpow_atTop (mul_pos hVmin hwmin)).eventually
      (eventually_gt_atTop ((eta1 j).modulus.absNorm:ℝ)),
      (tendsto_rpow_atTop (mul_pos hVmin hwmin)).eventually
      (eventually_gt_atTop ((eta2 j).modulus.absNorm:ℝ))] with U h1 h2
    exact ⟨h1,h2⟩
  filter_upwards [Filter.eventually_all.mpr hlarge,eventually_gt_atTop (1:ℝ)] with U hlarge hU
  refine ⟨hU,?_⟩
  intro V w hV hw j
  have hp : Vmin*wmin≤V*w := mul_le_mul hV hw hwmin.le (hVmin.trans_le hV).le
  have he : U^(Vmin*wmin)≤(U^V)^w := by
    rw [←Real.rpow_mul (zero_lt_one.trans hU).le]
    exact Real.rpow_le_rpow_of_exponent_le hU.le hp
  exact ⟨(hlarge j).1.trans_le he,(hlarge j).2.trans_le he⟩

/-- The literal canonical physical prime amplitude has exactly the native
normalized-slot norm at this ordinary anchor. No mark-energy premise is used.
The fixed prime mask and the character's own holes are explicitly retained. -/
theorem canonical_mark_norm {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (eta : Character)
    (hM : M≤Ideal.span {fixedBadMask})
    (theta : Slot→RayQuotient.Characters M H) (V : ℝ→ℂ)
    (hVs : Function.support V⊆Set.Icc (1:ℝ) 2)
    (U : ℝ) (w : Slot→ℝ) (external : Slot→ℂ) (u : FreeRow) (s : Slot)
    (hU : 0 < U) (hz : (external s).re=17/50)
    (hlarge : (eta.modulus.absNorm:ℝ) < U^(w s)) :
    ‖HeckePrimeRow.canonicalPrimeAmplitude M H u.val V 2 (U^(w s)) (external s)‖ =
      ‖normalizedSlot eta (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools M H 2 U w s)
        (originalCoefficients M H hH eta theta (fun x=>star (V x)) U w
          (fun _=>33/50) (fun k=>-(external k).im) s) 0 (U^(w s))‖ := by
  have hP : 0 < U^(w s) := Real.rpow_pos_of_pos hU _
  have hcop (P : Ideal O) (hpool : P∈CenteredMomentPrimeSlot.primePool M H 2 (U^(w s)))
      (hV : V ((P.absNorm:ℝ)/(U^(w s)))≠0) : IsCoprime P eta.modulus := by
    have hp := (Finset.mem_filter.mp hpool).2.1
    have hnorm : U^(w s)≤(P.absNorm:ℝ) := by
      have hv := (hVs hV).1
      simpa only [one_mul] using (le_div_iff₀ hP).mp hv
    exact ProbeRaySlots.prime_coprime_of_norm_gt eta ⟨P,hp⟩ (hlarge.trans_le hnorm)
  have he := physical_slot_conj M H eta fixedBadMask u.val (dvd_mul_right _ _) hM
    V 2 (U^(w s)) (external s) hP hcop
  have hcoeff (P : Ideal O) (hpool : P∈CenteredMomentPrimeSlot.primePool M H 2 (U^(w s))) :
      originalCoefficients M H hH eta theta (fun x=>star (V x)) U w
        (fun _=>33/50) (fun k=>-(external k).im) s P =
      physicalSlotCoefficient eta V (U^(w s)) (external s) P := by
    have hp := (Finset.mem_filter.mp hpool).2.1
    unfold originalCoefficients
    rw [relative_pool M H hH eta (theta s) 2 (U^(w s)) P hpool,
      physicalSlotCoefficient_annular eta V (U^(w s)) (external s) P hp.ne_zero hP]
    congr 2
    rw [hz]
    norm_num
  have hslot : normalizedSlot eta fixedBadMask 1 u.val
      (originalPools M H 2 U w s)
      (originalCoefficients M H hH eta theta (fun x=>star (V x)) U w
        (fun _=>33/50) (fun k=>-(external k).im) s) 0 (U^(w s)) =
      normalizedSlot eta fixedBadMask 1 u.val (CenteredMomentPrimeSlot.primePool M H 2 (U^(w s)))
        (physicalSlotCoefficient eta V (U^(w s)) (external s)) 0 (U^(w s)) := by
    unfold normalizedSlot CenteredMomentHeckeSlots.rowSlot originalPools
    congr 1
    exact Finset.sum_congr rfl (fun P hP=>by rw [hcoeff P hP])
  have hunit : ∀ (pool : Finset (Ideal O)) (coef : Ideal O→ℂ) (t P : ℝ),
      normalizedSlot eta (fixedBadMask*idealGenerator 1) 1 u.val pool coef t P =
        normalizedSlot eta fixedBadMask 1 u.val pool coef t P := by
    intro pool coef t P
    simp only [normalizedSlot,CenteredMomentHeckeSlots.rowSlot,one_mul,
      natural_unit_mask_coefficient (CenteredMomentNaturalRowSource.naturalRow eta u.val u.property.1)]
  rw [hunit]
  rw [hslot,he,RCLike.norm_conj]

end
end QRH.Cycle092.SourceWindowCompact
#print axioms QRH.Cycle092.SourceWindowCompact.finite_label_annuli_eventually
#print axioms QRH.Cycle092.SourceWindowCompact.canonical_mark_norm
