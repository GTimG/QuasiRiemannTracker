/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The outer ordinary escape on one original source Batch fiber. The full
source label, orientation, actual zero and original masks are retained. -/
import Candidate.C092.transport.WitnessRowSupActualP4
import Candidate.C092.transport.DirectCountCombined

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedPacketWitness
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths ConcretePrimeRowBridge CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorDictionary
open HeckeDetectorCoefficientTransfer HeckeDetectorRawFiber HeckeDetectorWitnessRows
open HeckeDetectorDyadicProfiles
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair
open QRH.Cycle092.WitnessRowSup QRH.Cycle092.SignedEnergy
local notation "O" => HeckeFamily.O

/-- A canonical coefficient representative for exactly the native unit mask. -/
def canonicalCharacter (η : Character) (u : FreeRow) : Character :=
  excluded (naturalRow η u.val u.property.1).character 1

lemma canonical_element (η : Character) (u : FreeRow) : ∀ n,
    elementCoeff (canonicalCharacter η u) n =
      rowTwist (elementHom η) (fixedBadMask*idealGenerator 1) 1 (1*u.val) n := by
  simpa only [canonicalCharacter,one_mul] using (naturalRow η u.val u.property.1).masked_element 1 one_ne_zero

/-- The standard source label and the canonical unit-mask character have
identical ideal coefficients. This does not reopen any excluded prime. -/
lemma canonical_ideal (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData η).character (momentElement u)) I =
      idealCoeff (canonicalCharacter η u) I := by
  rw [momentData_coeff,canonicalCharacter,excluded_one_ideal,
    (naturalRow η u.val u.property.1).ideal,rowMaskElement_eq_fixed]

/-- The literal polynomial of the actual same-zero ordinary witness. -/
def fiberPlain {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slots : Type}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slots U a ε cutoff T allowance i) (u : FreeRow) : ℂ :=
  polynomial (F.family u (F.witness u).label) false positiveAnnular
    (U^(F.witness u).m) (F.witness u).zero.re (F.witness u).toWitness.frequency

lemma fiberPlain_eq_actualPlain {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slots : Type}
    {Z d a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slots (Z^d) a ε cutoff T allowance i) (u : FreeRow) :
    fiberPlain F u = actualPlain (F.witness u) := rfl

/-- Genuine rowwise ordinary witness moment on a fixed source fiber. The
only source input is the earlier profile-uniform pair conclusion; it may be
supplied by pairAt_fixed_height from P.1's PairOpenWidth. No moving-profile
or mixed inverse-ordinary moment is assumed. -/
theorem fiber_ordinary_moment {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (reverse : Bool) (controls : Finset (ℕ×ℕ)) :
    ∃ J : ℕ,∃ C : ℝ,0 < C ∧
    ∀ {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slots : Type}
      {U a ε cutoff T allowance : ℝ} {i : ℕ},
    ∀ (F : Fiber M H Label Slots U a ε cutoff T allowance i)
      (ηL ηW : Character),F.reverse=reverse → F.rowData=momentData ηW →
    ∀ (selected : Finset Slot) (mark : Slot→FreeRow→ℂ)
      (WL : 𝓢(ℝ,ℂ)) (hWL : Function.support (WL:ℝ→ℂ) ⊆ Icc (1/4:ℝ) (9/4))
      (tL XL K : ℝ),1 < U → 0 ≤ a → 0 ≤ T → 0 ≤ allowance → 0 ≤ K →
      (∀ p : Profiles (1/4) (9/4),finiteEnergyOn selected F.rows ηL ηW
        (p.profile 0) (p.profile 1) tL 0 XL (U^F.m) mark ≤ K*(p.control controls)^2) →
      (∑ u∈F.rows,‖original ηL (fixedBadMask*idealGenerator 1) 1 u.val WL tL XL*
        fiberPlain F u*∏ k∈selected,mark k u‖^2) ≤
        12*K*(sourceControl controls WL)^2*C^2*
          (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*J+1) := by
  let V := orientedProfile reverse positiveAnnular
  have hVs : Function.support V ⊆ Icc (1/4:ℝ) (9/4) := oriented_detector_log_support reverse 0
  have hVsm : ContDiff ℝ ∞ V := oriented_detector_log_smooth reverse 0
  obtain ⟨J,C,hC,hrow⟩ := original_pair_rowwise (Slot:=Slot) V hVs hVsm controls
  refine ⟨J,C,hC,?_⟩
  intro M H Label Slots U a ε cutoff T allowance i F ηL ηW hrev hdata
    selected mark WL hWL tL XL K hU ha hT hall hK hsource
  let χ := canonicalCharacter ηW
  let sig : FreeRow→ℝ := fun u=>(F.witness u).zero.re
  let freq : FreeRow→ℝ := fun u=>orientedFrequency reverse (F.witness u).toWitness.frequency
  have hsig (u : FreeRow) (hu : u∈F.rows) : sig u ∈ Icc (0:ℝ) 1 :=
    ⟨ha.trans (F.witness u).zero_lower,(F.witness u).toWitness.real_part_upper⟩
  have hfreq (u : FreeRow) (hu : u∈F.rows) : |freq u| ≤ 2*Real.pi*allowance+(3*i : ℕ)*T := by
    have hf := (F.witness u).toWitness.frequency_bound
    cases reverse <;> simpa [freq,orientedFrequency] using hf
  have hr := hrow selected F.rows ηL ηW WL hWL tL XL (U^F.m) K
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) hK mark hsource χ
    (fun u hu=>canonical_element ηW u) (fun _=>1) 1
    (2*Real.pi*allowance+(3*i : ℕ)*T) (by norm_num) (by positivity)
    (fun _ _=>by norm_num) (fun _ _=>le_rfl) sig freq hsig hfreq
  have hvalue (u : FreeRow) (hu : u∈F.rows) :
      ‖fiberPlain F u‖ =
        ‖polynomial (χ u) false V (U^F.m) (sig u) (freq u)‖ := by
    have hc : ∀ I : Ideal O,idealCoeff (F.family u F.label) I =
        if reverse then starRingEnd ℂ (idealCoeff (χ u) I) else idealCoeff (χ u) I := by
      intro I
      have h := F.row_coeff u hu I
      rw [hdata,hrev] at h
      simpa only [momentElement,χ,←canonical_ideal ηW u I] using h
    have hm := (F.witness u).toWitness.right_exponent hU
    rw [F.fixed_right u hu] at hm
    unfold fiberPlain
    rw [F.fixed_label u hu,hm]
    exact norm_of_oriented_coefficients _ _ reverse hc false positiveAnnular _ _ _
      (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
  simp only [one_mul,mul_one] at hr
  convert hr using 1
  apply Finset.sum_congr rfl
  intro u hu
  simp only [norm_mul,mul_pow,hvalue u hu]
  ring

#print axioms canonical_ideal
#print axioms fiber_ordinary_moment
end
end QRH.Cycle092.MixedPacketWitness
