/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual outer ordinary escape. P.1 is used as an earlier positive pair source;
the physical reciprocal and its contour are independent of the witness. -/
import Candidate.C092.transport.MixedPacketWitnessFiber
import Candidate.C092.transport.MixedPacketWitnessKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedPacketWitness
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set OAI OAI.SevenEighths ConcretePrimeRowBridge CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily HeckeRowClosure
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorBatch
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorDictionary
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WitnessRowSup
local notation "O" => HeckeFamily.O

lemma fiber_plain_lower {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slots : Type}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slots U a ε cutoff T allowance i) (hU : 1 < U)
    (u : FreeRow) (hu : u∈F.rows) :
    U^((2*a-1)*F.m-2*ε) ≤ ‖fiberPlain F u‖^2 := by
  have hm := (F.witness u).toWitness.right_exponent hU
  rw [F.fixed_right u hu] at hm
  have hs := (F.witness u).plain_spike
  change U^((2*a-1)*(F.witness u).m-2*ε) ≤ ‖fiberPlain F u‖^2 at hs
  rwa [hm] at hs

/-- Full source labels retain their actual excluded-prime/ray character on
this same physical fiber. Nothing is replaced by a larger comparison family. -/
lemma source_fiber_data {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (η : Character) {Slots : Type}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (B : Batch M H (Sum Bool (RayQuotient.Characters M H)) Slots U a ε cutoff T allowance i)
    (hdata : B.data=sourceMomentData M H hH S hS η)
    (bin : B.Bin) (label : Sum Bool (RayQuotient.Characters M H))
    (left right : Fin (dyadicLength U)) (hne : (B.fiberRows bin label left right).Nonempty) :
    (B.fiber bin label left right hne).rowData = momentData (sourceMomentBase M H hH S hS η label) := by
  change B.data label = _
  rw [hdata,sourceMomentData_base]

/-- Concrete ordinary middle escape from the earlier profile-uniform P.1
pair source, on one authentic same-zero fiber. The ordinary lower bound is
proved from the witness; only the actual retained physical amplitude bins
and a same-subclass cardinality bound remain as inputs. -/
theorem fiber_mixed_return {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (reverse : Bool) (controls : Finset (ℕ×ℕ)) :
    ∃ J : ℕ,∃ C : ℝ,0 < C ∧
    ∀ {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slots : Type}
      {U a ε cutoff T allowance : ℝ} {i : ℕ},
    ∀ (F : Fiber M H Label Slots U a ε cutoff T allowance i)
      (ηL ηW : Character),F.reverse=reverse → F.rowData=momentData ηW →
    ∀ (selected : Finset Slot) (mark : Slot→FreeRow→ℂ)
      (WL : 𝓢(ℝ,ℂ)) (hWL : Function.support (WL:ℝ→ℂ) ⊆ Icc (1/4:ℝ) (9/4))
      (tL XL K epsilon R G Ccount total inverse selectedLower : ℝ)
      (full reciprocal : FreeRow→ℂ),
      1 < U → 0 ≤ a → 0 ≤ T → 0 ≤ allowance → 0 ≤ K → 1 ≤ Ccount →
      (∀ p : Profiles (1/4) (9/4),finiteEnergyOn selected F.rows ηL ηW
        (p.profile 0) (p.profile 1) tL 0 XL (U^F.m) mark ≤
          (K*U^(1+epsilon))*(p.control controls)^2) →
      (F.rows.card:ℝ) ≤ Ccount*U^(R-G) →
      (∀ u∈F.rows,U^selectedLower ≤ ‖∏k∈selected,mark k u‖) →
      (∀ u∈F.rows,‖full u‖ ≤ U^total) →
      (∀ u∈F.rows,‖reciprocal u‖ ≤ U^inverse) →
      (∑u∈F.rows,‖original ηL (fixedBadMask*idealGenerator 1) 1 u.val WL tL XL*
        full u*reciprocal u‖) ≤ Ccount*
        max 1 (12*K*(sourceControl controls WL)^2*C^2*
          (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*J+1))*
        U^(total+inverse-selectedLower-((2*a-1)*F.m-2*ε)/2+(R+1+epsilon)/2-G/2) := by
  obtain ⟨J,C,hC,hpair⟩ := fiber_ordinary_moment (Slot:=Slot) reverse controls
  refine ⟨J,C,hC,?_⟩
  intro M H Label Slots U a ε cutoff T allowance i F ηL ηW hrev hdata
    selected mark WL hWL tL XL K epsilon R G Ccount total inverse selectedLower
    full reciprocal hU ha hT hall hK hc hsource hcount hselected hfull hinverse
  let A := 12*K*(sourceControl controls WL)^2*C^2*
    (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*J+1)
  have he := hpair F ηL ηW hrev hdata selected mark WL hWL tL XL (K*U^(1+epsilon))
    hU ha hT hall (by positivity) hsource
  have henergy : (∑u∈F.rows,‖original ηL (fixedBadMask*idealGenerator 1) 1 u.val WL tL XL*
      fiberPlain F u*∏k∈selected,mark k u‖^2) ≤ max 1 A*U^(1+epsilon) := by
    apply he.trans
    calc
      _ = A*U^(1+epsilon) := by dsimp [A];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  exact saturated_second_bin F.rows
    (fun u=>original ηL (fixedBadMask*idealGenerator 1) 1 u.val WL tL XL)
    (fiberPlain F) (fun u=>∏k∈selected,mark k u) full reciprocal U R G total inverse
    ((2*a-1)*F.m-2*ε) selectedLower epsilon Ccount (max 1 A)
    (zero_lt_one.trans hU) hc (le_max_left _ _) hcount (fiber_plain_lower F hU)
    hselected hfull hinverse henergy

#print axioms source_fiber_data
#print axioms fiber_mixed_return
end
end QRH.Cycle092.MixedPacketWitness
