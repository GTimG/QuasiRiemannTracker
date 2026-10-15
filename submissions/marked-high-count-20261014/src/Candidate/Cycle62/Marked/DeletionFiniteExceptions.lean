import Candidate.Cycle62.Marked.DeletionRawAssembly
import Candidate.LocalMoment.PlainUnmarkedAdapter

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open LocalMoment CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O

/-- The fixed exception set is finite even when the amplitude anchor
modulus differs from the detector base modulus. Intersecting the two
moduli enlarges the exception set and recovers the supported-core theorem. -/
theorem fixed_initial_exceptions_finite (η : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) :
    {u : FreeRow | ¬initialKeep η Q u.val}.Finite := by
  have hh := fixed_exceptional_free_finite η (internalQ Q η)
    (internalQ_ne_zero Q hQ0 η) (internalQ_ne_top Q hQt η)
    (inf_le_left.trans hQ72) inf_le_right
  apply hh.subset
  intro u hu hkeep
  have hex : CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
      1 u.val := by
    by_contra hn
    exact hu ⟨u.property.1,hn⟩
  apply hkeep.2
  obtain ⟨χ,ψ,hprim,hind,hmod,hcoeff⟩ := hex
  exact ⟨χ,ψ,hprim,hind,inf_le_left.trans hmod,hcoeff⟩

/-- A single fixed finite set removes every bad initial row in the entire
finite detector dictionary, including independent amplitude anchors. -/
theorem fixed_initial_exception_union {Label : Type*} [Fintype Label]
    (η : Label→Character) (Q : Label→Ideal O)
    (hQ0 : ∀j,Q j≠0) (hQt : ∀j,Q j≠⊤) (hQ72 : ∀j,Q j≤Ideal.span {(72:O)}) :
    ∃E : Finset FreeRow,∀u : FreeRow,u∉E ↔ ∀j,initialKeep (η j) (Q j) u.val := by
  let E : Label→Finset FreeRow := fun j=>
    (fixed_initial_exceptions_finite (η j) (Q j) (hQ0 j) (hQt j) (hQ72 j)).toFinset
  refine ⟨Finset.univ.biUnion E,?_⟩
  intro u
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,not_exists]
  have he (j : Label) : u∈E j ↔ ¬initialKeep (η j) (Q j) u.val :=
    Set.Finite.mem_toFinset _
  simp only [he,not_not]

/-- Finite omitted cores are absorbed by the marked power whenever its
residual density exponent is nonnegative. The source pointwise bound
supplies the same envelope on retained and omitted rows. -/
theorem finite_exception_weighted_extension {Row : Type*}
    (rows E : Finset Row) (f : Row→ℝ) (C envelope target : ℝ)
    (htarget : 0≤target) (henv : envelope≤target)
    (hpoint : ∀u∈rows,f u≤envelope)
    (hgood : (∑u∈rows.filter (fun u=>u∉E),f u)≤C*target) :
    (∑u∈rows,f u)≤(C+(E.card:ℝ))*target := by
  have hbad : (∑u∈rows.filter (fun u=>u∈E),f u)≤(E.card:ℝ)*target := by
    calc
      _ ≤ ∑u∈rows.filter (fun u=>u∈E),target :=
        Finset.sum_le_sum (fun u hu=>(hpoint u (Finset.mem_filter.mp hu).1).trans henv)
      _ = ((rows.filter (fun u=>u∈E)).card:ℝ)*target := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ htarget
        exact_mod_cast (Finset.card_le_card
          (show rows.filter (fun u=>u∈E)⊆E from fun u hu=>(Finset.mem_filter.mp hu).2))
  have hpart := Finset.sum_filter_add_sum_filter_not rows (fun u=>u∈E) f
  calc
    _ = (∑u∈rows.filter (fun u=>u∈E),f u)+(∑u∈rows.filter (fun u=>u∉E),f u) := hpart.symm
    _ ≤ (E.card:ℝ)*target+C*target := add_le_add hbad hgood
    _ = _ := by ring

/-- The actual small-root window has ample room to pay every fixed
exceptional core from the same raw amplitude envelope. -/
theorem small_root_exception_envelope (U N κ ρ A gain : ℝ)
    (hU : 1<U) (hN : 1≤N) (hcap : N≤U^κ) (hρ : 0≤ρ)
    (hgain : gain≤(1-6*κ)*ρ) :
    U^A≤U^(A-gain)*(U/N^6)^ρ := by
  have hUp : 0<U := zero_lt_one.trans hU
  have hw := (small_root_window U N κ hU hN hcap).1
  have hwin := Real.rpow_le_rpow (Real.rpow_nonneg hUp.le _) hw hρ
  have hp : U^gain≤(U/N^6)^ρ := by
    calc
      _ ≤ U^((1-6*κ)*ρ) := Real.rpow_le_rpow_of_exponent_le hU.le hgain
      _ = (U^(1-6*κ))^ρ := Real.rpow_mul hUp.le _ _
      _ ≤ _ := hwin
  calc
    _ = U^(A-gain)*U^gain := by rw [←Real.rpow_add hUp];congr 1;ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hUp.le _)

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.fixed_initial_exception_union
#print axioms OAI.SevenEighths.Deletion26.finite_exception_weighted_extension
#print axioms OAI.SevenEighths.Deletion26.small_root_exception_envelope
