import Candidate.Cycle63.Marked.DeletionRawOrdinary
import Candidate.Cycle63.Marked.DeletionRawRescale
import Candidate.Cycle63.Marked.DeletionRawSlots
import Candidate.LocalMoment.PlainUnmarkedAdapter

/- Original module: Candidate.Cycle63.Marked.DeletionRawAssembly. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open LocalMoment
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- Actual oriented zero rows inherit any small-root marked estimate.
The large-root estimate, exceptional cores, summation, and height losses
are discharged by the verified ordinary density and sixth-power lift. -/
theorem actual_marked_raw_from_small_roots {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss tailε : ℝ)
    (hloss : 0<loss) (htailε : 0<tailε) (htailmax : tailε≤5/7) :
    ∃J₀ : ℕ,∃C₀ D₀ : ℝ,0<C₀ ∧ 0<D₀ ∧
      ∀(J : ℕ)(C : ℝ),0≤C → ∀(reverse : Label→Bool)(a T U κ A gain : ℝ),
      33/40≤a → a≤7/8 → 0≤T → 1≤U → 0≤κ →
      ∀(R : Finset NonzeroFrequency)(f : NonzeroFrequency→ℝ),
      (∀u∈R,rawFrequencyNorm u≤U ∧ orientedActualZeroRow D.data reverse a T u) →
      (∀u∈R,f u≤U^A) →
      (∀B : NZIdeal,(B.val.absNorm : ℝ)≤U^κ →
        (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
          (C*(1+T)^J)*U^(A-gain)*(U/(B.val.absNorm : ℝ)^6)^(unmarkedDensity (2*a-1)+loss)) →
      (∑u∈R,f u) ≤ (C+C₀)*D₀*(1+T)^(J+J₀)*
        U^(unmarkedDensity (2*a-1)+loss+A-
          min gain (κ*(6*(unmarkedDensity (2*a-1)+loss)-1-tailε))) := by
  obtain ⟨J₀,C₀,hC₀,hordinary⟩ := actual_ordinary_weighted_fibers D loss hloss
  obtain ⟨D₀,hD₀,hlift⟩ := raw_marked_split_lift tailε htailε
  refine ⟨J₀,C₀,D₀,hC₀,hD₀,?_⟩
  intro J C hC reverse a T U κ A gain ha ha' hT hU hκ R f hR hf hsmall
  let ρ := unmarkedDensity (2*a-1)+loss
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hbase : 1≤1+T := by linarith
  have hρ : 1+tailε≤6*ρ := by
    dsimp [ρ]
    have hh := unmarkedDensity_ge_two_sevenths (show 2*a-1≤3/4 by linarith)
    linarith
  have hheight₁ : C*(1+T)^J≤(C+C₀)*(1+T)^(J+J₀) := by
    apply (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₀.le) (by positivity)).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (Nat.le_add_right J J₀))
      (add_nonneg hC hC₀.le)
  have hheight₀ : C₀*(1+T)^J₀≤(C+C₀)*(1+T)^(J+J₀) := by
    apply (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (by positivity)).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (Nat.le_add_left J₀ J))
      (add_nonneg hC hC₀.le)
  have hh := hlift U ((C+C₀)*(1+T)^(J+J₀)) ρ κ A gain hU (by positivity) hκ hρ R f
    (fun B hB=>(hsmall B hB).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hheight₁ (Real.rpow_nonneg hUp.le _))
        (Real.rpow_nonneg (by positivity) _)))
    (fun B _=>(hordinary reverse a T U (U^A) ha ha' hT hUp
      (Real.rpow_nonneg hUp.le _) R f hR hf B).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hheight₀ (Real.rpow_nonneg hUp.le _))
        (Real.rpow_nonneg (by positivity) _)))
  convert hh using 1
  dsimp [ρ]
  ring

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.actual_marked_raw_from_small_roots
end

/- Original module: Candidate.Cycle63.Marked.DeletionFiniteExceptions. -/
section

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
end
