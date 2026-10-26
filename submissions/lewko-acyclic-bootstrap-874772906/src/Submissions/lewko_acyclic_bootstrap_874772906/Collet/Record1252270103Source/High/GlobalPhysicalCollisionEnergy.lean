/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Full singleton energies pay the literal marked Newton slots after actual frozen
puncture extraction. Row-only centering and positive weights remain unchanged. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalMarkedSlots

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentSecondHeightFamily
open Record1252270103Second
open QRH.Record1252270103Source.Collision
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
local notation "O" => ActualEisensteinCubic.O
variable {ι Row : Type*} [Fintype ι]

theorem actual_marked_slots_energy_of_full_singletons
    (s : Input ι) (K R : Row→Ideal O) (hKR : ∀u,K u∣R u)
    (τ : Row→Character) (t : Row→ℝ) (z : Row→O)
    (rows : Finset Row) (D : Row→ℂ)
    (B bound : ℝ) (hB : 1≤B) (hP : ∀i,1≤s.P i)
    (hβ : ∀i,∀p∈s.slots i,‖restoredSlotCoeff s i p‖≤B)
    (hN : ∀i,∀p∈s.slots i,(p.absNorm:ℝ)≤2*s.P i)
    (N : ℕ) (hslots : Fintype.card ι≤N)
    (hs : ∀E⊆equalityEdges (I:=ι),(∑u∈rows,
      ‖D u*(∏q : {q // singletonBlock (edgeSetoid E) q},
        normalizedSlot (τ u) (fixedBadMask*idealGenerator (R u)) 1 (z u)
          (s.slots (singletonRepresentative (edgeSetoid E) q))
          (restoredSlotCoeff s (singletonRepresentative (edgeSetoid E) q)) (t u)
          (s.P (singletonRepresentative (edgeSetoid E) q)))‖^2)≤bound) :
    (∑u∈rows,‖D u*markedNewtonSlots s (K u) (R u) (τ u) (t u) (z u)‖^2)≤
      collisionProjectionCost B 256 N*bound := by
  have hh := normalized_marked_energy_of_full_singletons τ
    (fun u=>fixedBadMask*idealGenerator (R u)) (fun _=>1) z t rows D
    s.slots (restoredSlotCoeff s) s.P B bound hB hP hβ s.prime hN N hslots hs
  apply le_trans _ hh
  apply Finset.sum_le_sum
  intro u hu
  rw [marked_newton_slots_collision s (K u) (R u) (hKR u)]
  by_cases hk : Squarefree (K u)
  · simp only [QRH.Record1252270103TwoIdeal.squarefreeIndicator,hk,ite_true,one_mul,le_refl]
  · simp only [QRH.Record1252270103TwoIdeal.squarefreeIndicator,hk,ite_false,zero_mul,mul_zero,
      norm_zero,zero_pow (by decide : 2≠0)]
    exact sq_nonneg _

/-- The weight may contain the original keep predicate and positive radial
window. The singleton side is the same centered ordinary row times full slots. -/
theorem actual_weighted_marked_cofactor_energy
    (s : Input ι) (K R : Row→Ideal O) (hKR : ∀u,K u∣R u)
    (τ : Row→Character) (t : Row→ℝ) (z : Row→O)
    (rows : Finset Row) (plain : Row→ℂ) (weight : Row→ℝ)
    (hw : ∀u∈rows,0≤weight u)
    (B bound : ℝ) (hB : 1≤B) (hP : ∀i,1≤s.P i)
    (hβ : ∀i,∀p∈s.slots i,‖restoredSlotCoeff s i p‖≤B)
    (hN : ∀i,∀p∈s.slots i,(p.absNorm:ℝ)≤2*s.P i)
    (N : ℕ) (hslots : Fintype.card ι≤N)
    (hs : ∀E⊆equalityEdges (I:=ι),(∑u∈rows,
      ‖plain u*(∏q : {q // singletonBlock (edgeSetoid E) q},
        normalizedSlot (τ u) (fixedBadMask*idealGenerator (R u)) 1 (z u)
          (s.slots (singletonRepresentative (edgeSetoid E) q))
          (restoredSlotCoeff s (singletonRepresentative (edgeSetoid E) q)) (t u)
          (s.P (singletonRepresentative (edgeSetoid E) q)))‖^2*weight u)≤bound) :
    (∑u∈rows,‖plain u*markedNewtonSlots s (K u) (R u) (τ u) (t u) (z u)‖^2*weight u)≤
      collisionProjectionCost B 256 N*bound := by
  have he (f : Row→ℂ) :
      (∑u∈rows,‖((Real.sqrt (weight u):ℂ)*plain u)*f u‖^2)=
        ∑u∈rows,‖plain u*f u‖^2*weight u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [mul_assoc,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw u hu)]
    ring
  have hh := actual_marked_slots_energy_of_full_singletons s K R hKR τ t z rows
    (fun u=>(Real.sqrt (weight u):ℂ)*plain u) B bound hB hP hβ hN N hslots
    (by intro E hE;rw [he];exact hs E hE)
  rw [he] at hh
  exact hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_marked_slots_energy_of_full_singletons
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_weighted_marked_cofactor_energy
