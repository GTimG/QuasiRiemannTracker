/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The checked physical and reference leaves join on their identical finite norm. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialNaturalPhysical
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialProjectedReference
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open QRH.Record1252270103Source.Collision
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [instD : DecidableEq ι]

theorem markedFiniteEnergy_eq_projected_norm (s : Input ι) (R : Ideal O) (A : O)
    (b X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (rows : Finset O) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀x,0≤(Φ x).re)
    (atoms : Finset (Ideal O)) (hS : ∀i,s.slots i⊆atoms) (hp : ∀I∈atoms,Prime I) :
    markedFiniteEnergy s R A b X₁ X₂ rows keep Φ K=
      ∑z∈rows,‖weightedPlain s.η (fixedBadMask*idealGenerator R) A s.t s.W₁ s.W₂
        b X₁ X₂ keep Φ K z*injectiveTuplePolynomial
          (fun i (I : atoms)=>normalizedRowCoeff s.η (fixedBadMask*idealGenerator R) A z s.t
            (s.slots i) (fun I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) (s.P i) I)‖^2 := by
  apply Finset.sum_congr rfl
  intro z hz
  have hdec : instD=Classical.decEq ι := Subsingleton.elim _ _
  cases hdec
  exact (weightedPlain_marked_row_norm s.η (fixedBadMask*idealGenerator R) A z s.t
    s.W₁ s.W₂ b X₁ X₂ keep Φ K s.slots
    (fun i I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) s.P atoms hS hp hX₁ hX₂
    (fun i=>(s.P_pos i).le) hΦ).symm

/-- The identity embedding extracts the exact reference norm from the
uniform all-subsets supplier. The original atom superset is unchanged. -/
theorem markedFiniteEnergy_le_projected (s : Input ι) (R : Ideal O) (A : O)
    (b X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (rows : Finset O) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀x,0≤(Φ x).re)
    (atoms : Finset (Ideal O)) (hS : ∀i,s.slots i⊆atoms) (hp : ∀I∈atoms,Prime I)
    (bound : ℝ)
    (href : projectedSubsetBound rows
      (fun z i (I : atoms)=>normalizedRowCoeff s.η (fixedBadMask*idealGenerator R) A z s.t
        (s.slots i) (fun I=>s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) (s.P i) I)
      (weightedPlain s.η (fixedBadMask*idealGenerator R) A s.t s.W₁ s.W₂ b X₁ X₂ keep Φ K) bound) :
    markedFiniteEnergy s R A b X₁ X₂ rows keep Φ K≤bound := by
  rw [markedFiniteEnergy_eq_projected_norm s R A b X₁ X₂ hX₁ hX₂ rows keep Φ K hΦ atoms hS hp]
  exact href ι (Function.Embedding.refl ι)

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.markedFiniteEnergy_eq_projected_norm
#print axioms QRH.Record1252270103Low.markedFiniteEnergy_le_projected
