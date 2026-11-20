/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Collision and inverse restoration of the original signed independent pair.
The only downstream inputs are literal cube-free surviving-family energies. -/
import Candidate.C092.transport.ColoredRootRestoreEnergy
import Candidate.C092.transport.ColoredRootRestoreCollision

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI.SevenEighths.Record12518109GainDeletion
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP
open KernelRowExpansion KernelRowPools KernelRowProfiles KernelMarkedRows KernelAssignmentReindex
open KernelCollisionEnergy KernelNaturalSlots RestorationFamily RestorationCollisionEnergy
open QRH.Cycle092.RegularColoredForward
local notation "Id" => Ideal HeckeFamily.O
variable {α:Type*} [Fintype α]

theorem weighted_unrestricted (S:Finset PrimeIdeal) (a:α→S→ℂ) (χ:Character)
    (ω₁ ω₂:Id→*₀ℂ) (D:Finset IdealPair) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) :
    weightedSum a (fun slot=>row χ ω₁ ω₂ D (sourceValue true S slot) W₁ W₂ X₁ X₂) =
      row χ ω₁ ω₂ D (fun _=>1) W₁ W₂ X₁ X₂*injectiveTuplePolynomial a := by
  unfold weightedSum injectiveTuplePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h:Function.Injective s
  · simp only [h,ite_true,sourceValue]
  · simp only [h,ite_false,mul_zero]

theorem signed_unrestricted (S:Finset PrimeIdeal) (χ:Character)
    (ω₁ ω₂:Id→*₀ℂ) (pool:α→Finset Id) (β:α→Id→ℂ) (P:α→ℝ)
    (D:Finset IdealPair) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ) (cX cY:ℂ) :
    signedRow true S χ ω₁ ω₂ pool β P D W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY =
      (cX*row χ ω₁ ω₂ D (fun _=>1) W₁ W₂ X₁ X₂-
        cY*row χ ω₁ ω₂ D (fun _=>1) W₁ W₂ Y₁ Y₂)*
      injectiveTuplePolynomial (naturalCoefficients χ S pool β P) := by
  unfold signedRow
  rw [weighted_unrestricted,weighted_unrestricted]
  ring

theorem signed_collision (r:Setoid α) (S:Finset PrimeIdeal)
    (tc:{q // ¬singletonBlock r q}→S) (χ:Character)
    (ω₁ ω₂:Id→*₀ℂ) (pool:α→Finset Id) (β:α→Id→ℂ) (P:α→ℝ)
    (D:Finset IdealPair) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ) (cX cY:ℂ) :
    signedRow true S χ ω₁ ω₂
      (fun q:{q // singletonBlock r q}=>pool (singletonRepresentative r q))
      (collisionBeta r S tc β) (fun q=>P (singletonRepresentative r q)) D W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY =
      (cX*row χ ω₁ ω₂ D (fun _=>1) W₁ W₂ X₁ X₂-
        cY*row χ ω₁ ω₂ D (fun _=>1) W₁ W₂ Y₁ Y₂)*injectiveTuplePolynomial
        (fun q:{q // singletonBlock r q}=>fun p:S=>
          if ∀ j:{q // ¬singletonBlock r q},p≠tc j then
            naturalCoefficients χ S pool β P (singletonRepresentative r q) p else 0) := by
  rw [signed_unrestricted]
  have hcoeff : naturalCoefficients χ S
      (fun q:{q // singletonBlock r q}=>pool (singletonRepresentative r q))
      (collisionBeta r S tc β) (fun q=>P (singletonRepresentative r q)) =
      (fun q:{q // singletonBlock r q}=>fun p:S=>
        if ∀ j:{q // ¬singletonBlock r q},p≠tc j then
          naturalCoefficients χ S pool β P (singletonRepresentative r q) p else 0) := by
    funext q p
    exact collision_coefficient r S tc χ pool β P q p
  rw [hcoeff]

def fullSigned (S:Finset PrimeIdeal) (χ:Character) (ω₁ ω₂:Id→*₀ℂ)
    (pool:α→Finset Id) (β:α→Id→ℂ) (P:α→ℝ)
    (D:Finset IdealPair) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ) (cX cY:ℂ) : ℂ :=
  (cX*row χ ω₁ ω₂ D (fun _=>1) W₁ W₂ X₁ X₂-
    cY*row χ ω₁ ω₂ D (fun _=>1) W₁ W₂ Y₁ Y₂)*
    ∏ i,CenteredMomentCommonMaskExpansion.naturalSlot χ (pool i) (β i) (P i)

omit [Fintype α] in
theorem signedRow_fintype_irrel (h₁ h₂:Fintype α) (inv:Bool) (S:Finset PrimeIdeal)
    (χ:Character) (ω₁ ω₂:Id→*₀ℂ) (pool:α→Finset Id) (β:α→Id→ℂ) (P:α→ℝ)
    (D:Finset IdealPair) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ) (cX cY:ℂ) :
    @signedRow α h₁ inv S χ ω₁ ω₂ pool β P D W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY =
    @signedRow α h₂ inv S χ ω₁ ω₂ pool β P D W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY := by
  cases Subsingleton.elim h₁ h₂
  rfl

set_option maxHeartbeats 600000 in
/-- Literal pre-root transfer. Both original signed arms survive every
collision, both native masks, every divisor and the actual injective marks. -/
theorem full_signed_energy (B ε:ℝ) (hB:1≤B) (hε:0<ε) :
    ∃ C:ℝ,0<C ∧ ∀ X:ℝ,1≤X → ∀ S:Finset PrimeIdeal,
      (∀ Q∈S,Supported Q.val ∧ (Q.val.absNorm:ℝ)≤X) →
      ∀ {Row:Type*} (rows:Finset Row) (ρ:Row→ℝ) (χ:Row→Character)
        (ω₁ ω₂:Id→*₀ℂ),(∀ d:Id×Id,‖color ω₁ ω₂ d‖≤1) →
      ∀ (pool:α→Finset Id) (β:α→Id→ℂ) (P:α→ℝ),
      (∀ i,pool i⊆primeValues S) → (∀ i,0<P i) →
      (∀ i I,I∈pool i → Supported I ∧ (I.absNorm:ℝ)≤2*P i) →
      (∀ i I,I∈pool i → ‖β i I‖≤B) →
      ∀ (W₁ W₂:ℝ→ℂ) (b M₁ M₂ X₁ X₂ Y₁ Y₂:ℝ) (cX cY:ℂ) (E:ℝ),
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → 0≤E → (∀ u∈rows,0≤ρ u) →
      (∀ (r:Setoid α) (tc:{q // ¬singletonBlock r q}→S)
        (A:Finset {q // singletonBlock r q}) (ti:A→S),Function.Injective ti →
        ∀ d∈divisorPool (supportedRectangle S b M₁ M₂),
        (∑ u∈rows,ρ u*‖signedRow false S (χ u) ω₁ ω₂
          (fun q:{q:{q // singletonBlock r q} // q∉A}=>pool (singletonRepresentative r q.val))
          (crossBeta A S ti (collisionBeta r S tc β))
          (fun q=>P (singletonRepresentative r q.val))
          (residualPool (supportedRectangle S b M₁ M₂) d) W₁ W₂
          (X₁/d.1.absNorm) (X₂/d.2.absNorm) (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) cX cY‖^2)≤E) →
      (∑ u∈rows,ρ u*‖fullSigned S (χ u) ω₁ ω₂ pool β P
        (supportedRectangle S b M₁ M₂) W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY‖^2)≤C*X^ε*E := by
  obtain ⟨Cc,hCc,hcollision⟩ := collision_product_energy (α:=α) B (ε/2) hB (half_pos hε)
  choose Ci hCi hinverse using fun r:Setoid α =>
    signed_inverse_energy (α:={q // singletonBlock r q}) B (ε/2) (zero_le_one.trans hB) (half_pos hε)
  let Cinv:=1+∑ r:Setoid α,Ci r
  have hCinv:0<Cinv := by
    have hh:=Finset.sum_nonneg (fun r (_:r∈(Finset.univ:Finset (Setoid α)))=>(hCi r).le)
    dsimp [Cinv];linarith
  have hiC (r:Setoid α):Ci r≤Cinv := by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (f:=Ci) (fun r _=>(hCi r).le) (Finset.mem_univ r)
    dsimp [Cinv];linarith
  refine ⟨Cc*Cinv,mul_pos hCc hCinv,?_⟩
  intro X hX S hS Row rows ρ χ ω₁ ω₂ hω pool β P hpool hP hp hβ W₁ W₂ b M₁ M₂ X₁ X₂ Y₁ Y₂ cX cY E hX₁ hX₂ hY₁ hY₂ hE hρ hroot
  let D:=supportedRectangle S b M₁ M₂
  let ordinary (u:Row):=cX*row (χ u) ω₁ ω₂ D (fun _=>1) W₁ W₂ X₁ X₂-
    cY*row (χ u) ω₁ ω₂ D (fun _=>1) W₁ W₂ Y₁ Y₂
  have hsingle (r:Setoid α) (tc:{q // ¬singletonBlock r q}→S) :
      (∑ u∈rows,ρ u*‖signedRow true S (χ u) ω₁ ω₂
        (fun q:{q // singletonBlock r q}=>pool (singletonRepresentative r q))
        (collisionBeta r S tc β) (fun q=>P (singletonRepresentative r q)) D W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY‖^2)
        ≤Cinv*X^(ε/2)*E := by
    have hβ':∀ q I,I∈pool (singletonRepresentative r q) → ‖collisionBeta r S tc β q I‖≤B :=
      by
        intro q I hI
        unfold collisionBeta maskedBeta
        split_ifs
        · exact hβ (singletonRepresentative r q) I hI
        · simpa only [norm_zero] using zero_le_one.trans hB
    have hh:=hinverse r X hX S hS rows ρ χ ω₁ ω₂ hω
      (fun q:{q // singletonBlock r q}=>pool (singletonRepresentative r q))
      (collisionBeta r S tc β) (fun q=>P (singletonRepresentative r q))
      (fun q=>hP (singletonRepresentative r q)) (fun q=>hp (singletonRepresentative r q)) hβ'
      W₁ W₂ b M₁ M₂ X₁ X₂ Y₁ Y₂ cX cY E hX₁ hX₂ hY₁ hY₂ hE hρ
      (by
        intro A ti hti d hd
        apply (le_of_eq ?_).trans (hroot r tc A ti hti d hd)
        apply Finset.sum_congr rfl
        intro u hu
        apply congrArg (fun z:ℂ=>ρ u*‖z‖^2)
        apply signedRow_fintype_irrel)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hiC r) (Real.rpow_nonneg (zero_le_one.trans hX) _)) hE)
  have hh:=hcollision X hX S hS rows ρ χ pool β P hpool hP hp hβ ordinary
    (Cinv*X^(ε/2)*E) (by positivity) hρ (by
      intro r tc
      simpa only [signed_collision,ordinary] using hsingle r tc)
  change (∑ u∈rows,ρ u*‖ordinary u*∏ i,CenteredMomentCommonMaskExpansion.naturalSlot
    (χ u) (pool i) (β i) (P i)‖^2)≤_
  apply hh.trans_eq
  calc
    _=(Cc*Cinv)*(X^(ε/2)*X^(ε/2))*E := by ring
    _=_ := by rw [←Real.rpow_add (zero_lt_one.trans_le hX),show ε/2+ε/2=ε by ring]

#print axioms full_signed_energy
end
end QRH.Cycle092.ColoredRootRestore
