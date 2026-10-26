/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Combine actual canonical slot deletion with the completed baseline zero-slot
theorem. This supplies an unconditional analytic input on the nonfixed
branch; common puncture and collision restoration is a separate application.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.NativeZeroInput
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.NativeSlotDeletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.FourthPower.NativeNonfixedEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- All positive ordinary lengths up to the enclosure are allowed. No
previous estimate for the mixed moment is an input to this theorem. -/
theorem canonical_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (aslot bslot a b radial Mcap L Lslot ε lo hi κ : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hrad : 0<radial) (hM : 0<Mcap) (hLslot : 0≤Lslot) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤V → (∀i∈F,|freq i|≤V) →
    ∀s : NaturalState Z 0 radial,s.puncture=1 → s.fixedModulus=Q → s.width≤Mcap →
    ∀A : Finset α,A⊆F → ∀p : Profiles a b,∀X₁ X₂ : ℝ,
      0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i:A=>primePool M H bslot (Z^(w i)))
        (fun (i:A) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:A=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control control)^2*(1+|t|+V)^degree*
        Z^(s.width+κ*(∑i∈F,w i)+ε) := by
  obtain ⟨js,Cs,hCs,hdelete⟩ := NativeSlotDeletion.canonical_delete M H hH F W
    aslot bslot radial Mcap Lslot (ε/2) lo hi κ haslot hWs hW hrad.le hM.le
    hLslot (by linarith) hβ hκ
  obtain ⟨jz,S,hzero⟩ := NativeZeroInput.zero_input a b radial 0 L Mcap (ε/2)
    ha haUpper hb hrad le_rfl hM (by linarith) hβ Q hQt hQ72
  refine ⟨js+jz,S,?_⟩
  intro η₀ hQη
  obtain ⟨Cz,hCz,hz⟩ := hzero η₀ hQη
  refine ⟨Cs*Cz,mul_pos hCs hCz,?_⟩
  filter_upwards [hdelete η₀,hz] with Z hd hz
  refine ⟨hd.1,?_⟩
  intro θ w σ freq t V hw hwL hσ hσhi hV hfreq s hu hQ hwidth A hAF p
    X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hZ : 0<Z := zero_lt_one.trans hd.1
  have hQI : s.fixedModulus=internalQ Q η₀ := by
    simpa only [show internalQ Q η₀=Q from inf_eq_left.mpr hQη] using hQ
  have he := hd.2 θ w σ freq t V hw hwL hσ hσhi hV hfreq 0 s hu hwidth Q hQI hQM
    A hAF (p.profile 0) (p.profile 1) X₁ X₂ hX₁ hX₂
  rw [←s.plainEnergy_eq_zero p t X₁ X₂] at he
  have hp := hz.2 s hQ hwidth p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hheight : (1+‖t‖)^jz≤(1+|t|+V)^jz := by
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hdc := diagonalControl_nonneg s.radial.profile
  have hbase : 0≤1+|t|+V := by positivity
  apply he.trans
  calc
    _ ≤ (Cs*(1+|t|+V)^js*Z^(ε/2+κ*(∑i∈F,w i)))*
        (Cz*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^jz*Z^(s.width+ε/2)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (Cs*(1+|t|+V)^js*Z^(ε/2+κ*(∑i∈F,w i)))*
        (Cz*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+V)^jz*Z^(s.width+ε/2)) := by
      gcongr
    _ = (Cs*Cz)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+V)^(js+jz)*
        Z^(s.width+κ*(∑i∈F,w i)+ε) := by
      rw [pow_add,show s.width+κ*(∑i∈F,w i)+ε=(ε/2+κ*(∑i∈F,w i))+(s.width+ε/2) by ring,
        Real.rpow_add hZ (ε/2+κ*(∑i∈F,w i)) (s.width+ε/2)]
      ring

end
end Candidate.FourthPower.NativeNonfixedEnergy
