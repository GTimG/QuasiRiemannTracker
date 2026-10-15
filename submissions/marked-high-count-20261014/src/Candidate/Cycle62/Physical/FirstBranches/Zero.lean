import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputZeroUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AddedZeroUniform

namespace OAI.SevenEighths.Cycle62FirstZero
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass CenteredMomentSourceInputTailUniform
open CenteredMomentFirstLocalization EisensteinSchwartzPoisson
open CenteredMomentExceptionalAmplitudePair CenteredMomentAddedZeroUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
/-- The first zero frequency uses the actual centered equal-product coefficient,
its literal volume, masks and all Schwartz profiles. The constant precedes every
live input and profile; independent input heights are retained inside those profiles.
This is the original powerful-product zero estimate, not a count hypothesis. -/
theorem actual_first_zero_frequency (hi:ι→ℝ)(wlo whi B ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→volume s.toData≤Z^B→
      ∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε := by
  exact CenteredMomentSourceInputZeroUniform.first_input_zero_capped
    hi wlo whi B ε hhi hwlo hwhi hB hε

/-- The artificial smooth-ball zero remains unamplified. Its genuine mask factor
is `-s₀`; the bound is on the actual finite Gauss zero with the original coefficient.
The support and coefficient norm gates are structural finite-source gates. -/
theorem actual_unamplified_added_zero {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O), Squarefree s →
      ∀ (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Z a s₀ θ : ℝ), 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 *
          Z ^ (a - s₀ + 2 * θ + ε * (a + θ))  := by
  exact CenteredMomentAddedZeroUniform.original_subset_source_energy A ε hε


omit [DecidableEq ι] in
/-- First zero terminal at the actual positive physical radius, including a
negative radius exponent. This is an actual normalized energy estimate. -/
theorem actual_first_zero_at_physical_radius (hi:ι→ℝ)(wlo whi B ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→volume s.toData≤Z^B→
      ∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(Mrow:ℝ),
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ (Z^Mrow)‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(Mrow+ε) := by
  obtain ⟨SΦ,C,hC,hb⟩ := actual_first_zero_frequency hi wlo whi B ε hhi hwlo hwhi hB hε
  refine ⟨SΦ,C,hC,?_⟩
  intro Z hZ s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV m A R seed Φ Mrow
  have hh := hb Z hZ s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV m A R seed Φ
    (Z^Mrow) (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  rw [Real.rpow_add (zero_lt_one.trans_le hZ)]
  simpa only [mul_assoc] using hh
end
end OAI.SevenEighths.Cycle62FirstZero
#print axioms OAI.SevenEighths.Cycle62FirstZero.actual_first_zero_frequency
#print axioms OAI.SevenEighths.Cycle62FirstZero.actual_unamplified_added_zero

#print axioms OAI.SevenEighths.Cycle62FirstZero.actual_first_zero_at_physical_radius
