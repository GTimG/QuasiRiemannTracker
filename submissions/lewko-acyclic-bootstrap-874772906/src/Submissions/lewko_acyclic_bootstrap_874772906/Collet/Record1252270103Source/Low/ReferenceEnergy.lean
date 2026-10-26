/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Generalized from Cycle61.Physical.FirstBranches.FixedComparison, source SHA256
576e3d7aff4f1bd817632e4c347999fa82ddc21e43c79b0277b25a58af52351b.
Underlying profile/scalar absorption: OpenAI/math, Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.ReferenceUniform

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Low
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound CenteredMomentCommonMaskExpansion
open CenteredMomentNaturalRowSource CenteredMomentOriginalRadialComparison
open CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskEnergy
open Cycle61Moment Cycle61FirstGeometry Cycle61FirstActual Cycle61FirstReflection
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Literal original energy with the whole initial mask, full normalizer and
independent norm-power profiles. All reflection and logarithmic losses have
already been absorbed by the genuine uniform reference theorem. -/
theorem actual_fixed_parent_short_reference_energy
    (κ Kcap : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ) (hKcap : 6*κ ≤ Kcap)
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0<a) (hlo : a≤1/4) (hhi : 1≤b)
    (hbΦ : 0<bΦ) (hMmin : 0<Mmin) (hMmax : Mmin≤Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    0<comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
    ∀j : Label, ∀M along short r cap : ℝ, Mmin≤M → M≤Mmax →
      0≤r → 0≤cap → short≤r → r+Kcap*cap≤49*M/100 →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀u t height : ℝ,
      (∀i,0≤w i) → (∀i,w i≤comparisonMesh Mmin Mmax ε) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → (∑i∈F,w i)≤cap →
    ∀hZ : 1<Z, ∀hM : 0≤M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
    energy s.character s.mask 1 0
      ((independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t).profile 0)
      ((independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t).profile 1)
      (fun i:F => primePool rayM H bslot (Z^(w i)))
      (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (t+freq i) I)
      (fun i:F => Z^(w i)) (Z^along) (Z^short) s.radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨hmesh,degree,S,hbound⟩ := actual_fixed_parent_short_reference rayM H hH
    κ Kcap hκlo hκhi hκbeta hKcap anchors Fmax Wslot aslot bslot lo hi
    haslot hsSlot hWslot hbslot a b bΦ Mmin Mmax ε ha hlo hhi hbΦ hMmin hMmax hε hbeta
  refine ⟨hmesh,degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,ht⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [ht] with Z hz
  refine ⟨hz.1,?_⟩
  intro j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p F hF θ w σ freq
    u t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  have hh := hz.2 j M along short r cap hmin hmax hr hcap hshort hbudget Φ hsΦ hpΦ p F hF θ
    w σ freq u t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  have heq := actual_unit_puncture_energy s rfl ha (p.profile 1) (p.profile 0)
    (p.support 1) (p.support 0) F (fun i => primePool rayM H bslot (Z^(w i)))
    (fun i => relativeCharacter rayM H hH η₀ (θ i)) (fun _ => Wslot)
    (fun i => Z^(w i)) σ freq
    (by intro i _ I hI; exact (Finset.mem_filter.mp hI).2.1)
    (by intro i _; exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    t u t (Z^along) (Z^short)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  dsimp only at hh ⊢
  exact heq.symm.trans_le hh

end
end OAI.SevenEighths.Record1252270103Low
#print axioms OAI.SevenEighths.Record1252270103Low.actual_fixed_parent_short_reference_energy
