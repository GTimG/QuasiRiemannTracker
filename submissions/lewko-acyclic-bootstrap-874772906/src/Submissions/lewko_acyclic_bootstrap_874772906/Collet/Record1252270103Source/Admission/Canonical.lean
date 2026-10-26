/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Ordinary masked admission from the literal earlier initial source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.Mask
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.RawCaps
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentEnergyBands
open QRH.Record12518109Source QRH.Record1252270103Low
local notation "O" => HeckeFamily.O

lemma clipped_length_mono (Z X Y : ℝ) (hZ : 1<Z) (hXY : X≤Y) :
    length Z X≤length Z Y :=
  Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 _))
    (max_le_max le_rfl hXY)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

/-- A single puncture constant works before the surviving subset, radius,
characters, profiles and outer height. No source theorem is instantiated at a
moving natural character; `η` is the fixed anchor in the supplied source. -/
theorem canonical_masked_energy_all_slots
    (Mslot : α→ℝ) (hMslot : ∀i,0≤Mslot i) (slotUpper δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀F : Finset α,
    ∀(B lam cap : ℝ),0≤lam → ∀(W : ℝ→ℂ)
      (a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ),0<a → 0≤b → 1<Z →
    ∀(η η₀ : Character)(Q : Ideal O)(degree : ℕ)(SP : Finset (ℕ×ℕ))(CP : ℝ),0≤CP →
      InitialAffineAt (α:=α) rayModulus Hray hH (SourceFace.mk B lam 0 B 0 cap) W
        slotUpper a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree SP CP →
    ∀(θ : α→RayQuotient.Characters rayModulus Hray)(w σ freq : α→ℝ)(t height : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤mesh) →
      (∀i∈F,σlo≤σ i) → (∀i∈F,σ i≤σhi) → 0≤height → (∀i∈F,|freq i|≤height) →
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),
        ‖idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I‖≤Mslot i) →
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),
        idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I≠0 →
        (I.absNorm:ℝ)≤slotUpper*Z^(w i)) →
    ∀(M m₁ m₂ total : ℝ),Mmin≤M → M≤Mmax → total≤cap*M →
      m₁+m₂+lam*total≤B*M → (∑i∈F,w i)≤total →
    ∀(p : Profiles a b)(X₁ X₂ : ℝ),0<X₁ → 0<X₂ →
      length Z X₁≤m₁ → length Z X₂≤m₂ →
    ∀(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀R : Ideal O,R≠0 →
      energy η (fixedBadMask*idealGenerator R) 1 t (p.profile 0) (p.profile 1)
        (fun i:F=>primePool rayModulus Hray slotUpper (Z^(w i)))
        (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:F=>Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*(R.radical.absNorm:ℝ)^δ*
        (CP*QuadraticInitialBound.diagonalControl Φ*(p.control SP)^2*
          (1+|t|+height)^degree*Z^(M+ε)) := by
  choose C₀ hC₀ hm using fun F : Finset α=>fixed_mask_energy_transfer_height
    F (fun _=>slotUpper) Mslot (fun i _=>hMslot i) δ hδ
  let C : ℝ:=1+∑F : Finset α,C₀ F
  have hC : 0<C := by
    have hh:=Finset.sum_nonneg (s:=(Finset.univ:Finset (Finset α))) (fun F _=>(hC₀ F).le)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro F B lam cap hlam W a b bΦ mesh σlo σhi Mmin Mmax ε Z ha hb hZ
    η η₀ Q degree SP CP hCP hsource θ w σ freq t height hw hmesh hσlo hσhi hh hv
    hβ hs M m₁ m₂ total hMlo hMhi hcap hbudget htotal p X₁ X₂ hX₁ hX₂ hx₁ hx₂
    Φ hΦs hΦ R hR
  have hZ0 : 0<Z:=zero_lt_one.trans hZ
  have hE : 0≤CP*QuadraticInitialBound.diagonalControl Φ*(p.control SP)^2*
      (1+|t|+height)^degree*Z^(M+ε) := by
    have hd:=QuadraticInitialBound.diagonalControl_nonneg Φ
    positivity
  have hCF : C₀ F≤C := by
    have hh:=Finset.single_le_sum (s:=(Finset.univ:Finset (Finset α)))
      (f:=C₀) (fun G _=>(hC₀ G).le) (Finset.mem_univ F)
    dsimp only [C]
    linarith
  apply le_trans _ (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCF (Real.rpow_nonneg (Nat.cast_nonneg _) δ)) hE)
  apply hm F η R hR t (p.profile 0) (p.profile 1) a b ha hb (p.support 0) (p.support 1)
    (fun i=>primePool rayModulus Hray slotUpper (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) (fun i hi I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=>Real.rpow_pos_of_pos hZ0 _) hβ hs X₁ X₂ hX₁ hX₂
    (initialKeep η (internalQ Q η₀)) (fun z hz=>hz.1) Φ (Z^M) _
    (Real.rpow_pos_of_pos hZ0 _) hΦ hE
  intro G hGF Y₁ Y₂ hY₁ hY₂ hYX₁ hYX₂
  have hsum : (∑i:G,w i)≤total := by
    rw [Finset.sum_coe_sort]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hGF (fun i hi _=>hw i hi)).trans htotal
  apply hsource G (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>freq i) t height
    (fun i=>hw i (hGF i.property)) (fun i=>hmesh i (hGF i.property))
    (fun i=>hσlo i (hGF i.property)) (fun i=>hσhi i (hGF i.property)) hh
    (fun i=>hv i (hGF i.property)) M hMlo hMhi Φ hΦs hΦ p Y₁ Y₂ hY₁ hY₂
  exact global_shortening_admission B lam cap m₁ m₂ total M _ _ _ hlam
    (length_nonneg Z Y₁ hZ) (length_nonneg Z Y₂ hZ)
    (Finset.sum_nonneg (fun i _=>hw i (hGF i.property)))
    ((clipped_length_mono Z Y₁ X₁ hZ hYX₁).trans hx₁)
    ((clipped_length_mono Z Y₂ X₂ hZ hYX₂).trans hx₂) hsum hcap hbudget

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.clipped_length_mono
#print axioms QRH.Record1252270103Source.Admission.canonical_masked_energy_all_slots
