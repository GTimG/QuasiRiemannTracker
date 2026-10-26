import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.CoarseEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.InitialState
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.Incumbent
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Physical
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentRetainedEnergy CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState ConcretePrimeRowBridge
open QuadraticInitialBound Cycle63Moment
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (R : Ideal O) [NeZero R]
local instance initialCoarseFinite : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
variable (H : Subgroup (O ⧸ R)ˣ) (hH : RayOrthogonality.globalUnits R ≤ H)

/-- The literal initial energy, including the original fixed mask and keep
predicate. Slot parameters retain their finite-subtype indexing. -/
def initialEnergy (W : ℝ → ℂ) (bslot Z width : ℝ) (η η₀ : Character) (Q : Ideal O)
    (T : Finset α) (θ : T → RayQuotient.Characters R H) (w σ v : T → ℝ)
    (t X₁ X₂ : ℝ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) : ℝ :=
  energy η (fixedBadMask*idealGenerator 1) 1 t W₁ W₂
    (fun i => primePool R H bslot (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^width)

def InitialCoarseAt (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax extra Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters R H) (w σ v : T → ℝ)
    (t height : ℝ), (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height →
  ∀ width : ℝ, Mmin ≤ width → width ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    X₁ ≤ Z^(Mmax+1) → X₂ ≤ Z^(Mmax+1) →
    initialEnergy R H hH W bslot Z width η η₀ Q T θ w σ v t X₁ X₂
      (p.profile 0) (p.profile 1) Φ ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(width+extra)

/-- The original incumbent supplies the plain moment. The fixed anchor's
logarithmic conductor width is paid uniformly over the finite dictionary. -/
theorem original_initial_coarse (W : ℝ → ℂ) (aslot bslot a b bΦ mesh lo hi Mmin Mmax ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hbΦ : 0 < bΦ)
    (hmesh : 0 ≤ mesh) (hMmin : 0 < Mmin) (hMM : Mmin ≤ Mmax)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (η : Label → Character) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      Q ≤ R → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ label : Label,
      InitialCoarseAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        (ε+2*(Fintype.card α : ℝ)*mesh) Z (η label) η₀ Q degree S C := by
  classical
  have hMmax : 0 < Mmax := hMmin.trans_le hMM
  have hhalf : 0 < ε/2 := by positivity
  obtain ⟨degree,S,hinc⟩ := Cycle63Moment.LowBranch.original_incumbent (α := α)
    R H hH W aslot bslot a b bΦ 0 (Mmax+1) lo hi (Mmax+1) (ε/2)
    haslot hWs hW hbslot ha haUpper hb hbΦ (by norm_num) (by linarith) hhalf hbeta
  have hchoices (T : Finset α) := coarse_energy_at (α := T) R H hH W aslot bslot lo hi
    haslot hWs hW.continuous mesh hmesh
  choose Cs hCs hcoarse using hchoices
  let K : ℝ := 1+∑ T : Finset α, Cs T ^ Fintype.card T
  have hCs0 (T : Finset α) : 0 ≤ Cs T := zero_le_one.trans (hCs T)
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (fun T (_ : T ∈ (Finset.univ : Finset (Finset α))) =>
      pow_nonneg (hCs0 T) (Fintype.card T))
    dsimp [K]; linarith
  have hCT (T : Finset α) : Cs T ^ Fintype.card T ≤ K := by
    have hh := Finset.single_le_sum (fun T (_ : T ∈ (Finset.univ : Finset (Finset α))) =>
      pow_nonneg (hCs0 T) (Fintype.card T)) (Finset.mem_univ T)
    dsimp [K]; linarith
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQR hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,_,hz⟩ := hinc η₀ Q hQR hQ0 hQt hQ72
  refine ⟨K*C₀,mul_pos hK hC₀,?_⟩
  have hanchor := fixed_anchor_width_uniform η Mmin (ε/(2*Mmax)) hMmin (by positivity)
  filter_upwards [hz,hanchor] with Z hz hanchor
  refine ⟨hz.1,?_⟩
  intro label T θ w σ v t height hw hwm hσlo hσhi hheight width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hwidth0 : 0 ≤ width := hMmin.le.trans hwidth
  let s := fixedParentState (η label) (internalQ Q η₀) Φ bΦ Z width hz.1 hwidth0 hΦ hΦpos
  have hlog : Real.logb Z ((η label).modulus.absNorm : ℝ) ≤ ε/2 := by
    apply (hanchor.2 label width hwidth).trans
    apply (mul_le_mul_of_nonneg_left hwidthmax (by positivity : 0 ≤ ε/(2*Mmax))).trans_eq
    field_simp
  have hs : s.width ≤ Mmax+1 := by
    dsimp only [s,fixedParentState_width]
    linarith
  have hh := hcoarse T a b bΦ 0 (Mmax+1) (Mmax+1) (ε/2) Z η₀ Q degree S C₀ hC₀.le
    hz.2.1 Finset.univ θ w σ v t height hw hwm hσlo hσhi hheight s rfl hs
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have henergy : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : (Finset.univ : Finset T) => primePool R H bslot (Z^(w i)))
      (fun (i : (Finset.univ : Finset T)) I =>
        idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i : (Finset.univ : Finset T) => Z^(w i)) X₁ X₂ s.radial.keep
        s.radial.profile s.radial.scale =
      initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
        (p.profile 0) (p.profile 1) Φ := by
    have hp : (∏ i : (Finset.univ : Finset T), Z^(w i)) = ∏ i : T, Z^(w i) :=
      Finset.prod_coe_sort Finset.univ (fun i : T => Z^(w i))
    have hr (z : O) :
        (∏ i : (Finset.univ : Finset T), CenteredMomentHeckeSlots.rowSlot
          s.character s.mask 1 z (primePool R H bslot (Z^(w i)))
          (fun I => idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) =
        ∏ i : T, CenteredMomentHeckeSlots.rowSlot
          s.character s.mask 1 z (primePool R H bslot (Z^(w i)))
          (fun I => idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t :=
      Finset.prod_coe_sort Finset.univ (fun i : T => CenteredMomentHeckeSlots.rowSlot
          s.character s.mask 1 z (primePool R H bslot (Z^(w i)))
          (fun I => idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t)
    simp only [energy,positiveSlotRow,hp,hr,initialEnergy]
    rfl
  rw [henergy] at hh
  have hcard : (Fintype.card T : ℝ) ≤ Fintype.card α := by
    exact_mod_cast (show Fintype.card T ≤ Fintype.card α by
      simpa using Finset.card_le_univ T)
  have he : s.width+ε/2+2*(Fintype.card T : ℝ)*mesh ≤
      width+(ε+2*(Fintype.card α : ℝ)*mesh) := by
    have hc := mul_le_mul_of_nonneg_right hcard hmesh
    change width + Real.logb Z ((η label).modulus.absNorm : ℝ) + ε/2 +
      2*(Fintype.card T : ℝ)*mesh ≤ _
    linarith
  have hd := diagonalControl_nonneg Φ
  have hZp : 0 < Z := zero_lt_one.trans hz.1
  apply hh.trans
  change (Cs T ^ Fintype.card T * C₀)*diagonalControl Φ*(p.control S)^2*
      (1+|t|+height)^degree*Z^(s.width+ε/2+2*(Fintype.card T : ℝ)*mesh) ≤ _
  have hcp := hCT T
  have hzp := Real.rpow_le_rpow_of_exponent_le hz.1.le he
  gcongr

end
end OAI.SevenEighths.Cycle63Physical

end Record1252270103Bootstrap.PR67
