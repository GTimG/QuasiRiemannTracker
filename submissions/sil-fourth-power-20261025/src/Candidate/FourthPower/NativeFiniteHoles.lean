/- Copyright (c) 2026 Sil. Apache-2.0.
Actual finite marked-prime exclusions, without a uniform estimate for
arbitrary replacement coefficients. The full canonical subset energies
are retained and only finitely many individual coefficients are removed.
-/
import Candidate.FourthPower.NativeNaturalChild
import Candidate.FourthPower.KernelCollisionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.FourthPower.NativeFiniteHoles
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentPrimeSlot CenteredMomentRayMaskedFloor QuadraticInitialBound
open CenteredMomentNaturalRowSource HeckeDyadic CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyCapacityRemoval
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

def holeCoefficient {α : Type*} (β : α→Id→ℂ) (R : α→Finset Id) (i : α) (I : Id) : ℂ :=
  if I∈R i then 0 else β i I

theorem slot_holes (χ : Character) (pool R : Finset Id) (β : Id→ℂ) (P : ℝ) :
    naturalSlot χ pool (fun I=>if I∈R then 0 else β I) P =
      naturalSlot χ pool β P-naturalSlot χ (pool∩R) β P := by
  unfold naturalSlot
  have hi : pool∩R=pool.filter (fun I=>I∈R) := by ext I; simp
  rw [←mul_sub,hi,Finset.sum_filter,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : I∈R <;> simp [h]

theorem removed_slot_bound (χ : Character) (pool R : Finset Id)
    (β : Id→ℂ) (P B : ℝ) (H : ℕ) (hP : 1≤P) (hB : 0≤B)
    (hR : R.card≤H) (hβ : ∀I∈pool,‖β I‖≤B) :
    ‖naturalSlot χ (pool∩R) β P‖≤(H:ℝ)*B := by
  apply (naturalSlot_norm χ R pool β P).trans
  have hsqrt : 1≤Real.sqrt P := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hP
  have hinv : (Real.sqrt P)⁻¹≤1 := inv_le_one_of_one_le₀ hsqrt
  have hcard : ((pool∩R).card:ℝ)≤H := by
    exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans hR
  unfold slotMass
  calc
    _ ≤ 1*∑I∈pool∩R,‖β I‖ := mul_le_mul_of_nonneg_right hinv (by positivity)
    _ ≤ 1*∑_I∈pool∩R,B := by
      apply mul_le_mul_of_nonneg_left _ zero_le_one
      exact Finset.sum_le_sum (fun I hI=>hβ I (Finset.mem_inter.mp hI).1)
    _ = ((pool∩R).card:ℝ)*B := by simp
    _ ≤ (H:ℝ)*B := mul_le_mul_of_nonneg_right hcard hB

/-- A literal finite-exclusion transfer. The only energy inputs are the
unmodified subset products, with their original row-dependent character. -/
theorem radial_holes {α : Type*} [DecidableEq α]
    (F : Finset α) (N H : ℕ) (hN : F.card≤N)
    (D : O→ℂ) (χ : O→Character) (pool R : α→Finset Id)
    (β : α→Id→ℂ) (P : α→ℝ) (B E radial : ℝ)
    (hB : 0≤B) (hE : 0≤E) (hP : ∀i∈F,1≤P i)
    (hR : ∀i∈F,(R i).card≤H) (hβ : ∀i∈F,∀I∈pool i,‖β i I‖≤B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hchildren : ∀A : Finset α,A⊆F →
      radialEnergy (fun z=>D z*∏i∈A,naturalSlot (χ z) (pool i) (β i) (P i)) keep Φ K≤E) :
    radialEnergy (fun z=>D z*∏i∈F,naturalSlot (χ z) (pool i)
      (holeCoefficient β R i) (P i)) keep Φ K ≤
      ((2:ℝ)^N*(max 1 ((H:ℝ)*B))^N)^2*E := by
  let L : ℝ := max 1 ((H:ℝ)*B)
  have hL : 1≤L := le_max_left _ _
  let G (J : F.powerset) (z : O) :=
    D z*∏i∈F\J.val,naturalSlot (χ z) (pool i) (β i) (P i)
  let A (J : F.powerset) (z : O) :=
    ((-1:ℂ)^J.val.card*∏i∈J.val,naturalSlot (χ z) (pool i∩R i) (β i) (P i))*G J z
  have hJ (J : F.powerset) : J.val⊆F := Finset.mem_powerset.mp J.property
  have hA (J : F.powerset) (z : O) : ‖A J z‖≤L^N*‖G J z‖ := by
    simp only [A,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_prod]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ∏_i∈J.val,L := Finset.prod_le_prod₀ (fun i _=>norm_nonneg _)
        (fun i hi=>(removed_slot_bound (χ z) (pool i) (R i) (β i) (P i) B H
          (hP i (hJ J hi)) hB (hR i (hJ J hi)) (hβ i (hJ J hi))).trans (le_max_right _ _))
      _ = L^J.val.card := Finset.prod_const _
      _ ≤ L^N := pow_le_pow_right₀ hL ((Finset.card_le_card (hJ J)).trans hN)
  have heq (z : O) : D z*∏i∈F,naturalSlot (χ z) (pool i) (holeCoefficient β R i) (P i)=
      ∑J : F.powerset,A J z := by
    change D z*∏i∈F,naturalSlot (χ z) (pool i) (fun I=>if I∈R i then 0 else β i I) (P i)=_
    simp_rw [slot_holes]
    rw [prod_sub_expansion,Finset.mul_sum]
    dsimp only [A,G]
    rw [←Finset.sum_coe_sort F.powerset (fun J : Finset α=>
      D z*(((-1:ℂ)^J.card*∏i∈J,naturalSlot (χ z) (pool i∩R i) (β i) (P i))*
        ∏i∈F\J,naturalSlot (χ z) (pool i) (β i) (P i)))]
    apply Finset.sum_congr rfl
    intro J hJ
    ring
  have hmass : (∑_J : F.powerset,L^N)≤(2:ℝ)^N*L^N := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe,Finset.card_powerset,
      Nat.cast_pow,Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hN) (by positivity)
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs; exact mul_nonneg (sq_nonneg _) (hΦ z); exact le_rfl)
  intro rows
  let ρ (z : O) : ℝ := if keep z then (Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hρ (z : O) : 0≤ρ z := by dsimp [ρ]; split_ifs; exact hΦ z; exact le_rfl
  have hG (J : F.powerset) : (∑z∈rows,ρ z*‖G J z‖^2)≤E := by
    have hsum := compact_radial_summable (G J) keep Φ K radial hK hs
    have hh := hsum.sum_le_tsum rows (fun z _=>by
      split_ifs; exact mul_nonneg (sq_nonneg _) (hΦ z); exact le_rfl)
    have hid (z : O) : ρ z*‖G J z‖^2=
        if keep z then ‖G J z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0 := by
      dsimp [ρ]; split_ifs <;> ring
    simp_rw [hid]
    exact hh.trans (hchildren (F\J.val) Finset.sdiff_subset)
  have hh := KernelCollisionEnergy.weighted_physical_energy rows ρ A G (fun _=>L^N) E
    (fun z _=>hρ z) (fun _=>by positivity) (fun J z _=>hA J z) hG
  have hbound := hh.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hmass 2) hE)
  apply (le_of_eq ?_).trans hbound
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  rw [heq]
  dsimp [ρ]
  split_ifs <;> ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem shortened_children {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α) (Holes : ℕ) (W : ℝ→ℂ) (aslot bslot a b radial Mcap L Lslot ε lo hi κ : ℝ)
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
    ∀Bmask : ℝ,∀s : NaturalState Z Bmask radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀A : Finset α,A⊆F → ∀R : α→Finset Id,(∀i∈A,(R i).card≤Holes) → ∀W₁ W₂ : 𝓢(ℝ,ℂ),
    ∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
        polynomial (naturalCharacter s.character z) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
        ∏i∈A,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (holeCoefficient
            (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R i) t) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i∈F,w i)+ε) := by
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W aslot bslot lo hi haslot hWs hW.continuous
  obtain ⟨degree,S,hbound⟩ := NativeNaturalChild.shortened_children M H hH F W
    aslot bslot a b radial Mcap L Lslot ε lo hi κ haslot hWs hW ha haUpper hb hrad hM
    hLslot hε hβ hκ Q hQt hQ72 hQM
  let cost : ℝ := ((2:ℝ)^F.card*(max 1 ((Holes:ℝ)*B))^F.card)^2
  have hcost : 0<cost := by dsimp [cost]; positivity
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbound⟩ := hbound η₀ hQη
  refine ⟨cost*C,mul_pos hcost hC,hbound.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V hw hwL hσ hσhi hV hfreq Bmask s hQ hwidth A hAF R hR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂
  let P := fun i=>Z^(w i)
  let pool := fun i=>primePool M H bslot (P i)
  let ν := fun i=>relativeCharacter M H hH η₀ (θ i)
  let β := fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight W (P i) (σ i) (freq i) I
  let D := fun z=>HeckeDyadic.polynomial (naturalCharacter s.character z) false W₁
      (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
    HeckeDyadic.polynomial (naturalCharacter s.character z) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂
  let E := C*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i∈F,w i)+ε)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hZpos := zero_lt_one.trans hZ.1
  have hE : 0≤E := by dsimp [E]; positivity
  have he := radial_holes A F.card Holes (Finset.card_le_card hAF) D
    (fun z=>naturalCharacter s.character z) pool R (fun i=>heightCoefficient (β i) t) P B E radial
    hB.le hE (fun i hi=>Real.one_le_rpow hZ.1.le (hw i (hAF hi))) hR (by
      intro i hi I hI
      exact (hcoeff (ν i) (P i) (σ i) (freq i) t (Real.rpow_pos_of_pos hZpos _)
        (hσ i (hAF hi)) (hσhi i (hAF hi)) I (Finset.mem_filter.mp hI).2.1.ne_zero).1)
    (effectiveState s).radial.keep s.radial.profile s.radial.scale s.radial.scale_pos
    s.radial_support s.radial.nonneg (by
      intro J hJA
      exact hZ.2 θ w σ freq t V hw hwL hσ hσhi hV hfreq Bmask s hQ hwidth J
        (hJA.trans hAF) W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂)
  have hmask (i : α) : holeCoefficient (fun i=>heightCoefficient (β i) t) R i =
      heightCoefficient (holeCoefficient β R i) t := by
    funext I
    by_cases h : I∈R i <;> simp [holeCoefficient,heightCoefficient,h]
  simp_rw [hmask] at he
  apply he.trans_eq
  dsimp [cost,E]
  ring

end
end Candidate.FourthPower.NativeFiniteHoles
