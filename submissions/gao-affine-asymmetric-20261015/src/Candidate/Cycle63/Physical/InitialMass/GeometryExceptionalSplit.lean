import Candidate.Cycle63.Physical.FixedInducingChosen
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondEnergySplit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily CenteredMomentChildRows RayFourExpansion
open CenteredMomentRestrictedEnergy
open CenteredExceptionalProfile CenteredMomentExceptionalReflection
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFiniteProfileExceptional CenteredMomentRankinRadical
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance geometryExceptionalSplitDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  Classical.decEq _

/-- The fixed-inducing filter does not choose one of the two ray characters
in the physical pair. Both changes of ray and the reflected row are exact. -/
theorem geometry_fixed_inducing_ray_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)}) (m A z : O)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m A z ↔
      FixedInducingRow (childCharacter η ξ) Q m A z := by
  constructor <;> intro h
  · have hh := fixedInducingRow_reflected η χ χ Q hQ m A z hml hm2 h
    simpa only [neg_neg] using
      fixedInducingRow_reflected η χ ξ Q hQ m A (-z) hml hm2 hh
  · have hh := fixedInducingRow_reflected η ξ ξ Q hQ m A z hml hm2 h
    simpa only [neg_neg] using
      fixedInducingRow_reflected η ξ χ Q hQ m A (-z) hml hm2 hh

theorem geometry_partRows_ray_eq (exceptional : Bool) (η : Character)
    (χ ξ : RayCharacter) (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (m : O) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) :
    partRows exceptional η χ Q m C D U R =
      partRows exceptional η ξ Q m C D U R := by
  cases exceptional
  · rw [partRows_false,partRows_false]
    ext z
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => not_congr
      (geometry_fixed_inducing_ray_iff η χ ξ Q hQ m _ z hml hm2)
  · ext z
    simp only [partRows,ite_true,Finset.mem_filter]
    exact and_congr_right fun _ =>
      geometry_fixed_inducing_ray_iff η χ ξ Q hQ m _ z hml hm2

theorem geometry_nonexceptional_pair (η : Character) (χ₀ χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (m : O) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (z : O)
    (hz : z∈partRows false η χ₀ Q m C D U R) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ∧
      nonexceptional η (ξ⁻¹) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) (-z) := by
  rw [partRows_false] at hz
  obtain ⟨hs,hn⟩ := Finset.mem_filter.mp hz
  have hz0 := sourceRows_nonzero C D U R z hs
  refine ⟨⟨hz0,?_⟩,⟨neg_ne_zero.mpr hz0,?_⟩⟩
  · exact fun h => hn ((geometry_fixed_inducing_ray_iff η χ₀ χ Q hQ m _ z hml hm2).mpr h)
  · exact (not_fixedInducingRow_reflection_iff η χ₀ (ξ⁻¹) Q hQ m _ z hml hm2).mp hn

theorem geometry_exceptional_reduced_pair (η : Character) (χ₀ χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter→Character)
    (hf : Family η C D hC hD U τ) (R : ℝ) (z : O)
    (hz : z∈partRows true η χ₀ Q m C D U R) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (CenteredMomentReflectedSource.reflected (τ (ξ⁻¹)))
        Q fixedBadMask 1 z := by
  have hnonzero := exceptional_part_nonzero η χ₀ Q m C D U R z hz
  have hex := exceptional_part_inducing η χ₀ Q m C D U R z hz
  have hexχ := (geometry_fixed_inducing_ray_iff η χ₀ χ Q hQ m _ z hml hm2).mp hex
  exact hf.both_inducing χ (ξ⁻¹) Q hQ m z hm hnonzero hml hm2 hexχ

theorem geometry_nonexceptional_reduced_pair (η : Character) (χ₀ χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter→Character)
    (hf : Family η C D hC hD U τ) (R : ℝ) (z : O)
    (hz : z∈partRows false η χ₀ Q m C D U R) :
    (z≠0 ∧ ¬FixedInducingRow (τ χ) Q fixedBadMask 1 z) ∧
      ((-z)≠0 ∧ ¬FixedInducingRow (τ (ξ⁻¹)) Q fixedBadMask 1 (-z)) := by
  have hp := geometry_nonexceptional_pair η χ₀ χ ξ Q hQ m hml hm2 C D U R z hz
  exact ⟨(hf.nonexceptional_iff χ Q m z hm hml hm2).mp hp.1,
    (hf.nonexceptional_iff (ξ⁻¹) Q m (-z) hm hml hm2).mp hp.2⟩

theorem geometry_sourceRows_union (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (m : O) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) (R : ℝ) :
    sourceRows C D U R = partRows true η χ Q m C D U R ∪
      partRows false η χ Q m C D U R := by
  rw [partRows_false]
  ext z
  simp only [partRows,ite_true,Finset.mem_union,Finset.mem_filter]
  tauto

theorem geometry_sourceRows_disjoint (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (m : O) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) (R : ℝ) :
    Disjoint (partRows true η χ Q m C D U R)
      (partRows false η χ Q m C D U R) := by
  rw [partRows_false]
  apply Finset.disjoint_left.mpr
  intro z ht hf
  exact (Finset.mem_filter.mp hf).2 (Finset.mem_filter.mp ht).2

/-- This split is linear before taking norms, so any moving scalar remains
inside its own physical block. -/
theorem geometry_physical_block_split (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (m : O) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (W : 𝓢(ℝ,ℂ))
    (K : ℝ) (n : Fin 4→ℤ) :
    physicalBlock η t S β C D hC hD U R (sourceRows C D U R) W K n =
      physicalBlock η t S β C D hC hD U R (partRows true η χ Q m C D U R) W K n +
      physicalBlock η t S β C D hC hD U R (partRows false η χ Q m C D U R) W K n := by
  rw [partRows_false]
  exact physicalBlock_filter_split η t S β C D hC hD U R _ W K n _

theorem geometry_source_row_energy_split (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (m : O) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) (R : ℝ) (f : O→ℝ) :
    (∑z∈sourceRows C D U R,f z) =
      (∑z∈partRows true η χ Q m C D U R,f z) +
      (∑z∈partRows false η χ Q m C D U R,f z) := by
  rw [geometry_sourceRows_union η χ Q m C D U R]
  exact Finset.sum_union (geometry_sourceRows_disjoint η χ Q m C D U R)

theorem geometry_joint_source_row_energy_split {Label : Type*} [Fintype Label]
    (η : Label→Character) (χ : Label→RayCharacter) (Q : Ideal O) (m : O)
    (C D : Label→Ideal O) (U : (j : Label)→Finset (CommonIndex (C j) (D j)))
    (R scalar : Label→ℝ) (f : Label→O→ℝ) :
    (∑j,scalar j*(∑z∈sourceRows (C j) (D j) (U j) (R j),f j z)) =
      (∑j,scalar j*(∑z∈partRows true (η j) (χ j) Q m (C j) (D j) (U j) (R j),f j z)) +
      (∑j,scalar j*(∑z∈partRows false (η j) (χ j) Q m (C j) (D j) (U j) (R j),f j z)) := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [geometry_source_row_energy_split (η j) (χ j) Q m (C j) (D j) (U j) (R j) (f j),mul_add]

def geometryExceptionalBlockExponent {ι : Type*} [Fintype ι]
    (s : CenteredMomentCommonRadialData.Input ι) (Z ε δ θ : ℝ)
    (C D : Ideal O) (Kphys r : ℝ) : ℝ :=
  2*ε+δ+θ*(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))+
    Real.logb Z (volume s.toData)/3+5*Real.logb Z Kphys/6-
    (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3-
    Real.logb Z (Ideal.absNorm (commonRadical C D):ℝ)-
    max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0

/-- Only the fixed-inducing branch is bounded separately. The ordinary
branch keeps the full joint physical norm needed for simultaneous selection. -/
theorem geometry_joint_physical_exceptional_split {Label : Type*} [Fintype Label]
    (η : Label→Character) (χ : Label→RayCharacter) (Q : Ideal O) (m : O)
    (t : Label→ℝ) (S : Label→Finset (Ideal O)) (β : Label→Ideal O→ℂ)
    (C D : Label→Ideal O) (hC : ∀j,Supported (C j)) (hD : ∀j,Supported (D j))
    (U : (j : Label)→Finset (CommonIndex (C j) (D j)))
    (R : Label→ℝ) (W : 𝓢(ℝ,ℂ)) (K : Label→ℝ) (n : Label→Fin 4→ℤ)
    (scalar : Label→ℂ) :
    ‖∑j,scalar j*physicalBlock (η j) (t j) (S j) (β j) (C j) (D j)
      (hC j) (hD j) (U j) (R j) (sourceRows (C j) (D j) (U j) (R j)) W (K j) (n j)‖ ≤
      (∑j,‖scalar j*physicalBlock (η j) (t j) (S j) (β j) (C j) (D j)
        (hC j) (hD j) (U j) (R j)
        (partRows true (η j) (χ j) Q m (C j) (D j) (U j) (R j)) W (K j) (n j)‖) +
      ‖∑j,scalar j*physicalBlock (η j) (t j) (S j) (β j) (C j) (D j)
        (hC j) (hD j) (U j) (R j)
        (partRows false (η j) (χ j) Q m (C j) (D j) (U j) (R j)) W (K j) (n j)‖ := by
  let exceptional := fun j=>scalar j*physicalBlock (η j) (t j) (S j) (β j) (C j) (D j)
    (hC j) (hD j) (U j) (R j)
    (partRows true (η j) (χ j) Q m (C j) (D j) (U j) (R j)) W (K j) (n j)
  let ordinary := fun j=>scalar j*physicalBlock (η j) (t j) (S j) (β j) (C j) (D j)
    (hC j) (hD j) (U j) (R j)
    (partRows false (η j) (χ j) Q m (C j) (D j) (U j) (R j)) W (K j) (n j)
  have he : (∑j,scalar j*physicalBlock (η j) (t j) (S j) (β j) (C j) (D j)
      (hC j) (hD j) (U j) (R j) (sourceRows (C j) (D j) (U j) (R j)) W (K j) (n j)) =
      (∑j,exceptional j)+(∑j,ordinary j) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [geometry_physical_block_split (η j) (χ j) Q m (t j) (S j) (β j)
      (C j) (D j) (hC j) (hD j) (U j) (R j) W (K j) (n j),mul_add]
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (le_refl _))

attribute [local irreducible] physicalBlock
set_option maxHeartbeats 600000 in
/-- Fixed-inducing physical blocks use the saved exceptional estimate.
The moving scalar is retained term by term in the joint finite sum. -/
theorem geometry_actual_exceptional_block_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi) (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ))
    (ε δ θ B Lbound : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (hB : 0≤B) (hL : 0≤Lbound) :
    ∃J : ℕ, ∃Sp : Finset (ℕ×ℕ), (0,0)∈Sp ∧ ∃Ck : ℝ, 0≤Ck ∧
    ∀Q : Ideal O, Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
    ∃K : ℝ, 0<K ∧ ∀ᶠZ : ℝ in atTop, 1<Z ∧
    ∀{Label : Type*} [Fintype Label] [DecidableEq Label],
    ∀(src : Label→CenteredMomentCommonRadialData.Input ι) (p : Profiles wlo whi),
    (∀j i,(src j).lo i=lo i) → (∀j i,(src j).hi i=hi i) →
    (∀j i,1≤(src j).P i) → (∀j,(src j).W₁=p.profile 0) → (∀j,(src j).W₂=p.profile 1) →
    ∀(C D : Label→Ideal O) (hC : ∀j,Supported (C j)) (hD : ∀j,Supported (D j))
      (R0 seed : Label→Ideal O),
    (∀j,R0 j≠0) → (∀j,seed j∣C j) → (∀j,seed j∣D j) →
    (∀j,((C j).absNorm:ℝ)≤Z^B) → (∀j,((D j).absNorm:ℝ)≤Z^B) →
    (∀j,primeSupport (C j)=primeSupport (D j)) →
    ∀(U : (j : Label)→Finset (CommonIndex (C j) (D j))) (r : Label→ℝ),
    (∀j,Z^(r j)≤(src j).X₁) → (∀j,Z^(r j)≤(src j).X₂) →
    (∀j,Z^(r j)≤(src j).Y₁) → (∀j,Z^(r j)≤(src j).Y₂) →
    ∀χ₀ : Label→RayCharacter, (∀j,idealCoeff (src j).η (C j)≠0) →
    ∀m : O, m≠0 → goodLambda∣m → (2:O)∣m →
    (∀j,CenteredMomentOriginalCommonHarmonic.sourceRadius (src j)≤Z^Lbound) →
    ∀(R Kphys : Label→ℝ), (∀j,0<Kphys j) →
    (∀j,(CenteredMomentSecondExceptionalFamily.expandedFactor (src j).η:ℝ)*
      (R0 j).absNorm*(C j).absNorm*(D j).absNorm*(4*R j)≤Z^B) →
    ∀(n : Label→Fin 4→ℤ) (scalar : Label→ℝ), (∀j,0≤scalar j) →
    (∑j,scalar j*(‖physicalBlock (src j).η (src j).t
      (finiteColumns (Fintype.piFinset (src j).pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient (src j) (R0 j) (seed j))
      (C j) (D j) (hC j) (hD j) (U j) (R j)
      (partRows true (src j).η (χ₀ j) Q m (C j) (D j) (U j) (R j)) W (Kphys j) (n j)‖/
      volume (src j).toData)) ≤
    Ck*∑j,scalar j*(CenteredMomentFiniteProfileExceptionalPhysical.profileFactor Sp (src j) p J Q K*
      ((∏i,(src j).lo i)*wlo*wlo)^(-2/3:ℝ)*
      Z^(geometryExceptionalBlockExponent (src j) Z ε δ θ (C j) (D j) (Kphys j) (r j))) := by
  obtain ⟨J,Sp,hSp,Ck,hCk,hbound⟩ := Cycle63FixedInducingChosen.chosen_exceptional_log_block
    wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sp,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ _ src p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hNC hND hCD
    U r hX1 hX2 hY1 hY2 χ₀ hη m hm hml hm2 hsource R Kphys hKphys hcond n scalar hscalar
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hb := hz.2 (src j) p (hlo j) (hhi j) (hP j) (hW1 j) (hW2 j)
    (C j) (D j) (hC j) (hD j) (R0 j) (seed j) (hR0 j) (hsC j) (hsD j)
    (hNC j) (hND j) (hCD j) (U j) (r j) (hX1 j) (hX2 j) (hY1 j) (hY2 j)
    (χ₀ j) (hη j) m hm hml hm2 (hsource j) (R j) (Kphys j) (hKphys j) (hcond j) (n j)
  let f := CenteredMomentFiniteProfileExceptionalPhysical.profileFactor Sp (src j) p J Q K
  let a := ((∏i,(src j).lo i)*wlo*wlo)^(-2/3:ℝ)
  let power := Z^(geometryExceptionalBlockExponent (src j) Z ε δ θ (C j) (D j) (Kphys j) (r j))
  have hreassoc : Ck*f*a*power=Ck*(f*a*power) := by
    rw [mul_assoc Ck f a,mul_assoc Ck (f*a) power]
  have hb' := hb.trans_eq hreassoc
  exact (mul_le_mul_of_nonneg_left hb' (hscalar j)).trans_eq
    (mul_left_comm (scalar j) Ck (f*a*power))

end
end OAI.SevenEighths.Cycle63InitialMass

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_fixed_inducing_ray_iff
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_partRows_ray_eq
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_nonexceptional_pair
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_exceptional_reduced_pair
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_nonexceptional_reduced_pair
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_sourceRows_union
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_sourceRows_disjoint
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_physical_block_split
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_source_row_energy_split
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_source_row_energy_split
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_joint_physical_exceptional_split
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_actual_exceptional_block_family
