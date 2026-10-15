/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B135
import Submissions.gao_cycle61_plane_20261013.Bundles.B136
import Submissions.gao_cycle61_plane_20261013.Bundles.B148
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalSplit; sha256 955a40ce88d9525633cec995d7e907417b99c4efe43dcd6a5663490c368573a5 -/
section
                                           
                                                            

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OAI.SevenEighths.Cycle61InitialMass
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
    (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)}) (m A z : O)
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
    (χ ξ : RayCharacter) (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)})
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
    (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)})
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
    (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter→ Character)
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
    (Q : Ideal O) (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter→ Character)
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
    (η : Label→ Character) (χ : Label→ RayCharacter) (Q : Ideal O) (m : O)
    (C D : Label→ Ideal O) (U : (j : Label)→ Finset (CommonIndex (C j) (D j)))
    (R scalar : Label→ℝ) (f : Label→ O→ℝ) :
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
    (η : Label→ Character) (χ : Label→ RayCharacter) (Q : Ideal O) (m : O)
    (t : Label→ℝ) (S : Label→ Finset (Ideal O)) (β : Label→ Ideal O→ℂ)
    (C D : Label→ Ideal O) (hC : ∀j,Supported (C j)) (hD : ∀j,Supported (D j))
    (U : (j : Label)→ Finset (CommonIndex (C j) (D j)))
    (R : Label→ℝ) (W : 𝓢(ℝ,ℂ)) (K : Label→ℝ) (n : Label→ Fin 4→ℤ)
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
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi) (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ))
    (ε δ θ B Lbound : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (hB : 0≤ B) (hL : 0≤ Lbound) :
    ∃J : ℕ, ∃Sp : Finset (ℕ×ℕ), (0,0)∈Sp ∧ ∃Ck : ℝ, 0≤ Ck ∧
    ∀Q : Ideal O, Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
    ∃K : ℝ, 0< K ∧ ∀ᶠZ : ℝ in atTop, 1< Z ∧
    ∀{Label : Type*} [Fintype Label] [DecidableEq Label],
    ∀(src : Label→ CenteredMomentCommonRadialData.Input ι) (p : Profiles wlo whi),
    (∀j i,(src j).lo i=lo i) → (∀j i,(src j).hi i=hi i) →
    (∀j i,1≤(src j).P i) → (∀j,(src j).W₁=p.profile 0) → (∀j,(src j).W₂=p.profile 1) →
    ∀(C D : Label→ Ideal O) (hC : ∀j,Supported (C j)) (hD : ∀j,Supported (D j))
      (R0 seed : Label→ Ideal O),
    (∀j,R0 j≠0) → (∀j,seed j∣C j) → (∀j,seed j∣D j) →
    (∀j,((C j).absNorm:ℝ)≤ Z^B) → (∀j,((D j).absNorm:ℝ)≤ Z^B) →
    (∀j,primeSupport (C j)=primeSupport (D j)) →
    ∀(U : (j : Label)→ Finset (CommonIndex (C j) (D j))) (r : Label→ℝ),
    (∀j,Z^(r j)≤(src j).X₁) → (∀j,Z^(r j)≤(src j).X₂) →
    (∀j,Z^(r j)≤(src j).Y₁) → (∀j,Z^(r j)≤(src j).Y₂) →
    ∀χ₀ : Label→ RayCharacter, (∀j,idealCoeff (src j).η (C j)≠0) →
    ∀m : O, m≠0 → goodLambda∣m → (2:O)∣m →
    (∀j,CenteredMomentOriginalCommonHarmonic.sourceRadius (src j)≤ Z^Lbound) →
    ∀(R Kphys : Label→ℝ), (∀j,0< Kphys j) →
    (∀j,(CenteredMomentSecondExceptionalFamily.expandedFactor (src j).η:ℝ)*
      (R0 j).absNorm*(C j).absNorm*(D j).absNorm*(4*R j)≤ Z^B) →
    ∀(n : Label→ Fin 4→ℤ) (scalar : Label→ℝ), (∀j,0≤ scalar j) →
    (∑j,scalar j*(‖physicalBlock (src j).η (src j).t
      (finiteColumns (Fintype.piFinset (src j).pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient (src j) (R0 j) (seed j))
      (C j) (D j) (hC j) (hD j) (U j) (R j)
      (partRows true (src j).η (χ₀ j) Q m (C j) (D j) (U j) (R j)) W (Kphys j) (n j)‖/
      volume (src j).toData)) ≤
    Ck*∑j,scalar j*(CenteredMomentFiniteProfileExceptionalPhysical.profileFactor Sp (src j) p J Q K*
      ((∏i,(src j).lo i)*wlo*wlo)^(-2/3:ℝ)*
      Z^(geometryExceptionalBlockExponent (src j) Z ε δ θ (C j) (D j) (Kphys j) (r j))) := by
  obtain ⟨J,Sp,hSp,Ck,hCk,hbound⟩ := Cycle61FixedInducingChosen.chosen_exceptional_log_block
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
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_fixed_inducing_ray_iff
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_partRows_ray_eq
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_nonexceptional_pair
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_exceptional_reduced_pair
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_nonexceptional_reduced_pair
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_sourceRows_union
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_sourceRows_disjoint
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_physical_block_split
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_source_row_energy_split
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_source_row_energy_split
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_joint_physical_exceptional_split
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_actual_exceptional_block_family

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalSplit -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySelectedSources; sha256 0d95cb798a981b40a52de268ce0aeba7bfb162b0bb42be9632db302609adcda4 -/
section
                                                          
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

/-- Reduce the actual weighted main source sum to supported common
allocations with unique arithmetic-label/projector keys. First dyads and
ray characters incur only the proved small-power cost. -/
theorem actual_geometry_selected_main_budget {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b ε Amax Dmax B ξ : ℝ)
    (hCs : 1≤ Cs)(hε : 0<ε)(hA : 0≤ Amax)(hD : 0≤ Dmax)(hB : 0≤ B)(hξ : 0≤ξ) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠZ : ℝ in atTop,1≤ Z ∧
      ∀(s : Input ι),Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K M A sigma reserve t : ℝ)
        (hK : 0< K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^Amax → K⁻¹≤ Z^Dmax →
      ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (G E : ℝ),0≤ G →
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let χ := fun j : rows=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
      let g := fun j : rows=>geometryBranch reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      (∀j,C j≠0) →
      (∀j,‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)≤ G) →
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→ actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,actualMainSource (child s (C (column j)) R (alloc j) (χ (column j)) t)
          (g (column j)) Z sigma 1 ξ reserve)≤ E) →
      (∑j : rows,∑alloc : actualAllocations s.pools (C j),
        w j alloc*actualMainSource (child s (C j) R alloc (χ j) t) (g j) Z sigma 1 ξ reserve)≤
          (K₀*G*Z^ε)*E := by
  obtain ⟨D,hDmass,hmass⟩ := actual_geometry_main_selection N Cs b ε hCs hε
  obtain ⟨F,hF,hcolumns⟩ := actual_first_selected_column_budget_indexed (ι:=ι)
    Amax Dmax B ξ ε hA hD hB hξ hε
  refine ⟨D*F,mul_pos hDmass hF,?_⟩
  filter_upwards [hcolumns] with Z hz
  refine ⟨hz.1,?_⟩
  intro s hn hM reflected R seed K M A sigma reserve t hK key weight hseed hz₁ hz₂
    hsource hsourcecap hV hKi rows G E hG C χ g w hC hscalar hselected
  have hZ : 0< Z := zero_lt_one.trans_le hz.1
  have hh := hmass s hn hM reflected R seed K Z ξ M A sigma reserve t hK hZ key weight
    rows G ((F*Z^ε)*E) hG hC hscalar (by
      intro S alloc halloc
      apply hz.2 s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi
        (fun j : rows=>j.val) Subtype.val_injective S
        (fun j=>actualMainSource (child s (C j.val) R (alloc j) (χ j.val) t)
          (g j.val) Z sigma 1 ξ reserve) E
        (fun j=>actual_geometry_main_nonneg reflected s R seed K Z ξ sigma reserve hK hZ
          key j.val.val (alloc j) t)
      intro chosen hchosen
      have hinj : Function.Injective (fun j=>
          (geometryFirstLabel s R seed K Z ξ hK key (chosen j).val.val,
            (chosen j).val.val.2.1.val)) := by
        intro j k he
        apply Subtype.ext
        exact (hchosen j).symm.trans (he.trans (hchosen k))
      exact hselected (fun j=>(chosen j).val) hinj
        (fun j=>alloc (chosen j)) (fun j=>halloc (chosen j)))
  apply hh.trans_eq
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_main_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySelectedSources -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryWeightedSelection; sha256 75d94e5c2a11c2590e10cdae31b97ff7a960862daae0d94d745649c629535815 -/
section
                                                           

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

/-- Variable label mass stays inside the selected sum, including labels
whose mass vanishes. No maximum over the varying masses is introduced. -/
theorem joint_variable_mass_selection {Label : Type*} [Fintype Label]
    {β : Label→ Type*} [∀l,Fintype (β l)] (weight cost : (l : Label)→β l→ℝ)
    (mass : Label→ℝ) (W E : ℝ) (hW : 0≤ W)
    (hw : ∀l a,0≤ weight l a) (hc : ∀l a,0≤ cost l a)
    (hm : ∀l,0≤ mass l) (hmass : ∀l,∑a,weight l a≤ W*mass l)
    (hjoint : ∀S : Finset Label,∀pick : (l : S)→β l.val,
      (∀l,weight l.val (pick l)≠0) →
      (∑l : S,mass l.val*cost l.val (pick l))≤ E) :
    (∑l,∑a,weight l a*cost l a)≤ W*E := by
  have hzero (l : Label)(h : mass l=0)(a : β l) : weight l a=0 := by
    have ht := (Finset.single_le_sum (fun a _=>hw l a) (Finset.mem_univ a)).trans (hmass l)
    rw [h,mul_zero] at ht
    exact le_antisymm ht (hw l a)
  have hh := joint_supported_weighted_selection
    (fun l a=>weight l a/mass l) (fun l a=>mass l*cost l a) W E hW
    (fun l a=>div_nonneg (hw l a) (hm l)) (fun l a=>mul_nonneg (hm l) (hc l a))
    (by
      intro l
      by_cases hz : mass l=0
      · simp only [hz,div_zero,Finset.sum_const_zero]; exact hW
      · rw [←Finset.sum_div]
        exact (div_le_iff₀ (lt_of_le_of_ne (hm l) (Ne.symm hz))).mpr (hmass l))
    (by
      intro S pick hne
      exact hjoint S pick (fun l hw0=>hne l (by simp [hw0])))
  have heq (l : Label)(a : β l) :
      weight l a/mass l*(mass l*cost l a)=weight l a*cost l a := by
    by_cases hz : mass l=0
    · simp [hz,hzero l hz a]
    · field_simp
  simpa only [heq] using hh

/-- Supported first common allocations are selected while their literal
column scalar and inverse-ideal mass remain inside the joint source sum. -/
theorem actual_geometry_weighted_main_selection (N : ℕ)(Cs b ε : ℝ)
    (hCs : 1≤ Cs)(hε : 0<ε) :
    ∃D : ℝ,0< D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A sigma reserve t : ℝ)
        (hK : 0< K)(hZ : 0< Z)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
        (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (E : ℝ),
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let χ := fun j : rows=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
      let g := fun j : rows=>geometryBranch reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      (∀j,C j≠0) →
      (∀S : Finset rows,∀pick : (j : S)→ actualAllocations s.pools (C j.val),
        (∀j,frozenCoefficient (pick j).val (C j.val) R s.ν s.W s.P≠0) →
        (∑j : S,mass j.val*actualMainSource (child s (C j.val) R (pick j) (χ j.val) t)
          (g j.val) Z sigma 1 ξ reserve)≤ E) →
      (∑j : rows,∑B : actualAllocations s.pools (C j),
        w j B*actualMainSource (child s (C j) R B (χ j) t) (g j) Z sigma 1 ξ reserve)≤ D*E := by
  obtain ⟨D,hD,hmass⟩ := actual_geometry_allocation_mass N Cs b ε hCs hε
  refine ⟨D,hD,?_⟩
  intro ι _ _ s hn hM reflected R seed K Z ξ M A sigma reserve t hK hZ key weight rows E
    C χ g w mass hC hjoint
  apply joint_variable_mass_selection w
    (fun j B=>actualMainSource (child s (C j) R B (χ j) t) (g j) Z sigma 1 ξ reserve)
    mass D E hD.le
    (fun j B=>geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b j.val B)
    (fun j B=>actual_geometry_main_nonneg reflected s R seed K Z ξ sigma reserve hK hZ key j.val B t)
    (fun j=>mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · intro j
    simpa only [mass,mul_assoc] using hmass s hn hM reflected R seed K Z ξ M A hK key weight j.val (hC j)
  · intro S pick hne
    apply hjoint S pick
    intro j hf
    apply hne j
    simp only [w,geometryAllocationWeight]
    dsimp only [C] at hf
    simp only [hf,ne_eq,not_true_eq_false,ite_false]

/-- Select actual arithmetic-label/projector representatives while retaining
the varying normalized column mass inside the joint sum. -/
theorem actual_geometry_weighted_selected_main_budget {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b ε Amax Dmax B ξ : ℝ)
    (hCs : 1≤ Cs)(hε : 0<ε)(hA : 0≤ Amax)(hD : 0≤ Dmax)(hB : 0≤ B)(hξ : 0≤ξ) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠZ : ℝ in atTop,1≤ Z ∧
      ∀(s : Input ι),Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K M A sigma reserve t : ℝ)
        (hK : 0< K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^Amax → K⁻¹≤ Z^Dmax →
      ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (E : ℝ),
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let χ := fun j : rows=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
      let g := fun j : rows=>geometryBranch reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      (∀j,C j≠0) →
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→ actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*actualMainSource (child s (C (column j)) R (alloc j) (χ (column j)) t)
          (g (column j)) Z sigma 1 ξ reserve)≤ E) →
      (∑j : rows,∑alloc : actualAllocations s.pools (C j),
        w j alloc*actualMainSource (child s (C j) R alloc (χ j) t) (g j) Z sigma 1 ξ reserve)≤
          (K₀*Z^ε)*E := by
  obtain ⟨D,hDmass,hmass⟩ := actual_geometry_weighted_main_selection N Cs b ε hCs hε
  obtain ⟨F,hF,hcolumns⟩ := actual_first_selected_column_budget_indexed (ι:=ι)
    Amax Dmax B ξ ε hA hD hB hξ hε
  refine ⟨D*F,mul_pos hDmass hF,?_⟩
  filter_upwards [hcolumns] with Z hz
  refine ⟨hz.1,?_⟩
  intro s hn hM reflected R seed K M A sigma reserve t hK key weight hseed hz₁ hz₂
    hsource hsourcecap hV hKi rows E C χ g w mass hC hselected
  have hZ : 0< Z := zero_lt_one.trans_le hz.1
  have hh := hmass s hn hM reflected R seed K Z ξ M A sigma reserve t hK hZ key weight
    rows ((F*Z^ε)*E) hC (by
      intro S alloc halloc
      apply hz.2 s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi
        (fun j : rows=>j.val) Subtype.val_injective S
        (fun j=>mass j.val*actualMainSource (child s (C j.val) R (alloc j) (χ j.val) t)
          (g j.val) Z sigma 1 ξ reserve) E
        (fun j=>mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (actual_geometry_main_nonneg reflected s R seed K Z ξ sigma reserve hK hZ
            key j.val.val (alloc j) t))
      intro chosen hchosen
      have hinj : Function.Injective (fun j=>
          (geometryFirstLabel s R seed K Z ξ hK key (chosen j).val.val,
            (chosen j).val.val.2.1.val)) := by
        intro j k he
        apply Subtype.ext
        exact (hchosen j).symm.trans (he.trans (hchosen k))
      exact hselected (fun j=>(chosen j).val) hinj
        (fun j=>alloc (chosen j)) (fun j=>halloc (chosen j)))
  apply hh.trans_eq
  ring


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.joint_variable_mass_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_weighted_main_selection

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_weighted_selected_main_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryWeightedSelection -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryCostSelection; sha256 822333097da210d23c8467173df59e4bd0ee98c5071508381491ae2c710d761a -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentPrimeElements
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentGaussNormalization CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius RayFourExpansion
local notation "O" => HeckeFamily.O
local instance geometryCostSelectionDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- Every literal extracted branch is nonnegative before any source split. -/
theorem actual_error_sources_nonneg {ι : Type*} [Fintype ι]
    (s : Input ι) (g : FirstBranchGeometry) (Z sigma Csec ξ reserve : ℝ)
    (hZ : 0< Z) (P : Finset (Ideal O))
    (τ : elementPool P→ Fin 3→ RayCharacter→ Character) :
    0≤ actualErrorSources s g Z sigma Csec ξ reserve P τ := by
  unfold actualErrorSources
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact mul_nonneg (by positivity) (localErrorCost_nonneg p (errorIndex i))
  · apply Finset.sum_nonneg
    intro χ _
    apply Finset.sum_nonneg
    intro B _
    unfold childNormalizedGaussSource normalizedGaussSource
    exact div_nonneg (sourceGaussEnergy_nonneg _ _ _ _ _
      (Real.rpow_pos_of_pos hZ _) (fun _=>ballProfile_nonneg _)) (volume_pos _).le

/-- First common-allocation mass is paid with its literal column scalar.
The cost can be the complete extracted source, with all prime/ray sums
still inside it. Only allocations with nonzero frozen coefficient are selected. -/
theorem actual_geometry_weighted_cost_selection (N : ℕ)(Cs b ε : ℝ)
    (hCs : 1≤ Cs)(hε : 0<ε) :
    ∃D : ℝ,0< D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A : ℝ)
        (hK : 0< K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
        (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (E : ℝ),
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      ∀cost : (j : rows)→ actualAllocations s.pools (C j)→ℝ,
      (∀j B,0≤ cost j B) → (∀j,C j≠0) →
      (∀S : Finset rows,∀pick : (j : S)→ actualAllocations s.pools (C j.val),
        (∀j,frozenCoefficient (pick j).val (C j.val) R s.ν s.W s.P≠0) →
        (∑j : S,mass j.val*cost j.val (pick j))≤ E) →
      (∑j : rows,∑B : actualAllocations s.pools (C j),w j B*cost j B)≤ D*E := by
  obtain ⟨D,hD,hmass⟩ := actual_geometry_allocation_mass N Cs b ε hCs hε
  refine ⟨D,hD,?_⟩
  intro ι _ _ s hn hM reflected R seed K Z ξ M A hK key weight rows E C w mass cost hc hC hjoint
  apply joint_variable_mass_selection w cost mass D E hD.le
    (fun j B=>geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b j.val B)
    hc (fun j=>mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · intro j
    simpa only [mass,mul_assoc] using hmass s hn hM reflected R seed K Z ξ M A hK key weight j.val (hC j)
  · intro S pick hne
    apply hjoint S pick
    intro j hf
    apply hne j
    simp only [w,geometryAllocationWeight]
    dsimp only [C] at hf
    simp only [hf,ne_eq,not_true_eq_false,ite_false]

/-- Full first-label selection for a nonnegative actual allocation cost.
Only the proved dyadic/ray multiplicity is paid; ideal labels and residual
projectors remain injectively indexed inside the selected joint sum. -/
theorem actual_geometry_weighted_selected_cost {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b ε Amax Dmax B ξ : ℝ)
    (hCs : 1≤ Cs)(hε : 0<ε)(hA : 0≤ Amax)(hD : 0≤ Dmax)(hB : 0≤ B)(hξ : 0≤ξ) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠZ : ℝ in atTop,1≤ Z ∧
      ∀(s : Input ι),Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K M A : ℝ)
        (hK : 0< K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^Amax → K⁻¹≤ Z^Dmax →
      ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))) (E : ℝ),
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      ∀cost : (j : rows)→ actualAllocations s.pools (C j)→ℝ,
      (∀j B,0≤ cost j B) → (∀j,C j≠0) →
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→ actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*cost (column j) (alloc j))≤ E) →
      (∑j : rows,∑alloc : actualAllocations s.pools (C j),w j alloc*cost j alloc)≤
        (K₀*Z^ε)*E := by
  obtain ⟨D,hDmass,hmass⟩ := actual_geometry_weighted_cost_selection N Cs b ε hCs hε
  obtain ⟨F,hF,hcolumns⟩ := actual_first_selected_column_budget_indexed (ι:=ι)
    Amax Dmax B ξ ε hA hD hB hξ hε
  refine ⟨D*F,mul_pos hDmass hF,?_⟩
  filter_upwards [hcolumns] with Z hz
  refine ⟨hz.1,?_⟩
  intro s hn hM reflected R seed K M A hK key weight hseed hz₁ hz₂ hsource hsourcecap hV hKi
    rows E C w mass cost hc hC hselected
  have hh := hmass s hn hM reflected R seed K Z ξ M A hK key weight
    rows ((F*Z^ε)*E) cost hc hC (by
      intro S alloc halloc
      apply hz.2 s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi
        (fun j : rows=>j.val) Subtype.val_injective S
        (fun j=>mass j.val*cost j.val (alloc j)) E
        (fun j=>mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (hc j.val (alloc j)))
      intro chosen hchosen
      have hinj : Function.Injective (fun j=>
          (geometryFirstLabel s R seed K Z ξ hK key (chosen j).val.val,
            (chosen j).val.val.2.1.val)) := by
        intro j k he
        apply Subtype.ext
        exact (hchosen j).symm.trans (he.trans (hchosen k))
      exact hselected (fun j=>(chosen j).val) hinj
        (fun j=>alloc (chosen j)) (fun j=>halloc (chosen j)))
  apply hh.trans_eq
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_sources_nonneg
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_weighted_cost_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_weighted_selected_cost

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryCostSelection -/
