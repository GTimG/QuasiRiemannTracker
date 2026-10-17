import Candidate.Cycle63.Physical.InitialMass.GeometrySecondSplit
import Candidate.Cycle63.Moment.JointAllocationEnergy

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentAllocationCost
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussNormalization
open CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

/-- The actual amplification weights pay a small power of the common
ideal and its inverse norm. The two allocation cardinalities are included. -/
theorem actual_geometry_allocation_mass (N : ℕ) (Cs b ε : ℝ) (hCs : 1≤Cs) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤N → (∀i,s.M i≤Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A : ℝ)(hK : 0<K)
        (key : ℤ×(Fin 5→ℤ))
        (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
        (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)),
      geometryColumnIdeal reflected s R seed K Z ξ hK key j≠0 →
      (∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j),
        geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B)≤
      D*‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*
        ((geometryColumnIdeal reflected s R seed K Z ξ hK key j).absNorm:ℝ)^(ε-1) := by
  obtain ⟨D,hD,hcard⟩ := actualAllocations_uniform_small_power (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2*(max 1 b)^N*(Cs^N)^2,by positivity,?_⟩
  intro ι _ _ s hn hM reflected R seed K Z ξ M A hK key weight j hC
  let C := geometryColumnIdeal reflected s R seed K Z ξ hK key j
  let scalar := geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j
  have hnorm : 0<(C.absNorm:ℝ) := CenteredMomentFirstScale.norm_pos _ hC
  have hc := hcard (ι:=ι⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin];omega) s.pools C hC
  have hc₂ := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hc 2
  rw [mul_pow,←Real.rpow_mul_natCast hnorm.le,show ε/2*(2:ℕ)=ε by norm_num] at hc₂
  have hf (B : actualAllocations s.pools C) : (frozenControl B.val s.M)^2≤(Cs^N)^2 := by
    apply pow_le_pow_left₀ (frozenControl_nonneg B.val s.M (fun i=>zero_le_one.trans (s.M_ge_one i)))
    unfold frozenControl
    calc
      _≤∏_i∈Finset.univ.filter (fun i=>B.val (Sum.inl i)≠1),Cs :=
        Finset.prod_le_prod₀ (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _=>hM i)
      _=Cs^((Finset.univ.filter (fun i=>B.val (Sum.inl i)≠1)).card) := by simp
      _≤Cs^N := pow_le_pow_right₀ hCs ((Finset.card_le_univ _).trans hn)
  have hp (B : actualAllocations s.pools C) :
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B≤
        ‖scalar‖^2*((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/C.absNorm)*(Cs^N)^2 := by
    unfold geometryAllocationWeight
    dsimp only
    split_ifs
    · exact mul_le_mul_of_nonneg_left (hf B) (by positivity)
    · positivity
  calc
    _≤∑_B : actualAllocations s.pools C,
        ‖scalar‖^2*((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/C.absNorm)*(Cs^N)^2 :=
      Finset.sum_le_sum (fun B _=>hp B)
    _=((actualAllocations s.pools C).card:ℝ)^2*
        (‖scalar‖^2*(max 1 b)^N*(Cs^N)^2/C.absNorm) := by simp;ring
    _≤(D^2*(C.absNorm:ℝ)^ε)*(‖scalar‖^2*(max 1 b)^N*(Cs^N)^2/C.absNorm) :=
      mul_le_mul_of_nonneg_right hc₂ (by positivity)
    _=_ := by rw [Real.rpow_sub hnorm,Real.rpow_one];ring

/-- Positivity needed for supported allocation selection comes from the
literal Gaussian energy and the nonnegative ball profile. -/
theorem actual_geometry_main_nonneg {ι : Type*} [Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ sigma reserve : ℝ)
    (hK : 0<K)(hZ : 0<Z)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))
    (t : ℝ) :
    0≤actualMainSource
      (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j) R B
        (geometryColumnCharacter reflected s R seed K Z ξ hK key j) t)
      (geometryBranch reflected s R seed K Z ξ hK key j) Z sigma 1 ξ reserve := by
  rw [actual_geometry_main_source_radius]
  unfold normalizedGaussSource
  exact div_nonneg (sourceGaussEnergy_nonneg _ _ _ _ _
    (first_main_radius_pos reflected K (volume s) Z ξ sigma reserve hZ _)
    (fun _=>ballProfile_nonneg _)) (volume_pos _).le

/-- Select only supported first common allocations, retaining a joint sum
of main sources. The actual allocation weights are discharged by the
original slot controls, including both allocation multiplicities. -/
theorem actual_geometry_main_selection (N : ℕ)(Cs b ε : ℝ)(hCs : 1≤Cs)(hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤N → (∀i,s.M i≤Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A sigma reserve t : ℝ)
        (hK : 0<K)(hZ : 0<Z)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
        (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (G E : ℝ),0≤G →
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let χ := fun j : rows=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
      let g := fun j : rows=>geometryBranch reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      (∀j,C j≠0) →
      (∀j,‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)≤G) →
      (∀S : Finset rows,∀pick : (j : S)→actualAllocations s.pools (C j.val),
        (∀j,frozenCoefficient (pick j).val (C j.val) R s.ν s.W s.P≠0) →
        (∑j : S,actualMainSource (child s (C j.val) R (pick j) (χ j.val) t)
          (g j.val) Z sigma 1 ξ reserve)≤E) →
      (∑j : rows,∑B : actualAllocations s.pools (C j),
        w j B*actualMainSource (child s (C j) R B (χ j) t) (g j) Z sigma 1 ξ reserve)≤(D*G)*E := by
  obtain ⟨D,hD,hmass⟩ := actual_geometry_allocation_mass N Cs b ε hCs hε
  refine ⟨D,hD,?_⟩
  intro ι _ _ s hn hM reflected R seed K Z ξ M A sigma reserve t hK hZ key weight rows G E hG
    C χ g w hC hscalar hjoint
  apply joint_supported_weighted_selection w
    (fun j B=>actualMainSource (child s (C j) R B (χ j) t) (g j) Z sigma 1 ξ reserve)
    (D*G) E (mul_nonneg hD.le hG)
    (fun j B=>geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b j.val B)
    (fun j B=>actual_geometry_main_nonneg reflected s R seed K Z ξ sigma reserve hK hZ key j.val B t)
  · intro j
    apply (hmass s hn hM reflected R seed K Z ξ M A hK key weight j.val (hC j)).trans
    calc
      _=D*(‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)) := by ring
      _≤D*G := mul_le_mul_of_nonneg_left (hscalar j) hD.le
  · intro S pick hne
    apply hjoint S pick
    intro j hf
    apply hne j
    simp only [w,geometryAllocationWeight]
    dsimp only [C] at hf
    simp only [hf,ne_eq,not_true_eq_false,ite_false]

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_allocation_mass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_nonneg

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_selection
