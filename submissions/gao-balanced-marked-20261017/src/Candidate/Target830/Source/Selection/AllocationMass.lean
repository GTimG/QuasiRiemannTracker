import Candidate.Target830.Source.BalancedAmplification
import Candidate.Cycle63.Physical.InitialMass.GeometryAllocationMass
import Candidate.Cycle63.Moment.JointAllocationEnergy

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open Cycle63InitialMass Target830.Source
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
        balancedAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B)≤
      D*‖balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*
        ((geometryColumnIdeal reflected s R seed K Z ξ hK key j).absNorm:ℝ)^(ε-1) := by
  obtain ⟨D,hD,hcard⟩ := actualAllocations_uniform_small_power (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2*(max 1 b)^N*(Cs^N)^2,by positivity,?_⟩
  intro ι _ _ s hn hM reflected R seed K Z ξ M A hK key weight j hC
  let C := geometryColumnIdeal reflected s R seed K Z ξ hK key j
  let scalar := balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j
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
      balancedAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B≤
        ‖scalar‖^2*((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/C.absNorm)*(Cs^N)^2 := by
    unfold balancedAllocationWeight
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


end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_allocation_mass
