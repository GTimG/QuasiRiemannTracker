/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B089
import Submissions.cycle61_c0125139.Bundles.B110
import Submissions.cycle61_c0125139.Bundles.B115
import Submissions.cycle61_c0125139.Bundles.B116
import Submissions.cycle61_c0125139.Bundles.B119
import Submissions.cycle61_c0125139.Bundles.B135

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondSourceBudget; sha256 a25663cfbdd24c1b0230d5a0795743608b49ee14690790da56a077045f70877e -/
section
                                                          

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSecondLocalization CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSupportedTailAggregate EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

/-- The zero-frequency term of the literal source, before normalization. -/
def originalSecondZero {ι : Type*} [Fintype ι] (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ((K:ℂ)*paperRadialFourier W 0)*sourceSecondZero
    (original s R seed).columns (original s R seed).beta s.η s.t

/-- Split the actual normalized source while keeping the retained terms
in one joint sum. Only the zero and discarded branches are bounded
separately by their absolute values. -/
theorem actual_joint_normalized_source_budget {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (slots : Label→ Finset α) (s : (l : Label)→ Input (slots l))
    (R seed : Label→ Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec : Label→ℝ) (Z ξ : ℝ)
    (hK : ∀l,0< K l)(weight : Label→ℝ)(hw : ∀l,0≤ weight l) :
    (∑l,weight l*normalizedGaussSource (s l) (R l) (seed l) W (K l))≤
      (∑l,(weight l/volume (s l))*(‖originalSecondZero (s l) (R l) (seed l) W (K l)‖+
        ‖secondDiscardedEnergy (s l).η (s l).t (original (s l) (R l) (seed l)).columns
          (original (s l) (R l) (seed l)).beta W (K l) (Tsec l) Z ξ‖))+
      ‖∑l,((weight l/volume (s l):ℝ):ℂ)*secondRetainedEnergy (s l).η (s l).t
        (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
          W (K l) (Tsec l) Z ξ‖ := by
  let ret := fun l=>secondRetainedEnergy (s l).η (s l).t
    (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
      W (K l) (Tsec l) Z ξ
  let tail := fun l=>secondDiscardedEnergy (s l).η (s l).t
    (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
      W (K l) (Tsec l) Z ξ
  let zero := fun l=>originalSecondZero (s l) (R l) (seed l) W (K l)
  let c := fun l=>weight l/volume (s l)
  have hc (l : Label) : 0≤ c l := div_nonneg (hw l) (volume_pos (s l)).le
  have he (l : Label) : weight l*normalizedGaussSource (s l) (R l) (seed l) W (K l)=
      c l*(zero l).re+c l*(ret l).re+c l*(tail l).re := by
    unfold normalizedGaussSource
    rw [sourceGaussEnergy_localized _ _ _ _ W (K l) (Tsec l) Z ξ (hK l)]
    simp only [Complex.add_re]
    dsimp only [c,zero,ret,tail,originalSecondZero]
    ring
  have hr : (∑l,c l*(ret l).re)≤‖∑l,(c l:ℂ)*ret l‖ := by
    have heq : (∑l,c l*(ret l).re)=(∑l,(c l:ℂ)*ret l).re := by
      simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [heq]
    exact Complex.re_le_norm _
  have hz : (∑l,(c l*(zero l).re+c l*(tail l).re))≤
      ∑l,c l*(‖zero l‖+‖tail l‖) := by
    apply Finset.sum_le_sum
    intro l hl
    calc
      _≤ c l*‖zero l‖+c l*‖tail l‖ := add_le_add
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hc l))
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hc l))
      _=_ := by ring
  simp_rw [he]
  calc
    _=(∑l,(c l*(zero l).re+c l*(tail l).re))+(∑l,c l*(ret l).re) := by
      simp only [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _≤ _ := add_le_add hz hr

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_normalized_source_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondSourceBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySecondSplit; sha256 327f697f682e8537b54288490fda387f280ad5f9db4bb14c0a112366e13828f0 -/
section
                                                         
                                                      
                                                      

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSecondLocalization
open CenteredMomentCommonProfile CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentLogDyadic CenteredMomentSupportedTailAggregate
local notation "O" => HeckeFamily.O

/-- The amplified main branch of the actual first geometry budget splits
into zero/tail costs and one retained sum across all original columns and
supported common allocations. Its main scale is tied to the arithmetic label. -/
theorem actual_geometry_main_second_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A sigma reserve b t : ℝ) (N : ℕ) (hK : 0< K) (hZ : 0< Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ) :
    let Live := ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=>logAnnulus))
    let C := fun j : Live=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
    let χ := fun j : Live=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
    let g := fun j : Live=>geometryBranch reflected s R seed K Z ξ hK key j.val
    let w := fun j : Live=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
    let Label := (j : Live) × actualAllocations s.pools (C j)
    let source := fun q : Label=>child s (C q.1) R q.2 (χ q.1) t
    let radius := fun q : Label=>firstMainRadius reflected K (volume s) Z ξ sigma reserve
      (geometryFirstLabel s R seed K Z ξ hK key q.1.val)
    let c := fun q : Label=>w q.1 q.2/volume (source q)
    ∀Tsec : Label→ℝ,
    (∑j : Live,∑B : actualAllocations s.pools (C j),
      w j B*actualMainSource (child s (C j) R B (χ j) t) (g j) Z sigma 1 ξ reserve)≤
      (∑q : Label,c q*(‖originalSecondZero (source q) (R*C q.1) q.1.val.2.1.val ballProfile (radius q)‖+
        ‖secondDiscardedEnergy (source q).η (source q).t
          (original (source q) (R*C q.1) q.1.val.2.1.val).columns
          (original (source q) (R*C q.1) q.1.val.2.1.val).beta
          ballProfile (radius q) (Tsec q) Z ξ‖))+
      ‖∑q : Label,(c q:ℂ)*secondRetainedEnergy (source q).η (source q).t
        (original (source q) (R*C q.1) q.1.val.2.1.val).columns
        (original (source q) (R*C q.1) q.1.val.2.1.val).beta
        ballProfile (radius q) (Tsec q) Z ξ‖ := by
  intro Live C χ g w Label source radius c Tsec
  have hh := actual_joint_normalized_source_budget (α:=ι) (Label:=Label)
    (fun q=>liveIndices q.2.val) source (fun q=>R*C q.1) (fun q=>q.1.val.2.1.val)
    ballProfile radius Tsec Z ξ
    (fun q=>first_main_radius_pos reflected K (volume s) Z ξ sigma reserve hZ _)
    (fun q=>w q.1 q.2)
    (fun q=>geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b q.1.val q.2)
  apply le_trans (le_of_eq ?_) hh
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro B hB
  rw [actual_geometry_main_source_radius]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_second_split

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySecondSplit -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAllocationMass; sha256 6885e5be9806089ba3a6e44b76a551b5b6c1a0b19e49a41b6146203c72102209 -/
section
                                                       
                                           

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentAllocationCost
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussNormalization
open CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

/-- The actual amplification weights pay a small power of the common
ideal and its inverse norm. The two allocation cardinalities are included. -/
theorem actual_geometry_allocation_mass (N : ℕ) (Cs b ε : ℝ) (hCs : 1≤ Cs) (hε : 0<ε) :
    ∃D : ℝ,0< D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A : ℝ)(hK : 0< K)
        (key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
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
      _≤ Cs^N := pow_le_pow_right₀ hCs ((Finset.card_le_univ _).trans hn)
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
    (hK : 0< K)(hZ : 0< Z)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))
    (t : ℝ) :
    0≤ actualMainSource
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
theorem actual_geometry_main_selection (N : ℕ)(Cs b ε : ℝ)(hCs : 1≤ Cs)(hε : 0<ε) :
    ∃D : ℝ,0< D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A sigma reserve t : ℝ)
        (hK : 0< K)(hZ : 0< Z)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
        (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (G E : ℝ),0≤ G →
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let χ := fun j : rows=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
      let g := fun j : rows=>geometryBranch reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      (∀j,C j≠0) →
      (∀j,‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)≤ G) →
      (∀S : Finset rows,∀pick : (j : S)→ actualAllocations s.pools (C j.val),
        (∀j,frozenCoefficient (pick j).val (C j.val) R s.ν s.W s.P≠0) →
        (∑j : S,actualMainSource (child s (C j.val) R (pick j) (χ j.val) t)
          (g j.val) Z sigma 1 ξ reserve)≤ E) →
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
      _≤ D*G := mul_le_mul_of_nonneg_left (hscalar j) hD.le
  · intro S pick hne
    apply hjoint S pick
    intro j hf
    apply hne j
    simp only [w,geometryAllocationWeight]
    dsimp only [C] at hf
    simp only [hf,ne_eq,not_true_eq_false,ite_false]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_allocation_mass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_nonneg

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_selection

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAllocationMass -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryZero; sha256 5aa05a4bd1e3112bcb65fe274d57d628ea5f4adaed057eb94ec364d34a36f49d -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                     
                                                       
                                          

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic Cycle61Moment
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstScale CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentOriginalCommonHarmonic CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceRow CenteredMomentSourceMass EisensteinSchwartzPoisson
open Cycle61SecondZero
local notation "O" => HeckeFamily.O

lemma original_zero_radiusTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    ‖originalSecondZero s R seed W K‖/volume s = radiusTerm s R seed W K := by
  rfl

def firstZeroReference (reflected : Bool) (Z A a : ℝ) (l : FirstSourceLabel) : ℝ :=
  a+A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
    Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)+
    Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)

def firstZeroSaving (reflected : Bool) (Z M A ξ reserve padding ε s₀ : ℝ)
    (l : FirstSourceLabel) : ℝ :=
  -M*(8754683599/120632400000)+frequencyLoss Z 32 ξ+reserve+
    ε*(A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+padding)-s₀

/-- The literal zero term at the enlarged main radius, with the first
projector and actual child normalization retained in both orientations. -/
theorem actual_first_label_main_zero (N : ℕ) (Cs bs lo hi ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    ∀ (s : Input ι), Fintype.card ι ≤ N → (∀ i,s.M i ≤ Cs) → s.upper ≤ bs →
    ∀ p : Profiles lo hi, s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (reflected : Bool) (l : FirstSourceLabel), Supported l.1.1 → Supported l.1.2 →
    CompletedGauss.primeSupport l.1.1 = CompletedGauss.primeSupport l.1.2 →
    ∀ (R seed : Ideal O), seed ≠ 0 →
    ∀ (B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (χ : Character) (t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P ≠ 0 →
    ∀ (W : 𝓢(ℝ,ℂ)) (Z beta M A a ξ reserve padding s₀ : ℝ), 1 < Z →
    3401/100000 ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Cycle61.Arithmetic.totalA beta → a ≤ M*Cycle61.Arithmetic.amp beta →
    volume s = Z^A → bs^N ≤ Z^padding → Z^s₀ ≤ (seed.absNorm:ℝ) →
    let u := child s (if reflected then l.1.2 else l.1.1) R B χ t
    Z^(-firstZeroReference reflected Z A a l)*
      (‖originalSecondZero u (R*(if reflected then l.1.2 else l.1.1)) seed W
        (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l)‖/volume u) ≤
      C₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
        Z^(firstZeroSaving reflected Z M A ξ reserve padding ε s₀ l) := by
  obtain ⟨C₀,hC₀,hbound⟩ := uniform_radius_certificates N Cs bs hi ε hCs hbs hε
  refine ⟨C₀,hC₀,?_⟩
  intro ι _ _ s hn hm hs p hp₁ hp₂ reflected l hC hD heq R seed hseed B χ t hB
    W Z beta M A a ξ reserve padding s₀ hZ hb hM hA ha hV hgeo hseedN
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
  let Rw := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
  let e := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
  have hselected : (if reflected then l.1.2 else l.1.1) ≠ 0 := by
    cases reflected <;> first | exact hC.1 | exact hD.1
  have hother : (if reflected then l.1.1 else l.1.2) ≠ 0 := by
    cases reflected <;> first | exact hD.1 | exact hC.1
  have hcn : Z^c ≤ ((if reflected then l.1.2 else l.1.1).absNorm:ℝ) := by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (norm_pos _ hselected)]
  have hv := actual_common_volume_cap N bs hbs s hn hs _ R B χ t hB Z A c padding hZ
    hgeo (le_of_eq hV) hcn
  have hh := hbound hv.1 lo hlo hhi (child s _ R B χ t) p
    (fun i => hm i.val) hs hp₁ hp₂ (R*(if reflected then l.1.2 else l.1.1)) seed hseed
    W Z beta M A a c d 0 Rw e (2*A-c-d+Rw+e-M) 0 (frequencyLoss Z 32 ξ) reserve
    (A-c+padding) s₀ hZ hb hM hA ha
    (ideal_log_nonneg _ hselected Z hZ) (ideal_log_nonneg _ hother Z hZ)
    (by norm_num) (by simp) hv.2 hseedN
  have hr : firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l =
      mainCommonRadius Z d (2*A-c-d+Rw+e-M) c (3*a) (frequencyLoss Z 32 ξ) reserve := by
    rw [hV,actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hZ]
    unfold mainCommonRadius
    congr 1
    dsimp only [c,d,Rw,e]
    ring
  dsimp only
  rw [hr,original_zero_radiusTerm]
  convert hh.1 using 1 <;>
    dsimp only [firstZeroReference,firstZeroSaving,c,d,Rw,e,radiusTerm] <;>
    congr 2 <;> ring

/-- Remove only the displayed positive reference power; the normalized
child volume is still literal. -/
lemma reference_power_remove (Z ref saving x bound : ℝ) (hZ : 0 < Z)
    (h : Z^(-ref)*x ≤ bound*Z^saving) : x ≤ bound*Z^(ref+saving) := by
  have hh := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le ref)
  have he : Z^ref*Z^(-ref) = 1 := by rw [←Real.rpow_add hZ]; simp
  apply (show x ≤ Z^ref*bound*Z^saving by simpa only [←mul_assoc,he,one_mul] using hh).trans_eq
  rw [Real.rpow_add hZ]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.original_zero_radiusTerm
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_label_main_zero
#print axioms OAI.SevenEighths.Cycle61InitialMass.reference_power_remove

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryZero -/
