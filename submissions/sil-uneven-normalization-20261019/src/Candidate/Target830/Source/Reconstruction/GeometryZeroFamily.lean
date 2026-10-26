import Candidate.Target830.Source.Schedule
import Candidate.Target830.Source.Reconstruction.ZeroScalar
import Candidate.Cycle63.Physical.InitialMass.SecondHighPayment
import Candidate.Cycle63.Physical.InitialMass.GeometrySecondSplit
import Candidate.Target830.Source.Reconstruction.ZeroUniform
import Candidate.Cycle63.Physical.InitialMass.GeometryAllocationMass

/- Original module: Candidate.Target830.Source.Reconstruction.GeometryZero. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Target830.Source.Reconstruction
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic Cycle63Moment
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstScale CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentOriginalCommonHarmonic CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceRow CenteredMomentSourceMass EisensteinSchwartzPoisson
open Cycle63SecondZero
variable {plane : SourcePlane}
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
  -M*(227876729/3446640000)+frequencyLoss Z 32 ξ+reserve+
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
    widthLower ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*plane.total beta → a ≤ M*plane.amp beta →
    volume s = Z^A → bs^N ≤ Z^padding → Z^s₀ ≤ (seed.absNorm:ℝ) →
    let u := child s (if reflected then l.1.2 else l.1.1) R B χ t
    Z^(-firstZeroReference reflected Z A a l)*
      (‖originalSecondZero u (R*(if reflected then l.1.2 else l.1.1)) seed W
        (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l)‖/volume u) ≤
      C₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
        Z^(firstZeroSaving reflected Z M A ξ reserve padding ε s₀ l) := by
  obtain ⟨C₀,hC₀,hbound⟩ := uniform_radius_certificates (plane:=plane) N Cs bs hi ε hCs hbs hε
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
end OAI.SevenEighths.Target830.Source.Reconstruction
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.original_zero_radiusTerm
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.actual_first_label_main_zero
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.reference_power_remove
end

/- Original module: Candidate.Target830.Source.Reconstruction.GeometryZeroFamily. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Target830.Source.Reconstruction
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstScale
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic EisensteinSchwartzPoisson
variable {plane : SourcePlane}
local notation "O" => HeckeFamily.O
local instance geometryZeroDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma actual_first_divisor_ne_zero (src : FirstBlockSource)
    (L : src.divisors) : L.val ≠ 0 := by
  apply (first_divisor_norm src (∑ I ∈ src.pool, (I.absNorm:ℝ)) ?_ L).1
  intro I hI
  exact Finset.single_le_sum (fun J _ => (show (0:ℝ) ≤ (J.absNorm:ℝ) from Nat.cast_nonneg _)) hI

/-- A fixed zero-mode constant works for every original column and live
common allocation; the residual first projector supplies its actual seed. -/
theorem actual_geometry_column_main_zero (N : ℕ) (Cs bs lo hi ε : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hlo : 0 < lo) (hhi : 0 ≤ hi) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    ∀ (s : Input ι), Fintype.card ι ≤ N → (∀ i,s.M i ≤ Cs) → s.upper ≤ bs →
    ∀ p : Profiles lo hi, s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (W : 𝓢(ℝ,ℂ)) (reflected : Bool) (R seed : Ideal O)
      (Z beta M A a ξ reserve padding : ℝ) (hZ : 1 < Z),
    widthLower ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*plane.total beta → a ≤ M*plane.amp beta →
    volume s = Z^A → bs^N ≤ Z^padding →
    ∀ key : ℤ×(Fin 5→ℤ),
    ∀ j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key),
    ∀ B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j),
    ∀ t : ℝ,
    frozenCoefficient B.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j) R s.ν s.W s.P ≠ 0 →
    let C := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j
    let u := child s C R B (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j) t
    let l := geometryFirstLabel s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j
    ‖originalSecondZero u (R*C) j.2.1.val W
      (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l)‖/volume u ≤
      C₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
        Z^(firstZeroReference reflected Z A a l+
          firstZeroSaving reflected Z M A ξ reserve padding ε
            (Real.logb Z (j.2.1.val.absNorm:ℝ)) l) := by
  obtain ⟨C₀,hC₀,hbound⟩ := actual_first_label_main_zero (plane:=plane) N Cs bs lo hi ε hCs hbs hlo hhi hε
  refine ⟨C₀,hC₀,?_⟩
  intro ι _ _ s hn hm hs p hp₁ hp₂ W reflected R seed Z beta M A a ξ reserve padding
    hZ hb hM hA ha hV hgeo key j B t hB
  let src := geometryFirstSource s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1
  have hseed := actual_first_divisor_ne_zero src j.2.1
  have hseedN : Z^(Real.logb Z (j.2.1.val.absNorm:ℝ)) ≤ (j.2.1.val.absNorm:ℝ) := by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (norm_pos _ hseed)]
  have hh := hbound s hn hm hs p hp₁ hp₂ reflected
    (geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j)
    src.hC src.hD src.sameSupport R j.2.1.val hseed B
    (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j) t hB W
    Z beta M A a ξ reserve padding (Real.logb Z (j.2.1.val.absNorm:ℝ))
    hZ hb hM hA ha hV hgeo hseedN
  exact reference_power_remove Z _ _ _ _ (zero_lt_one.trans hZ) hh

/-- Sum the literal split's zero costs. The actual normalized column mass
and its first label/projector stay inside the sum after allocation payment. -/
theorem actual_geometry_zero_family (N : ℕ) (Cs bs lo hi ε εmass : ℝ)
    (hCs : 1 ≤ Cs) (hbs : 1 ≤ bs) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hε : 0 < ε) (hεmass : 0 < εmass) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    ∀ (s : Input ι), Fintype.card ι ≤ N → (∀ i,s.M i ≤ Cs) → s.upper ≤ bs →
    ∀ p : Profiles lo hi, s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (W : 𝓢(ℝ,ℂ)) (reflected : Bool) (R seed : Ideal O)
      (Z beta M A a ξ reserve padding : ℝ) (hZ : 1 < Z),
    widthLower ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*plane.total beta → a ≤ M*plane.amp beta →
    volume s = Z^A → bs^N ≤ Z^padding →
    ∀ key : ℤ×(Fin 5→ℤ),
    ∀ weight : Cycle63JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ,
    ∀ rows : Finset (FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)), ∀ t : ℝ,
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let C := fun j : rows => geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j.val
    let u := fun (j : rows) (B : actualAllocations s.pools (C j)) =>
      child s (C j) R B (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j.val) t
    let l := fun j : rows => geometryFirstLabel s R seed (Z^M) Z ξ hK key j.val
    (∑ j : rows, ∑ B : actualAllocations s.pools (C j),
      (geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B/
        volume (u j B))*‖originalSecondZero (u j B) (R*C j) j.val.2.1.val W
          (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve (l j))‖) ≤
      K₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖*
        ∑ j : rows, ‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M A hK key weight j.val‖^2*
          ((C j).absNorm:ℝ)^(εmass-1)*
          Z^(firstZeroReference reflected Z A a (l j)+
            firstZeroSaving reflected Z M A ξ reserve padding ε
              (Real.logb Z (j.val.2.1.val.absNorm:ℝ)) (l j)) := by
  obtain ⟨C₀,hC₀,hzero⟩ := actual_geometry_column_main_zero (plane:=plane) N Cs bs lo hi ε hCs hbs hlo hhi hε
  obtain ⟨D,hD,hmass⟩ := actual_geometry_allocation_mass N Cs bs εmass hCs hεmass
  refine ⟨D*C₀,mul_pos hD hC₀,?_⟩
  intro ι _ _ s hn hm hs p hp₁ hp₂ W reflected R seed Z beta M A a ξ reserve padding
    hZ hb hM hA ha hV hgeo key weight rows t hK C u l
  let F := C₀*(p.control {(0,0)})^2*‖paperRadialFourier W 0‖
  let power := fun j : rows => Z^(firstZeroReference reflected Z A a (l j)+
    firstZeroSaving reflected Z M A ξ reserve padding ε
      (Real.logb Z (j.val.2.1.val.absNorm:ℝ)) (l j))
  let mass := fun j : rows => ‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M A hK key weight j.val‖^2*
    ((C j).absNorm:ℝ)^(εmass-1)
  have hC (j : rows) : C j ≠ 0 := by
    cases reflected
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1).hC.1
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hK key j.val.1).hD.1
  have hterm (j : rows) (B : actualAllocations s.pools (C j)) :
      (geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B/
        volume (u j B))*‖originalSecondZero (u j B) (R*C j) j.val.2.1.val W
          (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve (l j))‖ ≤
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B*(F*power j) := by
    by_cases hB : frozenCoefficient B.val (C j) R s.ν s.W s.P ≠ 0
    · have hh := hzero s hn hm hs p hp₁ hp₂ W reflected R seed Z beta M A a ξ reserve padding
        hZ hb hM hA ha hV hgeo key j.val B t hB
      rw [div_mul_eq_mul_div,mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hh
        (geometryAllocationWeight_nonneg reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B)
    · have hw : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B=0 := by
        simp only [geometryAllocationWeight,C,hB,ite_false]
      rw [hw,zero_div,zero_mul,zero_mul]
  calc
    _ ≤ ∑ j : rows, ∑ B : actualAllocations s.pools (C j),
        geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B*(F*power j) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun B _ => hterm j B))
    _ ≤ ∑ j : rows, (D*mass j)*(F*power j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [←Finset.sum_mul]
      have hmj : (∑ B : actualAllocations s.pools (C j),
          geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK key weight N bs j.val B) ≤
          D*mass j := by
        simpa only [mass,C,mul_assoc] using
          hmass s hn hm reflected R seed (Z^M) Z ξ M A hK key weight j.val (hC j)
      exact mul_le_mul_of_nonneg_right hmj (by dsimp only [F,power]; positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [F,power,mass]
      ring

end
end OAI.SevenEighths.Target830.Source.Reconstruction
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.actual_first_divisor_ne_zero
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.actual_geometry_column_main_zero
#print axioms OAI.SevenEighths.Target830.Source.Reconstruction.actual_geometry_zero_family
end
