import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainNormalized
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondLiveBlock CenteredMomentSecondLocalization
open CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile CenteredMomentLogDyadic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local instance mainOrdinaryContractionSumDecidable {ι : Type*} :
    DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The fixed-inducing part changes only the original physical row set. -/
def mainExceptionalDatum (d : SecondInputDatum α) (χ : RayCharacter)
    (Q : Ideal O) (m : O) : SecondInputDatum α :=
  {d with rows:=partRows true d.input.η χ Q m d.C d.D d.inactive d.radius
          rows_ne:=fun z hz=>sourceRows_nonzero _ _ _ _ z (Finset.mem_filter.mp hz).1}

/-- Split a complete original source family before any ordinary-row contraction. -/
theorem main_original_exceptional_split {Label : Type*} [Fintype Label]
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (χ : Label→RayCharacter)
    (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ))
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) :
    ‖∑l,w l*(d l).block.value W‖ ≤
      (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value W‖)+
      ‖∑l,w l*(ordinarySecondDatum (d l) (χ l) Q m).block.value W‖ := by
  have he (l : Label) : (d l).block.value W =
      (mainExceptionalDatum (d l) (χ l) Q m).block.value W +
      (ordinarySecondDatum (d l) (χ l) Q m).block.value W := by
    have hvalue := congrArg (fun rows=>physicalBlock (d l).block.character
      (d l).block.height (d l).block.pool (d l).block.beta (d l).C (d l).D
      (d l).hC (d l).hD (d l).inactive (d l).radius rows W (d l).K (d l).dyad) (hrows l)
    exact hvalue.trans (geometry_physical_block_split (d l).input.η (χ l) Q m (d l).input.t
      _ _ (d l).C (d l).D (d l).hC (d l).hD (d l).inactive (d l).radius W (d l).K (d l).dyad)

  simp_rw [he,mul_add]
  rw [Finset.sum_add_distrib]
  exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (le_refl _))

/-- Constants precede the entire moving family. The sole analytic input is
its literal ordinary normalized bound, on the original selected labels. -/
theorem main_original_from_normalized (W : 𝓢(ℝ,ℂ)) (A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label]
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (χ : Label→RayCharacter)
    (Q : Ideal O) (m : O) (E H : ℤ→ℝ),
    (∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) →
    (∀r∈secondRatioBins (fun l=>(d l).block),0≤E r) →
    (∀r∈secondRatioBins (fun l=>(d l).block),0<H r) →
    SecondNormalizedBound W degree windowDegree
      (fun l=>ordinarySecondDatum (d l) (χ l) Q m) w E H →
    ‖∑l,w l*(d l).block.value W‖ ≤
      (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value W‖)+
      C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hbound⟩ := restricted_second_ratio_from_normalized (α:=α)
    W A degree windowDegree hc hs
  refine ⟨C,hC,?_⟩
  intro Label _ d w χ Q m E H hrows hE hH hnorm
  exact (main_original_exceptional_split d w χ Q m W hrows).trans
    (add_le_add_right (hbound (fun l=>ordinarySecondDatum (d l) (χ l) Q m)
      w E H hE hH hnorm) _)

attribute [local irreducible] geometryLowSecondDatum geometryMainSecondWeight

section Actual
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "N" => Fintype.card α
local notation "firsts" => GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key
local notation "blocks" => geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂

/-- The literal joint main retained sum: first allocation weight, child seed,
original puncture and second Fourier scales are unchanged. -/
def geometryMainRetainedSum (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ) : ℂ :=
  ∑q : firsts,
    (geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t q:ℂ)*
    secondRetainedEnergy
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q).η
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q).t
      (finiteColumns (Fintype.piFinset (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q).pools))
      (coefficient (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q)
        (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) q.1.val.2.1.val)
      ballProfile
      (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val))
      (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)) Z ξ

/-- Original full-block filtering precedes the inducing split. -/
theorem actual_main_retained_nonzero_sum (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ) :
    geometryMainRetainedSum reflected s R seed Z Mrow amp ξ reserve b t hZ key Mprice Aprice weight =
      ∑j : blocks,
        geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val*
        (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          j.val.1 hz₁ hz₂ j.val.2).block.value ballProfile := by
  have hassembly := actual_joint_retained_assembly
    (fun q : firsts=>liveIndices q.2.val)
    (fun q=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q)
    (fun q=>R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)
    (fun q=>q.1.val.2.1.val)
    (fun q=>actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus) q.1.val q.1.property)
    (fun _=>hz₁) (fun _=>hz₂) ballProfile
    (fun q=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val))
    (fun q=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)) Z ξ
    (fun q=>first_main_radius_pos reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hZ) _)
    (fun q=>(geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t q:ℂ))
  have heq : geometryMainRetainedSum reflected s R seed Z Mrow amp ξ reserve b t hZ key Mprice Aprice weight =
      ∑j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key,
        geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j*
        (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          j.1 hz₁ hz₂ j.2).block.value ballProfile := by
    simpa only [geometryMainRetainedSum,geometryMainSecondWeight,geometryLowSecondDatum] using hassembly
  rw [heq]
  let datum := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.1 hz₁ hz₂ j.2).block
  let coeff := geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight
  let live := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    frozenCoefficient j.1.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val) R s.ν s.W s.P≠0
  conv_rhs => rw [Finset.sum_coe_sort blocks (fun j=>coeff j*(datum j).value ballProfile)]
  conv_rhs => rw [geometryMainNonzeroBlocks,Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · by_cases hlive : live j
    · have hz : (datum j).value ballProfile=0 := by
        by_contra hn
        exact h ⟨hlive,hn⟩
      rw [hz,mul_zero]
    · have hw : coeff j=0 := by
        simp only [coeff,geometryMainSecondWeight,geometryLowFirstWeight,geometryAllocationWeight,
          live] at hlive ⊢
        simp only [hlive,ite_false,zero_div,Complex.ofReal_zero,zero_mul]
      change coeff j*(datum j).value ballProfile=0
      rw [hw,zero_mul]

end Actual

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
