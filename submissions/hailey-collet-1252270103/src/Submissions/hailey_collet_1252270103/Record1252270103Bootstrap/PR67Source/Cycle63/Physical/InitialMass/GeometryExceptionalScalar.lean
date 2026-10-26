import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryScalarCompensation
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryWidth
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAmplification
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePresentation
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentFirstAllocationGaussEnergy

lemma exceptional_side_power (Z V I P R E S : ℝ) (hZ : 1<Z)
    (hV : 0<V) (hI : 0<I) (hP : 0<P) (hR : 0<R) (hE : 0<E) :
    Z^(Real.logb Z P+Real.logb Z V-Real.logb Z I+
      Real.logb Z R+Real.logb Z E+S)=P*(V/I)*R*E*Z^S := by
  have hz := zero_lt_one.trans hZ
  simp only [Real.rpow_add hz,Real.rpow_sub hz,
    Real.rpow_logb hz hZ.ne' hP,Real.rpow_logb hz hZ.ne' hV,
    Real.rpow_logb hz hZ.ne' hI,Real.rpow_logb hz hZ.ne' hR,
    Real.rpow_logb hz hZ.ne' hE]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometryExceptionalScalarSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
/-- The actual side normalization already contains the entire presented
conductor. The radical factor is retained for the arithmetic label sum. -/
theorem actual_geometry_exceptional_denominator (reflected : Bool)
    (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    let src := geometryFirstSource s R seed K Z ξ hK key j.1
    let χ := geometryColumnCharacter reflected s R seed K Z ξ hK key j
    let I := geometryColumnIdeal reflected s R seed K Z ξ hK key j
    let v := geometryExponents s R seed K Z ξ j.1.val
    let S := if reflected then max (3*v 1-5*v 0-v 3) 0/6
      else max (3*v 0-5*v 1-v 3) 0/6
    Z^(if reflected then rightExponent (Real.logb Z (volume s.toData)) v
      else leftExponent (Real.logb Z (volume s.toData)) v)=
      ((commonRadical src.C src.D).absNorm:ℝ)*(volume s.toData/(I.absNorm:ℝ))*
        ((χ.modulus.absNorm:ℝ)/(fixedPresentationCost*(s.η.modulus.absNorm:ℝ)))*Z^S*
          Z^(geometrySurplus v) := by
  intro src χ I v S
  have hC := norm_pos src.C src.hC.1
  have hD := norm_pos src.D src.hD.1
  have hP := norm_pos (commonRadical src.C src.D) (commonRadical_ne_zero _ _)
  have hR := active_norm_pos src.C src.D
  have hE := norm_pos _ (subsetGenerator_supported src.C src.D src.hC src.inactive).1
  have hq := fixed_presentation_norm s.η χ src.C src.D src.inactive
    (actual_geometry_column_modulus reflected s R seed K Z ξ hK key j)
  simp only [eisEmbedding_norm_sq_eq_absNorm_span] at hq
  have hfixed := fixedPresentationCost_pos
  have hη := norm_pos s.η.modulus s.η.modulus_ne_bot
  have hV := volume_pos s.toData
  cases reflected
  · change Z^(Real.logb Z ((commonRadical src.C src.D).absNorm:ℝ)+
      Real.logb Z (volume s.toData)-Real.logb Z (src.C.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor src.C src.D}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val)
        src.inactive}).absNorm:ℝ)+S+geometrySurplus v)=_
    rw [Real.rpow_add (zero_lt_one.trans hZ),exceptional_side_power Z _ _ _ _ _ S hZ hV hC hP hR hE,hq]
    simp only [I,geometryColumnIdeal,Bool.false_eq_true,ite_false]
    dsimp only [src] at hC hD ⊢
    field_simp [hC.ne',hD.ne']
   
  · change Z^(Real.logb Z ((commonRadical src.C src.D).absNorm:ℝ)+
      Real.logb Z (volume s.toData)-Real.logb Z (src.D.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor src.C src.D}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val)
        src.inactive}).absNorm:ℝ)+S+geometrySurplus v)=_
    rw [Real.rpow_add (zero_lt_one.trans hZ),exceptional_side_power Z _ _ _ _ _ S hZ hV hD hP hR hE,hq]
    simp only [I,geometryColumnIdeal,ite_true]
    dsimp only [src] at hC hD ⊢
    field_simp [hC.ne',hD.ne']
   
lemma div_mul_rpow_le (x W Z s : ℝ) (hx : 0≤x) (hW : 0<W) (hZ : 1≤Z) (hs : 0≤ s) :
    x/(W*Z^s)≤x/W :=
  div_le_div_of_nonneg_left hx hW (le_mul_of_one_le_right hW.le (Real.one_le_rpow hZ hs))

/-- Squared geometry scalars are at most the exceptional reference denominator.
Physical D appears as D on the left and 1/D on the reflected right. -/
theorem actual_geometry_exceptional_scalar (reflected : Bool)
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (M Z ξ : ℝ) (hZ : 1<Z)
    (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)) :
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.1
    let χ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j
    let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j
    let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
    let S := if reflected then max (3*v 1-5*v 0-v 3) 0/6
      else max (3*v 0-5*v 1-v 3) 0/6
    ‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M (Real.logb Z (volume s.toData))
      hK key (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2/(I.absNorm:ℝ)≤
      (if reflected then 1/(src.D.absNorm:ℝ)
        else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ))*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/(commonRadical src.C src.D).absNorm)*
      ((volume s.toData/(I.absNorm:ℝ))/
        ((χ.modulus.absNorm:ℝ)*(volume s.toData/(I.absNorm:ℝ))^2*Z^S)) := by
  intro hK src χ I v S
  have hC := norm_pos src.C src.hC.1
  have hD := norm_pos src.D src.hD.1
  have hP := norm_pos (commonRadical src.C src.D) (commonRadical_ne_zero _ _)
  have hq := norm_pos χ.modulus χ.modulus_ne_bot
  have hV := volume_pos s.toData
  have hfixed := fixedPresentationCost_pos
  have hη := norm_pos s.η.modulus s.η.modulus_ne_bot
  have hpower := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) S
  have hp := actual_geometry_exceptional_denominator reflected s R seed (Z^M) Z ξ hK hZ key j
  have hsurplus := actual_geometry_surplus_nonneg s R seed (Z^M) Z ξ hZ j.1.val
  have hW : 0<((commonRadical src.C src.D).absNorm:ℝ)*(volume s.toData/(I.absNorm:ℝ))*
      ((χ.modulus.absNorm:ℝ)/(fixedPresentationCost*(s.η.modulus.absNorm:ℝ)))*Z^S := by
    have hI : 0<(I.absNorm:ℝ) := by cases reflected <;> assumption
    exact mul_pos (mul_pos (mul_pos hP (div_pos hV hI)) (div_pos hq (mul_pos hfixed hη))) hpower
  cases reflected
  · simp only [Bool.false_eq_true,ite_false] at hp ⊢
    change Z^(leftExponent (Real.logb Z (volume s.toData)) v)=_ at hp
    have hh := div_le_div_of_nonneg_right
      (actual_geometry_left_scalar_sq s R seed W M Z ξ hZ a₁ a₂ ha₁ ha₂ hs₁ hs₂ key j) hC.le
    apply hh.trans
    change (_*(src.C.absNorm:ℝ)*(src.D.absNorm:ℝ)/Z^(leftExponent _ v))/(src.C.absNorm:ℝ)≤_
    rw [hp]
    refine (div_le_div_of_nonneg_right (div_mul_rpow_le _ _ _ _ (by positivity) hW hZ.le hsurplus)
      hC.le).trans (le_of_eq ?_)
    simp only [src,χ,I,v,S,geometryColumnIdeal,Bool.false_eq_true,ite_false] at *
    field_simp [hC.ne',hD.ne',hP.ne',hq.ne',hV.ne',hfixed.ne',hη.ne',hpower.ne']
   
  · simp only [ite_true] at hp ⊢
    change Z^(rightExponent (Real.logb Z (volume s.toData)) v)=_ at hp
    have he : ‖geometryColumnScalar true s R seed (Z^M) Z ξ M
        (Real.logb Z (volume s.toData)) hK key
        (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2=
        1/Z^(rightExponent (Real.logb Z (volume s.toData)) v) := by
      dsimp only [v]
      simp only [geometryColumnScalar,ite_true,norm_inv,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,
        Real.sq_sqrt (Real.rpow_nonneg (zero_lt_one.trans hZ).le _),one_div]
    rw [he,hp]
    refine (div_le_div_of_nonneg_right (div_mul_rpow_le _ _ _ _ zero_le_one hW hZ.le hsurplus)
      (Nat.cast_nonneg _)).trans (le_of_eq ?_)
    simp only [src,χ,I,v,S,geometryColumnIdeal,ite_true] at *
    field_simp [hC.ne',hD.ne',hP.ne',hq.ne',hV.ne',hfixed.ne',hη.ne',hpower.ne']
   
/-- The actual allocation weight pays the presented exceptional denominator
while retaining the physical side factor and arithmetic radical. -/
theorem actual_geometry_exceptional_allocation_weight (reflected : Bool)
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (M Z ξ : ℝ) (hZ : 1<Z)
    (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key))
    (N : ℕ) (b : ℝ)
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j)) :
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.1
    let χ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j
    let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j
    let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
    let S := if reflected then max (3*v 1-5*v 0-v 3) 0/6
      else max (3*v 0-5*v 1-v 3) 0/6
    geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (volume s.toData)) hK key
      (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) N b j B≤
      ((if reflected then 1/(src.D.absNorm:ℝ)
        else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ))*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/(commonRadical src.C src.D).absNorm)*
      ((volume s.toData/(I.absNorm:ℝ))/
        ((χ.modulus.absNorm:ℝ)*(volume s.toData/(I.absNorm:ℝ))^2*Z^S)))*
        ((max 1 b)^N*((actualAllocations s.pools I).card:ℝ)*(frozenControl B.val s.M)^2) := by
  intro hK src χ I v S
  let U := (if reflected then 1/(src.D.absNorm:ℝ)
        else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ))*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/(commonRadical src.C src.D).absNorm)*
      ((volume s.toData/(I.absNorm:ℝ))/
        ((χ.modulus.absNorm:ℝ)*(volume s.toData/(I.absNorm:ℝ))^2*Z^S))
  let T := (max 1 b)^N*((actualAllocations s.pools I).card:ℝ)*(frozenControl B.val s.M)^2
  have hg := actual_geometry_exceptional_scalar reflected s R seed W M Z ξ hZ
    a₁ a₂ ha₁ ha₂ hs₁ hs₂ key j
  change ‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M
    (Real.logb Z (volume s.toData)) hK key
    (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2/(I.absNorm:ℝ)≤U at hg
  have ht : 0≤T := by dsimp [T]; positivity
  have hu : 0≤U := (by positivity : 0≤‖geometryColumnScalar reflected s R seed
    (Z^M) Z ξ M (Real.logb Z (volume s.toData)) hK key
    (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2/(I.absNorm:ℝ)).trans hg
  change _≤U*T
  unfold geometryAllocationWeight
  dsimp only
  split_ifs
  · have hh := mul_le_mul_of_nonneg_right hg ht
    convert hh using 1; dsimp only [T,I]; ring
  · exact mul_nonneg hu ht

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
