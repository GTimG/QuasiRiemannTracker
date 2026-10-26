import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.TerminalRadius
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceNormalization

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily ActualEisensteinCubic CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstScale
open CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O

lemma outside_power (K V E R Z : ℝ) (hK : 0<K) (hV : 0<V)
    (hE : 0<E) (hR : 0<R) (hZ : 1<Z) :
    K/(V*E*Real.sqrt R)=
      Z^(Real.logb Z K-Real.logb Z V-Real.logb Z E-Real.logb Z R/2) := by
  have hz := zero_lt_one.trans hZ
  have hs : Z^(Real.logb Z R/2)=Real.sqrt R := by
    rw [div_eq_mul_inv,Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hR]
    norm_num [Real.sqrt_eq_rpow]
  rw [Real.rpow_sub hz,Real.rpow_sub hz,Real.rpow_sub hz,
    Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hV,
    Real.rpow_logb hz hZ.ne' hE,hs]
  ring

/-- The literal first-transform scalar, after canceling both actual column
scales, leaves exactly the active half-radical and inactive whole radical.
The inactive Möbius weight remains visible. -/
theorem actual_scalar_outside (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (K A₀ B₀ V Z : ℝ)
    (hK : 0<K) (hA : 0<A₀) (hB : 0<B₀) (hV : 0<V) (hZ : 1<Z) :
    ‖scalar C D hC E K A₀ B₀‖*Real.sqrt A₀*Real.sqrt B₀/V =
      ‖inactiveWeight C D E‖*
      Z^(Real.logb Z K-Real.logb Z V-
        Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)/2) := by
  have hE := norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR := active_norm_pos C D
  have hroot : Real.sqrt ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      ‖eisEmbedding (activeConductor C D)‖ := by
    rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]
  rw [←outside_power K V _ _ Z hK hV hE hR hZ,hroot,
    ←eisEmbedding_norm_sq_eq_absNorm_span,scalar_norm C D hC E K A₀ B₀ hK hA hB]
  have ha : Real.sqrt A₀≠0 := (Real.sqrt_pos.mpr hA).ne'
  have hb : Real.sqrt B₀≠0 := (Real.sqrt_pos.mpr hB).ne'
  field_simp

/-- The actual Möbius coefficient costs at most one. The dyadic column
normalizers are canceled before using the common radical side bounds. -/
theorem actual_scalar_outside_le (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (M A₀ B₀ V Z : ℝ)
    (hA : 0<A₀) (hB : 0<B₀) (hV : 0<V) (hZ : 1<Z) :
    ‖scalar C D hC E (Z^M) A₀ B₀‖*Real.sqrt A₀*Real.sqrt B₀/V ≤
      Z^(M-Real.logb Z V-
        Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)/2) := by
  have hz := zero_lt_one.trans hZ
  rw [actual_scalar_outside C D hC E _ _ _ _ _ (Real.rpow_pos_of_pos hz _) hA hB hV hZ,
    Real.logb_rpow hz hZ.ne']
  exact mul_le_of_le_one_left (Real.rpow_nonneg hz.le _)
    (QuadraticInitialBound.norm_ideal_moebius_le_one _)

/-- Exact balance for one common label. Global joint Cauchy requires the
cross-label geometry-bin payment proved in GeometryPayment. -/
theorem actual_joint_power (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (Z M A E : ℝ) (hZ : 1<Z) :
    let c := Real.logb Z ((commonPart C D).absNorm:ℝ)
    let d := Real.logb Z ((commonPart D C).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical C D).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)
    let Bc := max (3*c-5*d-R) 0/6
    let Bd := max (3*d-5*c-R) 0/6
    Z^(M-A-R/2-E)*Real.sqrt (Z^(p+A-c+R+E+Bc))*
      Real.sqrt (Z^(p+A-d+R+E+Bd)) ≤ Z^M := by
  dsimp only
  have hz := zero_lt_one.trans hZ
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hh := Cycle61.Physical.actual_joint_side_exponent C D hC hD Z M A E hZ
  dsimp only at hh
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_scalar_outside
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_scalar_outside_le
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_power
