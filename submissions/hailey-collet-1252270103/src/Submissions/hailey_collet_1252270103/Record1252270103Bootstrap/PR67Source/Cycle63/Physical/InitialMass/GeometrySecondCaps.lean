import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondChildCaps
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondActualRowBudget
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization

/-- The actual label-dependent cutoff satisfies the polynomial envelope
needed for second-dyad selection. It holds for either first rectangle. -/
theorem actual_geometry_main_cutoff_cap {ι : Type*}[Fintype ι][DecidableEq ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ sigma reserve b M : ℝ)
    (N : ℕ)(hK : 0<K)(hZ : 1<Z)(hb : 0<b)(hξ : 0≤ξ)
    (hsigma : 0≤ sigma)(hreserve : 0≤ reserve)(hKM : K≤Z^M)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    frequencyRadius (firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
      (geometryFirstLabel s R seed K Z ξ hK key j)) Z ξ≤b^(2*N)*Z^(M+ξ/2) := by
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  have hh := main_fourier_scale_upper reflected src.C src.D
    (Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive})
    src.hC.1 src.hD.1 (subsetGenerator_supported src.C src.D src.hC src.inactive).1
    src.sameSupport K (volume s) Z sigma (frequencyLoss Z 32 ξ) reserve b N
    hK (volume_pos s) hZ hb hsigma (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ) hreserve
  change firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
    (geometryFirstLabel s R seed K Z ξ hK key j)≤b^(2*N)*K at hh
  unfold frequencyRadius
  calc
    _≤(b^(2*N)*K)*Z^(ξ/2) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by linarith) _)
    _≤(b^(2*N)*Z^M)*Z^(ξ/2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKM (pow_nonneg hb.le _)) (Real.rpow_nonneg (by linarith) _)
    _=_ := by rw [Real.rpow_add (zero_lt_one.trans hZ)];ring

/-- A single threshold bounds all supported first-child source radii.
It is fixed before the original source, the selected columns and allocations. -/
theorem eventual_geometry_child_source_cap (N : ℕ)(b bs ε : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι][DecidableEq ι]
      (s : Input ι)(A : ℝ),Fintype.card ι≤N → Endpoints b bs bs s → volume s≤Z^A →
      ∀(C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ),
      frozenCoefficient B.val C R s.ν s.W s.P≠0 → sourceRadius (child s C R B χ t)≤Z^(A+ε) := by
  filter_upwards [(tendsto_rpow_atTop hε).eventually
    (eventually_ge_atTop (geometry N b bs bs)),eventually_gt_atTop (1:ℝ)] with Z hgeom hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ s A hcard he hV C R B χ t hne
  have hn := norm_ge_one C (allocation_ne s C B)
  have hg : 0≤geometry N b bs bs := (geometry_ge_one N b bs bs hb hbs hbs).trans' (by norm_num)
  calc
    _≤geometry N b bs bs*volume s/(C.absNorm:ℝ) :=
      actual_common_child_source_cap N b bs hb hbs s hcard he C R B χ t hne
    _≤geometry N b bs bs*volume s := div_le_self (mul_nonneg hg (volume_pos s).le) hn
    _≤Z^ε*Z^A := mul_le_mul hgeom hV (volume_pos s).le (Real.rpow_nonneg (by linarith) _)
    _=_ := by rw [←Real.rpow_add (zero_lt_one.trans hZ),add_comm]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
