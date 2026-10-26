import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryMainRadius
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondSourceControls

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstScale CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- A supported first common child has a source cap from the original
volume and fixed profile support, uniformly in its character and height. -/
theorem actual_common_child_source_cap {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤b)(hbs : 1≤bs)
    (s : Input ι)(hcard : Fintype.card ι≤N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    sourceRadius (child s C R B χ t)≤geometry N b bs bs*volume s/(C.absNorm:ℝ) := by
  have hr := (radius_bound N b bs bs hb hbs hbs (child s C R B χ t)
    ((live_card_le B.val).trans hcard) (endpoints_child b bs bs s he C R B χ t)).2
  have hv := common_volume_le N b hb s hcard he.1 C R B χ t hne
  apply hr.trans
  apply (mul_le_mul_of_nonneg_left hv (by positivity : 0≤b^N*bs*bs)).trans_eq
  unfold geometry
  rw [show 2*N=N+N by omega,pow_add]
  ring

/-- The main-ball correction prevents the second Fourier scale from
exceeding the original physical scale, apart from fixed support factors.
This coarse bound is only used to count dyadic intervals. -/
theorem main_fourier_scale_upper (reflected : Bool)(C D E : Ideal O)
    (hC : C≠0)(hD : D≠0)(hE : E≠0)(heq : primeSupport C=primeSupport D)
    (K V Z sigma delta reserve b : ℝ)(N : ℕ)
    (hK : 0<K)(hV : 0<V)(hZ : 1<Z)(hb : 0<b)
    (hsigma : 0≤sigma)(hdelta : 0≤delta)(hreserve : 0≤reserve) :
    (b^N*V/((if reflected then D else C).absNorm:ℝ))^2/
      mainCommonRadius Z (Real.logb Z ((if reflected then C else D).absNorm:ℝ))
        (nominalLog C D E K V Z)
        (Real.logb Z ((if reflected then D else C).absNorm:ℝ)) sigma delta reserve≤b^(2*N)*K := by
  have hc := norm_pos C hC
  have hd := norm_pos D hD
  have he := norm_pos E hE
  have hr := active_norm_pos C D
  have hz : 0<Z := zero_lt_one.trans hZ
  have hege : (1:ℝ)≤E.absNorm := norm_ge_one E hE
  have hrge : (1:ℝ)≤(Ideal.span {activeConductor C D}).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have helog := Real.logb_nonneg hZ hege
  have hrlog := Real.logb_nonneg hZ hrge
  cases reflected <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals
    apply (Real.logb_le_logb hZ (by unfold mainCommonRadius; positivity) (by positivity)).mp
    unfold mainCommonRadius nominalLog
    rw [nominal_equal_support C D E hC hD heq K V]
    simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow,
      Real.logb_rpow hz hZ.ne']
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
  · linarith [le_max_left (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)) 0]
  · linarith [le_max_left (Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ)) 0]

/-- Exact Fourier logarithm for either first rectangle. This retains the
six-amplifier saving and cancels the inactive first radical explicitly. -/
theorem main_fourier_frequency_log (reflected : Bool)(C D E : Ideal O)
    (hC : C≠0)(hD : D≠0)(hE : E≠0)(heq : primeSupport C=primeSupport D)
    (K V Z sigma delta reserve ξ b : ℝ)(N : ℕ)
    (hK : 0<K)(hV : 0<V)(hZ : 1<Z)(hb : 0<b) :
    let c := Real.logb Z ((if reflected then D else C).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then C else D).absNorm:ℝ)
    let R := frequencyRadius ((b^N*V/((if reflected then D else C).absNorm:ℝ))^2/
      mainCommonRadius Z d (nominalLog C D E K V Z) c sigma delta reserve) Z ξ
    Real.logb Z R+Real.logb Z (E.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      Real.logb Z K-max (c-d) 0-2*sigma-delta-reserve+
        2*(N:ℝ)*Real.logb Z b+ξ/2 := by
  dsimp only
  have hc := norm_pos C hC
  have hd := norm_pos D hD
  have he := norm_pos E hE
  have hr := active_norm_pos C D
  have hz : 0<Z := zero_lt_one.trans hZ
  cases reflected <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals
    unfold frequencyRadius mainCommonRadius nominalLog
    rw [nominal_equal_support C D E hC hD heq K V]
    simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow,
      Real.logb_rpow hz hZ.ne']
    norm_num only [Nat.cast_ofNat]
    by_cases h : Real.logb Z (C.absNorm:ℝ)≤Real.logb Z (D.absNorm:ℝ)
    · rw [max_eq_right (show Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ)≤0 by linarith),
        max_eq_left (show 0≤Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ) by linarith)]
      ring
    · rw [max_eq_left (show 0≤Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ) by linarith),
        max_eq_right (show Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)≤0 by linarith)]
      ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_child_source_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_fourier_scale_upper

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_fourier_frequency_log
