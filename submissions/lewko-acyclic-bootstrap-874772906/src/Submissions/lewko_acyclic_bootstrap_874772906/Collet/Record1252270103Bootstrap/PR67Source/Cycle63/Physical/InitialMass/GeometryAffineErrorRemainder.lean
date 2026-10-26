import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineRemainder
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentAmplifiedRetainedRadius EisensteinSchwartzPoisson
open CenteredMomentPrimeElements CenteredMomentAmplificationErrorEnergy RayFourExpansion
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineErrorRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

section Source
variable (s : Input ι) (R seed : Ideal O) (Ψ : 𝓢(ℝ,ℂ)) (Z Mrow amp ξ reserve t : ℝ) (hZ : 1<Z)
  (reflected : Bool) (key : ℤ×(Fin 5→ℤ)) (P : Finset (Ideal O))
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
local notation "AFIndex" => GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ hK key
variable (υ : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
    elementPool P→Fin 3→RayCharacter→ Character)
local notation "phase" => (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q))
local notation "first" => geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ hK key t
local notation "g" => (fun f : AFIndex=>geometryBranch reflected s R seed (Z^Mrow) Z ξ hK key (Subtype.val (Sigma.fst f)))
local notation "w" => (fun f : AFIndex=>geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mrow
  (Real.logb Z (volume s)) hK key phase (Fintype.card ι) (9/4) (Subtype.val (Sigma.fst f)) (Sigma.snd f))

/-- The complete extracted source before the prime average. First allocation
weights remain undivided. -/
def geometryAffineErrorSourceTotal : ℝ :=
  ∑f : AFIndex,w f*actualErrorSources (ι:=liveIndices f.2.val) (first f) (g f) Z (3*amp) 1 ξ reserve P (υ f)

/-- The exact retained term, using the original extracted Fourier cutoff. -/
def geometryAffineErrorRetainedSum : ℂ :=
  jointErrorRetained (First:=AFIndex) (fun f : AFIndex=>liveIndices f.2.val) first g w ballProfile
    Z (3*amp) ξ reserve P υ
    (fun f q i=>firstErrorTailFourier (Fintype.card ι) (9/4) (volume s)
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key (Subtype.val (Sigma.fst f)))
      q.val (errorIndex i+1)
      (firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key (Subtype.val (Sigma.fst f)))
        Z Mrow (volume s) amp (frequencyLoss Z 32 ξ) reserve q.val (errorIndex i+1)))
end Source

variable [Cycle63.AffineLedger] in
/-- All extracted zero and tail terms of a parent with puncture `R`, seed `seed` and radial scale `Z^Mrow` are paid after the single
literal prime average. The exact retained norm keeps its own 56/P factor. -/
theorem eventual_actual_affine_error_parent_remainder
    (Cs μ : ℝ) (hCs : 1≤Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀(R seed : Ideal O)(Mrow : ℝ),Squarefree seed → 0≤Mrow → Mrow≤1 →
    ∀beta : ℝ,Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop →
      Real.logb Z (volume s)≤Cycle63.AffineLedger.totalA beta →
    ∀P : Finset (Ideal O),P.Nonempty →
      (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀Q∈P,(Q.absNorm:ℝ)≤Z^(Cycle63.AffineLedger.amp beta)) →
      (∀q : elementPool P,∀i I,I∈s.slots i→ IsCoprime (Ideal.span {q.val}) I) →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
    ∀υ : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
          elementPool P→Fin 3→RayCharacter→ Character,
      (56/(P.card:ℝ))*geometryAffineErrorSourceTotal s R seed Ψ Z Mrow (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(Cycle63.AffineLedger.zeroSaving:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)+
      (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s R seed Ψ Z Mrow (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
  have hraw := eventual_actual_geometry_error_remainder (α:=ι)
    (Fintype.card ι) Cs (9/4) (1/4) (9/4) 1 3 3 (μ/64) (μ/128) (μ/128) (μ/128)
    (Cycle63.AffineLedger.zeroSaving:ℝ)
    hCs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := hraw
  let zconst := Cz*‖paperRadialFourier ballProfile 0‖
  let tconst := Ct*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  refine ⟨1+168*zconst+56*tconst,by dsimp [zconst,tconst];positivity,?_⟩
  have hpad := (tendsto_rpow_atTop (show 0<μ/128 by positivity)).eventually
    (eventually_ge_atTop (geometry (Fintype.card ι) (9/4) (9/4) (9/4)))
  filter_upwards [hraw,eventual_geometry_small_frequency μ hμ,hpad] with Z hr hfreq hpad
  intro hZ s p caps R seed Mrow hseed hMrow hMrow1 beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ
  have ha := (Cycle63.AffineLedger.amp_pos hb).le
  have haB : Cycle63.AffineLedger.amp beta≤3 := (Cycle63.AffineLedger.amp_bounds hb).2.trans (by linarith only [Cycle63.AffineLedger.amplifierCap_le_one])
  have hh := hr.2 s R seed Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1 Mrow
    (Cycle63.AffineLedger.amp beta) (μ/8) (μ/128) t (9/4) (9/4) hZ hb (by norm_num) hMrow
    (by linarith only [hMrow1]) ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) (by norm_num) (by norm_num) caps.endpoints hpad hseed hseed.ne_zero
    caps.sourcePositive caps.sourceCap caps.volumeLog caps.poolCap P hp hbad hpcap hcop reflected key υ
  have hn : (1:ℝ)≤P.card := by exact_mod_cast hne.card_pos
  have haverageNonneg : 0≤56/(P.card:ℝ) :=
    div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have haverage : 56/(P.card:ℝ)≤56 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr
    linarith
  have hzero := actual_error_zero_prime_average P Z (μ/128) hne hZ (by positivity) hp hbad
  have hz := geometry_affine_zero_loss Z μ (Real.logb Z (volume s)) beta Mrow hμ hcap
    (abs_le.mp caps.volumeLog).2 hb hfreq.2.2
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hz
  have htail := Real.rpow_le_rpow_of_exponent_le hZ.le
    (by linarith only [hMrow1] : -(Cycle63.AffineLedger.zeroSaving:ℝ)≤
      -(Cycle63.AffineLedger.zeroSaving:ℝ)+(1-Mrow))
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hseedNorm : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed.ne_zero)
  have hzconst : 0≤zconst := by dsimp [zconst];positivity
  have htconst : 0≤tconst := by dsimp [tconst];positivity
  have hzavg := mul_le_mul hzero hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by norm_num : (0:ℝ)≤168)
  have htavg := mul_le_mul haverage htail (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by norm_num : (0:ℝ)≤56)
  have h₁ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzavg
    (mul_nonneg (mul_nonneg hzconst (sq_nonneg (p.control {(0,0)}))) hside)) hseedNorm.le
  have h₂ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htavg
    (mul_nonneg (mul_nonneg htconst (sq_nonneg (p.control {(0,0)}))) hside)) hseedNorm.le
  have hrest : 0≤(p.control {(0,0)})^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
      Z^(-(Cycle63.AffineLedger.zeroSaving:ℝ)+(1-Mrow))/(seed.absNorm:ℝ) := by
    positivity
  have hnorm : geometryAffineErrorSourceTotal s R seed Ψ Z Mrow (Cycle63.AffineLedger.amp beta) (μ/64) (μ/8)
      t hZ reflected key P υ≤
      zconst*(p.control {(0,0)})^2*errorZeroPrimeWeight Z (μ/128) P*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(zeroPaymentExponent Z 1 Mrow (Real.logb Z (volume s)) (Cycle63.AffineLedger.amp beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))/(seed.absNorm:ℝ)+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(Cycle63.AffineLedger.zeroSaving:ℝ))/(seed.absNorm:ℝ)+
      ‖geometryAffineErrorRetainedSum s R seed Ψ Z Mrow (Cycle63.AffineLedger.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
    convert hh using 1 <;>
      simp only [geometryAffineErrorSourceTotal,geometryAffineErrorRetainedSum,
        geometryLowFirstChild,zconst,tconst];
      first | rfl | (ring_nf; rfl)
  have hnorm' := mul_le_mul_of_nonneg_left hnorm haverageNonneg
  simp only [div_eq_mul_inv] at h₁ h₂ hrest hnorm' ⊢
  nlinarith only [hnorm',h₁,h₂,hrest]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
