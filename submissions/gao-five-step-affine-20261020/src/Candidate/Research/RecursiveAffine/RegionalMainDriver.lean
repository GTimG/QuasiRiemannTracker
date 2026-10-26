/- Copyright (c) 2026 Hailey Collet; modifications (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainPayment

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RegionalMain
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss Cycle63FinalNatural
open CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialMass

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance regionalMainPaymentFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The actual affine main-source driver retains a regional LOW return RL
in addition to the unchanged own-HIGH cost CH. The same original physical
selector, first masses/child volumes, two common energies, ratio image,
prime average and amplifier coefficient are used. The returned source term
is multiplied by precisely the same `Z^(3*delta-amp)` factor as own HIGH.

The continuing premise is the selected physical LOW-source bound with
a supplied regional returned scalar RL. Constructing it from a strictly
deeper source is a separate obligation. The theorem does not assume the final parent
source inequality, does not impose a global second junction on that scalar,
and does not claim the scalar has been constructed or counted. For a finite
terminal-depth family RL may be its actual weighted value. Source caps and
profile/height quantifiers remain the explicit native parent-driver domain.

Proof: native parent source operator with low coefficient CL+RL; after the
physical LOW/HIGH partition the scalar expression reassociates as
CL+(RL+CH). This is a proof implementation against native declarations,
not a checked endpoint; see the separate check scope in README. -/
theorem actual_affine_main_parent_component_payment_with_regional_returns
    [Cycle63.AffineLedger]
    (A dl dh : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤N)(B L : ℝ)(hB : 0≤B)(hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤g.μ/8)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (KL : ℝ)(hKL : 0≤KL)(Cs : ℝ)(hCs : 1≤Cs) :
    ∃Ksel : ℝ,0<Ksel ∧ ∃Cm : ℝ,0≤Cm ∧ ∃Chigh : ℝ,0≤Chigh ∧
    ∃SE : Finset (ℕ×ℕ),∃dE : ℕ,∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(s : Input T)(p : Profiles (1/4) (9/4))
      (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z)
      (η₀ : Character)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ),
      CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W 2 Z →
    ∀(R seed : Ideal O)(Mrow : ℝ),R≠0 → Squarefree seed → (R.absNorm:ℝ)≤Z^(20:ℝ) → 0≤ Mrow →
      Mrow≤1 → Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+g.μ/16 →
      (∀j,w j ≤ mesh) →
      (Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B →
    ∀beta : ℝ,beta=Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) →
    ∀(S : Finset (ℕ×ℕ))(D : ℕ),SE⊆S → dE≤D →
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height →
    ∀χ₀ : RayCharacter,
    let amp:=Cycle63.AffineLedger.amp beta
    let P:=CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^amp)
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    let low:=geometryAffineLowTarget g (Fintype.card T) amp omega mesh+(1-Mrow)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    ∀RL CH : ℝ,0≤RL → 0≤CH →
    GeometryAffineMainSelectedBranches g.δ (g.μ/64) Z amp (g.μ/8) firstHeight
      ((KL*control)*Z^low+RL) CH dl dh hZ reflected s R seed Mrow key Ψ χ₀ Qfix fixedBadMask
      caps.zero₁ caps.zero₂ →
    (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      ‖geometryMainRetainedSum reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight hZ key Mrow (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (g.μ/64) q))‖≤
      Cm*control*Z^(-((Cycle63.AffineLedger.lowReserve/2):ℝ)+(1-Mrow))+Chigh*Z^(3*g.δ-amp)*(RL+CH) := by
  obtain ⟨Ksel,hKsel,hselection⟩:=uniform_actual_affine_physical_selection (α:=α) Cs g.δ (g.μ/64) hCs
    g.δ_pos (div_nonneg g.μ_pos.le (by norm_num))
  obtain ⟨Ce,hCe,SE,dE,Co,hCo,hcontract⟩:=actual_affine_main_parent_retained_contraction (α:=α)
    M H hH A (max dl dh) (max dl dh) hc hs Sbad hbad W εaffine mesh hε hmesh
    Qfix hQ hQt hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Cs
  obtain ⟨Cb,hCb,hratio⟩:=uniform_actual_affine_main_parent_ratio_payment (α:=α) Cs εaffine g.δ hε g.δ_pos
  have hpool:=eventual_affine_cell_prime_pools M H hH Sbad hbad g.δ g.δ_pos
  refine ⟨Ksel,hKsel,Ce+Co*(56*geometryAmplifierCoefficientCap*Cb*Ksel*KL),by have := geometryAmplifierCoefficientCap_pos;positivity,
    Co*(56*geometryAmplifierCoefficientCap*Cb*Ksel),by have := geometryAmplifierCoefficientCap_pos;positivity,SE,dE,?_⟩
  filter_upwards [hselection,hcontract,hratio,hpool,eventual_geometry_small_frequency g.μ g.μ_pos]
    with Z hsel hcZ hrZ hpoolZ hfZ
  rw [←hμ] at hcZ hrZ
  refine ⟨hcZ.1,?_⟩
  intro hZ T s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot haff
    beta hbeta S D hSE hdE Ψ reflected key firstHeight height hheight χ₀ amp P omega low control RL CH hRL hCH
    hbranches
  have hside : 0<geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)
  have hcontrol : 0≤ control := by dsimp only [control];positivity
  have hcell:=Cycle63.AffineLedger.originalCell_mem hzslot
  have hb : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop := by
    rw [hbeta]
    exact Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤amp := (Cycle63.AffineLedger.amp_pos hb).le
  have hamp3 : amp≤3 := (Cycle63.AffineLedger.amp_bounds hb).2.trans
    (by linarith only [Cycle63.AffineLedger.amplifierCap_le_one])
  have hcoef:=geometry_affine_main_amplifier_bound beta hb
  have hn:=actual_affine_main_normalized_of_selected_low_high Cs g.δ (g.μ/64) Ksel Z
    ((KL*control)*Z^low+RL) CH dl dh hZ hKsel.le (by positivity) hCH (hsel T) reflected s p caps R seed Mrow
    hseed hMrow amp (g.μ/8) firstHeight key Ψ χ₀ Qfix fixedBadMask ballProfile caps.zero₁ caps.zero₂ hbranches
  let selected:=geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4)
    firstHeight (Fintype.card T) hZ key caps.zero₁ caps.zero₂
  let datum:=fun j : selected=>geometryLowSecondDatum reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8)
    (9/4) firstHeight (Fintype.card T) hZ key j.val.1 caps.zero₁ caps.zero₂ j.val.2
  let E:=Ksel*Z^g.δ*((KL*control)*Z^low+(RL+CH))
  have hE : 0≤E := by dsimp only [E];positivity
  let ratio:=∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A
  have hnorm : SecondNormalizedBound ballProfile (max dl dh) (max dl dh)
      (fun j=>ordinarySecondDatum (datum j) χ₀ Qfix fixedBadMask)
      (fun j=>geometryMainSecondWeight reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key Mrow (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (g.μ/64) q)) j.val)
      (fun _=>E) (fun _=>1) := by
    simpa only [geometryMainOrdinaryDatum,add_assoc] using hn
  have hp:=hcZ.2 hZ T s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm
    hzslot haff beta hbeta Ψ reflected key firstHeight (fun _=>χ₀) (fun _=>E) (fun _=>1)
    (fun _ _=>hE) (fun _ _=>by norm_num) (by simpa only [datum,selected] using hnorm)
  have hratioPaid : ratio≤Cb*E*Z^g.δ := by
    simpa only [ratio,datum,selected] using
      ((hrZ.2 hZ T s p caps R seed Mrow amp hseed hMrow (by linarith only [hMrow1]) hamp0 hamp3 reflected
        key firstHeight).2.1 E hE A)
  have hprime : Z^(amp-g.δ)≤(P.card:ℝ) := by
    have hh:=(hpoolZ.2 (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) hcell.1 hcell.2.1).2
    simpa only [P,amp,hbeta] using hh
  have hcount : Fintype.card T≤N :=
    (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective).trans hN
  have htargets:=affine_main_final_branch_exponents g εaffine hε hμ (Fintype.card T) N hcount
    B L amp omega mesh hB hL hδ hfZ.2.2 hmeshμ
  have hN1 : (1:ℝ)≤(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hseed.ne_zero)
  have hex : Ce*geometryAffineExceptionalShell reflected Z key*(p.control SE)^2*
      (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)≤
      Ce*control*Z^(-((Cycle63.AffineLedger.lowReserve/2):ℝ)+(1-Mrow)) := by
    rw [geometry_affine_exceptional_shell_eq (Fintype.card T) Z hZ]
    have hprofile:=pow_le_pow_left₀ (p.control_nonneg SE) (profile_control_mono p hSE) 2
    have hbase : (1+‖firstHeight‖)^dE≤(1+|firstHeight|+height)^D := by
      rw [Real.norm_eq_abs]
      exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdE)
    have hpow:=Real.rpow_le_rpow_of_exponent_le hZ.le
      (by linarith only [geometry_affine_main_reserve_half] :
        -(1/100:ℝ)+(1-Mrow)≤-((Cycle63.AffineLedger.lowReserve/2):ℝ)+(1-Mrow))
    have hh : Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control SE)^2*
        (1+‖firstHeight‖)^dE≤Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control S)^2*
        (1+|firstHeight|+height)^D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprofile (mul_nonneg hCe.le hside.le))
        hbase (pow_nonneg (by positivity) _) (by positivity)
    have hm:=mul_le_mul hh hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity)
    have hX : 0≤Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control SE)^2*
        (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ)+(1-Mrow)) := by positivity
    refine (div_le_self hX hN1).trans ?_
    convert hm using 1;dsimp only [control];ring
  exact geometry_affine_main_contracted_payment_linear Z (P.card:ℝ) amp g.δ low
    (-((Cycle63.AffineLedger.lowReserve/2):ℝ)+(1-Mrow))
    ((amplifierCap 2 0 1+6*amp)/(amp/2)) geometryAmplifierCoefficientCap Cb Ksel KL (RL+CH) Ce Co control
    _ _ ratio hZ hprime hcoef.1 hcoef.2 hCb.le hKsel.le hKL (add_nonneg hRL hCH) hCo.le hcontrol
    (by simpa only [P,amp,ratio,datum,selected,mul_assoc] using hp) hex hratioPaid
    (by dsimp only [low];linarith only [htargets.1])

end
end OAI.SevenEighths.Cycle153RegionalMain

#print axioms OAI.SevenEighths.Cycle153RegionalMain.actual_affine_main_parent_component_payment_with_regional_returns
