/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine corrected exceptional child estimate pays the physical block.
Only finite polynomial caps and the original character-family identity enter;
the full allocation count, frozen weights, divisor seed and row selector remain. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.SelectedExceptionalNormalizedMaskedPhysical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondEffectiveScalar
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalNormalizedMasked
noncomputable section
open OAI OAI.SevenEighths OAI.SevenEighths.Record1252270103Source
open Filter ExceptionalWindow
open scoped Classical BigOperators SchwartzMap
open Record1252270103Second Record1252270103GlobalSelected
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentFirstSectors
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondSectorColumns CenteredMomentSecondNonexceptional
open CenteredMomentSecondWholeKernel CenteredMomentSecondSectorRetained CenteredMomentSecondWindowBudget
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentMobiusRegroup RayFourExpansion
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile CenteredMomentSourceProfileMass
open ConcretePrimeRowBridge CenteredExceptionalProfile CenteredMomentChildRows CenteredMomentSecondHeightFamily
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open QRH.Record1252270103Source.ForcedCost
local notation "O"=>ActualEisensteinCubic.O
local notation "coefficient"=>QRH.Record1252270103Source.High.CoupledFirst.coefficient
open SecondSectorDatum High.GlobalPhysical Admission.SelectedSecondNatural Cycle61InitialMass
open CenteredMomentFirstAmplificationChoice CenteredMomentEnergyChildState
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance selectedExceptionalFamilySum {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {α:Type*} [Fintype α]


open QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
open QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
open OAI.SevenEighths.Record1252270103Source.ExceptionalWindow

/-- Payment on the same original CompleteFamily, before any radical or
harmonic summation. The effective phase remains the actual normalized phase. -/
def familyPayment {Label:Type*}{slots:Label→Finset α}{W:𝓢(ℝ,ℂ)}{Z:ℝ}
    (f:CorrectedFamilyData slots W Z)(rad:CorrectedFamilyData.RadialData f)(Q:Ideal O)
    (J:Finset α→ℕ)(T:Finset α→Finset (ℕ×ℕ))(C₀ K₀ Cphys:Finset α→ℝ)
    (ε εL power:ℝ)(decay:ℕ)(q:f.Carrier):ℝ :=
  datumPayment (f.datum Q q) (T (slots q.1)) (f.W₁ q.1) (f.W₂ q.1) (rad.profile q) Q
    Z ε εL power (rad.scale q) (rad.upper q) (rad.rawLower q)
    (C₀ (slots q.1)) (K₀ (slots q.1)) (Cphys (slots q.1)) (J (slots q.1)) decay

/-- Genuine masked fixed-Q exceptional bound for the complementary original
family. Constants are fixed before all moving data. The only hypotheses are
literal support/polynomial Caps, supplied on initial data by the checked
canonical constructor; no energy or physical norm assumption is used. -/
theorem exceptional_complete_family_radical
    (W:𝓢(ℝ,ℂ))(decay:ℕ)
    (a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell power B:ℝ)(depth:ℕ)
    (ha:0<a)(hb:0≤b)(hε:0<ε)(hεL:0<εL)
    (hBχ:0≤Bη+BR+Bfreq+BH+1)(hBA:0≤BA)(hBpool:0≤Bpool)
    (hell:0<ell)(hpower0:0≤power)(hpower:power<1/2):
    ∃J:Finset α→ℕ,∃T:Finset α→Finset (ℕ×ℕ),(∀A,(0,0)∈T A) ∧
    ∀Q:Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→
    ∃C₀ K₀ Cphys:Finset α→ℝ,
      (∀A,0<C₀ A ∧ 0<K₀ A ∧ 0≤Cphys A) ∧
    ∀Z:ℝ,1<Z→
    ∀{Label:Type*}[Fintype Label](slots:Label→Finset α)(f:CorrectedFamilyData slots W Z),
    f.rowMask≠0→goodLambda∣f.rowMask→(2:O)∣f.rowMask→
    ∀rad:CorrectedFamilyData.RadialData f,
    PolynomialCaps f rad Q a b Bη BR Bfreq BH BA Bpool Bplain BD ell B depth→
    ‖∑q,f.phase Q q*(f.block Q q).value W‖≤
      ∑q,‖secondEffectiveWeight (f.block Q) (f.phase Q) W q‖*
        familyPayment f rad Q J T C₀ K₀ Cphys ε εL power decay q := by
  have hp(A:Finset α):=masked_exceptional_physical_from_caps (ι:=A) W decay
    a b ε εL Bη BR Bfreq BH BA Bpool Bplain BD ell power depth
    ha hb hε hεL hBχ hBA hBpool hell hpower0 hpower
  choose J T hT hp using hp
  refine ⟨J,T,hT,?_⟩
  intro Q hQ0 hQ hQ72
  choose C₀ hC₀ K₀ Cphys hK₀ hCphys hp using fun A=>hp A Q hQ0 hQ hQ72
  refine ⟨C₀,K₀,Cphys,fun A=>⟨hC₀ A,hK₀ A,hCphys A⟩,?_⟩
  intro Z hZ Label inst slots f hm hmLam hm2 rad hc
  rw [actual_second_effective_sum (f.block Q) (f.phase Q) W]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  let d:=f.datum Q q
  have hg:=exceptional_original_gates slots f.input f.modifier f.puncture f.seed
    f.physicalScale f.sectorScale Z f.mesh W f.seed_squarefree f.zero₁ f.zero₂ f.physical_pos
    f.referenceRay Q f.rowMask q
  have hf:∀χ:RayCharacter,∀I:Ideal O,Supported I→(IsCoprime d.C I∨IsCoprime d.D I)→
      ∀v:ℝ,heightCoeff (d.τ χ) v I=heightCoeff d.input.η v I*
        idealRowHom d.block.frequency I*rayCharacter χ (primaryGenerator I):=d.family.height_eq
  have hex:∀z∈d.rows,FixedInducingRow (childCharacter d.input.η (f.referenceRay q.1)) Q f.rowMask d.block.frequency z:=
    exceptional_rows_fixed slots f.input f.modifier f.puncture f.seed f.physicalScale f.sectorScale Z f.mesh W
      f.seed_squarefree f.zero₁ f.zero₂ f.physical_pos f.referenceRay Q f.rowMask q
  have cc:=hc q
  have hh:=hp d.slots (f.W₁ q.1) (f.W₂ q.1) cc.support1 cc.support2 d.input cc.profile1 cc.profile2 cc.scales
    Z hZ d.input.η d.τ d.input.t (f.A₁ q.1) (f.A₂ q.1) (f.frozen q.1) (f.marked q.1) d.R d.seed (f.pool q.1)
    d.C d.D d.hC d.hD hg.2.2.1 hg.2.2.2 d.sameSupport hg.1
    d.inactive hf d.radius d.rows f.rowMask (f.referenceRay q.1) hm hmLam hm2 d.rows_ne hex
    (rad.profile q) (rad.scale q) (rad.upper q) cc.radial_pos cc.brad_nonneg cc.radial_nonneg
    cc.radial_support cc.radial_major cc.character_cap cc.frequency_cap cc.height_cap cc.fixed_cap
    (rad.rawLower q) cc.raw_pos cc.raw_X1 cc.raw_X2 cc.raw_Y1 cc.raw_Y2 cc.allocations d.K d.K_pos d.dyad
  apply hh.trans
  change _≤datumPayment d (T d.slots) (f.W₁ q.1) (f.W₂ q.1) (rad.profile q) Q
    Z ε εL power (rad.scale q) (rad.upper q) (rad.rawLower q) (C₀ d.slots) (K₀ d.slots) (Cphys d.slots) (J d.slots) decay
  unfold datumPayment
  apply div_le_div_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · unfold radicalDivisorSum
      apply Finset.sum_le_sum
      intro L hL
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact masked_paired_window_common_radical d.input d.C d.D d.R d.R d.hC.1 d.hD.1 d.sameSupport
        (T d.slots) (f.W₁ q.1) (f.W₂ q.1) (rad.profile q) Q L d.inactive
        Z ε εL power (rad.rawLower q) (rad.upper q) (Real.logb Z (rad.scale q)) (C₀ d.slots) (K₀ d.slots)
        (J d.slots) d.input.t hpower0 (zero_lt_one.trans hZ).le cc.brad_nonneg (hK₀ d.slots).le
    · have hn:0≤normalizer d.C d.D d.inactive:=(normalizer_pos d.C d.D d.hC d.inactive).le
      have ho:0≤outerScalar d.C d.D d.K d.dyad:=by have hK:=d.K_pos;unfold outerScalar;positivity
      exact mul_nonneg (hCphys d.slots) (mul_nonneg ho hn)
  · exact pow_nonneg (add_nonneg zero_le_one
      (div_nonneg (mul_nonneg (dyadicScale_pos _).le (dyadicScale_pos _).le)
        (mul_nonneg (dyadicScale_pos _).le (dyadicScale_pos _).le))) _
end
end QRH.Record1252270103Source.Low.SelectedExceptionalNormalizedMasked
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalizedMasked.exceptional_complete_family_radical
