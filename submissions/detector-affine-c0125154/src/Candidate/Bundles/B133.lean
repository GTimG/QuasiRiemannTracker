/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B083
import Candidate.Bundles.B120
import Candidate.Bundles.B131
import Candidate.Bundles.B132
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondHighCoordinates; sha256 af3d86d908c1f55fbf52015ad77fb35e1e41776f9b76dc9cedcc096bef5ba65e -/
section
                                                  

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61Moment Cycle61HighGeometry
local notation "O" => HeckeFamily.O

/-- The actual high-source exponent coordinates: outside scalar, missing
radical, retained frequency cap, and remaining raw volume. -/
def actualHighCoordinates (reflected left second : Bool) (l : FirstSourceLabel)
    (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε : ℝ) : Fin 4→ℝ :=
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
  let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
  let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
  let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
  let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
  let g₂ := Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))
  let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
  let ω := frequencyLoss Z 32 ξ+reserve
  ![-a+(2*A-c-d+R+E-M+max (d-c) 0+6*a+ω-(A-c))+(g₂-t₂-b₂),
    Real.logb Z ((firstSourceMissing left l).absNorm:ℝ),
    M-R-max (c-d) 0+Lc-6*a-ω+ε,A-c-b₂]

/-- Exact high scalar payment in the coordinates used for joint binning. -/
theorem actual_high_coordinate_payment (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1< Z) (hb : 3401/100000≤ b ∧ b≤1/25)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤ M)
    (hA : A≤ M*Cycle61.Arithmetic.totalA b)
    (ha : a≤ M*Cycle61.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)≤
      S-M*(720486667/30493190000000)+(1-ρ)*ω+ρ*ε := by
  have hh := actual_high_scalar_payment reflected left second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a ξ reserve ε hZ hb hδ hM hA ha
  dsimp only at hh ⊢
  rw [actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hZ,
    actual_second_normalizer_power C₂ D₂ hC₂ U Z hZ] at hh
  have hz := zero_lt_one.trans hZ
  simp only [←Real.rpow_sub hz,←Real.rpow_add hz] at hh
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hh
  convert he using 1 <;> dsimp [highExponentValue,actualHighCoordinates] <;> ring

/-- Upward bin rounding keeps the strict high reserve, with an explicit loss. -/
theorem actual_high_rounded_payment (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1< Z) (hb : 3401/100000≤ b ∧ b≤1/25)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤ M)
    (hA : A≤ M*Cycle61.Arithmetic.totalA b)
    (ha : a≤ M*Cycle61.Arithmetic.amp b) (width : ℝ) (hw : 0< width) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (exponentBinUpper width (exponentBin width
      (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)))≤
      S-M*(720486667/30493190000000)+(1-ρ)*ω+ρ*ε+4*width := by
  have hh := actual_high_coordinate_payment reflected left second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a ξ reserve ε hZ hb hδ hM hA ha
  have hbnd := high_exponent_bin_payment width δ hw hδ
    (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)
  dsimp only at hh ⊢
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_coordinate_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_rounded_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondHighCoordinates -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondHighBox; sha256 7bc8e44f24620533bd44258e5d681bdcdfdc100dbf8661706cacb6492d3ca888 -/
section
                                                         
                                                       
                                                      

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSectorLocalization Cycle61Moment Cycle61HighGeometry Cycle61FinalCapacity
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

lemma ideal_log_box (I : Ideal O) (hI : I≠0) (Z B : ℝ) (hZ : 1< Z)
    (hcap : (I.absNorm:ℝ)≤ Z^B) : 0≤ Real.logb Z (I.absNorm:ℝ) ∧ Real.logb Z (I.absNorm:ℝ)≤ B := by
  exact ⟨Real.logb_nonneg hZ (norm_ge_one I hI),
    (Real.logb_le_iff_le_rpow hZ (norm_pos I hI)).mpr hcap⟩

/-- Every inactive subset has norm at most the first common ideal. -/
lemma common_subset_log_box (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (Z B : ℝ) (hZ : 1< Z)
    (hcap : (C.absNorm:ℝ)≤ Z^B) :
    0≤ Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) ∧
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤ B := by
  have hpos := firstCommonSubsetNorm_pos C D hC U
  have hrad := firstCommonSubsetNorm_pos C D hC Finset.univ
  have hd : (∏P∈U,P.val)∣∏P : CommonIndex C D,P.val :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  have hn := Nat.le_of_dvd hrad (map_dvd Ideal.absNorm hd)
  have hh := commonRadical_norm_le C D hC.1 hD.1
  rw [first_common_radical_product] at hh
  have hnorm : ((∏P∈U,P.val).absNorm:ℝ)≤ Z^B :=
    (Nat.cast_le.mpr hn).trans ((hh.trans (min_le_left _ _)).trans hcap)
  apply ideal_log_box _ _ Z B hZ hnorm
  exact Ideal.absNorm_eq_zero_iff.not.mp (Nat.ne_of_gt hpos)

/-- Coarse source-norm caps give a fixed box for all four high coordinates.
The box is independent of the source, allocations and row count. -/
theorem actual_high_coordinate_box (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε B : ℝ) (hZ : 1< Z) (hB : 0≤ B)
    (hfirst : (l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B)
    (hsecond : (C₂.absNorm:ℝ)≤ Z^B ∧ (D₂.absNorm:ℝ)≤ Z^B)
    (hM : |M|≤ B) (hA : |A|≤ B) (ha : |a|≤ B)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤ B)
    (hε : |ε|≤ B) :
    ∀i,-(32*B)≤ actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε i ∧
      actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε i≤32*B := by
  have hc₀ := ideal_log_box l.1.1 hC.1 Z B hZ hfirst.1
  have hd₀ := ideal_log_box l.1.2 hD.1 Z B hZ hfirst.2
  have hc : 0≤ Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ) ∧
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)≤ B := by
    cases reflected <;> assumption
  have hd : 0≤ Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ) ∧
      Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)≤ B := by
    cases reflected <;> assumption
  have hb₂ : 0≤ Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) ∧
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)≤ B := by
    cases second
    · exact ideal_log_box C₂ hC₂.1 Z B hZ hsecond.1
    · exact ideal_log_box D₂ hD₂.1 Z B hZ hsecond.2
  have hE := common_subset_log_box l.1.1 l.1.2 hC hD l.2.val Z B hZ hfirst.1
  change 0≤ Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ) ∧
    Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)≤ B at hE
  have ht := common_subset_log_box C₂ D₂ hC₂ hD₂ U Z B hZ hsecond.1
  obtain ⟨hp,hEp,hR₀,hpc,hpd,hRp,hLc⟩ := actual_first_gates left l hC hD Z hZ
  have hr0 : 0≤ Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    have hn : 0<(Ideal.span {activeConductor l.1.1 l.1.2}).absNorm := by
      exact_mod_cast active_norm_pos l.1.1 l.1.2
    exact_mod_cast hn
  have hl0 : 0≤ Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ) :=
    Real.logb_nonneg hZ (normValue_ge_one _ (first_source_numerator_ne_zero left l hC))
  have hmissing := first_missing_norm_le left l hC hD
  have hm := ideal_log_box (firstSourceMissing left l)
    (Ideal.absNorm_eq_zero_iff.not.mp (Nat.ne_of_gt hmissing.1)) Z B hZ
    ((Nat.cast_le.mpr hmissing.2.1).trans hfirst.1)
  have hg0 : 0≤ Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)) :=
    Real.logb_nonneg hZ (normValue_ge_one _ (commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))
  have hg := (Real.logb_le_iff_le_rpow hZ
    (normValue_pos _ (commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))).mpr
      ((actual_common_norm_le C₂ D₂ hC₂ hD₂ heq₂).trans hsecond.1)
  have hcd : 0≤ max (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) 0 ∧
      max (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) 0≤ B :=
    ⟨le_max_right _ _,max_le (by linarith [hc.2,hd.1]) hB⟩
  have hdc : 0≤ max (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) 0 ∧
      max (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) 0≤ B :=
    ⟨le_max_right _ _,max_le (by linarith [hd.2,hc.1]) hB⟩
  rcases abs_le.mp hM with ⟨hMlo,hMhi⟩
  rcases abs_le.mp hA with ⟨hAlo,hAhi⟩
  rcases abs_le.mp ha with ⟨halo,hahi⟩
  rcases abs_le.mp hω with ⟨hωlo,hωhi⟩
  rcases abs_le.mp hε with ⟨hεlo,hεhi⟩
  intro i
  fin_cases i <;> dsimp [actualHighCoordinates] <;> constructor <;>
    linarith [hc.1,hc.2,hd.1,hd.2,hb₂.1,hb₂.2,hE.1,hE.2,ht.1,ht.2,hm.1,hm.2,hcd.1,hcd.2,hdc.1,hdc.2]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.ideal_log_box
#print axioms OAI.SevenEighths.Cycle61InitialMass.common_subset_log_box
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_coordinate_box

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondHighBox -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighSelected; sha256 63da61983ed9c5489b6b01ac7f8ce109121e4f2055a24e307001d6041bc08a85 -/
section
                                                     
                                                 
                                                          
                                                         

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization Cycle61Moment Cycle61HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- The fixed lower-volume loss belongs to the outside scalar coordinate. -/
def childHighCoordinates (x : Fin 4→ℝ) (εv : ℝ) : Fin 4→ℝ :=
  fun j=>x j+if j=0 then εv else 0

lemma child_high_exponent_value (δ εv : ℝ) (x : Fin 4→ℝ) :
    highExponentValue δ (childHighCoordinates x εv)=highExponentValue δ x+εv := by
  simp [highExponentValue,childHighCoordinates]
  ring

lemma child_high_coordinate_box (x : Fin 4→ℝ) (B εv : ℝ)
    (hx : ∀j,-B≤ x j ∧ x j≤ B) :
    ∀j,-(B+|εv|)≤ childHighCoordinates x εv j ∧
      childHighCoordinates x εv j≤ B+|εv| := by
  intro j
  have hh:=hx j
  have he:=abs_le.mp (le_refl |εv|)
  by_cases hj : j=0
  · subst j
    simp only [childHighCoordinates,ite_true]
    constructor <;> linarith
  · simp only [childHighCoordinates,hj,ite_false]
    constructor <;> linarith [abs_nonneg εv]

/-- The literal child denominator is paid uniformly before the moving source.
No estimate of a high density or a selected row is assumed here. -/
theorem eventual_actual_child_high_coefficient (N : ℕ) (lo εv : ℝ)
    (hlo : 0< lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected left second : Bool) (l : FirstSourceLabel)
    (_hC : Supported l.1.1) (_hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(_hC₂ : Supported C₂)
    (U : Finset (CommonIndex C₂ D₂))(M a ξ reserve ε : ℝ),
    let x:=childHighCoordinates (actualHighCoordinates reflected left second l C₂ D₂ U
      Z M (Real.logb Z (volume s)) a ξ reserve ε) εv
    Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume
      (child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U/Z^(Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))≤ Z^(x 0) := by
  filter_upwards [eventual_common_inverse_volume N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected left second l hC hD heq Rfirst B χ t hB
    C₂ D₂ hC₂ U M a ξ reserve ε
  have hZ:=zero_lt_one.trans hz.1
  let A:=Real.logb Z (volume s)
  let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  have hc : (0:ℝ)<(if reflected then l.1.2 else l.1.1).absNorm := by
    cases reflected
    · exact norm_pos _ hC.1
    · exact norm_pos _ hD.1
  have hV : Z^A=volume s:=Real.rpow_logb hZ hz.1.ne' (volume_pos s)
  have hratio : ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)/volume s=
      (Z^(A-c))⁻¹ := by
    rw [Real.rpow_sub hZ,hV,Real.rpow_logb hZ hz.1.ne' hc,inv_div]
  have hi:=hz.2 s hcard hlow _ Rfirst B χ t hB
  rw [hratio] at hi
  have hm:=mul_le_mul_of_nonneg_left hi
    (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ l).le
  have hr : firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/
      volume (child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t)≤
      Z^εv*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c)) := by
    simpa only [div_eq_mul_inv,mul_left_comm] using hm
  have hh:=mul_le_mul_of_nonneg_left hr (Real.rpow_pos_of_pos hZ (-a)).le
  have hn:=div_nonneg (normalizer_pos C₂ D₂ hC₂ U).le
    (Real.rpow_pos_of_pos hZ (Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ))).le
  apply (mul_le_mul_of_nonneg_right hh hn).trans_eq
  rw [←hV,actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hz.1,
    actual_second_normalizer_power C₂ D₂ hC₂ U Z hz.1]
  simp only [←Real.rpow_sub hZ,←Real.rpow_add hZ]
  congr 1
  dsimp [childHighCoordinates,actualHighCoordinates,A,c]
  rw [Real.logb_rpow hZ hz.1.ne']
  ring

/-- The missing-radical bin coordinate is an exact identity. -/
lemma actual_child_high_missing (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2) (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε εv : ℝ) (hZ : 1< Z) :
    ((firstSourceMissing left l).absNorm:ℝ)=Z^((childHighCoordinates
      (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε) εv) 1) := by
  have hn:= (first_missing_norm_le left l hC hD).1
  have hp : (0:ℝ)<(firstSourceMissing left l).absNorm := by exact_mod_cast hn
  simpa [childHighCoordinates,actualHighCoordinates] using
    (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hp).symm

/-- Fixed geometric support supplies the arithmetic gates for both signs.
The remaining hypotheses are scalar caps, not analytic density estimates. -/
theorem actual_geometry_high_coordinate_gates {α : Type} [Fintype α] [DecidableEq α]
    (s : Input α)(Rseed seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : FirstColumnIndex (geometryFirstSource s Rseed seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (M A a reserve ε εv B b δ : ℝ)(hZ : 1< Z)(hB : 0≤ B)
    (hfirst : ((geometryFirstLabel s Rseed seed K Z ξ hK bin column).1.1.absNorm:ℝ)≤ Z^B ∧
      ((geometryFirstLabel s Rseed seed K Z ξ hK bin column).1.2.absNorm:ℝ)≤ Z^B)
    (hsecond : (d₂.C.absNorm:ℝ)≤ Z^B ∧ (d₂.D.absNorm:ℝ)≤ Z^B)
    (hMbox : |M|≤ B)(hAbox : |A|≤ B)(habox : |a|≤ B)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤ B)(hε : |ε|≤ B)
    (hb : 3401/100000≤ b ∧ b≤1/25)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4)(hM : 0≤ M)
    (hA : A≤ M*Cycle61.Arithmetic.totalA b)(ha : a≤ M*Cycle61.Arithmetic.amp b) :
    let l:=geometryFirstLabel s Rseed seed K Z ξ hK bin column
    let x:=childHighCoordinates (actualHighCoordinates reflected left second l d₂.C d₂.D U
      Z M A a ξ reserve ε) εv
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d:=Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E:=Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    ((firstSourceMissing left l).absNorm:ℝ)=Z^(x 1) ∧
      (∀j,-(32*B+|εv|)≤ x j ∧ x j≤32*B+|εv|) ∧
      highExponentValue δ x≤ p+A-c+R+E+max (3*c-5*d-R) 0/6-
        M*(720486667/30493190000000)+(1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+
          unmarkedDensity δ*ε+εv := by
  intro l x c d R E p
  have hC : Supported l.1.1 := (geometryFirstSource s Rseed seed K Z ξ hK bin column.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s Rseed seed K Z ξ hK bin column.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s Rseed seed K Z ξ hK bin column.1).sameSupport
  refine ⟨actual_child_high_missing reflected left second l hC hD d₂.C d₂.D U
    Z M A a ξ reserve ε εv hZ,?_,?_⟩
  · exact child_high_coordinate_box _ (32*B) εv
      (actual_high_coordinate_box reflected left second l hC hD d₂.C d₂.D d₂.hC d₂.hD
        d₂.sameSupport U Z M A a ξ reserve ε B hZ hB hfirst hsecond hMbox hAbox habox hω hε)
  · have hh:=actual_high_coordinate_payment reflected left second l hC hD heq
      d₂.C d₂.D d₂.hC d₂.hD d₂.sameSupport U Z b δ M A a ξ reserve ε hZ hb hδ hM hA ha
    rw [child_high_exponent_value]
    exact add_le_add hh (le_refl εv)

/-- Nonzero literal retention derives the third bin coordinate. Fixed unit
costs are absorbed before the first label, projector and second row move. -/
theorem eventual_actual_child_high_frequency (u₀ : O)(b ε : ℝ)(N : ℕ)
    (hb : 0< b)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀(reflected left second : Bool)(unit : FirstSourceLabel→ Oˣ)
      (l : NonzeroJointSourceLabel left u₀ (fun k=>(unit k:O)))
      (_hC : Supported l.val.1.1.1)(_hD : Supported l.val.1.1.2),
      primeSupport l.val.1.1.1=primeSupport l.val.1.1.2 →
      ∀(V M a reserve ξ εv : ℝ),0< V → ξ≤ε →
      let R:=frequencyRadius (firstMainFourierScale reflected (Z^M) V Z ξ (3*a) reserve b N l.val.1) Z ξ
      let A:=(commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
        nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
      retainedWeight R (normValue A)≠0 →
      let x:=childHighCoordinates (actualHighCoordinates reflected left second l.val.1
        l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1 Z M (Real.logb Z V) a ξ reserve ε) εv
      0≤ x 2 ∧ normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val)≤ Z^(x 2) := by
  filter_upwards [eventual_actual_joint_frequency_budget u₀ b ε N hb hε] with Z hz
  refine ⟨hz.1,?_⟩
  intro reflected left second unit l hC hD heq V M a reserve ξ εv hV hξ R A hret x
  have hp:=zero_lt_one.trans hz.1
  have hh:=hz.2 reflected left unit l hC hD heq (Z^M) V a (frequencyLoss Z 32 ξ) reserve ξ
    (Real.rpow_pos_of_pos hp M) hV hξ hret
  rw [Real.logb_rpow hp hz.1.ne'] at hh
  simpa [x,childHighCoordinates,actualHighCoordinates,normValue,sub_add_eq_sub_sub] using hh

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_child_high_coefficient
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_high_missing
#print axioms OAI.SevenEighths.Cycle61InitialMass.child_high_exponent_value
#print axioms OAI.SevenEighths.Cycle61InitialMass.child_high_coordinate_box

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_coordinate_gates

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_child_high_frequency

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighSelected -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.ScalarSupport; sha256 53334a5c20e9006e84a5171b1534a3ad243fe760770675decfa207f9bdce96bd -/
section
                                                   
                                                                     

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstReferenceSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSourceReduction CenteredMomentSourceMass
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic CenteredMomentCanonicalFirst
open CenteredMomentExceptionalAmplitudePair CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization ActualEisensteinCubic
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance scalarSupportDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The norm-aligning phase kills zero physical blocks before applying
source support. Hence the scalar bound needs no support assertion about
unused columns in a padded input pool. -/
theorem actual_phase_scalar_volume (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) (hK : 0< K)
    (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
    (q : FirstSourceCoordinate s R seed K Z ξ) :
    ‖normPhase (coordinateBlock s R seed W K Z ξ q)*
      (originalFirstBlock s R seed K Z ξ hK q).outside‖*volume s.toData≤
      (4/((∏i,s.lo i)*a₁*a₂))*K*
        Real.sqrt ((q.1.val.1.absNorm:ℝ)*q.1.val.2.absNorm)/
          (‖eisEmbedding (primeSubsetGenerator
            (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val)‖^2*
            ‖eisEmbedding (activeConductor q.1.val.1 q.1.val.2)‖) := by
  by_cases hn : coordinateBlock s R seed W K Z ξ q=0
  · simp only [hn,normPhase,norm_zero,Complex.ofReal_zero,zero_div,zero_mul]
    exact div_nonneg (mul_nonneg (mul_nonneg (div_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)) ha₁.le) ha₂.le))
        hK.le) (Real.sqrt_nonneg _)) (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  · have hh := original_scalar_volume s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
      (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) q.1.val.1 q.1.val.2
      (originalFirstBlock s R seed K Z ξ hK q).hC
      (originalFirstBlock s R seed K Z ξ hK q).hD q.2.1.val
      (originalFirstBlock s R seed K Z ξ hK q).rows W (fun _=>logAnnulus)
      K (dyadicScale (q.2.2 0)) (dyadicScale (q.2.2 1))
      (dyadicScale (q.2.2 2)) (dyadicScale (q.2.2 3)) (Real.log 4)
      hK (dyadicScale_pos _) (dyadicScale_pos _)
      (fun _ _ h=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ h) hn
    rw [Real.exp_log (by norm_num : (0:ℝ)<4)] at hh
    apply le_trans _ hh
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg _)
        (normPhase_norm (coordinateBlock s R seed W K Z ξ q)))
      (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData).le


/-- The same support bound in the geometry coordinates used by joint
Cauchy. The two common-ideal norm factors remain explicit. -/
theorem actual_phase_scalar_power (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (M Z ξ : ℝ) (hZ : 1< Z)
    (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
    (q : FirstSourceCoordinate s R seed (Z^M) Z ξ) :
    ‖normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)*
      (originalFirstBlock s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) q).outside‖≤
      (4/((∏i,s.lo i)*a₁*a₂))*Real.sqrt ((q.1.val.1.absNorm:ℝ)*q.1.val.2.absNorm)*
        Z^(outsideExponent M (Real.logb Z (volume s.toData))
          (geometryExponents s R seed (Z^M) Z ξ q)) := by
  have hz : 0< Z := zero_lt_one.trans hZ
  have hK : 0< Z^M := Real.rpow_pos_of_pos hz _
  have hV := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
  have hh := actual_phase_scalar_volume s R seed W (Z^M) Z ξ hK
    a₁ a₂ ha₁ ha₂ hs₁ hs₂ q
  have hC := (originalFirstBlock s R seed (Z^M) Z ξ hK q).hC
  let e := primeSubsetGenerator (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val
  let r := activeConductor q.1.val.1 q.1.val.2
  have he : 0<((Ideal.span {e}).absNorm:ℝ) :=
    CenteredMomentFirstScale.norm_pos _ (CenteredMomentFirstCanonicalFamily.subsetGenerator_supported
      q.1.val.1 q.1.val.2 hC q.2.1.val).1
  have hr : 0<((Ideal.span {r}).absNorm:ℝ) :=
    CenteredMomentFirstScale.active_norm_pos _ _
  have hp := outside_power (Z^M) (volume s.toData)
    ((Ideal.span {e}).absNorm:ℝ) ((Ideal.span {r}).absNorm:ℝ) Z hK hV he hr hZ
  rw [Real.logb_rpow hz hZ.ne'] at hp
  have hroot : Real.sqrt ((Ideal.span {r}).absNorm:ℝ)=‖eisEmbedding r‖ := by
    rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]
  rw [hroot,←eisEmbedding_norm_sq_eq_absNorm_span] at hp
  calc
    _ ≤ ((4/((∏i,s.lo i)*a₁*a₂))*Z^M*
        Real.sqrt ((q.1.val.1.absNorm:ℝ)*q.1.val.2.absNorm)/
        (‖eisEmbedding e‖^2*‖eisEmbedding r‖))/volume s.toData :=
      (le_div_iff₀ hV).mpr hh
    _ = (4/((∏i,s.lo i)*a₁*a₂))*
        Real.sqrt ((q.1.val.1.absNorm:ℝ)*q.1.val.2.absNorm)*
        (Z^M/(volume s.toData*‖eisEmbedding e‖^2*‖eisEmbedding r‖)) := by ring
    _ = _ := by
      rw [hp]
      congr 2
      dsimp [outsideExponent,geometryExponents,geometryNorms,geometryIdeals,e,r]
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      ring


lemma normalized_square_bound (Z o l n m C f : ℝ) (hZ : 0< Z)
    (hn : 0≤ n) (hm : 0≤ m) (hf : 0≤ f)
    (hbound : f≤ C*Real.sqrt (n*m)*Z^o) :
    f^2/Z^(2*o+l)≤ C^2*n*m/Z^l := by
  have hh := pow_le_pow_left₀ hf hbound 2
  simp only [mul_pow,Real.sq_sqrt (mul_nonneg hn hm)] at hh
  apply (div_le_div_of_nonneg_right hh (Real.rpow_nonneg hZ.le _)).trans_eq
  rw [Real.rpow_add hZ,←Real.rpow_mul_natCast hZ.le,
    show o*(2:ℕ)=2*o by norm_num;ring]
  field_simp

/-- The normalized left scalar pays the actual product of common-ideal
norms. Their later cancellation is retained in the joint source budget. -/
theorem actual_geometry_left_scalar_sq (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (M Z ξ : ℝ) (hZ : 1< Z)
    (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)) :
    ‖geometryColumnScalar false s R seed (Z^M) Z ξ M (Real.logb Z (volume s.toData))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key
      (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2≤
      (4/((∏i,s.lo i)*a₁*a₂))^2*
        (j.1.val.1.val.1.absNorm:ℝ)*j.1.val.1.val.2.absNorm/
          Z^(leftExponent (Real.logb Z (volume s.toData))
            (geometryExponents s R seed (Z^M) Z ξ j.1.val)) := by
  have hh := actual_phase_scalar_power s R seed W M Z ξ hZ a₁ a₂ ha₁ ha₂ hs₁ hs₂ j.1.val
  have hb := normalized_square_bound Z
    (outsideExponent M (Real.logb Z (volume s.toData))
      (geometryExponents s R seed (Z^M) Z ξ j.1.val))
    (leftExponent (Real.logb Z (volume s.toData))
      (geometryExponents s R seed (Z^M) Z ξ j.1.val))
    (j.1.val.1.val.1.absNorm:ℝ) (j.1.val.1.val.2.absNorm:ℝ)
    (4/((∏i,s.lo i)*a₁*a₂)) _ (zero_lt_one.trans hZ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (norm_nonneg _) hh
  simpa only [geometryColumnScalar,geometryFirstSource,Bool.false_eq_true,ite_false,norm_div,div_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)] using hb

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_phase_scalar_volume

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_phase_scalar_power

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_left_scalar_sq

end
/- END ORIGINAL Cycle61.Physical.InitialMass.ScalarSupport -/
