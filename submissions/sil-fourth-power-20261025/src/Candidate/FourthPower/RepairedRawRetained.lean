/- Copyright (c) 2026 Sil. Apache-2.0.
Generic RAW nonexceptional block and finite retained assembly. These lemmas
consume the explicit already supplied normalized block contract; the Root
lane must instantiate that contract from its genuine centered admissions.
No old restored-root constructor or normalized supplier cost is imported.

-/
import Candidate.FourthPower.RepairedRawColumnBudget
import Candidate.FourthPower.RepairedGroupedConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedRawRetained
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentHeckeColumnWindow CenteredMomentFirstAmplificationChoice
open MixedSupplierOriginalFrequency
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar CenteredMomentSectorLocalization
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFirstSectors CenteredMomentActiveSource
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockHarmonicMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiveNormalization
open MixedSupplierFourthRow MixedSupplierSource
open MixedSupplierPositive MixedSupplierOuterActive MixedInnerExceptionalBlock
open MixedFirstExceptionalNormalization MixedFirstGeometricCaps MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalLedger
open OuterFreshWindowPair OuterFreshRows OuterFreshConsumer OuterFreshNonexceptionalBlock
open OuterFreshSelected OuterFreshCutoffAllowance OuterFreshRootAdmission OuterFreshDeclaredMass
open OuterFreshSelectedKernel OuterFreshAllocationMass
open RepairedRawReference RepairedRawColumnBudget RepairedGroupedConsumer
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ:=Classical.decEq _
variable {ι:Type u}[Fintype ι]{a b:ℝ}

/-- Actual sharp column support is obtained from a NONZERO member of the
same selected sum. The normalized block contract is explicit here; this is
an adapter, not a claim that the Root lane's analytic input is automatic. -/
theorem raw_block_of_normalized
    (q:Data ι)(x:Frozen q)(hP:∀i,0<q.P i)(r:Source (RestIndex q) a b)
    (ha:0<a)(hm:Matches q x r ha)(seed:Id)(η τ:Character)(ξ χ₀:RayCharacter)(Q:Id)
    (C₁ D₁:Id)(hC₁:Supported C₁)(hD₁:Supported D₁)(hCD₁:CompletedGauss.primeSupport C₁=CompletedGauss.primeSupport D₁)
    (E₁:Finset (CommonIndex C₁ D₁))(Kroot Vroot Z θ:ℝ)
    (hKroot:0<Kroot)(hVroot:0<Vroot)(hZ:1<Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C₁ D₁=>P.val) E₁*activeConductor C₁ D₁})
    (n₁:ℤ)(C₂ D₂:Id)(hC₂:Supported C₂)(hD₂:Supported D₂)(U:Finset (CommonIndex C₂ D₂))
    (n₂:Fin 4→ℤ)(tp radius gain C B δ εw εa Kslot t₀ V:ℝ)
    (hC:0≤C)(hδ:0≤δ)(hKslot:0≤Kslot)(hV:0≤V)
    (hCcap:(C₂.absNorm:ℝ)≤Z^B)(hDcap:(D₂.absNorm:ℝ)≤Z^B)
    (N degree:ℕ)(control:Finset (ℕ×ℕ))
    (hblock:
      let Kchild:=nominalChildScale C₁ D₁ E₁ Kroot Vroot Z θ n₁
      let Rdecl:=declaredWidth q η Kroot Z (deficit C₁ D₁ E₁ Kroot Vroot Z n₁)
        (Real.logb Z (C₁.absNorm:ℝ)) θ C₂ D₂ U
      let H:=heightCoeff τ tp C₂*star (heightCoeff τ tp D₂)
      Z^gain*‖normalization (r.X₁*r.X₂) r.P‖^2*
        ‖H*physicalAverage q x r seed τ ξ χ₀ Q C₂ D₂ hC₂ hD₂ U tp radius ballProfile Kchild n₂‖≤
      C*(outerScalar C₂ D₂ Kchild n₂*normalizer C₂ D₂ U)*
        (‖H‖*(Z^εa*Real.sqrt (((C₂.absNorm:ℝ)^δ*(rootFactor r/(C₂.absNorm:ℝ)))*
          ((D₂.absNorm:ℝ)^δ*(rootFactor r/(D₂.absNorm:ℝ))))*
          angleEnvelope r 1 Kslot N degree control t₀ tp V Z Rdecl εw))) :
    let Kchild:=nominalChildScale C₁ D₁ E₁ Kroot Vroot Z θ n₁
    let H:=heightCoeff τ tp C₂*star (heightCoeff τ tp D₂)
    Z^gain*‖H*physicalAverage q x r seed τ ξ χ₀ Q C₂ D₂ hC₂ hD₂ U tp radius ballProfile Kchild n₂‖≤
      C*(firstReference q τ C₁ Vroot*rawProfileRoot r*profileCore r Kslot N degree control t₀ tp V)*
        Z^(4*θ+εw+εa+2*B*δ)*pairWeight C₂ D₂ := by
  let Kchild:=nominalChildScale C₁ D₁ E₁ Kroot Vroot Z θ n₁
  let H:=heightCoeff τ tp C₂*star (heightCoeff τ tp D₂)
  let P:=physicalAverage q x r seed τ ξ χ₀ Q C₂ D₂ hC₂ hD₂ U tp radius ballProfile Kchild n₂
  have hbase:0≤firstReference q τ C₁ Vroot*rawProfileRoot r*profileCore r Kslot N degree control t₀ tp V:=
    mul_nonneg (mul_nonneg (firstReference_nonneg q hP τ C₁ Vroot) (rawProfileRoot_nonneg r))
      (profileCore_nonneg r Kslot N degree control t₀ tp V hKslot hV)
  change Z^gain*‖H*P‖≤_
  by_cases hzero:H*P=0
  · simp only [hzero,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hbase)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) (pairWeight_nonneg _ _)
  have hPn:P≠0:=right_ne_zero_of_mul hzero
  obtain ⟨y,hy,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hPn
  have hcols:=actual_outer_column_scales q x y r ha hm seed τ ξ C₂ D₂ hC₂ hD₂ U tp radius
    (outerRows false q x y τ ξ χ₀ Q C₂ D₂ U radius) ballProfile Kchild n₂ (right_ne_zero_of_mul hterm)
  have hbudget:=actual_block_sharp_budget_le q hP r ha η τ C₁ D₁ hC₁ hD₁ hCD₁ E₁
    Kroot Vroot Z θ hKroot hVroot hZ hmod n₁ C₂ D₂ hC₂ hD₂ U n₂ hcols.1 hcols.2
    B δ εw εa Kslot hδ hKslot hCcap hDcap N degree control t₀ tp V hV
  have hnorm:‖normalization (r.X₁*r.X₂) r.P‖^2=1/sourceVolume r:=
    normalization_sq (r.X₁*r.X₂) (mul_pos (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂))
      r.P (fun i=>zero_lt_one.trans_le (r.hP i))
  have hpaid:Z^gain*‖normalization (r.X₁*r.X₂) r.P‖^2*‖H*P‖≤
      C*((firstReference q τ C₁ Vroot*rawProfileRoot r*profileCore r Kslot N degree control t₀ tp V/sourceVolume r)*
        Z^(4*θ+εw+εa+2*B*δ)*pairWeight C₂ D₂) := by
    apply hblock.trans
    convert mul_le_mul_of_nonneg_left hbudget hC using 1 <;> (try dsimp only [rawProfileRoot]) <;> ring
  rw [hnorm] at hpaid
  have hh:(Z^gain*‖H*P‖)/sourceVolume r≤
      (C*(firstReference q τ C₁ Vroot*rawProfileRoot r*profileCore r Kslot N degree control t₀ tp V)*
        Z^(4*θ+εw+εa+2*B*δ)*pairWeight C₂ D₂)/sourceVolume r := by
    convert hpaid using 1 <;> (try dsimp only [rawProfileRoot,H,P,Kchild]) <;> ring
  exact (div_le_div_iff_of_pos_right (sourceVolume_pos r)).mp hh

/-- Exact selected grouping before the common/unit/dyadic triangle.
The padded selected scale is restored once; no sourceVolume is divided. -/
theorem selected_sum_le_blocks (q:Data ι)(x:Frozen q)(hqP:∀i,0<q.P i)
    (r:Source (RestIndex q) a b)(seed:Id)(τ:Character)(ξ χ₀:RayCharacter)(Q:Id)
    (tp K T Z ζ H:ℝ)(Φ:𝓢(ℝ,ℂ)) :
    ‖selectedSum q x τ (fun y=>fixedPart false q x y r seed τ ξ χ₀ Q tp Φ K T Z ζ H)‖≤
      MixedSelectedVolume.scale q*
        ∑p:FixedLabel (fixedPool q x r seed),∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,
          ‖(heightCoeff τ tp p.val.1*star (heightCoeff τ tp p.val.2))*
            physicalAverage q x r seed τ ξ χ₀ Q p.val.1 p.val.2
              (commonLabels_supported _ _ _ p.property).1 (commonLabels_supported _ _ _ p.property).2 U
              tp (frequencyRadius T Z ζ) Φ K (fun i=>(n i:ℤ))‖ := by
  have hs:0≤MixedSelectedVolume.scale q:=(MixedSelectedVolume.scale_pos q hqP).le
  unfold selectedSum
  rw [selected_fixed_parts false]
  simp_rw [←scale_mul_physical_average q x hqP r seed τ ξ χ₀ Q]
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hs]
  apply le_of_eq
  ring

/-- Uniform finite assembly of supplied RAW physical blocks. The block
estimate remains an explicit upstream interface, discharged by
raw_block_of_normalized after the Root lane invokes its analytic supplier.
The genuine seed harmonic mass is proved internally for the actual columns.
-/
theorem uniform_raw_retained_from_blocks (B Lrad Cr εmass:ℝ)
    (hB:0≤B)(hL:0≤Lrad)(hCr:0<Cr)(hε:0<εmass) :
    ∃Cmass:ℝ,0<Cmass ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(κ:Type u)[Fintype κ],∀q:Data κ,∀x:Frozen q,∀hqP:∀i,0<q.P i,
    ∀a b:ℝ,∀r:Source (RestIndex q) a b,∀ha:0<a,Matches q x r ha→
    ∀seed:Id,Squarefree seed→sourceNormCap r.P b r.T r.d≤Z^B→
    ∀(τ:Character)(ξ χ₀:RayCharacter)(Q:Id)(tp K T ζ H gain A:ℝ),
      0<K→frequencyRadius T Z ζ≤Cr*Z^Lrad→H≤Z^B→0≤A→
    (∀p:FixedLabel (fixedPool q x r seed),∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,
      Z^gain*‖(heightCoeff τ tp p.val.1*star (heightCoeff τ tp p.val.2))*
        physicalAverage q x r seed τ ξ χ₀ Q p.val.1 p.val.2
          (commonLabels_supported _ _ _ p.property).1 (commonLabels_supported _ _ _ p.property).2 U
          tp (frequencyRadius T Z ζ) ballProfile K (fun i=>(n i:ℤ))‖≤A*pairWeight p.val.1 p.val.2)→
    Z^gain*‖selectedSum q x τ (fun y=>fixedPart false q x y r seed τ ξ χ₀ Q tp ballProfile K T Z ζ H)‖≤
      Cmass*MixedSelectedVolume.scale q*A*Z^εmass/(seed.absNorm:ℝ) := by
  obtain ⟨Cmass,hCmass,hmass⟩:=actual_block_harmonic_mass B Lrad Cr εmass hB hL hCr hε
  refine ⟨Cmass,hCmass,?_⟩
  filter_upwards [hmass,eventually_gt_atTop (1:ℝ)] with Z hmassZ hZ
  refine ⟨hZ,?_⟩
  intro κ instκ q x hqP a b r ha hm seed hseed hcap τ ξ χ₀ Q tp K T ζ H gain A hK hrad hH hA hpoint
  let β:=commonColumn q x seed
  have hcoeff (I:Id)(hn:β I≠0):sourceCoefficient r ha seed I≠0 := by
    have he:=common_coefficient q x r ha hm seed I
    change commonColumn q x seed I≠0 at hn
    rw [he] at hn
    exact right_ne_zero_of_mul hn
  have hseedI (I:Id)(_hI:I∈sourceColumns r)(hn:β I≠0):seed∣I:=
    source_coefficient_seed r ha seed I (hcoeff I hn)
  have hnorm (I:Id)(_hI:I∈sourceColumns r)(hn:β I≠0):(I.absNorm:ℝ)≤Z^B:=
    (original_coefficient_cap r ha seed I (hcoeff I hn)).2.trans hcap
  have hm:=hmassZ seed hseed hseed.ne_zero (sourceColumns r) β hseedI hnorm K
    (frequencyRadius T Z ζ) H hK hrad hH
  have hsum:(∑p:FixedLabel (fixedPool q x r seed),∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,pairWeight p.val.1 p.val.2)≤
      Cmass*Z^εmass/(seed.absNorm:ℝ) := by
    simp only [ActiveBlocks,ActiveSubsets,Fintype.sum_sigma] at hm
    convert hm using 1 <;> rfl
  have htriangle:=selected_sum_le_blocks q x hqP r seed τ ξ χ₀ Q tp K T Z ζ H ballProfile
  have hz:0<Z:=zero_lt_one.trans hZ
  have hscale:0≤MixedSelectedVolume.scale q:=(MixedSelectedVolume.scale_pos q hqP).le
  calc
    _≤Z^gain*(MixedSelectedVolume.scale q*
        ∑p:FixedLabel (fixedPool q x r seed),∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,
          ‖(heightCoeff τ tp p.val.1*star (heightCoeff τ tp p.val.2))*
            physicalAverage q x r seed τ ξ χ₀ Q p.val.1 p.val.2
              (commonLabels_supported _ _ _ p.property).1 (commonLabels_supported _ _ _ p.property).2 U
              tp (frequencyRadius T Z ζ) ballProfile K (fun i=>(n i:ℤ))‖):=
      mul_le_mul_of_nonneg_left htriangle (Real.rpow_nonneg hz.le _)
    _=MixedSelectedVolume.scale q*
        ∑p:FixedLabel (fixedPool q x r seed),∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,
          Z^gain*‖(heightCoeff τ tp p.val.1*star (heightCoeff τ tp p.val.2))*
            physicalAverage q x r seed τ ξ χ₀ Q p.val.1 p.val.2
              (commonLabels_supported _ _ _ p.property).1 (commonLabels_supported _ _ _ p.property).2 U
              tp (frequencyRadius T Z ζ) ballProfile K (fun i=>(n i:ℤ))‖ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤MixedSelectedVolume.scale q*
        ∑p:FixedLabel (fixedPool q x r seed),∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,A*pairWeight p.val.1 p.val.2:=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _=>Finset.sum_le_sum
        (fun U _=>Finset.sum_le_sum (fun n _=>hpoint p U n)))) hscale
    _=(MixedSelectedVolume.scale q*A)*
        (∑p:FixedLabel (fixedPool q x r seed),∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,pairWeight p.val.1 p.val.2):=by
      simp only [Finset.mul_sum,mul_assoc]
    _≤(MixedSelectedVolume.scale q*A)*(Cmass*Z^εmass/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hscale hA)
    _=_:=by ring

/-- Cancel the internally paid gain only after all common/divisor/cutoff
losses are included in extra. The outer harmless window loss remains. -/
theorem cancel_gain (Z gain window extra E B:ℝ)(hZ:1<Z)(hB:0≤B)
    (hpaid:extra≤gain)(h:Z^gain*E≤B*Z^(window+extra)) : E≤B*Z^window := by
  have hz:=zero_lt_one.trans hZ
  have hg:=Real.rpow_pos_of_pos hz gain
  apply (mul_le_mul_iff_right₀ hg).mp
  apply h.trans
  have hexp : window+extra≤window+gain := by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le hexp
  apply (mul_le_mul_of_nonneg_left hp hB).trans_eq
  rw [Real.rpow_add hz]
  ring

end
end Candidate.FourthPower.RepairedRawRetained

