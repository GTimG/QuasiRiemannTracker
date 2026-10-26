import Candidate.Target830.Source.Reconstruction.GeometryAmplifiedRemainder
import Candidate.Target830.Source.Error.Main
import Candidate.Target830.Source.ErrorReconstruction.Parameters
import Candidate.Target830.Source.Reconstruction.GeometryAffineExceptionalGates
import Candidate.Target830.Source.ErrorReconstruction.GeometryAffineErrorSpecs
import Candidate.Target830.Source.ErrorReconstruction.GeometryAffineErrorAggregate
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorJointNormalizedTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorAbsoluteBox
import Candidate.Target830.Source.Assembly.InitialHeight
import Candidate.Affine.Supply
import Candidate.Target830.Source.Assembly.SourceMesh
import Candidate.Target830.Physical.AffineInput
import Candidate.Target830.High.MainUniform
import Candidate.Target830.Source.Assembly.PaidComponents
import Candidate.Target830.Source.ErrorReconstruction.GeometryAffineErrorCompletePayment

/- Original module: Candidate.Target830.Source.ErrorReconstruction.GeometryAffineErrorFamily. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Target830.Source.ErrorReconstruction
open OAI.SevenEighths.Cycle63InitialMass
open OAI.SevenEighths.Target830.Source
noncomputable section
variable {plane : SourcePlane}
open OAI.SevenEighths.Target830.Source.Reconstruction
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentPrimeElements CenteredMomentAllocatedRayDictionary CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAnnularInput
open RayFourExpansion Cycle63Moment CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle63InitialSource CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable
attribute [local irreducible] Finset.univ SecondInputDatum.block geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild geometryJointErrorDatum geometryJointErrorWeight
  geometryJointErrorRawNormalizedSource geometryJointErrorPhysicalScalarCost geometryJointErrorRawScalarLabelSum

variable {α : Type} [Fintype α]
section Zero
variable (reflected : Bool)(s : Input α)(R seed : Ideal O)
  (Z M amp ξ reserve b t : ℝ)(hZ : 1 < Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
  (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→Character)
  (Mprice Aprice : ℝ)(weight : Cycle63JointSource.SourceCoordinate s R seed (Z^M) Z ξ→ℂ)
  (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
local notation "Sources" => GeometryJointErrorSourceIndex (reflected:=reflected) (s:=s) (R:=R) (seed:=seed)
  (Z:=Z) (M:=M) (ξ:=ξ) (t:=t) (hZ:=hZ) (key:=key) (P:=P)
local notation "Selected" => GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂

/-- Zero first coefficients contribute zero without removing original labels. -/
theorem affine_error_family_raw_source_zero
    (χ : Selected→RayCharacter)(Q : Ideal O)(W : 𝓢(ℝ,ℂ))(side : Bool)(te u : ℝ)(l : Sources)
    (hzero : geometryAllocationWeight reflected s R seed (Z^M) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key weight (Fintype.card α) b l.1.1.val l.1.2=0) :
    geometryJointErrorRawNormalizedSource reflected s R seed Z M amp ξ reserve b t hZ key P υ
      Mprice Aprice weight hz₁ hz₂ χ Q W side te u l=0 := by
  rw [geometry_joint_error_raw_source]
  unfold OAI.SevenEighths.Cycle63InitialMass.geometryErrorRawNormalizedSum
  simp only [hzero,OAI.SevenEighths.Cycle63InitialMass.errorNormalizedCoefficient,
    mul_zero,zero_mul,zero_div,Complex.ofReal_zero]
  exact actual_geometry_error_zero_normalized_sum _ _ _ _ _
end Zero


open CenteredMomentNaturalFixedRaySource CenteredMomentSecondInputCapacitySource
variable (rayM : Ideal O) [NeZero rayM]
local instance affineErrorFamilyFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The actual complete error family is uniform before all moving source data. -/
theorem actual_affine_error_normalized_family
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβ : 51/100 ≤ HeckeZeroSupremum.beta)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(Q : Ideal O)(hQM : Q ≤ rayM)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)(hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (εaffine mesh : ℝ)(hε : 0 < εaffine)(hmesh0 : 0 ≤ mesh)
    (hmesh : mesh < Source.amplifierMinimum/2)
    (hmeshμ : mesh ≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh ≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8)) :
    ∀T : Finset α,∃degree windowDegree dN : ℕ,∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0 ≤ Cn ∧
      ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec (plane:=plane) rayM H hH Sbad W hW.continuous hWs Ψ ηseed η₀ mesh εaffine T
          degree windowDegree (internalQ Q η₀) SN dN Cn Z := by
  let μ:=geometryLossUnit 1 εaffine
  let N:=Fintype.card α
  let L₂:=3*((N:ℝ)+2)
  let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 L₂ N
  have hμ : 0 < μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ ≤ 1/128 := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ : 0 < δ:=(geometry_final_dictionary_budgets μ 31 3 4 3 130 L₂ N hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by dsimp [L₂];positivity)).1
  have hδcap : δ ≤ μ/8 := by
    have hh:=(geometry_final_dictionary_budgets μ 31 3 4 3 130 L₂ N hμ
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by dsimp [L₂];positivity)).2.2.1
    linarith only [hh,hμ]
  obtain ⟨Cs,hCs,hcaps⟩:=Source.LowPhysical.eventual_actual_affine_exceptional_source_gates (α:=α) rayM H hH W hW.continuous hWs
  obtain ⟨K,hK,hscalar⟩:=eventual_actual_affine_error_normalized_scalar_schedule (plane:=plane) (α:=α) rayM H hH
    Sbad hbad W hW.continuous hWs εaffine mesh hε hmesh
  obtain ⟨Cb,hCb,hbox⟩:=eventual_actual_geometry_error_absolute_box N 130 1 (9/4) (9/4) (μ/64) δ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith only [hμcap]) hδ
  intro T
  let : DecidableEq T:=Classical.decEq T
  obtain ⟨degree,Sp,hmenu⟩:=actual_finiteT_affine_error_normalized_menu (plane:=plane) (α:=α) rayM H hH W hWs hW T
    ηseed μ Cs hμ hCs hβ
  obtain ⟨Cg,hCg,hpaid⟩:=hmenu η₀ Q hQM hQ hQt hQ72
  let ray:ℝ:=(Fintype.card RayCharacter:ℝ)^2
  let lower:=lowerFactor N 1 (1/4)
  have hlower : 0 < lower:=lowerFactor_pos N 1 (1/4) (by norm_num) (by norm_num)
  let Cn:=ray*Cg*(2+4*Real.pi)^degree*(Cb/lower)*16*K
  have hCn : 0 ≤ Cn := by dsimp [Cn,ray];positivity
  refine ⟨degree,degree,degree,Sp,Cn,hCn,?_⟩
  filter_upwards [hcaps,hscalar,hpaid,hbox,eventual_geometry_small_frequency μ hμ,
    eventual_actual_geometry_affine_error_puncture_of_scales N,
    eventual_actual_affine_error_prime_width (plane:=plane) rayM H Sbad hbad,
    OAI.SevenEighths.Target830.Source.Reconstruction.eventual_actual_affine_exceptional_child_coprime (plane:=plane)
      rayM H hH Sbad hbad W hW.continuous hWs mesh hmesh]
    with Z hc hscalarZ hpaidZ hb hω hpuncture hprimeWidth hcoprime
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone reflected key firstHeight height hheight hfreq s μ' N' δ' amp P control exponent υ hυ
  have caps:=hc.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have paid:=actual_affine_error_normalized_menu_source_aligned (plane:=plane) (α:=T) rayM H hH W hW.continuous hWs
    N μ δ Cs Cg Sp degree ηseed η₀ Q Z hZ hpaidZ.2 θ w σ freq hσ state hη p
    t X₁ X₂ hX₁ hX₂ height mesh hμ hμcap hw (fun j=>(hwm j).trans hmeshcap)
    hmesh0 hwm hheight hfreq ⟨hwlo,hwhi⟩ hhi₁ hhi₂ hcone caps
  have cell:=actual_affine_error_cell_gates (plane:=plane) (α:=T) rayM H hH η₀ θ W hW.continuous hWs w σ freq hσ
    state p t X₁ X₂ hX₁ hX₂ hZ ⟨hwlo,hwhi⟩ hcone
  have hcell : widthLower ≤ Source.widthCellUpper (∑j,w j) ∧
      Source.widthCellUpper (∑j,w j) ≤ 1/25 := by
    simpa only [cell.1] using cell.2.2.2
  have hamp : |amp| ≤ 130 := by
    have ha:=amplifier_bounds plane hcell
    exact (abs_of_nonneg (le_trans (by norm_num [Source.amplifierMinimum]) ha.1)).le.trans (ha.2.trans (by norm_num))
  let error:=μ/8+μ/128+μ/8+geometryFinalErrorDictionaryRate μ N*(Fintype.card T:ℝ)+
    (frequencyLoss Z 32 (μ/64)+μ/8+μ/8)/6+kappa0*mesh+δ
  have herr : error ≤ μ := by
    have hold:=geometry_final_error_raw_loss μ
      (frequencyLoss Z 32 (μ/64)+μ/8) mesh (Fintype.card T) N hμ caps.card hω.2.2 hmeshμ
    have hk : kappa0≤(3/4:ℝ) := by norm_num [kappa0]
    have hm:=mul_le_mul_of_nonneg_right hk hmesh0
    dsimp only [error]
    linarith only [hold,hm]
  have hloss : error+μ/8+4*δ+μ/8 ≤ 64*μ := by
    have hh:=geometry_final_error_physical_loss μ error hμ herr
    linarith only [hh,hδcap]
  let phase:=fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q)
  have hphysical (second : Bool) := affine_error_frequency_loss_raw_scalar_bound (plane:=plane) (α:=α) rayM H hH
    Sbad W hW.continuous hWs (μ/8) (μ/8) εaffine δ (μ/64) δ mesh K Z hscalarZ.2 hZ T η₀
    θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
    reflected second error δ (μ/8) hδ.le hloss Ψ key firstHeight firstHeight υ
  have hz₁ : s.W₁ 0=0:=caps.zero₁
  have hz₂ : s.W₂ 0=0:=caps.zero₂
  let χ:=fun _ : GeometryJointErrorSelectedIndex reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
    firstHeight hZ key P υ hz₁ hz₂=>(1:RayCharacter)
  refine ⟨χ,(fun _=>1),?_,?_⟩
  · intro _ _;norm_num
  apply geometry_joint_error_normalized_bound reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
    firstHeight hZ key P υ 1 (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀) ballProfile
  intro second te u
  rw [geometry_joint_error_raw_sum_sources]
  let box:=geometryErrorAbsoluteBox Z N 130 1 (9/4)
  let Hactual:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key
  have hHactual : 0 ≤ Hactual:=by dsimp only [Hactual];rw [geometry_affine_support_constant];exact (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  have htotal:=geometry_joint_error_scalar_menu_height_box_payment reflected second s 1 1 Z 1 amp
    (μ/64) (μ/8) (9/4) firstHeight firstHeight error δ 1 (Real.logb Z (volume s)) hZ key P phase υ
    (Fintype.card T) (Fintype.card T) le_rfl hz₁ hz₂
    (fun l=> geometryJointErrorRawNormalizedSource reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
      firstHeight hZ key P υ 1 (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
      ballProfile second te u l)
    ray Cg (p.control Sp) lower (box.card:ℝ) Cb (16*Hactual*K) height te u δ δ δ
    (4*δ+δ-7/60000000) L₂ degree degree hheight (by dsimp [ray];positivity) hCg.le
    hlower (Nat.cast_nonneg _) hCb.le (mul_nonneg (mul_nonneg (by norm_num) hHactual) hK.le) (by omega) hb.2.1
    (by
      intro l
      let q:=l.1
      let prime:=l.2.1
      let i:=l.2.2.1
      let ψ:=l.2.2.2.1
      let Bp:=l.2.2.2.2
      let weight:=geometryAllocationWeight reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) 1
        (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key phase
        (Fintype.card T) (9/4) q.1.val q.2
      by_cases hf : frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) 1 s.ν s.W s.P=0
      · have hwzero : weight=0:=actual_geometry_error_first_weight_zero reflected s 1 1 (Z^(1:ℝ))
          Z (μ/64) 1 (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
          key phase (Fintype.card T) (9/4) q.1.val q.2 hf
        have hz:=affine_error_family_raw_source_zero (α:=T) reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
          firstHeight hZ key P υ 1 (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
          ballProfile second te u l hwzero
        apply hz.le.trans_eq
        change 0=_*((56/(P.card:ℝ)*weight*_/_)*_)
        rw [hwzero];simp only [mul_zero,zero_mul,zero_div]
      · have hp:=(actual_affine_error_prime_norm_cap (plane:=plane) rayM H Sbad hbad Z hZ _ hcell) prime
        have hcp:=hcoprime.2 (ι:=T) η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hwm
          _ hcell.1 hcell.2 prime
          (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) 1 q.2
          (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) firstHeight
        have hcop : ∀j I,I∈(geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight q).slots j→
          IsCoprime (Ideal.span {prime.val}) I:=by
          unfold geometryLowFirstChild;exact hcp
        have hsource : sourceRadius s ≤ Z^(130:ℝ):=caps.sourceCap.trans
          (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
        have hA : |Real.logb Z (volume s)| ≤ 130:=caps.volumeLog.trans (by norm_num)
        have hωabs : |frequencyLoss Z 32 (μ/64)+μ/8| ≤ 130:=by
          rw [abs_of_nonneg (by linarith only [hω.2.1,hμ])]
          linarith only [hω.2.2,hμcap]
        have hboxRows:=hb.2.2 reflected s 1 1 1 amp (μ/8) firstHeight hZ caps.card caps.endpoints
          (by simp) hz₁ hz₂ hsource hA (by norm_num) hamp hωabs key q hf prime.val hp.1 i hcop
          Bp (υ q prime i ψ) firstHeight
        have hraw:=actual_geometry_affine_error_raw_normalized_menu s Z μ δ amp Cs Cg N Sp degree η₀ Q
          height mesh hZ p caps paid (by linarith only [hω.2.1,hμ]) reflected firstHeight key q prime.val i hp.1
          hcop Bp (υ q prime i ψ) firstHeight ψ (hυ q prime i ψ) hf
          (hprimeWidth.2 _ hcell.1 hcell.2 prime)
          (fun n side=> hpuncture.2 reflected s 1 p Cs amp (μ/64) (μ/8) firstHeight hZ caps
            (by simp) key q prime.val hp.1 hp.2 i Bp (υ q prime i ψ) firstHeight n side)
          P weight (geometryAllocationWeight_nonneg ..) ballProfile second te u box hboxRows.2.2.2.2
        have he:=geometry_joint_error_raw_source (α:=T) reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
          firstHeight hZ key P υ 1 (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
          ballProfile second te u l
        apply he.le.trans
        unfold geometryErrorNormalizedMenuLabelsConclusion at hraw
        simp only [Fintype.sum_unique] at hraw
        have heerror : μ/8*1+μ/64/2+μ/8+geometryFinalErrorDictionaryRate μ N*(Fintype.card T:ℝ)+
          (frequencyLoss Z 32 (μ/64)+μ/8+μ/8*1)/6+kappa0*mesh+δ=error:=by dsimp only [error];ring
        simp only [heerror] at hraw
        convert hraw using 1
        · rfl
        · unfold geometryJointErrorRawScalarLabelSum
          dsimp only [ray,lower,weight,q,prime,i,ψ,Bp,L₂]
          ring)
    (by
      have hp:=hphysical second
      rw [geometry_joint_error_raw_scalar_cost_eq_physical] at hp
      simpa only [Hactual,geometry_affine_support_constant] using hp)
  apply htotal.trans_eq
  dsimp only [Cn,control,Hactual]
  rw [show δ+3*L₂*δ+δ+(4*δ+δ-7/60000000)=exponent by dsimp [exponent,δ',μ',N',δ,L₂,N];ring]
  ring
end
end OAI.SevenEighths.Target830.Source.ErrorReconstruction
#print axioms OAI.SevenEighths.Target830.Source.ErrorReconstruction.affine_error_family_raw_source_zero

#print axioms OAI.SevenEighths.Target830.Source.ErrorReconstruction.actual_affine_error_normalized_family
end

/- Original module: Candidate.Target830.Source.Assembly.ErrorMono. -/
section
set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound Cycle63Moment
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (R : Ideal O) [NeZero R]
local instance : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
variable (H : Subgroup (O ⧸ R)ˣ) (hH : RayOrthogonality.globalUnits R≤ H)

/-- A proved smaller source error is enlarged only after the finite
parameters, mesh and controls have been fixed. -/
theorem initial_affine_error_mono (plane : SourcePlane)
    (W : ℝ→ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax εsmall εbig Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (hC : 0≤ C) (hZ : 1< Z) (he : εsmall≤εbig)
    (h : Physical.InitialAffineAt (P:=plane) (α:=α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
      εsmall Z η η₀ Q degree S C) :
    Physical.InitialAffineAt (P:=plane) (α:=α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
      εbig Z η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  have hb:=h T θ w σ v t height hw hwm hσlo hσhi hh hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  apply hb.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    (by have hd:=diagonalControl_nonneg Φ; positivity)
end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.initial_affine_error_mono
end

/- Original module: Candidate.Target830.Source.Assembly.InitialSupplier. -/
section
/- Actual arbitrary detector-label supplier for .874830.
Character identities and predecessor attribution retained; Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate SchwartzMap
open Filter HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open ProbePhysical CenteredMomentDetectorDictionary Cycle25ProbeFinalAssembly
open Cycle25WeightedNumeratorPhysical CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentLogDyadic
open Cycle63MarkedPlain Cycle63InitialMass
local notation "O" => HeckeFamily.O
/-- The initial affine moment for one detector label. -/
theorem detector_label_initial_affine_capped (plane : SourcePlane) {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤))
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (ε : ℝ) (hε : 0< ε) (hεcap : ε≤1/10000000000000000) (mesh : ℝ) (hmesh0 : 0< mesh)
    (hmesh : mesh ≤ chosenMesh ε) (bΦ : ℝ) (hbΦ : 2≤ bΦ) :
    let ηl := sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,
      Physical.InitialAffineAt (P:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=> conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
        ηl ηl (weighted_sourceFixedIdeal S) degree Sd C := by
  intro ηl
  let W:=fun x=> conj (S.W x)
  have hW : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (S.W.smooth ⊤)
  have hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
    intro x hx
    exact S.complex_support (by intro hz;exact hx (by change conj (S.W x)=0;rw [hz];simp))
  obtain ⟨hm0,hmcomp,hmcommon,hmmu,hmamp,hmmarked⟩:=chosen_mesh_admission ε hε
  have hmeshlt : mesh< Source.amplifierMinimum/2:=hmesh.trans_lt hmamp
  have hmeshμ : mesh≤ geometryLossUnit 1 (ε/4)/8:=hmesh.trans hmmu
  have hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 (ε/4)/8):=
    hmesh.trans hmcommon
  have hmarkedmesh : mesh≤ Marked830Plain.rawMesh830*Marked830Plain.rawCore830:=hmesh.trans hmmarked
  have hε4 : 0< ε/4 := by positivity
  let row := naturalRowOf ηl (detector_label_modulus S η label)
  obtain ⟨τ,hτ,_hτcap,hpaid⟩:=TargetHigh830.actual_affine_main_uniform_paid (plane:=plane) (α:=Fin D.N)
    S.modulus ⊤ le_top 0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad
    W hW hs hβlo hβhi ηl 1 row 1 (by norm_num) (ε/4) mesh bΦ hε4 (by linarith) hmeshlt hmesh0.le
    hmeshμ hmeshcap hmarkedmesh hbΦ
  have hp:=hpaid (weighted_sourceFixedIdeal S) (weighted_sourceFixedIdeal_le_modulus S)
    (weighted_source_fixed_gates S ηl).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
    (weighted_source_fixed_gates S ηl).2.2.2
  have hex : excluded row.character 1 = ηl := detector_label_excluded S η label
  rw [hex] at hp
  have herror : ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset (Fin D.N),∃Se : Finset (ℕ×ℕ),∃De : ℕ,∃Ce : ℝ,0≤ Ce ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          ErrorReconstruction.GeometryAffineErrorPaidSpec (plane:=plane) S.modulus ⊤ le_top S.S W hW.continuous hs Ψ ηl ηl mesh (ε/4)
            T Se De Ce Z := by
    intro Ψ _ _
    apply ErrorReconstruction.actual_affine_error_uniform_paid_of_normalized (plane:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
      0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad W hW.continuous hs Ψ ηl ηl (ε/4) mesh
      hε4 hmeshlt (internalQ (weighted_sourceFixedIdeal S) ηl) (weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
      (weighted_source_fixed_gates S ηl).2.2.2
    exact ErrorReconstruction.actual_affine_error_normalized_family (plane:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
      S.S S.exclusions.bad W hW hs hβlo Ψ ηl ηl (weighted_sourceFixedIdeal S)
      (weighted_sourceFixedIdeal_le_modulus S) (weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
      (weighted_source_fixed_gates S ηl).2.2.2 (ε/4) mesh hε4 hmesh0.le hmeshlt hmeshμ hmeshcap
  have hbudget := literal_affine_geometry_budget_of_main_error (plane:=plane) S.modulus ⊤ le_top S.S S.exclusions.bad
    W hW.continuous hs ηl ηl (weighted_sourceFixedIdeal S) bΦ mesh (ε/4) τ hε4 hmeshlt hp herror
  obtain ⟨degree,Sd,C,hC,hev⟩ := literal_geometry_initial_affine (plane:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
    W hW hs ηl ηl (weighted_sourceFixedIdeal S) bΦ mesh ε τ (geometryLossUnit 1 (ε/4)/64)
    (by linarith) hmesh0 hε hτ
    (div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) hε4) (by norm_num))
    (hmesh.trans hmcomp) hβlo (by linarith) (weighted_sourceFixedIdeal_le_modulus S)
    (weighted_source_fixed_gates S ηl).1 (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
    (weighted_source_fixed_gates S ηl).2.2.2 logAnnulus_compact logAnnulus_smooth hbudget
  exact ⟨degree,Sd,C,hC,hev⟩

/-- The actual source is proved at a smaller capped error and then enlarged;
all masks, profiles, heights and the fixed mesh are unchanged. -/
theorem detector_label_initial_affine (plane : SourcePlane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤))
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (ε : ℝ) (hε : 0<ε) (mesh : ℝ) (hmesh0 : 0 < mesh)
    (hmesh : mesh ≤ sourceMesh ε) (bΦ : ℝ) (hbΦ : 2≤ bΦ) :
    let ηl:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,
      Physical.InitialAffineAt (P:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=> conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
        ηl ηl (weighted_sourceFixedIdeal S) degree Sd C := by
  intro ηl
  have hs:=capped_error_bounds hε
  obtain ⟨degree,Sd,C,hC,hev⟩:=detector_label_initial_affine_capped plane S η label hβlo hβhi
    (cappedError ε) hs.1 hs.2.2 mesh hmesh0 hmesh bΦ hbΦ
  refine ⟨degree,Sd,C,hC,?_⟩
  filter_upwards [hev,eventually_gt_atTop (1:ℝ)] with U hu hU
  exact initial_affine_error_mono (α:=Fin D.N) S.modulus ⊤ le_top plane
    (fun x=> conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1
    (cappedError ε) ε U ηl ηl (weighted_sourceFixedIdeal S) degree Sd C hC.le hU hs.2.1 hu

/-- Complete genuine arbitrary detector-label moments for both finite planes.
The common strictly positive source mesh precedes the slot dictionary. -/
theorem actual_label_initial_moments (plane : SourcePlane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (mesh : ℝ) (hmesh0 : 0 < mesh) (hmesh : mesh ≤ sourceMesh D.t) :
    Physical.InitialTransport.LabelInitialMoments plane S mesh := by
  intro η bΦ hbΦ label
  exact detector_label_initial_affine plane S η label hβlo hβhi D.t D.t_pos mesh hmesh0 hmesh bΦ hbΦ

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.detector_label_initial_affine_capped

#print axioms OAI.SevenEighths.Target830.Source.Assembly.detector_label_initial_affine
#print axioms OAI.SevenEighths.Target830.Source.Assembly.actual_label_initial_moments
end
