import Candidate.Target836.SourceProvider.ErrorMain
import Candidate.Target836.Source836.GeometryAffineExceptionalGates
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target836.Error836.GeometryAffineErrorSpecs
import Candidate.Target836.Error836.GeometryAffineErrorAggregate
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorJointNormalizedTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorAbsoluteBox

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Target836ErrorPayment
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
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
    (hmesh : mesh < (902420521/120632400000:ℝ)/2)
    (hmeshμ : mesh ≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh ≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8)) :
    ∀T : Finset α,∃degree windowDegree dN : ℕ,∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0 ≤ Cn ∧
      ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec rayM H hH Sbad W hW.continuous hWs Ψ ηseed η₀ mesh εaffine T
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
  obtain ⟨Cs,hCs,hcaps⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) rayM H hH W hW.continuous hWs
  obtain ⟨K,hK,hscalar⟩:=eventual_actual_affine_error_normalized_scalar_schedule (α:=α) rayM H hH
    Sbad hbad W hW.continuous hWs εaffine mesh hε hmesh
  obtain ⟨Cb,hCb,hbox⟩:=eventual_actual_geometry_error_absolute_box N 130 1 (9/4) (9/4) (μ/64) δ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith only [hμcap]) hδ
  intro T
  let : DecidableEq T:=Classical.decEq T
  obtain ⟨degree,Sp,hmenu⟩:=actual_finiteT_affine_error_normalized_menu (α:=α) rayM H hH W hWs hW T
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
    eventual_actual_affine_error_prime_width rayM H Sbad hbad,
    OAI.SevenEighths.Target836SourceAssembly.eventual_actual_affine_exceptional_child_coprime
      rayM H hH Sbad hbad W hW.continuous hWs mesh hmesh]
    with Z hc hscalarZ hpaidZ hb hω hpuncture hprimeWidth hcoprime
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone reflected key firstHeight height hheight hfreq s μ' N' δ' amp P control exponent υ hυ
  have caps:=hc.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have paid:=actual_affine_error_normalized_menu_source_aligned (α:=T) rayM H hH W hW.continuous hWs
    N μ δ Cs Cg Sp degree ηseed η₀ Q Z hZ hpaidZ.2 θ w σ freq hσ state hη p
    t X₁ X₂ hX₁ hX₂ height mesh hμ hμcap hw (fun j=>(hwm j).trans hmeshcap)
    hmesh0 hwm hheight hfreq ⟨hwlo,hwhi⟩ hhi₁ hhi₂ hcone caps
  have cell:=actual_affine_error_cell_gates (α:=T) rayM H hH η₀ θ W hW.continuous hWs w σ freq hσ
    state p t X₁ X₂ hX₁ hX₂ hZ ⟨hwlo,hwhi⟩ hcone
  have hcell : 3401/100000 ≤ Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑j,w j)) ∧
      Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑j,w j)) ≤ 1/25 := by
    simpa only [cell.1] using cell.2.2.2
  have hamp : |amp| ≤ 130 := by
    have ha:=Named.amp_bounds hcell
    exact (abs_of_nonneg (le_trans (by norm_num) ha.1)).le.trans (ha.2.trans (by norm_num))
  let error:=μ/8+μ/128+μ/8+geometryFinalErrorDictionaryRate μ N*(Fintype.card T:ℝ)+
    (frequencyLoss Z 32 (μ/64)+μ/8+μ/8)/6+(3/4)*mesh+δ
  have herr : error ≤ μ := geometry_final_error_raw_loss μ
    (frequencyLoss Z 32 (μ/64)+μ/8) mesh (Fintype.card T) N hμ caps.card hω.2.2 hmeshμ
  have hloss : error+μ/8+4*δ+μ/8 ≤ 64*μ := by
    have hh:=geometry_final_error_physical_loss μ error hμ herr
    linarith only [hh,hδcap]
  let phase:=fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q)
  have hphysical (second : Bool) := affine_error_frequency_loss_raw_scalar_bound (α:=α) rayM H hH
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
    (fun l=>geometryJointErrorRawNormalizedSource reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
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
      · have hp:=(actual_affine_error_prime_norm_cap rayM H Sbad hbad Z hZ _ hcell) prime
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
          (fun n side=>hpuncture.2 reflected s 1 p Cs amp (μ/64) (μ/8) firstHeight hZ caps
            (by simp) key q prime.val hp.1 hp.2 i Bp (υ q prime i ψ) firstHeight n side)
          P weight (geometryAllocationWeight_nonneg ..) ballProfile second te u box hboxRows.2.2.2.2
        have he:=geometry_joint_error_raw_source (α:=T) reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
          firstHeight hZ key P υ 1 (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
          ballProfile second te u l
        apply he.le.trans
        unfold geometryErrorNormalizedMenuLabelsConclusion at hraw
        simp only [Fintype.sum_unique] at hraw
        have heerror : μ/8*1+μ/64/2+μ/8+geometryFinalErrorDictionaryRate μ N*(Fintype.card T:ℝ)+
          (frequencyLoss Z 32 (μ/64)+μ/8+μ/8*1)/6+(3/4)*mesh+δ=error:=by dsimp only [error];ring
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
end OAI.SevenEighths.Target836ErrorPayment
#print axioms OAI.SevenEighths.Target836ErrorPayment.affine_error_family_raw_source_zero

#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_affine_error_normalized_family
