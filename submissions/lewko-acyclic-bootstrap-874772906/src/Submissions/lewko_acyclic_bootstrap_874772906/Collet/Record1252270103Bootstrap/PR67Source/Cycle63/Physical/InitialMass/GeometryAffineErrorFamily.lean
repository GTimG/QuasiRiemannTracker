import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineErrorCompletePayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineErrorAggregate
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorJointNormalizedTransport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorAbsoluteBox
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
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
attribute [local instance] geometryErrorOrdinaryContractionDecidable
attribute [local irreducible] Finset.univ SecondInputDatum.block geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild geometryJointErrorDatum geometryJointErrorWeight
  geometryJointErrorRawNormalizedSource geometryJointErrorPhysicalScalarCost geometryJointErrorRawScalarLabelSum

variable {α : Type} [Fintype α]
section Zero
variable (reflected : Bool)(s : Input α)(R seed : Ideal O)
  (Z M amp ξ reserve b t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
  (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→ Character)
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
  unfold geometryErrorRawNormalizedSum
  simp only [hzero,errorNormalizedCoefficient,mul_zero,zero_mul,zero_div,Complex.ofReal_zero]
  exact actual_geometry_error_zero_normalized_sum _ _ _ _ _
end Zero

open CenteredMomentNaturalFixedRaySource CenteredMomentSecondInputCapacitySource
variable (rayM : Ideal O) [NeZero rayM]
local instance affineErrorFamilyFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H)

set_option maxHeartbeats 400000 in
variable [Cycle63.AffineLedger] in
/-- The actual complete error family at a parent is uniform before all moving source data.
The first puncture has norm at most `Z^Rcap` and the mesh fits the error mask `28 + Rcap`. -/
theorem actual_affine_error_normalized_parent_family
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (Ψ : 𝓢(ℝ,ℂ))(η₀ : Character)(Q : Ideal O)(hQM : Q≤ rayM)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (εaffine mesh Rcap Cs : ℝ)(hε : 0<εaffine)(hmesh0 : 0≤ mesh)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)(hRcap0 : 0≤Rcap)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 (28+Rcap) 1 (geometryLossUnit 1 εaffine/8))
    (hCs : 1≤Cs) :
    ∀T : Finset α,∃degree windowDegree dN : ℕ,∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0≤Cn ∧
      ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedParentSpec rayM H hH Sbad W Ψ η₀ mesh εaffine Rcap Cs T
          degree windowDegree (internalQ Q η₀) SN dN Cn Z := by
  let μ:=geometryLossUnit 1 εaffine
  let N:=Fintype.card α
  let L₂:=3*((N:ℝ)+2)
  let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 L₂ N
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/128 := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ : 0<δ:=(geometry_final_dictionary_budgets μ 31 3 4 3 130 L₂ N hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by dsimp [L₂];positivity)).1
  have hδcap : δ≤μ/8 := by
    have hh:=(geometry_final_dictionary_budgets μ 31 3 4 3 130 L₂ N hμ
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by dsimp [L₂];positivity)).2.2.1
    linarith only [hh,hμ]
  obtain ⟨K,hK,hscalar⟩:=eventual_actual_affine_error_normalized_scalar_schedule (α:=α)
    Cs εaffine hCs hε
  obtain ⟨Cb,hCb,hbox⟩:=eventual_actual_geometry_error_absolute_box N 130 1 (9/4) (9/4) (μ/64) δ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith only [hμcap]) hδ
  intro T
  let : DecidableEq T:=Classical.decEq T
  obtain ⟨degree,Sp,hmenu⟩:=actual_finiteT_affine_error_normalized_menu (α:=α) rayM H hH W hWs hW T
    μ Cs (28+Rcap) hμ hCs (by linarith only [hRcap0]) hβ
  obtain ⟨Cg,hCg,hpaid⟩:=hmenu η₀ Q hQM hQ hQt hQ72
  let ray:ℝ:=(Fintype.card RayCharacter:ℝ)^2
  let lower:=lowerFactor N 1 (1/4)
  have hlower : 0<lower:=lowerFactor_pos N 1 (1/4) (by norm_num) (by norm_num)
  let Cn:=ray*Cg*(2+4*Real.pi)^degree*(Cb/lower)*16*K
  have hCn : 0≤Cn := by dsimp [Cn,ray];positivity
  refine ⟨degree,degree,degree,Sp,Cn,hCn,?_⟩
  filter_upwards [hscalar,hpaid,hbox,eventual_geometry_small_frequency μ hμ,
    eventual_actual_geometry_affine_error_puncture_of_scales N,
    eventual_actual_affine_error_prime_width rayM H Sbad hbad,
    eventual_affine_cell_prime_pools rayM H hH Sbad hbad 1 one_pos,
    eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh]
    with Z hscalarZ hpaidZ hb hω hpuncture hprimeWidth hpools hcoprime
  intro hZ s p caps hb₁ hb₂ hplain hwindows θ w σ freq hm R seed Mrow hR hseed hRcap hMrow hMrow1 hfit
    hw hwm hσ hzslot haff beta hbeta reflected key firstHeight height hheight hfreq
  subst hbeta
  intro μ' N' δ' amp P control exponent υ hυ
  have hN : Fintype.card T≤N := Fintype.card_le_of_injective _ Subtype.val_injective
  have capsN : GeometryAffineExceptionalSourceGates s p N Cs Z:={caps with card:=hN}
  have paid:=actual_affine_error_normalized_menu_parent_aligned (α:=T) rayM H hH W N μ δ Cs Cg (28+Rcap)
    Sp degree η₀ Q Z hZ hpaidZ.2 s p capsN hb₁ hb₂ hplain hwindows θ w σ freq hm Mrow hfit height mesh
    hμ hμcap hw (fun j=>(hwm j).trans hmeshcap) hmesh0 hwm hσ hheight hfreq hzslot haff _ rfl
  have hcellmem:=Cycle63.AffineLedger.originalCell_mem hzslot
  have hcell:=Cycle63.AffineLedger.cellUpper_bounds hcellmem.1 hcellmem.2.1
  have hamp : |amp|≤130 := by
    rw [abs_of_nonneg (Cycle63.AffineLedger.amp_pos hcell).le]
    exact (Cycle63.AffineLedger.amp_bounds hcell).2.trans
      (by linarith only [Cycle63.AffineLedger.amplifierCap_le_one])
  let error:=μ/8+μ/128+μ/8+geometryFinalErrorDictionaryRate μ N*(Fintype.card T:ℝ)+
    (frequencyLoss Z 32 (μ/64)+μ/8+μ/8)/6+Cycle63.Optimization.slotPrice*mesh+δ
  have herr : error≤μ := geometry_final_error_raw_loss μ
    (frequencyLoss Z 32 (μ/64)+μ/8) mesh (Fintype.card T) N hμ hN hω.2.2 hmeshμ
  have hloss : error+μ/8+4*δ+μ/8≤64*μ := by
    have hh:=geometry_final_error_physical_loss μ error hμ herr
    linarith only [hh,hδcap]
  let phase:=fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (μ/64) q)
  have hPne : P.Nonempty := (hpools.2 _ hcellmem.1 hcellmem.2.1).1
  have hPprime : ∀Q∈P,Prime Q:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  have hPbad : ∀Q∈P,Q∉fixedBadPrimes:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  have hslot : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I:=
    hcoprime.2 _ hcell.1 hcell.2 s η₀ θ w σ freq W hm hwm
  have hphysical (second : Bool) := affine_error_frequency_loss_raw_scalar_bound (α:=α)
    Cs (μ/8) (μ/8) εaffine δ (μ/64) δ K Z hscalarZ.2 hZ T s p capsN P hPne hPprime hPbad hslot
    R seed hseed hseed.ne_zero Mrow hMrow reflected second amp error δ (μ/8) hδ.le hloss Ψ key
    firstHeight firstHeight υ
  have hz₁ : s.W₁ 0=0:=caps.zero₁
  have hz₂ : s.W₂ 0=0:=caps.zero₂
  let χ:=fun _ : GeometryJointErrorSelectedIndex reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4)
    firstHeight hZ key P υ hz₁ hz₂=>(1:RayCharacter)
  refine ⟨χ,(fun _=>1),?_,?_⟩
  · intro _ _;norm_num
  apply geometry_joint_error_normalized_bound reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4)
    firstHeight hZ key P υ Mrow (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀) ballProfile
  intro second te u
  rw [geometry_joint_error_raw_sum_sources]
  let box:=geometryErrorAbsoluteBox Z N 130 1 (9/4)
  let Hactual:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key
  have hHactual : 0≤Hactual:=by
    dsimp only [Hactual];rw [geometry_affine_support_constant]
    exact (geometry_high_factor_pos reflected 64 key (by norm_num)).le
  have hn : (0:ℝ)<seed.absNorm:=CenteredMomentFirstScale.norm_pos seed hseed.ne_zero
  have htotal:=geometry_joint_error_scalar_menu_height_box_payment reflected second s R seed Z 1 Mrow amp
    (μ/64) (μ/8) (9/4) firstHeight firstHeight error δ Mrow (Real.logb Z (volume s)) hZ key P phase υ
    (Fintype.card T) (Fintype.card T) le_rfl hz₁ hz₂
    (fun l=>geometryJointErrorRawNormalizedSource reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4)
      firstHeight hZ key P υ Mrow (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
      ballProfile second te u l)
    ray Cg (p.control Sp) lower (box.card:ℝ) Cb (16*Hactual*K/(seed.absNorm:ℝ)) height te u δ δ (1-Mrow) δ
    (4*δ+δ-(Cycle63.AffineLedger.lowReserve/2)) L₂ degree degree hheight (by dsimp [ray];positivity) hCg.le
    hlower (Nat.cast_nonneg _) hCb.le
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hHactual) hK.le) hn.le) (by omega) hb.2.1
    (by
      intro l
      let q:=l.1
      let prime:=l.2.1
      let i:=l.2.2.1
      let ψ:=l.2.2.2.1
      let Bp:=l.2.2.2.2
      let weight:=geometryAllocationWeight reflected s R seed (Z^Mrow) Z (μ/64) Mrow
        (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key phase
        (Fintype.card T) (9/4) q.1.val q.2
      by_cases hf : frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) R s.ν s.W s.P=0
      · have hwzero : weight=0:=actual_geometry_error_first_weight_zero reflected s R seed (Z^Mrow)
          Z (μ/64) Mrow (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
          key phase (Fintype.card T) (9/4) q.1.val q.2 hf
        have hz:=affine_error_family_raw_source_zero (α:=T) reflected s R seed Z Mrow amp (μ/64) (μ/8)
          (9/4) firstHeight hZ key P υ Mrow (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
          ballProfile second te u l hwzero
        apply hz.le.trans_eq
        change 0=_*((56/(P.card:ℝ)*weight*_/_)*_)
        rw [hwzero];simp only [mul_zero,zero_mul,zero_div]
      · have hp:=(actual_affine_error_prime_norm_cap rayM H Sbad hbad Z hZ _ hcell) prime
        have hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight q).slots j→
          IsCoprime (Ideal.span {prime.val}) I:=by
          unfold geometryLowFirstChild
          exact actual_child_full_slot_coprime s (Ideal.span {prime.val}) (hslot prime)
            (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (μ/64)
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) R q.2
            (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64)
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) firstHeight
        have hsource : sourceRadius s≤Z^(130:ℝ):=caps.sourceCap.trans
          (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
        have hA : |Real.logb Z (volume s)|≤130:=caps.volumeLog.trans (by norm_num)
        have hM : |Mrow|≤130:=by
          rw [abs_of_nonneg hMrow]
          linarith only [hMrow1]
        have hωabs : |frequencyLoss Z 32 (μ/64)+μ/8|≤130:=by
          rw [abs_of_nonneg (by linarith only [hω.2.1,hμ])]
          linarith only [hω.2.2,hμcap]
        have hboxRows:=hb.2.2 reflected s R seed Mrow amp (μ/8) firstHeight hZ hN caps.endpoints
          hseed hz₁ hz₂ hsource hA hM hamp hωabs key q hf prime.val hp.1 i hcop
          Bp (υ q prime i ψ) firstHeight
        have hraw:=actual_geometry_affine_error_raw_normalized_menu s R seed Z μ δ amp Cs Cg Mrow
          (28+Rcap) N Sp degree η₀ Q height mesh hZ p capsN paid (by linarith only [hω.2.1,hμ])
          reflected firstHeight key q prime.val i hp.1 hcop Bp (υ q prime i ψ) firstHeight ψ
          (hυ q prime i ψ) hf (hprimeWidth.2 _ hcell.1 hcell.2 prime)
          (fun n side=>hpuncture.2 reflected s R seed p Cs Mrow amp (μ/64) (μ/8) firstHeight Rcap hZ
            capsN hR hRcap hseed key q prime.val hp.1 hp.2 i Bp (υ q prime i ψ) firstHeight n side)
          P weight (geometryAllocationWeight_nonneg ..) ballProfile second te u box hboxRows.2.2.2.2
        have he:=geometry_joint_error_raw_source (α:=T) reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4)
          firstHeight hZ key P υ Mrow (Real.logb Z (volume s)) phase hz₁ hz₂ χ (internalQ Q η₀)
          ballProfile second te u l
        apply he.le.trans
        unfold geometryErrorNormalizedMenuLabelsConclusion at hraw
        simp only [Fintype.sum_unique] at hraw
        have heerror : μ/8*1+μ/64/2+μ/8+geometryFinalErrorDictionaryRate μ N*(Fintype.card T:ℝ)+
          (frequencyLoss Z 32 (μ/64)+μ/8+μ/8*1)/6+Cycle63.Optimization.slotPrice*mesh+δ=error:=by
          dsimp only [error];ring
        simp only [heerror] at hraw
        convert hraw using 1
        unfold geometryJointErrorRawScalarLabelSum
        dsimp only [ray,lower,weight,q,prime,i,ψ,Bp,L₂]
        ring)
    (by
      have hp:=hphysical second
      have hp' : geometryJointErrorPhysicalScalarCost reflected second s R seed Z 1 Mrow amp (μ/64) (μ/8)
          (9/4) firstHeight firstHeight error δ Mrow (Real.logb Z (volume s)) hZ key P phase υ (Fintype.card T)≤
          16*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*K*
            Z^(4*δ+δ-((Cycle63.AffineLedger.lowReserve/2):ℝ))/(seed.absNorm:ℝ) :=
        (geometry_joint_error_raw_scalar_cost_eq_physical reflected second s R seed Z 1 Mrow amp (μ/64)
          (μ/8) (9/4) firstHeight firstHeight error δ Mrow (Real.logb Z (volume s)) hZ key P phase υ
          (Fintype.card T)).symm.le.trans hp
      refine hp'.trans_eq ?_
      simp only [Hactual,geometry_affine_support_constant]
      ring)
  apply htotal.trans_eq
  dsimp only [Cn,control,Hactual]
  rw [show δ+3*L₂*δ+(1-Mrow)+δ+(4*δ+δ-(Cycle63.AffineLedger.lowReserve/2))=exponent by
    dsimp [exponent,δ',μ',N',δ,L₂,N]
    ring]
  ring

set_option maxHeartbeats 400000 in
/-- The actual complete error family is uniform before all moving source data: the
parent family at the unit puncture and seed and the radial scale one. -/
theorem actual_affine_error_normalized_family
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(Q : Ideal O)(hQM : Q≤ rayM)
    (hQ : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (εaffine mesh : ℝ)(hε : 0<εaffine)(hmesh0 : 0≤ mesh)
    (hmesh : mesh<Cycle63.Arithmetic.amplifierFloor/2)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8)) :
    ∀T : Finset α,∃degree windowDegree dN : ℕ,∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0≤Cn ∧
      ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec rayM H hH Sbad W hW.continuous hWs Ψ ηseed η₀ mesh εaffine T
          degree windowDegree (internalQ Q η₀) SN dN Cn Z := by
  obtain ⟨Cs,hCs,hsources⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) rayM H hH W
    hW.continuous hWs
  have hgeneral:=actual_affine_error_normalized_parent_family (α:=α) rayM H hH Sbad hbad W hW hWs hβ Ψ η₀ Q
    hQM hQ hQt hQ72 εaffine mesh 0 Cs hε hmesh0 hmesh hmeshμ le_rfl
    (by simpa only [add_zero] using hmeshcap) hCs
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  intro T
  obtain ⟨degree,windowDegree,dN,SN,Cn,hCn,hg⟩:=hgeneral T
  refine ⟨degree,windowDegree,dN,SN,Cn,hCn,?_⟩
  filter_upwards [hg,hsources,
    Cycle63Moment.fixed_anchor_width_uniform (fun _:Unit=>ηseed) 1 (geometryLossUnit 1 εaffine/16)
      one_pos (by positivity)] with Z hgZ hs hanchor
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hwin reflected key firstHeight height
    hheight hfreq s μ N δ amp P control exponent υ hυ
  let : DecidableEq T:=Classical.decEq T
  obtain ⟨hmatch,hfit,hzslot,haff,hbeta⟩:=affine_exceptional_first_level_data rayM H hH
    W hW.continuous hWs η₀ ηseed θ w σ freq hσ state hη p t X₁ X₂ hX₁ hX₂ hZ (geometryLossUnit 1 εaffine)
    hwin (hanchor.2 () 1 le_rfl)
  have caps:=hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin
  have aux:=actual_affine_error_auxiliary_gates rayM H hH η₀ θ W hW.continuous hWs w σ freq hσ state p
    t X₁ X₂ hX₁ hX₂ hZ hw hwin
  have h:=hgZ hZ s p {caps with card:=le_rfl} aux.1 aux.2.1 aux.2.2.1 aux.2.2.2.2.1 θ w σ freq hmatch
    1 1 1 one_ne_zero squarefree_one (by simp) zero_le_one le_rfl hfit hw hwm hσ hzslot haff _ hbeta
    reflected key firstHeight height hheight hfreq υ hυ
  rw [sub_self,add_zero,show ((1:Ideal O).absNorm:ℝ)=1 by simp,div_one] at h
  exact h

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
