/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B155
import Candidate.Bundles.B159
import Candidate.Bundles.B161
import Candidate.Bundles.B164
import Candidate.Bundles.B171
import Candidate.Bundles.B185

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainRatioPayment; sha256 af1310e55b8ac36560a01469708dfa53b223cd4a5a4569876e3dae8580a4a624 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                           
                                                          
                                                  

set_option autoImplicit false
set_option maxHeartbeats 160000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile
open CenteredMomentExceptionalAmplitudePair RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O

/-- The ratio image is paid from the actual common four-dyad box. No source
label cardinality or normalized-energy estimate enters this bound. -/
theorem eventual_actual_geometry_main_ratio_payment {α : Type}[Fintype α][DecidableEq α]
    (B loss b bs ξ ε : ℝ) (hB : 0≤ B) (hloss : 0< loss)
    (hb : 1≤ b) (hbs : 1≤ bs) (hξ : 0≤ξ) (hξloss : ξ≤ loss) (hε : 0<ε) :
    ∃Cb : ℝ,0< Cb ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(reflected : Bool)(s : Input α)(R seed : Ideal O)
      (M amp reserve t : ℝ)(hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))
      (_hend : Endpoints b bs bs s)(_hseed : Squarefree seed)
      (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      sourceRadius s≤ Z^B → |Real.logb Z (volume s)|≤ B → |M|≤ B → |amp|≤ B →
      |frequencyLoss Z 32 ξ+reserve|≤ B → 0≤ amp → 0≤ reserve →
      let selected := geometryMainNonzeroBlocks reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ key hz₁ hz₂
      let datum := fun j : selected => geometryLowSecondDatum reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ key j.val.1 hz₁ hz₂ j.val.2
      (∀j,(datum j).block.dyad∈geometryMainAbsoluteBox Z (Fintype.card α) B loss b) ∧
      ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤ Cb*Z^ε ∧
      (∀(E : ℝ),0≤ E → ∀A : ℕ,
        (∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A)≤ Cb*E*Z^ε) ∧
      ∀(χ : selected→ RayCharacter)(Q : selected→ Ideal O)(m : selected→ O)
        (E : ℝ),0≤ E → ∀A : ℕ,
        (∑r∈secondRatioBins (fun j=>(ordinarySecondDatum (datum j) (χ j) (Q j) (m j)).block),
          E/(1+dyadicScale r)^A)≤ Cb*E*Z^ε := by
  obtain ⟨Cb,hCb,hbox⟩ := eventual_actual_geometry_main_absolute_box
    (Fintype.card α) B loss b bs ξ ε hB hloss hb hbs hξ hξloss hε
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hbox] with Z hz
  refine ⟨hz.1,?_⟩
  intro reflected s R seed M amp reserve t hZ key hend hseed hz₁ hz₂
    hsource hA hM hamp hω hamp0 hreserve selected datum
  have mem (j : selected) : (datum j).block.dyad∈geometryMainAbsoluteBox Z (Fintype.card α) B loss b := by
    have hf := (Finset.mem_filter.mp j.property).2.1
    have hraw := hz.2.2 reflected s R seed M amp reserve t
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) le_rfl hend hseed hz₁ hz₂
      hsource hA hM hamp hω hamp0 hreserve key j.val.1.1.val j.val.1.1.property j.val.1.2 hf j.val.2
    exact hraw
  have hcard : ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤ Cb*Z^ε := by
    have hcount : ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤
        (geometryMainAbsoluteBox Z (Fintype.card α) B loss b).card := by
      exact_mod_cast second_ratio_bins_card_le_box (fun j=>(datum j).block) _ mem
    exact hcount.trans hz.2.1
  have decay (E : ℝ) (hE : 0≤ E) (A : ℕ) :
      (∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A)≤ Cb*E*Z^ε := by
    have hpaid := second_ratio_decay_le_box (fun j=>(datum j).block) _ mem E hE A
    have hbound := mul_le_mul_of_nonneg_right hz.2.1 hE
    exact hpaid.trans (hbound.trans_eq (by ring))
  refine ⟨mem,hcard,decay,?_⟩
  intro χ Q m E hE A
  simpa only [ordinary_second_ratio_bins] using decay E hE A

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_main_ratio_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainRatioPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainRatioPayment; sha256 2f44747b5e6abdec9d9dc988d10fc9360b7dbc6f7df74af568cce5778759c863 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                            
                                                                  

set_option autoImplicit false
set_option maxHeartbeats 160000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile
open CenteredMomentExceptionalAmplitudePair RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle61InitialSource
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedRayDictionary
local notation "O" => HeckeFamily.O

private theorem affine_ratio_plain_zero (p : Profiles (1/4) (9/4)) (i : Fin 2) :
    p.profile i 0=0 := by
  by_contra h
  have hh := (p.support i h).1
  norm_num at hh

variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineMainRatioPaymentFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤ H)

/-- Actual affine source receipts pay the shared ratio image uniformly over
original subsets. The ratio loss is independent of the positive physical
localization rates, and every Fourier scale keeps the actual subset count. -/
theorem uniform_actual_affine_main_ratio_payment
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εaffine εratio : ℝ)(hεaffine : 0<εaffine)(hεratio : 0<εratio) :
    ∃Cb : ℝ,0< Cb ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(T : Finset α)(η₀ : Character)(θ : T→ RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
      (t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,0≤ w i) → (41/100:ℝ)≤ length Z X₁ → (41/100:ℝ)≤ length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
      (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
      let s := affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑i,w i))
      let amp := Cycle61.Arithmetic.amp beta
      let μ := geometryLossUnit 1 εaffine
      0<μ/64 ∧ 0<μ/8 ∧
      ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ),
      let selected := geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight
        (Fintype.card T) hZ key (affine_ratio_plain_zero p 0) (affine_ratio_plain_zero p 1)
      let datum := fun j : selected=>geometryLowSecondDatum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key j.val.1 (affine_ratio_plain_zero p 0)
          (affine_ratio_plain_zero p 1) j.val.2
      ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤ Cb*Z^εratio ∧
      (∀(E : ℝ),0≤ E → ∀A : ℕ,
        (∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A)≤ Cb*E*Z^εratio) ∧
      ∀(χ : selected→ RayCharacter)(Q : selected→ Ideal O)(m : selected→ O)(E : ℝ),0≤ E → ∀A : ℕ,
        (∑r∈secondRatioBins (fun j=>(ordinarySecondDatum (datum j) (χ j) (Q j) (m j)).block),
          E/(1+dyadicScale r)^A)≤ Cb*E*Z^εratio := by
  let μ := geometryLossUnit 1 εaffine
  have hμ : 0<μ := geometry_loss_unit_pos 1 εaffine (by norm_num) hεaffine
  have hμcap : μ≤1/128 :=
    (min_le_right (εaffine/128) _).trans
      ((min_le_right ((7/30000000)*1/128) _).trans (min_le_right (1/128) (1/128)))
  have data (T : Finset α) := eventual_actual_geometry_main_ratio_payment (α:=T)
    3 (μ/8) (9/4) (9/4) (μ/64) εratio (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (by positivity) (by linarith) hεratio
  choose C hC hpaid using data
  let total := 1+∑T : Finset α,C T
  have hnonneg : ∀T : Finset α,0≤ C T := fun T=>(hC T).le
  have htotal : 0< total := by
    have hh := Finset.sum_nonneg (s:=Finset.univ) (fun T _=>hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T≤ total := by
    have hh := Finset.single_le_sum (fun T _=>hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  obtain ⟨Cs,hCs,hsources⟩ := eventual_actual_affine_exceptional_source_gates (α:=α)
    rayM H hH W hW hWs
  refine ⟨total,htotal,?_⟩
  filter_upwards [Filter.eventually_all.mpr hpaid,hsources,eventual_geometry_small_frequency μ hμ]
    with Z hp hs hf
  refine ⟨hs.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi s beta amp μ'
  refine ⟨by positivity,by positivity,?_⟩
  intro reflected key firstHeight selected datum
  have caps := hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have hcell := Cycle61.Moment.originalCell_mem ⟨hwlo,hwhi⟩
  have hb := Cycle61.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0< amp := Cycle61.Arithmetic.amp_pos hb
  have hamp : |amp|≤3 := by
    rw [abs_of_pos hamp0]
    exact (Cycle61.Arithmetic.amp_bounds hb).2.trans (by norm_num)
  have hω : |frequencyLoss Z 32 (μ/64)+μ/8|≤3 := by
    rw [abs_of_nonneg hf.2.1]
    exact hf.2.2.trans (by linarith)
  have main := (hp T).2 reflected s 1 1 1 amp (μ/8) firstHeight hZ key caps.endpoints squarefree_one
    (affine_ratio_plain_zero p 0) (affine_ratio_plain_zero p 1) caps.sourceCap caps.volumeLog
    (by norm_num) hamp hω hamp0.le (by positivity)
  have hZε : 0≤ Z^εratio := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  refine ⟨main.2.1.trans (mul_le_mul_of_nonneg_right (hle T) hZε),?_,?_⟩
  · intro E hE A
    apply (main.2.2.1 E hE A).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hle T) hE) hZε
  · intro χ Q m E hE A
    apply (main.2.2.2 χ Q m E hE A).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hle T) hE) hZε

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_actual_affine_main_ratio_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainRatioPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineUniformRemainder; sha256 1bfd1246682d3f1be1258a68a34351225acacbd8106faff2b37a7a38d3511ee3 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                           
                                                                

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500

namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonProfile CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentLogDyadic
open CanonicalQuadraticSieve CenteredMomentPrimeElements RayFourExpansion
local notation "O" => HeckeFamily.O

/-- Constants and thresholds are fixed before choosing the original live subset.
Each subset retains its actual cardinality in its source and Fourier cutoff. -/
theorem uniform_actual_affine_main_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ beta : ℝ, 3401/100000 ≤ beta ∧ beta ≤ 1/25 →
      Real.logb Z (volume s) ≤ Cycle61.Arithmetic.totalA beta →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
      geometryAffineMainSourceTotal s Ψ Z (Cycle61.Arithmetic.amp beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) +
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 (Cycle61.Arithmetic.amp beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q => normPhase (coordinateBlock s 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))‖ := by
  have data (T : Finset α) := eventual_actual_affine_main_remainder (ι := T) Cs μ hCs hμ hcap
  choose C hC hbound using data
  let total := 1 + ∑ T : Finset α, C T
  have hnonneg : ∀ T : Finset α, 0 ≤ C T := fun T => (hC T).le
  have htotal : 0 < total := by
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun T _ => hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T ≤ total := by
    have hsum := Finset.single_le_sum (fun T _ => hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total, htotal, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
  intro hZ T s p caps beta hb hcone Ψ t reflected key
  apply (hz T hZ s p caps beta hb hcone Ψ t reflected key).trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (hle T) (sq_nonneg _)
    · exact (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  · exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _

/-- The extracted source and retained norm keep the same single prime average
while constants and thresholds are collected over original slot subsets. -/
theorem uniform_actual_affine_error_remainder {α : Type} [Fintype α] [DecidableEq α]
    (Cs μ : ℝ) (hCs : 1 ≤ Cs) (hμ : 0 < μ) (hcap : μ ≤ 1/128) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ T : Finset α, ∀ (s : Input T) (p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z →
    ∀ beta : ℝ, 3401/100000 ≤ beta ∧ beta ≤ 1/25 →
      Real.logb Z (volume s) ≤ Cycle61.Arithmetic.totalA beta →
    ∀ P : Finset (Ideal O), P.Nonempty →
      (∀ Q ∈ P, Prime Q) → (∀ Q ∈ P, Q ∉ fixedBadPrimes) →
      (∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z^(Cycle61.Arithmetic.amp beta)) →
      (∀ q : elementPool P, ∀ i I, I ∈ s.slots i → IsCoprime (Ideal.span {q.val}) I) →
    ∀ (Ψ : 𝓢(ℝ,ℂ)) (t : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)),
    ∀ υ : GeometryLowFirstIndex reflected s 1 1 (Z^(1 : ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1 : ℝ)) key →
          elementPool P → Fin 3 → RayCharacter → Character,
      (56/(P.card : ℝ)) * geometryAffineErrorSourceTotal s Ψ Z (Cycle61.Arithmetic.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ ≤
      C * (p.control {(0,0)})^2 *
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) +
      (56/(P.card : ℝ)) * ‖geometryAffineErrorRetainedSum s Ψ Z (Cycle61.Arithmetic.amp beta)
        (μ/64) (μ/8) t hZ reflected key P υ‖ := by
  have data (T : Finset α) := eventual_actual_affine_error_remainder (ι := T) Cs μ hCs hμ hcap
  choose C hC hbound using data
  let total := 1 + ∑ T : Finset α, C T
  have hnonneg : ∀ T : Finset α, 0 ≤ C T := fun T => (hC T).le
  have htotal : 0 < total := by
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun T _ => hnonneg T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : C T ≤ total := by
    have hsum := Finset.single_le_sum (fun T _ => hnonneg T) (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total, htotal, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
  intro hZ T s p caps beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ
  apply (hz T hZ s p caps beta hb hcone P hne hp hbad hpcap hcop Ψ t reflected key υ).trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (hle T) (sq_nonneg _)
    · exact (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  · exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_actual_affine_main_remainder
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_actual_affine_error_remainder

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineUniformRemainder -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineRetainedBudget; sha256 cd6e2f328fee2848369e17a1cca6e2afce62f02b96548d0be8336953e9712a2f -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                      
                                                                  

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationRadicalChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle61InitialSource
open CenteredMomentLogDyadic RayFourExpansion
open CenteredMomentChildRows CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAllocatedRayDictionary
local notation "O" => HeckeFamily.O

private theorem retained_remainder_join
    (budget main error nm ne average coeff Cm Ce factor : ℝ)
    (havg : 0 ≤ average) (havg56 : average ≤ 56)
    (hcoeff : 0 ≤ coeff) (hcoeff2048 : coeff ≤ 2048)
    (hCm : 0 ≤ Cm) (hfactor : 0 ≤ factor)
    (hb : budget ≤ average * (coeff * main + error))
    (hm : main ≤ Cm * factor + nm)
    (he : average * error ≤ Ce * factor + average * ne) :
    budget ≤ (56 * 2048 * Cm + Ce) * factor + average * (coeff * nm + ne) := by
  have hmain := mul_le_mul_of_nonneg_left hm (mul_nonneg havg hcoeff)
  have hcoef : average * coeff * Cm ≤ 56 * 2048 * Cm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul havg56 hcoeff2048 hcoeff (by norm_num)) hCm
  have hpaid := mul_le_mul_of_nonneg_right hcoef hfactor
  nlinarith only [hb, hmain, he, hpaid]

private def amplifiedRadiusFrame {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (Z amp μ : ℝ) (reflected : Bool) (key : ℤ × (Fin 5 → ℤ))
    (Ψ : 𝓢(ℝ,ℂ)) (height : ℝ) (P : Finset (Ideal O)) (radius : ℝ) (hK : 0 < radius) : Prop :=
  let Label := ↥(firstLiveColumns (geometryFirstSource s 1 1 radius Z (μ/64) hK key) (fun _ => logAnnulus))
  let C := fun j : Label => geometryColumnIdeal reflected s 1 1 radius Z (μ/64) hK key j.val
  let χ := fun j : Label => geometryColumnCharacter reflected s 1 1 radius Z (μ/64) hK key j.val
  let g := fun j : Label => geometryBranch reflected s 1 1 radius Z (μ/64) hK key j.val
  let mass := fun j : Label => geometryAllocationWeight reflected s 1 1 radius Z (μ/64) 1
    (Real.logb Z (volume s)) hK key
    (fun q => normPhase (coordinateBlock s 1 1 Ψ radius Z (μ/64) q)) (Fintype.card ι) (9/4) j.val
  ∃ τ : (j : Label) → actualAllocations s.pools (C j) → elementPool P → Fin 3 → RayCharacter → Character,
    (∀ j B q i ψ, (τ j B q i ψ).modulus.absNorm ≤
      radicalBound (childCharacter (χ j) ψ) fixedBadMask q.val (errorMovingExponent (errorIndex i))) ∧
    geometryLiveBudget reflected s 1 1 radius Z (μ/64) 1 (Real.logb Z (volume s)) hK key
      (fun q => normPhase (coordinateBlock s 1 1 Ψ radius Z (μ/64) q)) (Fintype.card ι) (9/4) height ≤
    (56/(P.card : ℝ))*
      (((amplifierCap 2 0 1+6*amp)/(amp/2))*
        (∑ j, ∑ B, mass j B * actualMainSource (child s (C j) 1 B (χ j) height) (g j)
          Z (3*amp) 1 (μ/64) (μ/8)) +
        ∑ j, ∑ B, mass j B * actualErrorSources (child s (C j) 1 B (χ j) height) (g j)
          Z (3*amp) 1 (μ/64) (μ/8) P (τ j B))

variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineRetainedBudgetFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The actual affine amplifier pays zero and tail terms uniformly over the
original slot subset. Its chosen radical family and exact retained sums remain. -/
theorem actual_affine_geometry_retained_budget
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (W : ℝ → ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (loss mesh μ : ℝ) (hloss : 0 < loss) (hμ : 0 < μ) (hμcap : μ ≤ 1/128)
    (hmesh : mesh < (902420521/120632400000 : ℝ)/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ (hZ : 1 < Z)
      (T : Finset α) (η₀ : Character) (θ : T → RayQuotient.Characters rayM H)
      (w σ freq : T → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc (33/50 : ℝ) (33/50))
      (bΦ : ℝ) (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
      (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (41/100 : ℝ) ≤ length Z X₁ → (41/100 : ℝ) ≤ length Z X₂ →
      length Z X₁ ≤ (44/100 : ℝ) → length Z X₂ ≤ (44/100 : ℝ) →
      (17/500 : ℝ) ≤ ∑ i, w i → (∑ i, w i) ≤ (1/25 : ℝ) →
      length Z X₁ + length Z X₂ + Cycle61.Arithmetic.lambda * (∑ i, w i) ≤ Cycle61.Arithmetic.B →
      let inp := affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑ i, w i))
      let amp := Cycle61.Arithmetic.amp beta
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      P.Nonempty ∧ Z^(amp-loss) ≤ (P.card : ℝ) ∧
      ∀ (reflected : Bool) (key : ℤ × (Fin 5 → ℤ)) (Ψ : 𝓢(ℝ,ℂ)) (height : ℝ),
      let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1 : ℝ)
      let First := GeometryLowFirstIndex reflected inp 1 1 (Z^(1 : ℝ)) Z (μ/64) hK key
      ∃ υ : First → elementPool P → Fin 3 → RayCharacter → Character,
        (∀ f q i ψ, (υ f q i ψ).modulus.absNorm ≤
          radicalBound (childCharacter
            (geometryColumnCharacter reflected inp 1 1 (Z^(1 : ℝ)) Z (μ/64) hK key f.1.val) ψ)
            fixedBadMask q.val (errorMovingExponent (errorIndex i))) ∧
        geometryLiveBudget reflected inp 1 1 (Z^(1 : ℝ)) Z (μ/64) 1
          (Real.logb Z (volume inp)) hK key
          (fun q => normPhase (coordinateBlock inp 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))
          (Fintype.card T) (9/4) height ≤
        C * (p.control {(0,0)})^2 *
          geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
          Z^(-(1/20 : ℝ)) +
        (56/(P.card : ℝ)) *
          (((amplifierCap 2 0 1 + 6*amp)/(amp/2)) *
            ‖geometryMainRetainedSum reflected inp 1 1 Z 1 amp (μ/64) (μ/8) (9/4) height hZ key
              1 (Real.logb Z (volume inp))
              (fun q => normPhase (coordinateBlock inp 1 1 Ψ (Z^(1 : ℝ)) Z (μ/64) q))‖ +
            ‖geometryAffineErrorRetainedSum inp Ψ Z amp (μ/64) (μ/8) height hZ reflected key P υ‖) := by
  obtain ⟨Cs, hCs, hsources⟩ := eventual_actual_affine_exceptional_source_gates (α := α)
    rayM H hH W hW hWs
  obtain ⟨Cm, hCm, hmain⟩ := uniform_actual_affine_main_remainder (α := α) Cs μ hCs hμ hμcap
  obtain ⟨Ce, hCe, herror⟩ := uniform_actual_affine_error_remainder (α := α) Cs μ hCs hμ hμcap
  refine ⟨56*2048*Cm+Ce, by positivity, ?_⟩
  have hamp := actual_affine_geometry_amplification (α := α) rayM H hH Sbad hbad W hW hWs
    loss mesh (μ/64) (μ/8) hloss hmesh (by positivity) (by linarith) (by positivity)
  have hcop := eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh
  filter_upwards [hsources, hmain, herror, hamp, hcop] with Z hs hm he ha hc
  refine ⟨hs.1, ?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone inp beta amp P
  have capsAmbient := hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have caps : GeometryAffineExceptionalSourceGates inp p (Fintype.card T) Cs Z :=
    { capsAmbient with card := le_rfl }
  have hcell := Cycle61.Moment.originalCell_mem ⟨hwlo, hwhi⟩
  have hb := Cycle61.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  have hV := actual_affine_exceptional_volume_cell rayM H hH η₀ θ W hW hWs w σ freq hσ
    state p t X₁ X₂ hX₁ hX₂ hZ hlo₁ hlo₂ ⟨hwlo, hwhi⟩ hcone
  have amplified := ha.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
  refine ⟨amplified.1, amplified.2.1, ?_⟩
  intro reflected key Ψ height hK First
  have hp : ∀ Q ∈ P, Prime Q := fun Q hQ => (primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  have hgood : ∀ Q ∈ P, Q ∉ fixedBadPrimes := fun Q hQ =>
    (primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  have hpcap : ∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z^amp := by
    intro Q hQ
    have hn := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) amp) (Finset.mem_sdiff.mp hQ).1
    simpa only [mul_one] using hn.2
  have hmatches : Matches rayM H hH inp η₀ θ w σ freq W 2 Z := by
    constructor <;> intros <;> rfl
  have hslots := hc.2 beta hb.1 hb.2 inp η₀ θ w σ freq W hmatches hwm
  have main := hm hZ T inp p caps beta hb hV Ψ height reflected key
  have errors := he hZ T inp p caps beta hb hV P amplified.1 hp hgood hpcap hslots Ψ height reflected key
  have hframeZ : amplifiedRadiusFrame inp Z amp μ reflected key Ψ height P Z (zero_lt_one.trans hZ) :=
    amplified.2.2 reflected key
    (fun q => normPhase (coordinateBlock inp 1 1 Ψ Z Z (μ/64) q)) (Fintype.card T) height
  have hRadius : (⟨Z,zero_lt_one.trans hZ⟩ : {r : ℝ // 0 < r}) = ⟨Z^(1 : ℝ),hK⟩ :=
    Subtype.ext (Real.rpow_one Z).symm
  have hType := congrArg (fun r : {r : ℝ // 0 < r} =>
    amplifiedRadiusFrame inp Z amp μ reflected key Ψ height P r.val r.property) hRadius
  have hframePow := Eq.mp hType hframeZ
  obtain ⟨τ, hτ, hbound⟩ := hframePow
  let υ := fun f : First => τ f.1 f.2
  refine ⟨υ, ?_, ?_⟩
  · intro f q i ψ
    exact hτ f.1 f.2 q i ψ
  have hn : (1 : ℝ) ≤ P.card := by exact_mod_cast amplified.1.card_pos
  have havg : 0 ≤ 56/(P.card : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have havg56 : 56/(P.card : ℝ) ≤ 56 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr
    linarith
  have hcoefficient := geometry_affine_main_amplifier_bound beta hb
  have hfactor : 0 ≤ (p.control {(0,0)})^2 *
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key *
        Z^(-(1/20 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (geometry_high_factor_pos reflected _ key
        (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simp only [mul_assoc] at hfactor
  have main' := main
  simp only [geometryAffineMainSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, mul_assoc] at main'
  have errors' := errors υ
  simp only [geometryAffineErrorSourceTotal, Fintype.sum_sigma, geometryLowFirstChild, υ, mul_assoc] at errors'
  have joined := retained_remainder_join _ _ _ _ _ _ _ Cm Ce _ havg havg56
    hcoefficient.1 hcoefficient.2 hCm.le hfactor hbound main' errors'
  convert joined using 1
  simp only [mul_assoc, amp, υ]

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_geometry_retained_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineRetainedBudget -/
