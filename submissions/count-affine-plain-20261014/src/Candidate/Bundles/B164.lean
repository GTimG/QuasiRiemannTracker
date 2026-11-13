/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B140
import Candidate.Bundles.B153
import Candidate.Bundles.B154
import Candidate.Bundles.B163

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorPuncture; sha256 80beae35a045824d10f53427ba9dec659e289e52ae98bbb56d37fdb594051a48 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                            
                                                              
                                                            

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondBlockAggregate
open CenteredMomentFirstCanonicalFamily Cycle61Moment
open CompletedGauss CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAnnularInput
local notation "O" => HeckeFamily.O

/-- A fixed error-puncture exponent follows from the actual first ideal,
amplifier prime and extracted second ideal. It has no slot-count parameter. -/
theorem geometry_error_puncture_norm (Z : ℝ) (hZ : 1< Z)
    (C E : Ideal O) (p : O) (k : ℕ) (hk : k≤7)
    (hC : (C.absNorm:ℝ)≤ Z^(4:ℝ))
    (hp : ((Ideal.span {p}).absNorm:ℝ)≤ Z^(3:ℝ))
    (hE : (E.absNorm:ℝ)≤ Z^(3:ℝ)) :
    (((C*(Ideal.span {p})^k)*E).absNorm:ℝ)≤ Z^(28:ℝ) := by
  have hpow : (((Ideal.span {p})^k).absNorm:ℝ)≤ Z^(21:ℝ) := by
    rw [map_pow,Nat.cast_pow]
    calc
      _≤(Z^(3:ℝ))^k := pow_le_pow_left₀ (Nat.cast_nonneg _) hp k
      _=Z^((3:ℝ)*k) := (Real.rpow_mul_natCast (zero_lt_one.trans hZ).le _ _).symm
      _≤ Z^(21:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le (by exact_mod_cast Nat.mul_le_mul_left 3 hk)
  rw [map_mul,Nat.cast_mul,map_mul,Nat.cast_mul]
  calc
    _≤(Z^(4:ℝ)*Z^(21:ℝ))*Z^(3:ℝ) :=
      mul_le_mul (mul_le_mul hC hpow (Nat.cast_nonneg _) (by positivity)) hE
        (Nat.cast_nonneg _) (by positivity)
    _=Z^(28:ℝ) := by rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)];norm_num

/-- The literal twice-extracted datum has both second ideals bounded by
a fixed exponent. The threshold may depend on the slot cap; the exponent
does not, and the Fourier scale below is the actual card α. -/
theorem eventual_actual_geometry_error_second_caps (N : ℕ)(b bs : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)
      (M amp ξ reserve t : ℝ)(hZ : 1< Z),
      Fintype.card α≤ N → Endpoints b bs bs s → volume s≤ Z^(2:ℝ) →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
        (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0 →
      ∀(p : O),p≠0 → ∀(i : Fin 3),
      (∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→ IsCoprime (Ideal.span {p}) I) →
      ∀(Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
        ((Ideal.span {p})^(errorIndex i+1))) (υ : Character)(v : ℝ)
        (n : GeometryErrorSecondIndex reflected s R seed Z M amp ξ reserve b t
          (Fintype.card α) hZ bin q p i Bp υ v),
      let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v hz₁ hz₂ n
      (d.C.absNorm:ℝ)≤ Z^(3:ℝ) ∧ (d.D.absNorm:ℝ)≤ Z^(3:ℝ) := by
  filter_upwards [eventual_geometry_error_child_source_cap N b bs 1 hb hbs (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s R seed M amp ξ reserve t hZ hn hend hvolume hz₁ hz₂ bin q hf p hp i hcop Bp υ v n d
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  have hchild := hz.2 s 2 hn hend hvolume _ R q.2 _ t hf p hp (errorIndex i+1) hcop
    (errorActiveAllocation _ _ Bp) υ v
  have hchild3 : sourceRadius (geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v)≤ Z^(3:ℝ) := by
    convert hchild using 1 <;> norm_num
    rfl
  have hseed1 := actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
    (fun _=>logAnnulus) q.1.val q.1.property
  have hrad := actual_geometry_error_source_radius_pos reflected s R seed Z M amp ξ reserve hZ bin q p i
  have hg := actual_retained_block_gates _
    (geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v)
    ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin q.1.val)*(Ideal.span {p})^(errorIndex i+1))
    q.1.val.2.1.val hseed1 hz₁ hz₂
    (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i)
    (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ bin q p i)
    Z ξ hrad n
  exact ⟨hg.2.2.1.trans hchild3,hg.2.2.2.trans hchild3⟩

/-- The actual affine error datum admits the common mask exponent 28.
Only source and arithmetic gates occur here; no energy estimate is assumed. -/
theorem actual_geometry_error_puncture {α : Type}[Fintype α][DecidableEq α]
    (reflected : Bool)(s : Input α)(seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ)(hZ : 1< Z)
    (hseed : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^(3:ℝ))(bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s 1 seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O)(hp : p≠0)(hpN : ((Ideal.span {p}).absNorm:ℝ)≤ Z^(3:ℝ))(i : Fin 3)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s 1 seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
      ((Ideal.span {p})^(errorIndex i+1))) (υ : Character)(v : ℝ)
    (n : GeometryErrorSecondIndex reflected s 1 seed Z M amp ξ reserve b t
      (Fintype.card α) hZ bin q p i Bp υ v)(second : Bool)
    (hsecond :
      let d:=geometryErrorSecondDatum reflected s 1 seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v hz₁ hz₂ n
      (d.C.absNorm:ℝ)≤ Z^(3:ℝ) ∧ (d.D.absNorm:ℝ)≤ Z^(3:ℝ)) :
    let d:=geometryErrorSecondDatum reflected s 1 seed Z M amp ξ reserve b t
      (Fintype.card α) hZ bin q p i Bp υ v hz₁ hz₂ n
    let puncture:=d.R*(if second then d.D else d.C)
    puncture≠0 ∧ (puncture.absNorm:ℝ)≤ Z^(28:ℝ) := by
  intro d puncture
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  let C:=geometryColumnIdeal reflected s 1 seed (Z^M) Z ξ hK bin q.1.val
  have hc:=actual_geometry_main_first_norm_caps s 1 seed (Z^M) Z ξ hK hZ.le
    hseed hz₁ hz₂ hsource bin q.1.val
  have hC : (C.absNorm:ℝ)≤ Z^(4:ℝ) := by
    cases reflected
    · exact hc.1
    · exact hc.2
  have hCn : C≠0 := by
    cases reflected
    · exact (geometryFirstSource s 1 seed (Z^M) Z ξ hK bin q.1.val.1).hC.1
    · exact (geometryFirstSource s 1 seed (Z^M) Z ξ hK bin q.1.val.1).hD.1
  have hE : ((if second then d.D else d.C).absNorm:ℝ)≤ Z^(3:ℝ) := by
    cases second
    · exact hsecond.1
    · exact hsecond.2
  have hR : d.R=C*(Ideal.span {p})^(errorIndex i+1) := by
    change (1*C)*(Ideal.span {p})^(errorIndex i+1)=_
    rw [one_mul]
  have hk : errorIndex i+1≤7 := by
    rcases error_extracted_index_cases i with h|h|h <;> omega
  constructor
  · apply mul_ne_zero
    · rw [hR]
      exact mul_ne_zero hCn (pow_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr hp))
    · cases second
      · exact d.hC.1
      · exact d.hD.1
  · change ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ _
    rw [hR]
    exact geometry_error_puncture_norm Z hZ C _ p _ hk hC hpN hE

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_error_puncture_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_second_caps
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_puncture

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorPuncture -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondNormalizedRestriction; sha256 8792cdd8af2e4fd9c3f26e40a3ad133dea2ef33fc8507f8b93688bd0da08954b -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                       

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- One label's complete positive normalized energy, retaining both rays and
all residual projectors. Restricting the outer labels does not alter this term. -/
def secondNormalizedLabelSum (reflected : Bool) (d : SecondInputDatum α)
    (w : ℂ) (t u : ℝ) : ℝ :=
  ∑χ : RayCharacter, ∑ψ : RayCharacter,
    ∑D∈d.block.divisors.filter Squarefree,
      ∑z∈secondLiveColumnRows d.block,
        (‖w‖*d.block.outside*volume d.input.toData)*
          (if reflected then
            ‖normalizedColumn (withHeight d.input (d.τ ψ⁻¹)
              (d.input.t+2*Real.pi*(u-(-t))))
              d.D d.hD d.R d.seed D (-z.val)‖^2
           else
            ‖normalizedColumn (withHeight d.input (d.τ χ)
              (d.input.t+2*Real.pi*(u-t)))
              d.C d.hC d.R d.seed D z.val‖^2)

theorem second_normalized_sum_labels (reflected : Bool)
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    secondNormalizedSum reflected d w t u =
      ∑l,secondNormalizedLabelSum reflected (d l) (w l) t u := by
  exact actual_second_column_reindex (fun l=>(d l).block) _

theorem second_normalized_label_nonneg (reflected : Bool)
    (d : SecondInputDatum α) (w : ℂ) (t u : ℝ) :
    0≤ secondNormalizedLabelSum reflected d w t u := by
  unfold secondNormalizedLabelSum
  apply Finset.sum_nonneg; intro χ _
  apply Finset.sum_nonneg; intro ψ _
  apply Finset.sum_nonneg; intro D _
  apply Finset.sum_nonneg; intro z _
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (second_outside_pos _).le)
      (CenteredMomentExceptionalAmplitudePair.volume_pos _).le
  · split <;> exact sq_nonneg _

/-- Dropping labels can only reduce either positive normalized energy. No
count of labels, rays, or residual ideals is introduced. -/
theorem second_normalized_restrict_le (p : Label→ Prop) [DecidablePred p]
    (reflected : Bool) (d : Label→ SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    secondNormalizedSum reflected (fun l : {l // p l}=>d l.val)
      (fun l=>w l.val) t u ≤ secondNormalizedSum reflected d w t u := by
  rw [second_normalized_sum_labels,second_normalized_sum_labels]
  rw [←Finset.sum_subtype (Finset.univ.filter p) (by simp)
    (fun l=>secondNormalizedLabelSum reflected (d l) (w l) t u)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun l _ _=>second_normalized_label_nonneg reflected (d l) (w l) t u)

/-- Effective weights are label-local, so the same restriction applies to
exact ratio fibers used by retained contraction. -/
theorem second_normalized_ratio_le (W : 𝓢(ℝ,ℂ)) (r : ℤ)
    (reflected : Bool) (d : Label→ SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    secondNormalizedSum reflected
      (fun l : SecondRatioFiber (fun l=>(d l).block) r=>d l.val)
      (secondEffectiveWeight
        (fun l : SecondRatioFiber (fun l=>(d l).block) r=>(d l.val).block)
        (fun l=>w l.val) W) t u ≤
      secondNormalizedSum reflected d
        (secondEffectiveWeight (fun l=>(d l).block) w W) t u := by
  exact second_normalized_restrict_le (fun l=>secondRatioIndex (d l).block=r)
    reflected d (secondEffectiveWeight (fun l=>(d l).block) w W) t u

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_normalized_sum_labels
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_normalized_label_nonneg
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_normalized_restrict_le
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_normalized_ratio_le

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondNormalizedRestriction -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondFullNormalizedContraction; sha256 e47642215cf61c8d114bd777a5f9ac803f1d02567036f0e456484f6e2e9d127e -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                               

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentLogDyadic
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- A uniform estimate for the whole positive family also estimates each
ratio fiber. The two inner Mellin energies use H=1; any outer physical
height factor remains in E. -/
theorem second_normalized_bound_of_full (W : 𝓢(ℝ,ℂ)) (degree windowDegree : ℕ)
    (d : Label→ SecondInputDatum α)(w : Label→ℂ)(E : ℝ)
    (hfull : ∀(reflected : Bool)(t u : ℝ),
      secondNormalizedSum reflected d
        (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
      (E*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) :
    SecondNormalizedBound W degree windowDegree d w (fun _=>E) (fun _=>1) := by
  intro r _ reflected t u
  have hh:=(second_normalized_ratio_le W r reflected d w t u).trans (hfull reflected t u)
  simpa only [div_one,mul_one,ite_self] using hh

/-- Complete normalized energies control the retained block sum. Only the
number of ratio bins is paid; the source-label count never appears. -/
theorem retained_from_full_normalized (W : 𝓢(ℝ,ℂ))(degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤ C ∧ ∀{L : Type*}[Fintype L]
      (d : L→ SecondInputDatum α)(w : L→ℂ)(E : ℝ),0≤ E →
      (∀(reflected : Bool)(t u : ℝ),
        secondNormalizedSum reflected d
          (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
        (E*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) →
      ‖∑l,w l*(d l).block.value W‖≤
        C*((secondRatioBins (fun l=>(d l).block)).card:ℝ)*E := by
  obtain ⟨C,hC,hcon⟩:=restricted_second_ratio_from_normalized (α:=α)
    W 0 degree windowDegree hc hs
  refine ⟨C,hC,?_⟩
  intro L _ d w E hE hfull
  have hh:=hcon d w (fun _=>E) (fun _=>1)
    (fun _ _=>hE) (fun _ _=>by norm_num)
    (second_normalized_bound_of_full W degree windowDegree d w E hfull)
  simpa only [pow_zero,div_one,Finset.sum_const,nsmul_eq_mul,mul_assoc] using hh

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_normalized_bound_of_full
#print axioms OAI.SevenEighths.Cycle61InitialMass.retained_from_full_normalized

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondFullNormalizedContraction -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondRatioBox; sha256 d6652208f0851946ad211c9ff23ef1ad6895718c7a72097c20939d7c3656c53b -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                   

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open CenteredMomentLogDyadic CenteredMomentSectorLocalization

/-- A common four-dyad box bounds the ratio image even when arbitrarily
many source labels share the same dyads. -/
theorem second_ratio_bins_card_le_box {Label : Type*} [Fintype Label]
    (s : Label → SecondBlockSource) (box : Finset (Fin 4 → ℤ))
    (hbox : ∀ l, (s l).dyad ∈ box) :
    (secondRatioBins s).card ≤ box.card := by
  let ratio := fun n : Fin 4 → ℤ => n 0 + n 1 - n 2 - n 3
  have hsub : secondRatioBins s ⊆ box.image ratio := by
    intro r hr
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image.mpr ⟨(s l).dyad, hbox l, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Pay the ratio overhead from its actual shared box. This estimate
does not bound the normalized energy; that remains a separate input. -/
theorem second_ratio_decay_le_box {Label : Type*} [Fintype Label]
    (s : Label → SecondBlockSource) (box : Finset (Fin 4 → ℤ))
    (hbox : ∀ l, (s l).dyad ∈ box) (E : ℝ) (hE : 0 ≤ E) (A : ℕ) :
    (∑ r ∈ secondRatioBins s, E / (1 + dyadicScale r)^A) ≤ (box.card : ℝ)*E := by
  have hcount : ((secondRatioBins s).card : ℝ) ≤ box.card := by
    exact_mod_cast second_ratio_bins_card_le_box s box hbox
  calc
    _ ≤ ∑ _r ∈ secondRatioBins s, E := Finset.sum_le_sum (fun r _ =>
      div_le_self hE (one_le_pow₀ (by linarith [dyadicScale_pos r])))
    _ = ((secondRatioBins s).card : ℝ)*E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hE

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_ratio_bins_card_le_box
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_ratio_decay_le_box

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondRatioBox -/
