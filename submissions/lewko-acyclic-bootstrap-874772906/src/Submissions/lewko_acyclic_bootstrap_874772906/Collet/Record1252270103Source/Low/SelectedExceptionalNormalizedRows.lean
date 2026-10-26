/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The complementary selected rows on the original complete-block family are
fixed inducing rows. The original coefficient and zero sector are retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedSecondNaturalState
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CompletedGauss RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondLiveBlock CenteredMomentSectorLocalization
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceProfileMass
open CenteredMomentActiveSource CenteredMomentCompleteCommon CenteredMomentFirstAmplificationChoice
open CenteredMomentRestrictedEnergy CenteredExceptionalProfile CenteredMomentChildRows Cycle61InitialMass
open OAI.SevenEighths.Record1252270103Source
open SecondSectorDatum High.GlobalPhysical Admission.SelectedSecondNatural
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance selectedExceptionalRowsSum {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {α Label:Type*} [Fintype α] [Fintype Label]
variable (slots:Label→Finset α)(s:∀l,Input (slots l))(modifier:∀l,Tuple (slots l)→ℂ)
    (R seed:Label→Ideal O)(K Tsec:Label→ℝ)(Z ξ:ℝ)(W:𝓢(ℝ,ℂ))
    (hseed:∀l,Squarefree (seed l))(hz₁:∀l,(s l).W₁ 0=0)(hz₂:∀l,(s l).W₂ 0=0)
    (hK:∀l,0<K l)(χ₀:Label→RayCharacter)(Q:Ideal O)(m:O)

def exceptionalDatum (q:CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ)):
    SecondInputDatum α :=
  familyDatum slots s modifier R seed hseed hz₁ hz₂ W K Tsec (fun _=>Z) (fun _=>ξ) hK
    (fun l q z=>¬regularKeep slots s modifier R seed K Tsec Z ξ χ₀ Q m l q z) q

/-- Complementation is performed after the original complete-block carrier
is fixed. Every retained row is nonzero, so the complement is exactly induction. -/
theorem exceptional_rows_fixed
    (q:CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ))
    (z:O)(hz:z∈(exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).rows):
    FixedInducingRow (childCharacter (s q.1).η (χ₀ q.1)) Q m
      (exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).block.frequency z := by
  have hn:z≠0 := (exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).rows_ne z hz
  have hk:¬nonexceptional (s q.1).η (χ₀ q.1) Q m
      (exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).block.frequency z :=
    ((restricted_retained_rows (slots q.1) (s q.1) (modifier q.1) (R q.1) (seed q.1)
      (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2.val
      (fun z=>¬regularKeep slots s modifier R seed K Tsec Z ξ χ₀ Q m q.1 q.2.val z) z).mp hz).2
  by_contra h
  exact hk ⟨hn,h⟩

theorem exceptional_live_row_fixed
    (r:secondLiveRows (fun q=>(exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).block)):
    FixedInducingRow (childCharacter (s r.val.1.1).η (χ₀ r.val.1.1)) Q m
      (exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1).block.frequency
      r.val.2.2.2.val := by
  apply exceptional_rows_fixed slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m
  exact r.val.2.2.2.property

/-- The same selected complement supplies the actual ray and either sign. -/
theorem exceptional_actual_row_fixed
    (r:secondLiveRows (fun q=>(exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q).block))
    (ψ:RayCharacter)(second:Bool)(hQ:Q≤Ideal.span {(72:O)})(hml:goodLambda∣m)(hm2:(2:O)∣m):
    FixedInducingRow
      (childCharacter (exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1).input.η ψ)
      Q m (exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1).block.frequency
      (if second then -r.val.2.2.2.val else r.val.2.2.2.val) := by
  have hk:¬nonexceptional (s r.val.1.1).η (χ₀ r.val.1.1) Q m
      (exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1).block.frequency
      r.val.2.2.2.val := fun h=>h.2
        (exceptional_live_row_fixed slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r)
  have hn:= (exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1).rows_ne
    r.val.2.2.2.val r.val.2.2.2.property
  cases second
  · by_contra hh
    exact hk ((nonexceptional_ray_independent (s r.val.1.1).η (χ₀ r.val.1.1) ψ Q hQ m _ _ hml hm2).mpr ⟨hn,hh⟩)
  · by_contra hh
    exact hk ((nonexceptional_reflection (s r.val.1.1).η (χ₀ r.val.1.1) ψ Q hQ m _ _ hml hm2).mpr ⟨neg_ne_zero.mpr hn,hh⟩)
/-- The complete family already retains both original common-character
nonzero gates and both seed divisibilities. They are not new analytic premises. -/
theorem exceptional_original_gates
    (q:CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ)):
    let d:=exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q
    idealCoeff d.input.η d.C≠0 ∧ idealCoeff d.input.η d.D≠0 ∧ d.seed∣d.C ∧ d.seed∣d.D := by
  have hl:=(Finset.mem_filter.mp q.2.val.1.property).2
  have hs:=modified_retained_seed_and_caps (slots q.1) (s q.1) (modifier q.1)
    (R q.1) (seed q.1) (hseed q.1) (hz₁ q.1) (hz₂ q.1)
    (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2.val
  exact ⟨hl.1,hl.2,hs.1,hs.2.1⟩

/-- The full modified column retains the original puncture mask. This uses
a nonzero literal tuple, never a nonzero ordinary column. -/
theorem modified_column_coprime {ι:Type*}[Fintype ι]
    (input:Input ι)(multiplier:Tuple ι→ℂ)(puncture seed I:Ideal O)
    (h:High.CoupledFirst.coefficient input multiplier puncture seed I≠0):
    IsCoprime I puncture := by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset input.pools)
    (High.CoupledFirst.tupleCoefficient input multiplier puncture seed) I h
  have hv0:=High.CoupledFirst.tuple_nonzero input multiplier puncture seed v hv0
  rw [←he]
  by_contra hn
  apply hv0
  simp only [profileCoefficient,hn,ite_false,mul_zero,zero_mul]

/-- A fixed exceptional modulus dividing the actual puncture is coprime to
both common ideals on the original modified live-label carrier. -/
theorem exceptional_common_coprime
    (q:CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ))
    (hQR:Q∣R q.1):
    let d:=exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q
    IsCoprime Q d.C ∧ IsCoprime Q d.D := by
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩:=commonLabel_witnesses _ _ _ _ q.2.val.1.val.property
  have hc:=(modified_column_coprime (s q.1) (modifier q.1) (R q.1) (seed q.1) I hβi).symm
  have hd:=(modified_column_coprime (s q.1) (modifier q.1) (R q.1) (seed q.1) J hβj).symm
  have hc':IsCoprime Q (commonPart I J):=
    (hc.of_isCoprime_of_dvd_left hQR).of_isCoprime_of_dvd_right (commonPart_dvd I J hIs.1)
  have hd':IsCoprime Q (commonPart J I):=
    (hd.of_isCoprime_of_dvd_left hQR).of_isCoprime_of_dvd_right (commonPart_dvd J I hJs.1)
  rw [hC] at hc'
  rw [hD] at hd'
  exact ⟨hc',hd'⟩

/-- The canonical retained ball majorizes every complementary row, including
rows in a zero selected sector. Its scale is the literal retained radius. -/
theorem exceptional_retained_majorant
    (q:CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ)):
    let d:=exceptionalDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q
    let H:=max 1 (4*d.radius/(normValue (commonFrequencyGenerator d.C d.D)*
      normValue (nonunitFrequencyGenerator d.C d.D d.inactive)))
    0<H ∧ ∀z∈d.rows,1≤(ballProfile (normValue z/H)).re := by
  refine ⟨zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro z hz
  have hr:=((restricted_retained_rows (slots q.1) (s q.1) (modifier q.1) (R q.1) (seed q.1)
    (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2.val
    (fun z=>¬regularKeep slots s modifier R seed K Tsec Z ξ χ₀ Q m q.1 q.2.val z) z).mp hz).1
  exact Cycle61FinalRadius.actual_retained_majorant _ _ _ z (liveRows_weight _ _ _ _ _ z hr)

end
end QRH.Record1252270103Source.Low.SelectedExceptionalNormalized
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.exceptional_rows_fixed
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.exceptional_live_row_fixed
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.exceptional_actual_row_fixed

#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.exceptional_original_gates

#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.modified_column_coprime
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.exceptional_common_coprime
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalNormalized.exceptional_retained_majorant
