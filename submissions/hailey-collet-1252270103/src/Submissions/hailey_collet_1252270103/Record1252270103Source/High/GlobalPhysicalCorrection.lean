/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The element-pool corrected MAIN coefficient is the literal ideal-pool
correction in the marked tuple coefficient; D resets to one exactly. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalMain
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.NewtonIdealCounts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindow
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentPrimeElements
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonRadialData CenteredMomentPrimePool CenteredMomentHeckeColumnWindow
open Record1252270103Source Record1252270103Source.Collision
open CenteredMomentFirstPhysicalSource
open QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O

theorem eligible_generator_pool (P S : Finset (Ideal O))
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (I : supportedColumns S) :
    Record1252270103Source.eligiblePool (elementPool P) (sourceGenerator S I)=
      elementPool (CenteredMomentPrimePool.eligiblePool P I) := by
  rw [←elementPool_eligible P hp hbad I]
  unfold Record1252270103Source.eligiblePool
  apply Finset.filter_congr
  intro p hp
  rw [←generator_span S I,Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton]

theorem corrected_generator_coefficient (P S : Finset (Ideal O))
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (c : supportedColumns S→ℂ) (I : supportedColumns S) :
    correctedCoefficient (elementPool P) (sourceGenerator S) c I=
      (((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P I).card)):ℂ)*c I := by
  unfold correctedCoefficient
  rw [elementPool_card P hp hbad,eligible_generator_pool P S hp hbad I,
    elementPool_card (CenteredMomentPrimePool.eligiblePool P I) (fun Q hQ=>hp Q (Finset.mem_filter.mp hQ).1)
      (fun Q hQ=>hbad Q (Finset.mem_filter.mp hQ).1)]
  have hcard : (CenteredMomentPrimePool.eligiblePool P I).card+
      (idealDividingPool P I).card=P.card := by
    simpa only [CenteredMomentPrimePool.eligiblePool,idealDividingPool,not_not] using
      (Finset.card_filter_add_card_filter_not (s:=P) (p:=fun Q=>¬Q∣(I:Ideal O)))
  have hc : ((CenteredMomentPrimePool.eligiblePool P I).card:ℂ)=
      (P.card:ℂ)-((idealDividingPool P I).card:ℂ) := by
    have hh : ((CenteredMomentPrimePool.eligiblePool P I).card:ℂ)+
        ((idealDividingPool P I).card:ℂ)=(P.card:ℂ) := by exact_mod_cast hcard
    exact eq_sub_of_add_eq hh
  rw [hc]
  push_cast
  rfl

theorem marked_column_multiplier {ι : Type*} [Fintype ι]
    (box : Finset (Tuple ι)) (A₁ A₂ D K : Ideal O) (F G : Ideal O→ℂ)
    (β : Tuple ι→ℂ) (I : Ideal O) :
    G I*finiteColumnCoefficient box (fun v=>markedSourceModifier A₁ A₂ D K F v*β v) I=
      finiteColumnCoefficient box
        (fun v=>markedSourceModifier A₁ A₂ 1 K (fun J=>G J*F (D*J)) v*β v) I := by
  unfold finiteColumnCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have he := (Finset.mem_filter.mp hv).2
  simp only [markedSourceModifier,sourceModifier,coupledFactor,one_mul,he]
  ring

/-- Exact corrected Input coefficient. Every frozen projector and original
column pool survives, while the new correction is evaluated on this column. -/
theorem actual_marked_corrected_coefficient {ι : Type*} [Fintype ι]
    (s : Input ι) (A₁ A₂ D K R seed : Ideal O) (F Γ : Ideal O→ℂ)
    (P : Finset (Ideal O)) (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (I : supportedColumns (finiteColumns (Fintype.piFinset s.pools))) :
    correctedCoefficient (elementPool P)
      (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
      (fun J=>CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K F) R seed J*Γ J) I=
      CoupledFirst.coefficient s
        (markedSourceModifier A₁ A₂ 1 K
          (fun J=>(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P J).card)):ℂ)*F (D*J)))
        R seed I*Γ I := by
  rw [corrected_generator_coefficient P _ hp hbad]
  rw [←mul_assoc]
  unfold CoupledFirst.coefficient CoupledFirst.tupleCoefficient
  apply congrArg (fun x:ℂ=>x*Γ I)
  exact marked_column_multiplier _ A₁ A₂ D K F
    (fun J=>(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P J).card)):ℂ))
    (fun v=>CenteredMomentSourceProfileMass.profileCoefficient R s.ν s.W s.P
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v) I

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.corrected_generator_coefficient
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_column_multiplier
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_marked_corrected_coefficient
