/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal correction is bounded only on actual nonzero source tuples. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.SecondRemainder.SupportedTuple
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.Projector
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.NewtonIdealCounts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationCount
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentAmplificationCount
open CenteredMomentOriginalCommonHarmonic Record1252270103Source Collision QRH.Record1252270103Low
local notation "O"=>ActualEisensteinCubic.O
local instance correctionTupleDecidable {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

lemma correction_norm_le_two (P : Finset (Ideal O)) (hP : P.Nonempty)
    (hp : ∀p∈P,Prime p) (I : Ideal O) (hI : I≠0)
    (Z ell B : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hlower : ∀p∈P,Z^ell≤(p.absNorm:ℝ))
    (hupper : (I.absNorm:ℝ)≤Z^B) (hsize : 2*(B/ell)≤(P.card:ℝ)) :
    ‖(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P I).card)):ℂ)‖≤2 := by
  have hc : ((idealDividingPool P I).card:ℝ)≤B/ell :=
    indexed_large_prime_divisor_count (idealDividingPool P I) (fun p=>p)
      (fun _ _ _ _ h=>h) (fun p h=>hp p (Finset.mem_filter.mp h).1) I hI
      (fun p h=>(Finset.mem_filter.mp h).2) Z ell B hZ hell
      (fun p h=>hlower p (Finset.mem_filter.mp h).1) hupper
  have hn : (0:ℝ)<P.card := by exact_mod_cast hP.card_pos
  have hd : (0:ℝ)<(P.card:ℝ)-(idealDividingPool P I).card := by linarith
  have hr : 0≤(P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P I).card) :=
    div_nonneg (Nat.cast_nonneg _) hd.le
  have hb : (P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P I).card)≤2 :=
    (div_le_iff₀ hd).mpr (by linarith)
  simpa only [←Complex.ofReal_natCast,←Complex.ofReal_sub,←Complex.ofReal_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr] using hb

def correctedModifier {ι : Type*} [Fintype ι] (P : Finset (Ideal O))
    (A₁ A₂ D K : Ideal O) (F : Ideal O→ℂ) : Tuple ι→ℂ :=
  markedSourceModifier A₁ A₂ 1 K
    (fun J=>(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P J).card)):ℂ)*F (D*J))

lemma marked_modifier_norm_le {ι : Type*} [Fintype ι]
    (A₁ A₂ D K : Ideal O) (F : Ideal O→ℂ) (v : Tuple ι)
    (bound : ℝ) (hb : 0≤bound) (hF : ‖F (D*finiteTupleProduct v)‖≤bound) :
    ‖markedSourceModifier A₁ A₂ D K F v‖≤bound := by
  have hi : ‖(QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*markedProduct v))‖≤1 := by
    unfold QRH.Record1252270103TwoIdeal.squarefreeIndicator
    split_ifs <;> norm_num
  rw [markedSourceModifier,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hi).trans
    (sourceModifier_norm_le A₁ A₂ D F v bound hb hF)

theorem corrected_modifier_bound {ι : Type*} [Fintype ι]
    (s : Input ι) (A₁ A₂ D K R seed : Ideal O) (F : Ideal O→ℂ)
    (P : Finset (Ideal O)) (hP : P.Nonempty) (hp : ∀p∈P,Prime p)
    (Z ell B Fcap : ℝ) (hZ : 1<Z) (hell : 0<ell) (hFcap : 0≤Fcap)
    (hlower : ∀p∈P,Z^ell≤(p.absNorm:ℝ)) (hsize : 2*(B/ell)≤(P.card:ℝ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B)
    (hF : ∀I,‖F I‖≤Fcap) :
    ∀v∈Fintype.piFinset s.pools,
      High.CoupledFirst.tupleCoefficient s (correctedModifier P A₁ A₂ D K F) R seed v≠0→
      ‖correctedModifier P A₁ A₂ D K F v‖≤2*Fcap := by
  intro v hv hn
  have hg:=tuple_radius s (correctedModifier P A₁ A₂ D K F) R seed hz₁ hz₂ v hn
  have hc:=correction_norm_le_two P hP hp (finiteTupleProduct v) hg.1 Z ell B hZ hell
    hlower (hg.2.trans hsource) hsize
  apply marked_modifier_norm_le A₁ A₂ 1 K _ v (2*Fcap) (by positivity)
  simpa only [one_mul,norm_mul] using
    mul_le_mul hc (hF (D*finiteTupleProduct v)) (norm_nonneg _) (by norm_num : (0:ℝ)≤2)

theorem corrected_one_modifier_bound {ι : Type*} [Fintype ι]
    (s : Input ι) (A₁ A₂ D K R seed : Ideal O)
    (P : Finset (Ideal O)) (hP : P.Nonempty) (hp : ∀p∈P,Prime p)
    (Z ell B : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hlower : ∀p∈P,Z^ell≤(p.absNorm:ℝ)) (hsize : 2*(B/ell)≤(P.card:ℝ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B) :
    ∀v∈Fintype.piFinset s.pools,
      High.CoupledFirst.tupleCoefficient s (correctedModifier P A₁ A₂ D K (fun _=>1)) R seed v≠0→
      ‖correctedModifier P A₁ A₂ D K (fun _=>1) v‖≤2 := by
  simpa only [mul_one] using corrected_modifier_bound s A₁ A₂ D K R seed (fun _=>1)
    P hP hp Z ell B 1 hZ hell (by norm_num) hlower hsize hz₁ hz₂ hsource (by intro I;norm_num)
end
end QRH.Record1252270103Source.SecondRemainder
#print axioms QRH.Record1252270103Source.SecondRemainder.correction_norm_le_two
#print axioms QRH.Record1252270103Source.SecondRemainder.corrected_one_modifier_bound
