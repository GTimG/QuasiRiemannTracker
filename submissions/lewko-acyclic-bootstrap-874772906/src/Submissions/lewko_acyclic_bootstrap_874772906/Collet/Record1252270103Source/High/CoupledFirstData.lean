/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal coupled finite coefficients, preserving the original tuple/column sets.
Support is extracted from an actual nonzero tuple, never an ordinary column sum.
Reuses pinned OpenAI/Hailey Collet source and common-label algebra. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CoupledProfile
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalActiveDictionary
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceZeroEnergy CenteredMomentAddedZeroUniform
open CenteredMomentSecondActiveCount CenteredMomentActiveSource CenteredMomentCommonHarmonicMass
open Record1252270103Source CenteredMomentOriginalCommonHarmonic
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance coupledFirstDataDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def tupleCoefficient (s:Input ι) (modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed:Ideal O) :=
  fun v=>modifier v*profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v

def coefficient (s:Input ι) (modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed:Ideal O) : Ideal O→ℂ :=
  finiteColumnCoefficient (Fintype.piFinset s.pools) (tupleCoefficient s modifier R seed)

theorem coupled_coefficient_eq (s:Input ι) (A₁ A₂ D₀:Ideal O) (F:Ideal O→ℂ) (R seed:Ideal O) :
    coefficient s (coupledFactor A₁ A₂ D₀ F) R seed=
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (coupledProfile A₁ A₂ D₀ F R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) := rfl

omit [DecidableEq ι] in
theorem tuple_nonzero (s:Input ι) (modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed:Ideal O)
    (v:Tuple ι) (hv:tupleCoefficient s modifier R seed v≠0) :
    profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v≠0 :=
  (mul_ne_zero_iff.mp hv).2

omit [DecidableEq ι] in
 theorem original_column_mask (s:Input ι) (modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed I:Ideal O) (h:coefficient s modifier R seed I≠0):
    seed∣I:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (tupleCoefficient s modifier R seed) I h
  have hv0 := tuple_nonzero s modifier R seed v hv0
  rw [←he]
  by_contra hn
  apply hv0
  simp only [profileCoefficient,hn,ite_false,mul_zero]

omit [DecidableEq ι] in
 theorem original_column_norm (s:Input ι) (modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed I:Ideal O)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (h:coefficient s modifier R seed I≠0):
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤sourceRadius s:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (tupleCoefficient s modifier R seed) I h
  have hv0 := tuple_nonzero s modifier R seed v hv0
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    have hh:=(s.support i hn).1
    linarith [s.lo_pos i]
  have hh:=profileCoefficient_product_bound R s.ν s.W s.P s.hi s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product hz hz₁ hz₂
    (fun i x hx=>(s.support i hx).2) (fun x hx=>s.support₁ hx) (fun x hx=>s.support₂ hx) v hv0
  rw [he] at hh
  simpa only [CenteredMomentOriginalCommonHarmonic.sourceRadius,map_one,Nat.cast_one,mul_one,div_one] using hh

omit [DecidableEq ι] in
 theorem actual_common_gates (s:Input ι) (modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed:Ideal O) (hs:Squarefree seed)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (C D:Ideal O)
    (hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed)))
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed)))):
    C≠0 ∧ D≠0 ∧ CompletedGauss.primeSupport C=CompletedGauss.primeSupport D ∧
      seed∣C ∧ seed∣D ∧ (Ideal.absNorm C:ℝ)≤sourceRadius s ∧ (Ideal.absNorm D:ℝ)≤sourceRadius s:=by
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s modifier R seed
  have hm (I:Ideal O) (_:I∈S) (hI:β I≠0):seed∣I:=original_column_mask s modifier R seed I hI
  have hp:(C,D)∈commonShell S β (Ideal.absNorm (CenteredMomentRankinRadical.commonRadical C D):ℝ):=
    Finset.mem_filter.mpr ⟨hlabel,le_rfl⟩
  have hh:=active_common_data S β seed hs hm _ (C,D) hp
  have hn:=commonLabel_norm_bounds S β (sourceRadius s)
    (fun I _ hI=>(original_column_norm s modifier R seed I hz₁ hz₂ hI).2) C D hlabel
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hn⟩

omit [DecidableEq ι] in
 theorem actual_original_common_mass (B δ:ℝ) (hB:0≤B) (hδ:0<δ):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z → ∀(s:Input ι) (modifier:CenteredMomentAddedZeroUniform.Tuple ι→ℂ),s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ∀R seed:Ideal O,Squarefree seed → seed≠0 → ∀Y:ℝ,
      (∑v∈partitionLabels (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed) Y,
        1/Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm))≤C*Z^δ/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hbound⟩:=common_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ s modifier hz₁ hz₂ hcap R seed hs hs0 Y
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s modifier R seed
  have hm (I:Ideal O) (_:I∈S) (hI:β I≠0):seed∣I:=original_column_mask s modifier R seed I hI
  have hN (I:Ideal O) (_:I∈S) (hI:β I≠0):(Ideal.absNorm I:ℝ)≤Z^B:=
    (original_column_norm s modifier R seed I hz₁ hz₂ hI).2.trans hcap
  apply hbound Z hZ seed hs hs0 (partitionLabels S β Y)
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β Y v).mp hv
    have hh:=active_common_data S β seed hs hm Y v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    have hp:=(mem_partitionLabels S β Y v).mp hv
    exact commonLabel_norm_bounds S β (Z^B) hN v.1.1 v.1.2 (Finset.mem_filter.mp hp.1).1


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.original_column_norm
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_common_gates
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_original_common_mass
