import Candidate.Target830.Marked.Schedule
import Candidate.Cycle63.Physical.InitialMass.MarkedParameterSchedule
import Candidate.Target830.Parameters
import Candidate.Target830.Source.LowPhysical.AffineMainLowPayment
import Candidate.Target830.High.AffinePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineUniformSchedule
import Candidate.Target830.High.MainCompletePayment

/- Original module: Candidate.Target830.Marked.UniformSchedule. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Marked830Plain
noncomputable section
open scoped Classical ContDiff
open Cycle63Moment Cycle63InitialMass Cycle63MarkedPlain

def rawHeight830 (τ : ℝ) : ℝ := min τ (rawCore830*rawWitness830/16)

theorem raw_height830_gates (τ : ℝ) (hτ : 0<τ) :
    0< rawHeight830 τ ∧ rawHeight830 τ≤τ ∧ rawHeight830 τ< rawCore830/2 ∧
      4*rawHeight830 τ< rawCore830*rawWitness830 := by
  have hpos : 0< rawCore830*rawWitness830/16 := by norm_num [rawCore830,rawWitness830]
  have hsmall : rawHeight830 τ≤ rawCore830*rawWitness830/16 := min_le_right _ _
  refine ⟨lt_min hτ hpos,min_le_left _ _,?_,?_⟩
  · exact hsmall.trans_lt (by norm_num [rawCore830,rawWitness830])
  · calc
      4*rawHeight830 τ≤4*(rawCore830*rawWitness830/16) := mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _< rawCore830*rawWitness830 := by norm_num [rawCore830,rawWitness830]

theorem raw_height830_preserves_budget (τ μ : ℝ) (J : ℕ)
    (h : 2*τ*((J:ℝ)+1)≤μ/8) : 2*rawHeight830 τ*((J:ℝ)+1)≤μ/8 := by
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (min_le_left τ (rawCore830*rawWitness830/16)) (by norm_num : (0:ℝ)≤2))
    (show (0:ℝ)≤(J:ℝ)+1 by positivity)
  exact hh.trans h

theorem existing_schedule_raw830_gates
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (μ B L bΦ τ : ℝ) (N : ℕ) (bound : ℕ→ℝ)
    (hμ : 0<μ) (hμcap : μ≤1/1000000000000000000) (hB : 0≤ B) (hL : 0≤ L)
    (hbΦ : 0≤ bΦ) (hτ : 0<τ) (hbound : ∀k,0≤ bound k) :
    let P := geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N bound hμ hB hL hbΦ hτ hbound
    P.e≤μ/294912 ∧
      12*P.e*((22:ℝ)+2)+8*rawWitness830+2*rawWitness830≤ rawRate830/2 ∧
      2*P.εslot*P.d≤ rawBin830*rawTiny830 N ∧
      (2*P.εslot*P.d)*(N:ℝ)≤μ/32 := by
  intro P
  have hh:=Cycle63MarkedPlain.existing_schedule_marked_gates W hWs hW μ B L bΦ τ N bound
    hμ (hμcap.trans (by norm_num)) hB hL hbΦ hτ hbound
  refine ⟨hh.1,?_,?_,hh.2.2.2⟩
  · norm_num [rawWitness830,rawRate830] at ⊢
    linarith [hh.1]
  · change 2*geometryFinalDictionaryRate μ 31 3 4 3 B L N*31≤ rawBin830*rawTiny830 N
    have hd := min_le_right (geometryCommonDictionaryRate μ 31 3 4 3 B L N)
      (μ/(64*(31+1)*((N:ℝ)+1)))
    change geometryFinalDictionaryRate μ 31 3 4 3 B L N≤ _ at hd
    have hn : (0:ℝ)<(N:ℝ)+1 := by positivity
    have hδ := (le_div_iff₀ (show (0:ℝ)<64*(31+1)*((N:ℝ)+1) by positivity)).mp hd
    unfold rawBin830 rawTiny830
    rw [mul_one_div]
    apply (le_div_iff₀ (show (0:ℝ)<1000000000*((N:ℝ)+1) by positivity)).mpr
    nlinarith only [hδ,hμcap]

/-- A common cutoff, chosen after the finite family of density degrees,
preserves the existing physical selector and also meets every marked
witness gate.  Its mesh was fixed independently in `markedGeometryMesh`. -/
theorem geometry_affine_marked_uniform_schedule {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (μ B L bΦ : ℝ) (N : ℕ) (bound : Finset α→ℕ→ℝ) (J : Finset α→ℕ)
    (hμ : 0<μ) (hμcap : μ≤1/1000000000000000000) (hB : 0≤ B) (hL : 0≤ L) (hbΦ : 0≤ bΦ)
    (hbound : ∀T k,0≤ bound T k) :
    ∃τ : ℝ, ∃hτ : 0<τ, τ≤μ/16 ∧ τ< rawCore830/2 ∧
      4*τ< rawCore830*rawWitness830 ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=geometryFinalDictionaryRate μ 31 3 4 3 B L N ∧ g.τ=τ ∧
      ∀T : Finset α,
        let P:=geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N (bound T)
          hμ hB hL hbΦ hτ (hbound T)
        P.profileBound=bound T ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
          8*P.τ≤ P.d*P.vslot ∧ 16*P.τ≤ P.d*P.vplain ∧
          2*P.τ*((J T:ℝ)+1)≤μ/8 ∧
          12*P.e*((22:ℝ)+2)+8*rawWitness830+2*rawWitness830≤ rawRate830/2 ∧
          2*P.εslot*P.d≤ rawBin830*rawTiny830 N ∧
          (2*P.εslot*P.d)*(N:ℝ)≤μ/32 := by
  let P₀ := fun T : Finset α=>
    geometryAffineFinalHighSchedule W hWs hW μ B L bΦ 1 N (bound T)
      hμ hB hL hbΦ (by norm_num) (hbound T)
  have rates := geometry_final_dictionary_budgets μ 31 3 4 3 B L N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hL
  have hs (T : Finset α) : 0<(P₀ T).vslot := rates.1
  have hp (T : Finset α) : 0<(P₀ T).vplain := by
    change 0< geometryFinalPlainRate μ 31/8
    exact div_pos rates.2.2.2.1 (by norm_num)
  obtain ⟨τ₀,hτ₀,hτcap,hgates⟩ := geometry_uniform_high_height P₀ J μ hμ hs hp
  let τ := rawHeight830 τ₀
  have hnew := raw_height830_gates τ₀ hτ₀
  have hτ : 0<τ := hnew.1
  have hle : τ≤τ₀ := hnew.2.1
  let P := fun T : Finset α=>
    geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N (bound T)
      hμ hB hL hbΦ hτ (hbound T)
  have hcutoff : 2*(P ∅).τ<(P ∅).d*(P ∅).vslot := by
    change 2*τ<(P₀ ∅).d*(P₀ ∅).vslot
    linarith [(hgates ∅).1]
  let g := geometryAffineLowScheduleOfHigh (P ∅) μ hμ
    (hμcap.trans (by norm_num)) rates.2.2.1 rfl rfl hcutoff
  refine ⟨τ,hτ,hle.trans hτcap,hnew.2.2.1,hnew.2.2.2,g,rfl,rfl,rfl,?_⟩
  intro T
  have hg := hgates T
  have hslot : 8*(P T).τ≤(P T).d*(P T).vslot := by
    change 8*τ≤(P₀ T).d*(P₀ T).vslot
    linarith [hg.2.1]
  have hplain : 16*(P T).τ≤(P T).d*(P T).vplain := by
    change 16*τ≤(P₀ T).d*(P₀ T).vplain
    linarith [hg.2.2.1]
  have hheight : 2*(P T).τ*((J T:ℝ)+1)≤μ/8 :=
    raw_height830_preserves_budget τ₀ μ (J T) hg.2.2.2
  have hm := existing_schedule_raw830_gates W hWs hW μ B L bΦ τ N (bound T)
    hμ hμcap hB hL hbΦ hτ (hbound T)
  exact ⟨rfl,rfl,rfl,rfl,hslot,hplain,hheight,hm.2.1,hm.2.2.1,hm.2.2.2⟩

theorem geometry_final_marked_schedule
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (μ B L bΦ τ : ℝ) (N : ℕ) (bound : ℕ→ℝ)
    (hμ : 0<μ) (hμcap : μ≤1/1000000000000000000) (hB : 0≤ B) (hL : 0≤ L)
    (hbΦ : 0≤ bΦ) (hτ : 0<τ) (hbound : ∀k,0≤ bound k)
    (hτzero : τ< rawCore830/2) (hτw : 4*τ< rawCore830*rawWitness830) :
    MarkedSchedule830
      (geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N bound hμ hB hL hbΦ hτ hbound)
      N W (33/50) (33/50) := by
  have hh := existing_schedule_raw830_gates W hWs hW μ B L bΦ τ N bound
    hμ hμcap hB hL hbΦ hτ hbound
  exact ⟨rfl,rfl,le_rfl,le_rfl,rfl,by norm_num [geometryAffineFinalHighSchedule,highParameters],
    hτzero,hτw,hh.2.1,hh.2.2.1⟩

end
end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.geometry_affine_marked_uniform_schedule
end

/- Original module: Candidate.Target830.High.UniformSchedule. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open Marked830Plain
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open Cycle63MarkedPlain
open scoped Classical ContDiff
open Filter HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve ConcretePrimeRowBridge Cycle63Moment
local notation "O" => HeckeFamily.O

variable {plane : SourcePlane}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Select every actual-subset density dictionary before fixing one common
height cutoff. Only the scalar loss rate uses the ambient cardinality.
The exact fiber receipt remains explicit until its separate proof is joined. -/
theorem actual_affine_high_uniform_schedule_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤3/4)
    (μ Cs bΦ : ℝ)(hμ : 0<μ)(hμcap : μ≤1/1000000000000000000)(hCs : 1≤ Cs)(hbΦ : 2≤ bΦ)
    (fiberReceipt : ∀T : Finset α,
      TargetHigh830.GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=TargetHigh830.geometryAffineHighDictionaryRate μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=δ ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        TargetHigh830.GeometryAffineHighScheduleGates W μ δ P ∧
        ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0< K ∧
        ∀(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}),
          ∀ᶠZ : ℝ in atTop,2≤ Z ∧
            TargetHigh830.GeometryAffineHighSelectedCostSpec (α:=T) M H hH plane W hbeta P μ δ
              (TargetHigh830.geometryAffineHighTarget μ δ) (fun _ _ _ _ _=> True)
              (excluded F₀.character R₀) Cs Sp degree K η₀ Q hQM hQ72 Z := by
  intro δ
  have high (T : Finset α) := TargetHigh830.actual_affine_high_selected_all_height_of_fibers (plane:=plane)
    (α:=T) M H hH η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs (Fintype.card α)
    hμ (hμcap.trans (by norm_num)) hCs (Fintype.card_le_of_injective (fun i : T=> i.val) Subtype.val_injective)
    (fiberReceipt T)
  choose bound hbound J hhigh using high
  have hL : 0≤3*((Fintype.card α:ℝ)+2) := by positivity
  have hb : 0≤ bΦ := by linarith
  obtain ⟨τ,hτ,hτcap,hτzero,hτw,g,hgμ,hgδ,hgτ,hschedule⟩:=Marked830Plain.geometry_affine_marked_uniform_schedule
    W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2)) bΦ (Fintype.card α) bound J
    hμ hμcap (by norm_num) hL hb (fun T k=>(hbound T k).le)
  refine ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,?_⟩
  intro T
  let P:=geometryAffineFinalHighSchedule W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2))
    bΦ τ (Fintype.card α) (bound T) hμ (by norm_num) hL hb hτ (fun k=>(hbound T k).le)
  have hs:=hschedule T
  have gates : TargetHigh830.GeometryAffineHighScheduleGates W μ δ P :=
    TargetHigh830.geometry_affine_high_schedule_gates W hWs hW μ bΦ τ (Fintype.card α) (bound T)
      hμ hbΦ hτ (fun k=>(hbound T k).le)
  refine ⟨P,rfl,rfl,hs.2.1,hs.2.2.1,hs.2.2.2.1,gates,?_⟩
  have hmarked : MarkedSchedule830 P (Fintype.card T) W (33/50) (33/50) :=
    (Marked830Plain.geometry_final_marked_schedule W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2))
      bΦ τ (Fintype.card α) (bound T) hμ hμcap (by norm_num) hL hb hτ
      (fun k=>(hbound T k).le) hτzero hτw).of_card_le
      (Fintype.card_le_of_injective (fun i : T=> i.val) Subtype.val_injective)
  exact hhigh T P hs.1 gates hmarked hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1

/-- Actual source caps are fixed before the shared schedule; each literal
affine high estimate then has its constants before any moving source. -/
theorem actual_affine_high_uniform_literal_schedule_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤3/4)
    (μ bΦ : ℝ)(hμ : 0<μ)(hμcap : μ≤1/1000000000000000000)(hbΦ : 2≤ bΦ)
    (fiberReceipt : ∀T : Finset α,
      TargetHigh830.GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=TargetHigh830.geometryAffineHighDictionaryRate μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=δ ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        TargetHigh830.GeometryAffineHighScheduleGates W μ δ P ∧
        ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0< K ∧
        ∀(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}),
          ∀ᶠZ : ℝ in atTop,2≤ Z ∧
            TargetHigh830.GeometryAffineMainHighSpec (α:=T) M H hH plane W hW.continuous hWs hbeta P μ δ
              (TargetHigh830.geometryAffineHighTarget μ δ) (excluded F₀.character R₀)
              Sp degree K η₀ Q hQM hQ72 Z := by
  intro δ
  obtain ⟨Cs,hCs,hcaps⟩:=Source.LowPhysical.eventual_actual_affine_exceptional_source_gates (α:=α) M H hH
    W hW.continuous hWs
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hhigh⟩:=actual_affine_high_uniform_schedule_of_fibers
    (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs bΦ hμ hμcap hCs hbΦ fiberReceipt
  refine ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,?_⟩
  intro T
  obtain ⟨P,hPτ,hPb,he,hκ,hv,gates,Sp,hSp,degree,K,hK,hpaid⟩:=hhigh T
  refine ⟨P,hPτ,hPb,he,hκ,hv,gates,Sp,hSp,degree,K,hK,?_⟩
  intro Q hQM hQ72
  filter_upwards [hpaid Q hQM hQ72,hcaps,eventual_geometry_small_frequency μ hμ]
    with Z hp hc hf
  refine ⟨hp.1,?_⟩
  apply TargetHigh830.affine_main_high_spec_of_receipts (α:=T) M H hH plane W hW.continuous hWs hbeta
    P μ δ (TargetHigh830.geometryAffineHighTarget μ δ) (excluded F₀.character R₀) Cs Sp degree K
    η₀ Q hQM hQ72 Z hμ (hμcap.trans (by norm_num)) hf.2 _ hp.2
  unfold Source.LowPhysical.GeometryAffineMainLowSourceSpec
  intro θ η w σ freq hσ b state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots inp
  exact geometry_affine_source_gates_actual_card inp p (Fintype.card α) Cs Z
    (hc.2 T η θ w σ freq hσ b state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots)

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_affine_high_uniform_schedule_of_fibers
#print axioms OAI.SevenEighths.TargetHigh830.actual_affine_high_uniform_literal_schedule_of_fibers
end

/- Original module: Candidate.Target830.High.MainUniform. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource
open CenteredMomentEnergyState CenteredMomentEnergyBands
local notation "O" => HeckeFamily.O

variable {plane : SourcePlane}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The common cutoff and the actual paid main terms are constructed from
the fixed natural source. The separate selected-fiber proof is the only
remaining high analytic premise. -/
theorem actual_affine_main_uniform_paid_of_fibers
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow η₀ u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)(hεcap : εaffine≤1/10000000000000000)
    (hmesh : mesh< Source.amplifierMinimum/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ Marked830Plain.rawMesh830*Marked830Plain.rawCore830)
    (hbΦ : 2≤ bΦ)
    (fiberReceipt : ∀T : Finset α,
      TargetHigh830.GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (geometryLossUnit 1 εaffine/8) 3 1 (geometryLossUnit 1 εaffine/64)) :
    ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤ M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineMainPaidSpec (plane:=plane) M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  let μ:=geometryLossUnit 1 εaffine
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/1000000000000000000 := by
    have hh:=min_le_left (εaffine/128)
      (min ((7/30000000:ℝ)*1/128) (min ((1:ℝ)/128) (1/128)))
    change μ≤εaffine/128 at hh
    linarith
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hhigh⟩:=
    actual_affine_high_uniform_literal_schedule_of_fibers (plane:=plane) (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀
      W hWs hW hβlo (by linarith) μ bΦ hμ hμcap hbΦ fiberReceipt
  refine ⟨τ,hτ,hτcap,?_⟩
  intro Q hQM hQ hQt hQ72
  have hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130
      (3*((Fintype.card α:ℝ)+2)) (Fintype.card α) := by
    simpa only [TargetHigh830.geometryAffineHighDictionaryRate,hgμ] using hgδ
  have hmeshμ' : mesh≤ g.μ/8 := by simpa only [hgμ] using hmeshμ
  have hmeshcap' : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8) := by
    simpa only [hgμ] using hmeshcap
  have hpaid:=actual_affine_main_uniform_paid_of_high (α:=α) M H hH A hc hs Sbad hbad
    W hW hWs hβlo hβhi (excluded F₀.character R₀) εaffine mesh hε hmesh hmesh0 g hgμ
    (Fintype.card α) le_rfl 130 (3*((Fintype.card α:ℝ)+2)) (by norm_num) (by positivity)
    hδ hmeshμ' hmeshcap' hmarkedmesh η₀ u₀ F₀ R₀ hu₀ η₀ Q hQM hQ hQt hQ72 (by
      intro T
      obtain ⟨P,hPτ,hPb,he,hκ,hv,gates,SH,hSH,dh,KH,hKH,hcost⟩:=hhigh T
      refine ⟨P,he.symm,hPτ.trans hgτ.symm,SH,dh,KH,hKH.le,?_⟩
      filter_upwards [hcost Q hQM hQ72] with Z hz
      simpa only [hgμ,hgδ] using hz.2)
  simpa only [hgμ] using hpaid

/-- The fixed-source main payment has no remaining analytic branch premise. -/
theorem actual_affine_main_uniform_paid
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow η₀ u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)(hεcap : εaffine≤1/10000000000000000)
    (hmesh : mesh< Source.amplifierMinimum/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ Marked830Plain.rawMesh830*Marked830Plain.rawCore830)
    (hbΦ : 2≤ bΦ)
    :
    ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤ M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineMainPaidSpec (plane:=plane) M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  exact actual_affine_main_uniform_paid_of_fibers (α:=α) M H hH A hc hs Sbad hbad W hW hWs
    hβlo hβhi η₀ u₀ F₀ R₀ hu₀ εaffine mesh bΦ hε hεcap hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hbΦ
    (fun T=> TargetHigh830.geometry_affine_high_selected_fiber_receipt (α:=T) η₀ u₀ F₀ R₀ hu₀
      (geometryLossUnit 1 εaffine) (geometry_loss_unit_pos 1 εaffine (by norm_num) hε))

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_affine_main_uniform_paid_of_fibers

#print axioms OAI.SevenEighths.TargetHigh830.actual_affine_main_uniform_paid
end
