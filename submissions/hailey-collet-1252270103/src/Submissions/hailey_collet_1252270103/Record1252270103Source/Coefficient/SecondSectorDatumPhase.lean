/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact two-sector phase identity on the original complete-block nonzero type.
Neither sector replaces the complete-block zero filter. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SecondSectorDatum
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondRemainder
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.Decomposition
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondSectorDatum
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open Cycle61InitialMass Record1252270103Second
open QRH.Record1252270103Source.High.GlobalPhysical
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance secondSectorPhaseSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

abbrev CompleteBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ : ℝ) :=
  {q : BlockIndex s modifier R seed H Tsec Z ξ //
    Record1252270103Second.originalBlock s modifier R seed W H Tsec Z ξ q≠0}

def sectorWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ T : ℝ)
    (keep : BlockIndex s modifier R seed H Tsec Z ξ→O→Prop)
    (q : CompleteBlock s modifier R seed W H Tsec Z ξ) : ℂ :=
  ((‖blockWeight s modifier R seed H Tsec Z ξ q.val‖/T:ℝ):ℂ)*
    normPhase (selectedSecondBlock s modifier R seed W H Tsec Z ξ q.val (keep q.val))

theorem norm_nonnegative_phased_sum {κ : Type*} [Fintype κ]
    (a : κ→ℝ) (ha : ∀q,0≤a q) (f : κ→ℂ) :
    ‖∑q,(a q:ℂ)*normPhase (f q)*f q‖=∑q,a q*‖f q‖ := by
  simp_rw [mul_assoc,normPhase_mul,←Complex.ofReal_mul,←Complex.ofReal_sum,
    Complex.norm_real,Real.norm_eq_abs]
  exact abs_of_nonneg (Finset.sum_nonneg (fun q _=>mul_nonneg (ha q) (norm_nonneg _)))

theorem sectorWeight_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ T : ℝ) (hT : 0<T)
    (keep : BlockIndex s modifier R seed H Tsec Z ξ→O→Prop)
    (q : CompleteBlock s modifier R seed W H Tsec Z ξ) :
    ‖sectorWeight s modifier R seed W H Tsec Z ξ T keep q‖≤
      ‖blockWeight s modifier R seed H Tsec Z ξ q.val‖/T := by
  have h : 0≤‖blockWeight s modifier R seed H Tsec Z ξ q.val‖/T :=
    div_nonneg (norm_nonneg _) hT.le
  rw [sectorWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (normPhase_norm _) h

/-- The phase identity includes all original complete nonzero blocks in
each sector, even when a selected sector is zero. -/
theorem second_sector_mass_phase (slots : Finset α) (s : Input slots)
    (modifier : Tuple slots→ℂ) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ T : ℝ) (hH : 0<H) (hT : 0<T)
    (keep : BlockIndex s modifier R seed H Tsec Z ξ→O→Prop) :
    secondSectorMass s modifier R seed W H Tsec Z ξ T keep=
      ‖∑q : CompleteBlock s modifier R seed W H Tsec Z ξ,
        sectorWeight s modifier R seed W H Tsec Z ξ T keep q*
          (modifiedDatumBlock
            (restrictedRetainedDatum slots s modifier R seed hseed hz₁ hz₂ H Tsec Z ξ hH
              q.val (keep q.val)) modifier).value W‖+
      ‖∑q : CompleteBlock s modifier R seed W H Tsec Z ξ,
        sectorWeight s modifier R seed W H Tsec Z ξ T (fun q z=>¬keep q z) q*
          (modifiedDatumBlock
            (restrictedRetainedDatum slots s modifier R seed hseed hz₁ hz₂ H Tsec Z ξ hH
              q.val (fun z=>¬keep q.val z)) modifier).value W‖ := by
  have hsector (p : BlockIndex s modifier R seed H Tsec Z ξ→O→Prop) :
      ‖∑q : CompleteBlock s modifier R seed W H Tsec Z ξ,
        sectorWeight s modifier R seed W H Tsec Z ξ T p q*
          (modifiedDatumBlock
            (restrictedRetainedDatum slots s modifier R seed hseed hz₁ hz₂ H Tsec Z ξ hH
              q.val (p q.val)) modifier).value W‖=
      (∑q∈(Finset.univ:Finset (BlockIndex s modifier R seed H Tsec Z ξ)).filter
          (fun q=>Record1252270103Second.originalBlock s modifier R seed W H Tsec Z ξ q≠0),
        ‖blockWeight s modifier R seed H Tsec Z ξ q‖*
          ‖selectedSecondBlock s modifier R seed W H Tsec Z ξ q (p q)‖)/T := by
    simp_rw [restricted_retained_block,sectorWeight]
    rw [norm_nonnegative_phased_sum _
      (fun q=>div_nonneg (norm_nonneg _) hT.le)]
    rw [←Finset.sum_subtype
      ((Finset.univ:Finset (BlockIndex s modifier R seed H Tsec Z ξ)).filter
        (fun q=>Record1252270103Second.originalBlock s modifier R seed W H Tsec Z ξ q≠0))
      (fun q=>by simp)
      (fun q=>‖blockWeight s modifier R seed H Tsec Z ξ q‖/T*
        ‖selectedSecondBlock s modifier R seed W H Tsec Z ξ q (p q)‖)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hsector keep,hsector (fun q z=>¬keep q z)]
  unfold secondSectorMass
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,add_div]

end
end QRH.Record1252270103Source.SecondSectorDatum
#print axioms QRH.Record1252270103Source.SecondSectorDatum.norm_nonnegative_phased_sum
#print axioms QRH.Record1252270103Source.SecondSectorDatum.sectorWeight_norm_le
#print axioms QRH.Record1252270103Source.SecondSectorDatum.second_sector_mass_phase
