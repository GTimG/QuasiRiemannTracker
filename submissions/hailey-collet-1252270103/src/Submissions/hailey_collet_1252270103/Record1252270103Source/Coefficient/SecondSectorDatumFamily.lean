/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All selected first labels stay inside one second-sector datum family.
Only finite algebra is used; no per-label source estimate is assumed. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SecondSectorDatumPhase
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
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance secondSectorFamilySumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

abbrev CompleteFamily (slots : Label→Finset α) (s : ∀l,Input (slots l))
    (modifier : ∀l,Tuple (slots l)→ℂ) (R seed : Label→Ideal O)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ : Label→ℝ) :=
  Σl,CompleteBlock (s l) (modifier l) (R l) (seed l) W (H l) (Tsec l) (Z l) (ξ l)

def familyDatum (slots : Label→Finset α) (s : ∀l,Input (slots l))
    (modifier : ∀l,Tuple (slots l)→ℂ) (R seed : Label→Ideal O)
    (hseed : ∀l,Squarefree (seed l)) (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ : Label→ℝ) (hH : ∀l,0<H l)
    (keep : ∀l,BlockIndex (s l) (modifier l) (R l) (seed l) (H l) (Tsec l) (Z l) (ξ l)→O→Prop)
    (q : CompleteFamily slots s modifier R seed W H Tsec Z ξ) : SecondInputDatum α :=
  restrictedRetainedDatum (slots q.1) (s q.1) (modifier q.1) (R q.1) (seed q.1)
    (hseed q.1) (hz₁ q.1) (hz₂ q.1) (H q.1) (Tsec q.1) (Z q.1) (ξ q.1)
    (hH q.1) q.2.val (keep q.1 q.2.val)

def familyWeight (slots : Label→Finset α) (s : ∀l,Input (slots l))
    (modifier : ∀l,Tuple (slots l)→ℂ) (R seed : Label→Ideal O)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ T a : Label→ℝ)
    (keep : ∀l,BlockIndex (s l) (modifier l) (R l) (seed l) (H l) (Tsec l) (Z l) (ξ l)→O→Prop)
    (q : CompleteFamily slots s modifier R seed W H Tsec Z ξ) : ℂ :=
  (a q.1:ℂ)*sectorWeight (s q.1) (modifier q.1) (R q.1) (seed q.1) W
    (H q.1) (Tsec q.1) (Z q.1) (ξ q.1) (T q.1) (keep q.1) q.2

theorem familyWeight_norm_le (slots : Label→Finset α) (s : ∀l,Input (slots l))
    (modifier : ∀l,Tuple (slots l)→ℂ) (R seed : Label→Ideal O)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ T a : Label→ℝ) (hT : ∀l,0<T l) (ha : ∀l,0≤a l)
    (keep : ∀l,BlockIndex (s l) (modifier l) (R l) (seed l) (H l) (Tsec l) (Z l) (ξ l)→O→Prop)
    (q : CompleteFamily slots s modifier R seed W H Tsec Z ξ) :
    ‖familyWeight slots s modifier R seed W H Tsec Z ξ T a keep q‖≤
      a q.1*(‖blockWeight (s q.1) (modifier q.1) (R q.1) (seed q.1)
        (H q.1) (Tsec q.1) (Z q.1) (ξ q.1) q.2.val‖/T q.1) := by
  rw [familyWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha q.1)]
  exact mul_le_mul_of_nonneg_left (sectorWeight_norm_le _ _ _ _ _ _ _ _ _ _ (hT q.1) _ _) (ha q.1)

/-- One exact joint family contains every selected first label and every
original complete nonzero second block. Both row sectors use that same type. -/
theorem second_sector_family_phase (slots : Label→Finset α) (s : ∀l,Input (slots l))
    (modifier : ∀l,Tuple (slots l)→ℂ) (R seed : Label→Ideal O)
    (hseed : ∀l,Squarefree (seed l)) (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ T a : Label→ℝ)
    (hH : ∀l,0<H l) (hT : ∀l,0<T l) (ha : ∀l,0≤a l)
    (keep : ∀l,BlockIndex (s l) (modifier l) (R l) (seed l) (H l) (Tsec l) (Z l) (ξ l)→O→Prop) :
    (∑l,a l*secondSectorMass (s l) (modifier l) (R l) (seed l) W
      (H l) (Tsec l) (Z l) (ξ l) (T l) (keep l))=
      ‖∑q : CompleteFamily slots s modifier R seed W H Tsec Z ξ,
        familyWeight slots s modifier R seed W H Tsec Z ξ T a keep q*
          (modifiedDatumBlock (familyDatum slots s modifier R seed hseed hz₁ hz₂ W H Tsec Z ξ hH keep q)
            (modifier q.1)).value W‖+
      ‖∑q : CompleteFamily slots s modifier R seed W H Tsec Z ξ,
        familyWeight slots s modifier R seed W H Tsec Z ξ T a (fun l q z=>¬keep l q z) q*
          (modifiedDatumBlock
            (familyDatum slots s modifier R seed hseed hz₁ hz₂ W H Tsec Z ξ hH (fun l q z=>¬keep l q z) q)
            (modifier q.1)).value W‖ := by
  have hsector (p : ∀l,BlockIndex (s l) (modifier l) (R l) (seed l) (H l) (Tsec l) (Z l) (ξ l)→O→Prop) :
      ‖∑q : CompleteFamily slots s modifier R seed W H Tsec Z ξ,
        familyWeight slots s modifier R seed W H Tsec Z ξ T a p q*
          (modifiedDatumBlock (familyDatum slots s modifier R seed hseed hz₁ hz₂ W H Tsec Z ξ hH p q)
            (modifier q.1)).value W‖=
      ∑l,a l*∑q : CompleteBlock (s l) (modifier l) (R l) (seed l) W (H l) (Tsec l) (Z l) (ξ l),
        (‖blockWeight (s l) (modifier l) (R l) (seed l) (H l) (Tsec l) (Z l) (ξ l) q.val‖/T l)*
          ‖selectedSecondBlock (s l) (modifier l) (R l) (seed l) W (H l) (Tsec l) (Z l) (ξ l) q.val (p l q.val)‖ := by
    simp_rw [familyDatum,restricted_retained_block,familyWeight,sectorWeight,←mul_assoc,←Complex.ofReal_mul]
    rw [norm_nonnegative_phased_sum
      (fun q : CompleteFamily slots s modifier R seed W H Tsec Z ξ =>
        a q.1*(‖blockWeight (s q.1) (modifier q.1) (R q.1) (seed q.1)
          (H q.1) (Tsec q.1) (Z q.1) (ξ q.1) q.2.val‖/T q.1))
      (fun q=>mul_nonneg (ha q.1) (div_nonneg (norm_nonneg _) (hT q.1).le))]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hsector keep,hsector (fun l q z=>¬keep l q z),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [second_sector_mass_phase (slots l) (s l) (modifier l) (R l) (seed l)
    (hseed l) (hz₁ l) (hz₂ l) W (H l) (Tsec l) (Z l) (ξ l) (T l) (hH l) (hT l) (keep l)]
  simp_rw [restricted_retained_block,sectorWeight]
  rw [norm_nonnegative_phased_sum _ (fun q=>div_nonneg (norm_nonneg _) (hT l).le),
    norm_nonnegative_phased_sum _ (fun q=>div_nonneg (norm_nonneg _) (hT l).le)]
  ring

end
end QRH.Record1252270103Source.SecondSectorDatum
#print axioms QRH.Record1252270103Source.SecondSectorDatum.familyWeight_norm_le
#print axioms QRH.Record1252270103Source.SecondSectorDatum.second_sector_family_phase
