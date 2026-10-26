/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual normalized forced children and a uniform attained envelope. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.JointForcedRows
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredPositiveEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.JointForced
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open Record1252270103Source Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def normalizedRow (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O)
    (τ:Character) (t:ℝ) (z:O):ℂ :=
  (Real.sqrt (volume s):ℂ)⁻¹*modifiedSourceRow s modifier R L τ t z

lemma normalized_row_sq (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O)
    (τ:Character) (t:ℝ) (z:O) :
    ‖normalizedRow s modifier R L τ t z‖^2=
      ‖modifiedSourceRow s modifier R L τ t z‖^2/volume s := by
  simp only [normalizedRow,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,Real.sq_sqrt (volume_pos s).le]
  ring

/-- Exact normalization through the actual rawReduction, not an assumed
common-ideal volume quotient. -/
theorem normalized_forced_row_bound (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O)
    (hL:L≠0) (τ:Character) (t:ℝ) (z:O) :
    ‖normalizedRow s modifier R L τ t z‖^2≤
      ((forcedLabels L (forcedSource s modifier R L)).card:ℝ)*
        ∑C:forcedLabels L (forcedSource s modifier R L),
          ((actualAllocations s.pools (C:Ideal O)).card:ℝ)*
            ∑B:actualAllocations s.pools (C:Ideal O),
              (‖frozenCoefficient B C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
                ‖normalizedRow (child s C R B τ t) (pulledModifier B modifier) (R*C) 1 τ t z‖^2 := by
  rw [normalized_row_sq]
  apply (div_le_div_of_nonneg_right (actual_forced_row_sq s modifier R L hL τ t z)
    (volume_pos s).le).trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x:ℝ=>((forcedLabels L (forcedSource s modifier R L)).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro C hC
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x:ℝ=>((actualAllocations s.pools (C:Ideal O)).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  rw [normalized_row_sq]
  have hb:=(allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1
  have hr:=raw_scale_identity B.val hb (s.X₁*s.X₂) s.P
  have hred:=rawReduction_pos B.val hb s.P s.P_pos
  have hvol:=volume_pos (child s C R B τ t)
  rw [child_volume_remaining] at hvol ⊢
  change remainingRaw B.val (s.X₁*s.X₂) s.P*rawReduction B.val s.P=volume s at hr
  rw [←hr]
  field_simp [hred.ne',hvol.ne']

/-- A finite child envelope only needs the genuinely contributing frozen
allocations. This is a rowwise algebraic consequence, not an energy premise. -/
theorem forced_row_envelope (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O)
    (hL:L≠0) (τ:Character) (t:ℝ) (z:O) (E:ℝ) (hE:0≤E)
    (hchild:∀C:forcedLabels L (forcedSource s modifier R L),
      ∀B:actualAllocations s.pools (C:Ideal O),frozenCoefficient B C R s.ν s.W s.P≠0→
        ‖normalizedRow (child s C R B τ t) (pulledModifier B modifier) (R*C) 1 τ t z‖^2≤E) :
    ‖normalizedRow s modifier R L τ t z‖^2≤
      forcedAllocationMass s modifier R L*(forcedProfileCost s*E)/(L.absNorm:ℝ) := by
  apply (normalized_forced_row_bound s modifier R L hL τ t z).trans
  have hterm (C:forcedLabels L (forcedSource s modifier R L))
      (B:actualAllocations s.pools (C:Ideal O)) :
      (‖frozenCoefficient B C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
        ‖normalizedRow (child s C R B τ t) (pulledModifier B modifier) (R*C) 1 τ t z‖^2≤
        (forcedProfileCost s/(L.absNorm:ℝ))*E := by
    by_cases hz:frozenCoefficient B C R s.ν s.W s.P=0
    · simp only [hz,norm_zero,zero_pow (by decide:2≠0),zero_div,zero_mul]
      exact mul_nonneg (div_nonneg (forcedProfileCost_nonneg s) (Nat.cast_nonneg _)) hE
    have hb:=(allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1
    have hc:=frozen_normalized_cost B.val hb C R (forcedLabel_ne_zero L _ C)
      (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.M s.P_pos s.ν_bound s.W_bound
      s.M_ge_one s.lower s.upper s.lower_pos s.slot_support
    have hred:=rawReduction_pos B.val hb s.P s.P_pos
    have hnL:(0:ℝ)<L.absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL)
    have hn:(L.absNorm:ℝ)≤(C:Ideal O).absNorm := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero
        (Ideal.absNorm_eq_zero_iff.not.mpr (forcedLabel_ne_zero L _ C)))
        (map_dvd Ideal.absNorm (forcedSource_label_seed s modifier R L hL C))
    exact (mul_le_mul_of_nonneg_left (hchild C B hz)
      (div_nonneg (sq_nonneg _) hred.le)).trans
      (mul_le_mul_of_nonneg_right (hc.trans
        (div_le_div_of_nonneg_left (forcedProfileCost_nonneg s) hnL hn)) hE)
  calc
    _≤((forcedLabels L (forcedSource s modifier R L)).card:ℝ)*
        ∑C:forcedLabels L (forcedSource s modifier R L),
          ((actualAllocations s.pools (C:Ideal O)).card:ℝ)*
            ∑_B:actualAllocations s.pools (C:Ideal O),(forcedProfileCost s/(L.absNorm:ℝ))*E := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro C hC
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>hterm C B)) (Nat.cast_nonneg _)
    _=_ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,forcedAllocationMass]
      simp only [Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro C hC
      ring

/-- Actual dependent common-factor/allocation fiber. -/
def ChildIndex (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O) :=
  ΣC:forcedLabels L (forcedSource s modifier R L),actualAllocations s.pools (C:Ideal O)

instance childIndexFintype (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O) :
    Fintype (ChildIndex s modifier R L) := inferInstanceAs (Fintype (ΣC:forcedLabels L
      (forcedSource s modifier R L),actualAllocations s.pools (C:Ideal O)))

def childValue (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O)
    (τ:Character) (t:ℝ) (z:O) (p:ChildIndex s modifier R L):ℝ :=
  ‖normalizedRow (child s p.1 R p.2 τ t) (pulledModifier p.2 modifier) (R*p.1) 1 τ t z‖^2

def activeChildren (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O) :
    Finset (ChildIndex s modifier R L) :=
  Finset.univ.filter (fun p=>frozenCoefficient p.2 p.1 R s.ν s.W s.P≠0)

lemma exists_active_child (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O)
    (hL:L≠0) (τ:Character) (t:ℝ) (z:O)
    (hn:normalizedRow s modifier R L τ t z≠0) :
    ∃p∈activeChildren s modifier R L,0<childValue s modifier R L τ t z p := by
  have hr:modifiedSourceRow s modifier R L τ t z≠0:=right_ne_zero_of_mul hn
  rw [actual_forced_row s modifier R L hL] at hr
  obtain ⟨C,_,hC⟩:=Finset.exists_ne_zero_of_sum_ne_zero hr
  obtain ⟨B,_,hB⟩:=Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hC)
  refine ⟨⟨C,B⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,left_ne_zero_of_mul hB⟩,?_⟩
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  apply mul_ne_zero _ (right_ne_zero_of_mul hB)
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (volume_pos _)).ne')

/-- One actual nonzero frozen allocation attains a sufficient envelope.
Empty fibers are excluded by the mother row itself, without an inhabitance hypothesis. -/
theorem selected_child (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O)
    (hL:L≠0) (τ:Character) (t:ℝ) (z:O)
    (hn:normalizedRow s modifier R L τ t z≠0) :
    ∃p:ChildIndex s modifier R L,
      frozenCoefficient p.2 p.1 R s.ν s.W s.P≠0 ∧
      0<childValue s modifier R L τ t z p ∧
      ‖normalizedRow s modifier R L τ t z‖^2≤
        forcedAllocationMass s modifier R L*(forcedProfileCost s*
          childValue s modifier R L τ t z p)/(L.absNorm:ℝ) := by
  obtain ⟨p₀,hp₀,hpos⟩:=exists_active_child s modifier R L hL τ t z hn
  obtain ⟨p,hp,hmax⟩:=Finset.exists_max_image (activeChildren s modifier R L)
    (childValue s modifier R L τ t z) ⟨p₀,hp₀⟩
  have hpv:0<childValue s modifier R L τ t z p:=lt_of_lt_of_le hpos (hmax p₀ hp₀)
  refine ⟨p,(Finset.mem_filter.mp hp).2,hpv,?_⟩
  apply forced_row_envelope s modifier R L hL τ t z _ hpv.le
  intro C B hb
  exact hmax ⟨C,B⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)

end
end QRH.Record1252270103Source.Admission.JointForced
#print axioms QRH.Record1252270103Source.Admission.JointForced.normalized_forced_row_bound
#print axioms QRH.Record1252270103Source.Admission.JointForced.forced_row_envelope
#print axioms QRH.Record1252270103Source.Admission.JointForced.selected_child
