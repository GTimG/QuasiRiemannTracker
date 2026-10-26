/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.certb_local_20261013.Bundles.B035
import Submissions.certb_local_20261013.Bundles.B065
import Submissions.certb_local_20261013.Bundles.B067
import Submissions.certb_local_20261013.Bundles.B069

/- BEGIN ORIGINAL MODULE Analytic.CommonMeshMonotonicity ; sha256 20adbbf7dc1714449e853f28c498fcc91be45de38d07ff7357663903f765ca00 -/
section


/-! Monotonicity of the common mesh in its initial range parameter. -/

set_option autoImplicit false

noncomputable section

namespace Cycle25.Energy

open OAI.SevenEighths
open CenteredMomentEnergyWidthRanges CenteredMomentEnergyWidthSchedule

private lemma range_mono_initial (M B L₁ L₂ : ℝ) (hL : L₁ ≤ L₂) (n : ℕ) :
    range M B L₁ n ≤ range M B L₂ n := by
  induction n with
  | zero => exact max_le_max_left 1 hL
  | succ n ih =>
      simp only [range, step]
      linarith

/-- A larger initial range uses a weakly smaller common mesh. -/
theorem commonMesh_antitone_L (Mcap Bmask L₁ L₂ ε : ℝ)
    (hM : 0 ≤ Mcap) (hB : 0 ≤ Bmask) (hε : 0 < ε) (hL : L₁ ≤ L₂) :
    commonMesh Mcap Bmask L₂ ε ≤ commonMesh Mcap Bmask L₁ ε := by
  have hcap : finalSourceCap Mcap Bmask L₁ ε ≤ finalSourceCap Mcap Bmask L₂ ε := by
    have hr := range_mono_initial Mcap Bmask L₁ L₂ hL (count Mcap ε)
    unfold finalSourceCap sourceCap
    linarith
  have hcap₁ : 0 ≤ finalSourceCap Mcap Bmask L₁ ε :=
    sourceCap_nonneg Mcap Bmask L₁ hM hB _
  have hscale : scale Mcap (finalSourceCap Mcap Bmask L₁ ε) ε ≤
      scale Mcap (finalSourceCap Mcap Bmask L₂ ε) ε := by
    unfold scale
    linarith
  have hscale₁ : 0 < scale Mcap (finalSourceCap Mcap Bmask L₁ ε) ε := by
    unfold scale
    positivity
  have hdiv : ε / (1000000 * scale Mcap (finalSourceCap Mcap Bmask L₂ ε) ε) ≤
      ε / (1000000 * scale Mcap (finalSourceCap Mcap Bmask L₁ ε) ε) := by
    apply div_le_div_of_nonneg_left hε.le (by positivity)
    exact mul_le_mul_of_nonneg_left hscale (by norm_num)
  unfold commonMesh fineMesh mesh reserve
  exact div_le_div_of_nonneg_right (min_le_min_left _ hdiv) (by norm_num)

#print axioms commonMesh_antitone_L

end Cycle25.Energy
end
/- END ORIGINAL MODULE Analytic.CommonMeshMonotonicity -/

/- BEGIN ORIGINAL MODULE Analytic.JointCommonRetainedBuffered ; sha256 111715e66bb2f34cc3b5ea7870f53bc2964fd0ee986d6d18a113c45497b5cc55 -/
section


/-! The actual common-source X/Y branch, with its inherited slots and
comparison scales, produces admissible data on the original slot type. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDyadic ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedProfile CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentPrimeSlot CenteredMomentHeckeExpansion
open CenteredMomentDivisorRectangle CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
local notation "O" => HeckeFamily.O

def commonSlotEmbedding {ι : Type*} [Fintype ι]
    (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) :
    CenteredMomentCommonProfile.liveIndices B.val ↪ ι where
  toFun i := i.val
  inj' := fun _ _ h => Subtype.ext h

theorem actual_common_retained_admissible
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
        (orders : Finset ι → ℕ) (edge e : ℝ), edge ≤ 1 → e ≤ 1/1000 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
        (hH : RayOrthogonality.globalUnits M ≤ H)
        (η : Character) (w : NonzeroElement) (parent : JointParentLabel η)
        (N : NaturalRow parent.val w.val) (puncture : Ideal O) (hpuncture : puncture ≠ 0)
        (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
        (source : Character) (A z : O) (t : ℝ)
        (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset
          (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2))) (branch : Bool)
        (Z d : ℝ) (η₀ : ι → Character) (V : ι → ℝ → ℂ)
        (alo bhi : ι → ℝ) (bin : ℕ) (Rwidth τ ηaux σmin σmax T : ℝ),
      s.W₁ = W₁ → s.W₂ = W₂ →
      (∀ i, s.slots i = primePool M H (bhi i) (s.P i)) →
      (∀ i I, s.ν i I = idealCoeff (η₀ i).inverse I) → (∀ i, s.W i = V i) →
      (∀ I : Ideal O, rowWeight source (fixedBadMask*idealGenerator (R*C)) A z t I =
        rowWeight parent.val (fixedBadMask*idealGenerator puncture) 1 w.val t I) →
      1 < Z → d ≠ 0 → 1 < Z^d → 0 ≤ Rwidth →
      s.X₁ ≤ (Z^d)^Rwidth → s.X₂ ≤ (Z^d)^Rwidth →
      s.Y₁ ≤ (Z^d)^Rwidth → s.Y₂ ≤ (Z^d)^Rwidth →
      (∀ i, 1 ≤ s.P i ∧ s.P i ≤ (Z^d)^Rwidth) → σmin ≤ 0 → 0 ≤ σmax →
      (∀ label, (bufferedProductFamily M H hH η₀
        (excluded N.character puncture) label).modulus.absNorm ≤ Z^d) →
      |t|+Z^τ/2 ≤ (3*bin+2 : ℕ)*Z^τ →
      (3+(3*bin+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux →
      (3+(3*bin+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux →
      (∀ i : liveIndices D allocation,
        2*(|Real.log (alo i.val.val)|+|Real.log (bhi i.val.val)|)+1 ≤ Real.log (s.P i.val.val)) →
      3*(bin+1 : ℕ)*Z^τ ≤ T →
      secondRetainedPositive (secondCommonData s C R B source A t).toSource
        D allocation branch z ≠ 0 →
      ∃ data : SurvivingBufferedData η w ι orders profileBound edge e,
        data.slots = embeddedSlots (allocationSlotEmbedding (commonSlotEmbedding s C B) D allocation) ∧
        ‖secondRetainedPositive (secondCommonData s C R B source A t).toSource
          D allocation branch z‖ = ‖data.value M H η₀ V bhi Z d‖ ∧
        d*data.length ≤ Real.logb Z (secondCommonVolume s C B)-
          Real.logb Z (formalReductionFactor D allocation (fun i => s.P i.val))+
          Real.logb Z (max 1 b₁*max 1 b₂) ∧
        data.Admissible M H hH η₀ alo bhi Rwidth τ ηaux σmin σmax Z d T := by
  obtain ⟨profileBound,hprofile,hdata⟩ := actual_source_allocated_admissible
    W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hW₁ hs₂ hW₂
  refine ⟨profileBound,hprofile,?_⟩
  intro ι instι instDι orders edge e hedge he M instM H hH η w parent N puncture hpuncture
    s C R B source A z t D allocation branch Z d η₀ V alo bhi bin Rwidth τ ηaux σmin σmax T
    hsW₁ hsW₂ hslots hν hW hrow hZ hd hbase hR hX₁ hX₂ hY₁ hY₂ hP hσmin hσmax
    hconductor hfreq hfour htwo hlog hbuffer hn
  let c := secondCommonData s C R B source A t
  let X₁ := if branch then c.X₁ else c.Y₁
  let X₂ := if branch then c.X₂ else c.Y₂
  have hx₁ : 0 < X₁ := by unfold X₁; split_ifs; exact c.X₁_pos; exact c.Y₁_pos
  have hx₂ : 0 < X₂ := by unfold X₂; split_ifs; exact c.X₂_pos; exact c.Y₂_pos
  have hN (j : Fin 2) : (1 : ℝ) ≤ Ideal.absNorm (B.val (Sum.inr j)) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B (Sum.inr j)))
  have hx₁cap : X₁ ≤ (Z^d)^Rwidth := by
    unfold X₁
    split_ifs
    · exact (div_le_self s.X₁_pos.le (hN 0)).trans hX₁
    · exact (div_le_self s.Y₁_pos.le (hN 0)).trans hY₁
  have hx₂cap : X₂ ≤ (Z^d)^Rwidth := by
    unfold X₂
    split_ifs
    · exact (div_le_self s.X₂_pos.le (hN 1)).trans hX₂
    · exact (div_le_self s.Y₂_pos.le (hN 1)).trans hY₂
  have heq : secondRetainedPositive c.toSource D allocation branch z =
      allocatedPositiveRow source (fixedBadMask*idealGenerator (R*C)) A z t
        (fun i : CenteredMomentCommonProfile.liveIndices B.val => primePool M H (bhi i.val) (s.P i.val))
        (fun i I => idealCoeff (η₀ i.val).inverse I*V i.val ((I.absNorm : ℝ)/s.P i.val))
        (fun i => s.P i.val) D allocation W₁ W₂ X₁ X₂ := by
    simp only [secondRetainedPositive,X₁,X₂,c,secondCommonData,commonData,hslots,hν,hW,hsW₁,hsW₂]
  have hne := ne_of_eq_of_ne heq.symm hn
  obtain ⟨data,hslots',hnorm,hlength,had⟩ := hdata (commonSlotEmbedding s C B) orders edge e
    hedge he M H hH η w parent N puncture hpuncture source
      (fixedBadMask*idealGenerator (R*C)) A z t hrow D allocation Z d X₁ X₂
      η₀ V alo bhi (fun i => s.P i.val) bin Rwidth τ ηaux σmin σmax T
      hZ hd hbase hx₁ hx₂ hR hx₁cap hx₂cap (fun i => hP i.val) hσmin hσmax
      hconductor hfreq hfour htwo hlog hbuffer hne
  refine ⟨data,hslots',(congrArg (fun x : ℂ => ‖x‖) heq).trans hnorm,?_,had⟩
  have hvolume : X₁*X₂*(∏ i : CenteredMomentCommonProfile.liveIndices B.val, s.P i.val) =
      secondCommonVolume s C B := by
    unfold X₁ X₂
    cases branch
    · change c.Y₁*c.Y₂*_ = c.X₁*c.X₂*_
      rw [c.same_product]
    · rfl
  simpa only [hvolume] using hlength

#print axioms actual_common_retained_admissible
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonRetainedBuffered -/

/- BEGIN ORIGINAL MODULE Analytic.JointFiniteWidthSectors ; sha256 93e01d3c9aa36ee9801f444b8e24940ece0f1d5e19a2217bdb1e91e8d1a726a1 -/
section


/-! Logarithmic sectors have a number of cells fixed before the scale.
An actual reference minimizes the single scalar width R/2+E; no pair
of simultaneous coordinatewise minima is assumed. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon

theorem exists_finite_width_bins {Row : Type*} (n N : ℕ) (e : ℝ) (he : 0 < e)
    (f : Row → Fin n → ℝ) (hf : ∀ u j, 0 ≤ f u j ∧ f u j ≤ N*e) :
    ∃ bin : Row → (Fin n → Fin (N+1)),
      ∀ u v, bin u = bin v → ∀ j, |f u j-f v j| < e := by
  let bin : Row → (Fin n → Fin (N+1)) := fun u j =>
    ⟨Nat.floor (f u j/e),Nat.lt_succ_of_le
      (Nat.floor_le_of_le ((div_le_iff₀ he).mpr (hf u j).2))⟩
  refine ⟨bin,?_⟩
  intro u v huv j
  have hb : Nat.floor (f u j/e) = Nat.floor (f v j/e) :=
    congrArg Fin.val (congrFun huv j)
  have hu₀ := Nat.floor_le (div_nonneg (hf u j).1 he.le)
  have hv₀ := Nat.floor_le (div_nonneg (hf v j).1 he.le)
  have hu₁ := Nat.lt_floor_add_one (f u j/e)
  have hv₁ := Nat.lt_floor_add_one (f v j/e)
  rw [hb] at hu₀ hu₁
  have hlu : (Nat.floor (f v j/e) : ℝ)*e ≤ f u j := (le_div_iff₀ he).mp hu₀
  have hlv : (Nat.floor (f v j/e) : ℝ)*e ≤ f v j := (le_div_iff₀ he).mp hv₀
  have hhu : f u j < ((Nat.floor (f v j/e) : ℝ)+1)*e := (div_lt_iff₀ he).mp hu₁
  have hhv : f v j < ((Nat.floor (f v j/e) : ℝ)+1)*e := (div_lt_iff₀ he).mp hv₁
  rw [abs_lt]
  constructor <;> nlinarith

theorem finite_width_bin_count (n N : ℕ) :
    Fintype.card (Fin n → Fin (N+1)) = (N+1)^n := by simp

theorem exists_first_scalar_reference {Row Slot : Type*} [Fintype Slot]
    (labels : Finset Row) (hne : labels.Nonempty) (s : Row → FirstJointLabel Slot) (Z : ℝ) :
    ∃ q ∈ labels, ∀ u ∈ labels,
      (s q).activeWidth Z/2+(s q).punctureWidth Z ≤
        (s u).activeWidth Z/2+(s u).punctureWidth Z :=
  labels.exists_min_image (fun u => (s u).activeWidth Z/2+(s u).punctureWidth Z) hne

theorem norm_ratio_of_log_width_gap (Z x y e : ℝ)
    (hZ : 1 < Z) (hx : 0 < x) (hy : 0 < y)
    (hwidth : Real.logb Z x-Real.logb Z y ≤ e) : x ≤ Z^e*y := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  calc
    x = Z^(Real.logb Z x) := (Real.rpow_logb hz hZ.ne' hx).symm
    _ ≤ Z^(e+Real.logb Z y) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = Z^e*y := by rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hy]

namespace FirstJointLabel
variable {Slot : Type*} [Fintype Slot]

def widthCoordinates (s : FirstJointLabel Slot) (Z : ℝ) : Fin 7 → ℝ :=
  ![s.leftWidth Z,s.rightWidth Z,s.radicalWidth Z,s.activeWidth Z,
    s.punctureWidth Z,s.leftAllowance Z,s.rightAllowance Z]

theorem width_coordinates_bounds (s : FirstJointLabel Slot) (Z B : ℝ)
    (hZ : 1 < Z) (hB : 0 ≤ B)
    (hC : (s.C.absNorm : ℝ) ≤ Z^B) (hD : (s.D.absNorm : ℝ) ≤ Z^B) :
    ∀ j, 0 ≤ s.widthCoordinates Z j ∧ s.widthCoordinates Z j ≤ 2*B := by
  have hcN : 0 < s.C.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hC.1)
  have hdN : 0 < s.D.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hD.1)
  have hc₀ : 0 ≤ s.leftWidth Z := Real.logb_nonneg hZ (by exact_mod_cast hcN)
  have hd₀ : 0 ≤ s.rightWidth Z := Real.logb_nonneg hZ (by exact_mod_cast hdN)
  have hc := Real.logb_le_logb_of_le hZ (by exact_mod_cast hcN) hC
  have hd := Real.logb_le_logb_of_le hZ (by exact_mod_cast hdN) hD
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hc hd
  change s.leftWidth Z ≤ B at hc
  change s.rightWidth Z ≤ B at hd
  obtain ⟨hp,hr,he,hBc,hBd⟩ := s.target_auxiliary_widths_nonneg Z hZ
  have ha := s.actual_joint_allowance Z hZ
  have heN : ((Ideal.span {s.puncture}).absNorm : ℝ) ≤ (s.C.absNorm : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hcN (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp
      ((subsetGenerator_span_dvd s.C s.D s.E).trans (commonPart_dvd s.C s.D s.hC.1))))
  have hePos : 0 < ((Ideal.span {s.puncture}).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (subsetGenerator_supported s.C s.D s.hC s.E).1)
  have heB := Real.logb_le_logb_of_le hZ hePos (heN.trans hC)
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at heB
  have he' : s.punctureWidth Z ≤ B := by
    simpa only [punctureWidth,eisEmbedding_norm_sq_eq_absNorm_span] using heB
  intro j
  fin_cases j <;> norm_num [widthCoordinates] <;> constructor <;> linarith

theorem targets_close_of_width_coordinates (s q : FirstJointLabel Slot) (Z A e : ℝ)
    (h : ∀ j, |s.widthCoordinates Z j-q.widthCoordinates Z j| < e) :
    |s.leftTargetWidth Z A-q.leftTargetWidth Z A| < 5*e ∧
    |s.rightTargetWidth Z A-q.rightTargetWidth Z A| < 5*e ∧
    |(s.activeWidth Z+s.punctureWidth Z+s.leftAllowance Z-2*s.leftWidth Z)-
      (q.activeWidth Z+q.punctureWidth Z+q.leftAllowance Z-2*q.leftWidth Z)| < 5*e ∧
    |(s.activeWidth Z+s.punctureWidth Z+s.rightAllowance Z-2*s.rightWidth Z)-
      (q.activeWidth Z+q.punctureWidth Z+q.rightAllowance Z-2*q.rightWidth Z)| < 5*e := by
  have h₀ := (abs_lt.mp (h 0))
  have h₁ := (abs_lt.mp (h 1))
  have h₂ := (abs_lt.mp (h 2))
  have h₃ := (abs_lt.mp (h 3))
  have h₄ := (abs_lt.mp (h 4))
  have h₅ := (abs_lt.mp (h 5))
  have h₆ := (abs_lt.mp (h 6))
  norm_num [widthCoordinates] at h₀ h₁ h₂ h₃ h₄ h₅ h₆
  simp only [leftTargetWidth,rightTargetWidth,abs_lt]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

theorem common_norms_close_of_width_coordinates (s q : FirstJointLabel Slot) (Z e : ℝ)
    (hZ : 1 < Z) (h : ∀ j, |s.widthCoordinates Z j-q.widthCoordinates Z j| < e) :
    (s.C.absNorm : ℝ) ≤ Z^e*(q.C.absNorm : ℝ) ∧
    (s.D.absNorm : ℝ) ≤ Z^e*(q.D.absNorm : ℝ) := by
  have h₀ := (abs_lt.mp (h 0)).2.le
  have h₁ := (abs_lt.mp (h 1)).2.le
  constructor
  · exact norm_ratio_of_log_width_gap Z _ _ e hZ
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hC.1))
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr q.hC.1)) h₀
  · exact norm_ratio_of_log_width_gap Z _ _ e hZ
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hD.1))
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr q.hD.1)) h₁

end FirstJointLabel

theorem exists_first_width_sectors {Row Slot : Type*} [Fintype Slot]
    (labels : Finset Row) (s : Row → FirstJointLabel Slot) (Z e : ℝ) (N : ℕ)
    (he : 0 < e) (hcap : ∀ u ∈ labels, ∀ j,
      0 ≤ (s u).widthCoordinates Z j ∧ (s u).widthCoordinates Z j ≤ N*e) :
    ∃ bin : (u : Row) → u ∈ labels → (Fin 7 → Fin (N+1)),
      (∀ u v hu hv, bin u hu = bin v hv → ∀ j,
        |(s u).widthCoordinates Z j-(s v).widthCoordinates Z j| < e) ∧
      ∀ b : Fin 7 → Fin (N+1),
        let cell := labels.attach.filter (fun u => bin u.val u.property = b)
        cell.Nonempty → ∃ q ∈ cell, ∀ u ∈ cell,
          (s q.val).activeWidth Z/2+(s q.val).punctureWidth Z ≤
            (s u.val).activeWidth Z/2+(s u.val).punctureWidth Z := by
  obtain ⟨bin,hbin⟩ := exists_finite_width_bins 7 N e he
    (fun u : {u : Row // u ∈ labels} => (s u.val).widthCoordinates Z)
    (fun u => hcap u.val u.property)
  refine ⟨fun u hu => bin ⟨u,hu⟩,?_,?_⟩
  · intro u v hu hv huv
    exact hbin ⟨u,hu⟩ ⟨v,hv⟩ huv
  · intro b cell hcell
    exact exists_first_scalar_reference cell hcell (fun u => s u.val) Z

/-- The number of logarithmic cells is selected before the scale and all
actual arithmetic labels, from a common norm cap alone. -/
theorem uniform_first_width_sector_count (B e : ℝ) (hB : 0 ≤ B) (he : 0 < e) :
    ∃ N : ℕ, ∀ {Row Slot : Type*} [Fintype Slot]
      (labels : Finset Row) (s : Row → FirstJointLabel Slot) (Z : ℝ), 1 < Z →
      (∀ u ∈ labels, (s u).C.absNorm ≤ (Z^B : ℝ) ∧ (s u).D.absNorm ≤ (Z^B : ℝ)) →
      ∃ bin : (u : Row) → u ∈ labels → (Fin 7 → Fin (N+1)),
        (∀ u v hu hv, bin u hu = bin v hv → ∀ j,
          |(s u).widthCoordinates Z j-(s v).widthCoordinates Z j| < e) ∧
        ∀ b : Fin 7 → Fin (N+1),
          let cell := labels.attach.filter (fun u => bin u.val u.property = b)
          cell.Nonempty → ∃ q ∈ cell, ∀ u ∈ cell,
            (s q.val).activeWidth Z/2+(s q.val).punctureWidth Z ≤
              (s u.val).activeWidth Z/2+(s u.val).punctureWidth Z := by
  obtain ⟨N,hN⟩ := exists_nat_ge (2*B/e)
  refine ⟨N,?_⟩
  intro Row Slot inst labels s Z hZ hcap
  apply exists_first_width_sectors labels s Z e N he
  intro u hu j
  obtain ⟨hl,hr⟩ := (s u).width_coordinates_bounds Z B hZ hB (hcap u hu).1 (hcap u hu).2 j
  exact ⟨hl,hr.trans ((div_le_iff₀ he).mp hN)⟩

#print axioms exists_finite_width_bins
#print axioms exists_first_scalar_reference
#print axioms exists_first_width_sectors
#print axioms uniform_first_width_sector_count
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFiniteWidthSectors -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSelectedGeometry ; sha256 91a0e1574d53db2e987d90759b3bb8e6416145f2b7c516c57a2b0145d16c998c -/
section




/-! Nominal low-bin width from the actual second physical block. This
keeps the enlarged first radius and the literal common-frequency norms. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge CenteredMomentSecondPhysicalLedger
open CenteredMomentSourceRow
open RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentSecondChildRadialWidth
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonProfile
open CenteredMomentAmplificationChildSourceCaps CenteredMomentEnergyChildState CenteredMomentEnergyState
open CenteredMomentFirstPhysicalSource

theorem eventually_selected_low_state_width
    (η₀ : Character) (parentLoss : ℝ) (hparentLoss : 0 < parentLoss) :
    ∀ᶠ Z : ℝ in Filter.atTop, ∀ hZ : 1 < Z,
    ∀ (P₁ Q₁ : Ideal O) (hP₁ : Supported P₁)
      (E₁ : Finset (CommonIndex P₁ Q₁)) (ξ₁ ξ₂ : RayCharacter)
      (F : FixedPair η₀ P₁ Q₁ hP₁ E₁ ξ₁ ξ₂) (parent : Character),
    (parent = F.left ∨ parent = F.right) →
    ∀ (C₁ D₁ : Ideal O) (hC₁ : Supported C₁),
    ∀ (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
    Family parent C₂ D₂ hC₂ hD₂ U family →
    ∀ (t : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ) (rows : Finset O)
      (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ)
      (H A M omegaLoss ξ sourceLoss Bmask : ℝ),
    0 < K → 0 < H → ∀ hBmask : 0 ≤ Bmask, Real.logb Z H ≤ A+sourceLoss →
    let c := Real.logb Z (C₁.absNorm : ℝ)
    let d := Real.logb Z (D₁.absNorm : ℝ)
    let R := Real.logb Z (normValue (activeConductor P₁ Q₁))
    let e := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex P₁ Q₁ => P.val) E₁))
    let radius := frequencyRadius (jointSecondNominal C₁ H Z A c d R e M (3/500) omegaLoss) Z ξ
    ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows W K n ≠ 0,
    ∀ (χ : RayCharacter) (Q : Ideal O),
    (actualState (τ := family) t columns β radius rows W K n hne Z Bmask hZ
      χ Q 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hBmask)).width ≤
      jointLowNominal M c d (3/500) omegaLoss
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) +
      (2*sourceLoss+parentLoss+ξ/2+Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))) := by
  filter_upwards [eventually_first_parent_width η₀ parentLoss hparentLoss] with Z hZ
  intro hZlive P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F parent hparent C₁ D₁ hC₁ C₂ D₂ hC₂ hD₂ U family hfamily
    t columns β rows W K n H A M omegaLoss ξ sourceLoss Bmask hK hH hBmask hsource c d R e radius hne χ Q
  have hparentcap : Real.logb Z (parent.modulus.absNorm : ℝ) ≤ R+e+parentLoss := by
    rcases hparent with rfl | rfl
    · exact (hZ.2 P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F).1
    · exact (hZ.2 P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F).2
  exact actual_joint_low_width C₁ C₂ D₂ hC₁.1 parent t columns β hC₂ hD₂ U family hfamily
    rows W K hK n H Z A c d R e M (3/500) omegaLoss ξ sourceLoss parentLoss
    hH hZ.1 rfl hsource hparentcap hne χ

#print axioms eventually_selected_low_state_width
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSelectedGeometry -/

/- BEGIN ORIGINAL MODULE Analytic.JointPhysicalBins ; sha256 0482f326d20b85519bad283bb5addd80e8bc126d97e44501e7710f863b44832e -/
section


/-! The literal physical block, including its complete pre-count scalar,
is bounded by post-transform bin sums of the projected kernel rows. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentSecondSectorColumns CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentMobiusRegroup
open CenteredMomentFixedRay CompletedGauss
local notation "O" => HeckeFamily.O

theorem actual_physicalBlock_kernel_precount (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (hrows : ∀ z ∈ rows, z ≠ 0) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (n : Fin 4 → ℤ) (H P : ℝ) :
    ‖physicalBlock η t S β C D hC hD U R rows W K n‖/(H*P) =
      secondPrecountFactor H P C D U K n*
        ‖projectedSecondKernelSum η t S β C D hC hD hCD U R rows W K n‖ := by
  rw [actual_physicalBlock_precount η t S β C D hC hD U R rows hrows W K hK n H P,
    normalizedBlock_eq_actual_children η t S β C D hC hD hCD,
    actualSecondChildren_norm_normalized η t S β C D hC hD hCD]

theorem projectedSecondKernelSum_norm_le_bins {κ : Type*} [Fintype κ]
    (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O) (bin : O → κ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    ‖projectedSecondKernelSum η t S β C D hC hD hCD U R rows W K n‖ ≤
      ∑ b : κ, ∑ L ∈ divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J : Ideal O)),
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ z ∈ rows.filter (fun z => bin z = b),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)*
            pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ*
            (projectedSecondKernelLabel η S β C D hC hD hCD U L χ ξ).kernelRow t z W K R n‖ := by
  let T := (divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J : Ideal O))) ×ˢ
    ((Finset.univ : Finset RayCharacter) ×ˢ ((Finset.univ : Finset RayCharacter) ×ˢ rows))
  let f := fun q : Ideal O × (RayCharacter × (RayCharacter × O)) =>
    (UniqueFactorizationMonoid.moebius q.1 : ℂ)*
      pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) q.2.1 q.2.2.1*
      (projectedSecondKernelLabel η S β C D hC hD hCD U q.1 q.2.1 q.2.2.1).kernelRow t q.2.2.2 W K R n
  have he : projectedSecondKernelSum η t S β C D hC hD hCD U R rows W K n = ∑ q ∈ T,f q := by
    simp only [projectedSecondKernelSum,T,f,Finset.sum_product,Finset.mul_sum,mul_assoc]
  rw [he]
  apply (norm_sum_le _ _).trans_eq
  rw [finite_row_bin_partition T (fun q => bin q.2.2.2)]
  simp only [Finset.sum_filter,T,f,Finset.sum_product]

theorem actual_physicalBlock_bin_majorant {κ : Type*} [Fintype κ]
    (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O) (bin : O → κ)
    (hrows : ∀ z ∈ rows, z ≠ 0) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (n : Fin 4 → ℤ) (H P : ℝ) (hH : 0 < H) (hP : 0 < P) :
    ‖physicalBlock η t S β C D hC hD U R rows W K n‖/(H*P) ≤
      ∑ b : κ, ∑ L ∈ divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J : Ideal O)),
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ z ∈ rows.filter (fun z => bin z = b),
          ‖(secondPrecountFactor H P C D U K n : ℂ)*(UniqueFactorizationMonoid.moebius L : ℂ)*
            pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ*
            (projectedSecondKernelLabel η S β C D hC hD hCD U L χ ξ).kernelRow t z W K R n‖ := by
  have hp := secondPrecountFactor_pos H P hH hP C D hC hD U K hK n
  rw [actual_physicalBlock_kernel_precount η t S β C D hC hD hCD U R rows hrows W K hK n H P]
  apply (mul_le_mul_of_nonneg_left
    (projectedSecondKernelSum_norm_le_bins η t S β C D hC hD hCD U R rows bin W K n) hp.le).trans_eq
  simp only [Finset.mul_sum,mul_assoc,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]

#print axioms actual_physicalBlock_kernel_precount
#print axioms actual_physicalBlock_bin_majorant
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointPhysicalBins -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.PlainInput ; sha256 455f02ac8fdcd8454096b3d8cb547a3789974f71f64c1386308c65535cba7538 -/
section



namespace OAI.SevenEighths.Cycle25ProbeDetectorPlainMarkedFineField
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter HeckeFamily CenteredMomentEnergyBands
open Cycle25ProbeFinalAssembly Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentDetectorPlainMomentParameters
open Cycle25CenteredMomentDetectorPlainSlotProfile

/-- One mesh works for all fixed detector inducing characters and the eventual
finite physical slot count. No improved terminal bound is used. -/
theorem terminal_plain_input {D : Cycle25.Weighted.MomentData}
    (S : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain) :
    weighted_PositiveFineSourceInput S κplain (Cycle25.Energy.commonMesh 2 0 1 (weighted_stageError D)) := by
  intro bΦ hbΦ
  obtain ⟨J,controls,he⟩ := Cycle25.Energy.terminal_positive_at (α:=Fin D.N)
    S.modulus ⊤ le_top (fun x=> conj (S.W x)) 1 2 (1/4) (9/4) bΦ 0 1
    (33/50) (33/50) 2 κplain (weighted_stageError D)
    (by norm_num) (weighted_conjugate_source_support S)
    (HeckeInverseAmplification.conjugate_profile_smooth _ (S.W.smooth ⊤)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbΦ
    (by norm_num) (by norm_num) hk hk1 (weighted_fixed_parameters D).2.2.1 hbeta hκbeta
  refine ⟨J,controls,?_⟩
  intro η₀
  obtain ⟨C,hC,hbound⟩ := he η₀ (weighted_sourceFixedIdeal S) (weighted_sourceFixedIdeal_le_modulus S)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero S) η₀)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) η₀)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 S))
  exact ⟨C,hC,hbound.mono (fun _ hz=> hz.2)⟩

open Cycle25ProbeDetectorPlainUnmarkedField CenteredMomentEnergyCappedWidthInduction
/-- Unmarked plain input extracted from the zero-slot part of the completed
Cycle25 certificate; fixed inducing characters are removed by the dictionary. -/
theorem terminal_zero_input {D : Cycle25.Weighted.MomentData}
    (S : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain) :
    ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal S) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A := by
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate (α:=Fin D.N)
    S.modulus ⊤ le_top (fun x=> conj (S.W x)) 1 2 (1/4) (9/4) weighted_radialSupportUpper
    0 1 (33/50) (33/50) 2 κplain (weighted_stageError D)
    (by norm_num) (weighted_conjugate_source_support S)
    (HeckeInverseAmplification.conjugate_profile_smooth _ (S.W.smooth ⊤))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) weighted_radialSupportUpper_spec.1
    (by norm_num) (by norm_num) hk (weighted_fixed_parameters D).2.2.1 hbeta hκbeta
  obtain ⟨J,controls,he⟩ := certified_terminal (α:=Fin D.N) S.modulus ⊤ le_top
    (fun x=> conj (S.W x)) 2 (1/4) (9/4) weighted_radialSupportUpper 0 1 (33/50) (33/50)
    2 κplain (weighted_stageError D) (by norm_num) (by norm_num) (by linarith)
    (weighted_fixed_parameters D).2.2.1 hcert
  refine ⟨J,controls,?_⟩
  intro η₀
  obtain ⟨Cz,Cp,hCz,hCp,hbound⟩ := he η₀ (weighted_sourceFixedIdeal S) (weighted_sourceFixedIdeal_le_modulus S)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero S) η₀)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) η₀)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 S))
  exact ⟨Cz,hCz,hbound.mono (fun _ hz=> hz.2.1)⟩
end
end OAI.SevenEighths.Cycle25ProbeDetectorPlainMarkedFineField
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.PlainInput -/
