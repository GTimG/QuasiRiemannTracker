/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Literal independently colored StrongPair leaves on actual sixth-free fibers,
retaining the actual original/reference componentwise rectangle.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafRectangles
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstAmplificationChoice
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondCanonical
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSectorLocalization
open LocalMoment ProbePhysical Record12518109GainRoot
open QRH.Cycle092 QRH.Cycle092.WholeSlot QRH.Cycle092.SixthCore
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open ProfileSeparation (commonPair scale pairWeight scale_pos)
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafGeometry_2c4266a2b3d1b8d2_001 (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {L : ℝ}


/-- Every actual occupied cofactor has its true core radius. No lower
radius cutoff or replacement ball is introduced. -/
theorem terminal_cofactor_geometry (U M : ℝ) (hU : 1< U) (R : Finset NonzeroFrequency)
    (hR : ∀z∈R,rawFrequencyNorm z≤ U^M) (B : HeckeInverseAmplification.NonzeroIdeal)
    (hB : (sixthFreeFiber R B).Nonempty) :
    0≤ coreWidth U M B ∧ coreWidth U M B≤ M ∧
      ∀u∈sixthFreeFiber R B,ProbeHighRowFamily.rowNorm u≤ U^(coreWidth U M B) := by
  refine ⟨coreWidth_nonneg R U M hU hR B hB,coreWidth_le U M hU B,?_⟩
  intro u hu
  have hh := hR _ (MeasuredBall.fiber_mem hu)
  rw [raw_sixth_norm] at hh
  rw [MeasuredBall.core_identity hU M B]
  apply (le_div_iff₀ ?_).mpr hh
  exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)) _

/-- The complete surviving T retains the actual original source quota. -/
theorem terminal_full_subset_quota {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : ι→ℝ) (hw : ∀i,0≤ w i) (A : Finset ι) (T : Finset A) (quota : ℝ)
    (hquota : (∑i,w i)≤ quota) : (∑i∈T,w i.val)≤ quota := by
  have h₁ : (∑i∈T,w i.val)≤∑i:A,w i.val :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun i _ _=> hw i.val)
  have h₂ : (∑i:A,w i.val)≤∑i,w i := by
    rw [Finset.sum_coe_sort A (fun i=> w i)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun i _ _=> hw i)
  exact h₁.trans (h₂.trans hquota)

/-- Divisor opening never enlarges either original ordinary cap. The
only collar is the genuine dyadic/profile factor at most three. -/
theorem terminal_divisor_length {U X Y n : ℝ} (hU : 1< U) (hX : 0< X) (hY : 0< Y)
    (hYbound : Y≤2*X) (e : Fin 2) (B : HeckeInverseAmplification.NonzeroIdeal) (D : Ideal O)
    (hD : D∈IdealMobiusDivisorSum.idealDivisors B.val) (hcap : length U X≤ n) :
    0<(scale e*Y)/(D.absNorm:ℝ) ∧
      length U ((scale e*Y)/(D.absNorm:ℝ))≤ n+Real.logb U 3 := by
  have hDn : (1:ℝ)≤(D.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (ne_zero_of_dvd_ne_zero B.property ((IdealMobiusDivisorSum.mem_idealDivisors B.property).mp hD)))
  have hp := mul_pos (ProfileSeparation.scale_pos e) hY
  refine ⟨div_pos hp (zero_lt_one.trans_le hDn),?_⟩
  have hscale := ProfileSeparation.scale_mem e
  have hd : (scale e*Y)/(D.absNorm:ℝ)≤3*X :=
    (div_le_self hp.le hDn).trans (by nlinarith [hscale.2])
  exact (length_mono U _ _ hU hd).trans
    ((length_mul_le U 3 X hU (by norm_num)).trans (by linarith))

/-- Exact finite source equality for all whole subproducts, including the
empty one. This lets a source on the genuine subtype T consume the same
finiteEnergyOn without changing a physical row. -/
theorem terminal_energy_subtype {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Finset ι) (s : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : ι→FreeRow→ℂ) :
    StrongPair.finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark=
      StrongPair.finiteEnergy s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ (fun i:T=> mark i.val) := by
  unfold StrongPair.finiteEnergyOn StrongPair.finiteEnergy
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.prod_coe_sort T (fun i=>‖mark i u‖^2)]

#print axioms terminal_cofactor_geometry
#print axioms terminal_full_subset_quota
#print axioms terminal_divisor_length
#print axioms terminal_energy_subtype
end
end QRH.Cycle092.RegularColoredForward
