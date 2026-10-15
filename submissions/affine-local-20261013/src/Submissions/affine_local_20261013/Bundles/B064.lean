/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B015
import Submissions.affine_local_20261013.Bundles.B056
import Submissions.affine_local_20261013.Bundles.B060
import Submissions.affine_local_20261013.Bundles.B061
import Submissions.affine_local_20261013.Bundles.B062

/- BEGIN ORIGINAL MODULE Physical.Packet ; sha256 85776cdfd167ba1eee0c8d1b989e29b6a326121ab4712afae23960a73e2e8ade -/
section


noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Local44.Physical
open Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_half_mass_bins
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (n U xi pad : ℝ) (boxes : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L delta loss epsilon Ccount Cmoment M : ℝ)
    (hn : BareWindow n) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hpad : 0 ≤ pad)
    (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hq : 0 ≤ q) (hqdelta : q ≤ delta/2)
    (hcard : (Fintype.card ι : ℝ) ≤ Ccount*U^R)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (Lc i*N i e) ≤ U^((boxes : ℝ)*xi))
    (hseries : ∀ i, Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e‖))
    (hs : ∀ i, Summable (fun e => ‖A i e‖*(N i e)^(-(1/2:ℝ))*
      max 1 (Lc i*N i e)^(delta/2)))
    (hmass : ∀ i, (∑' e, ‖A i e‖*(N i e)^(-(1/2:ℝ))*
      max 1 (Lc i*N i e)^(delta/2)) ≤ M)
    (hselected : ∀ j ∈ Finset.range (boxes+1), ∀ i,
      U^(q*transportCapacity n ((j : ℝ)*xi+xi+pad)-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i, ‖P i‖ ≤ U^(q*L))
    (hselection : ∀ j ∈ Finset.range (boxes+1), ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi boxes (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((boxes+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*baseCapacity n/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+pad)/2) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hrho : 0 ≤ delta/2 := hq.trans hqdelta
  let B (j : ℕ) (i : ι) := normalizedBox U xi boxes j (delta/2) M
    (fun e=> max 1 (Lc i*N i e)) (fun e=> A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)
  have hsplit (i : ι) : (∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) =
      ∑ j ∈ Finset.range (boxes+1), ((M*U^(-delta*((j : ℝ)*xi)/2) : ℝ):ℂ)*B j i := by
    have hh := normalized_box_reconstruction U xi boxes (delta/2) M hU0 hM.ne'
      (fun e=> max 1 (Lc i*N i e)) (fun e=> A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) (hseries i)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 3
    ring
  have henergy (j : ℕ) (hj : j ∈ Finset.range (boxes+1)) :
      (∑ i, ‖B j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon) :=
    normalized_dilation_box_fourth base A S N hN Lc (delta/2) U xi boxes j valid (Q j) M
      (Cmoment*U^(1+epsilon)) hM hU hxi hrho hzero hupper hs hmass (hselection j hj)
  exact finite_half_mass_bins Finset.univ boxes B Q P _ n U R q L xi pad delta loss epsilon
    Ccount Cmoment M hn hU hc hm hM.le hq hqdelta hxi hpad (by simpa using hcard)
    (fun i hi=> hsplit i) (fun j hj i hi=> hselected j hj i) (fun i hi=> hfull i) henergy

end Local44.Physical
end
/- END ORIGINAL MODULE Physical.Packet -/

/- BEGIN ORIGINAL MODULE Analytic.JointAllocatedAdmissible ; sha256 375db295b264fa49e505d1fe001aca37fba3348ed265f2a8f7e07df5c4e09f60 -/
section



/-! The source scales and frequencies imply all buffered admissibility
fields. Allocation and slot inclusion introduce no conductor assumption. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CenteredMomentNaturalRowSource
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentSecondHeightFamily
open CenteredMomentDivisorExtraction
local notation "O" => HeckeFamily.O

theorem allocated_plain_scale_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) (X U : ℝ) (hX : 0 ≤ X) (hU : 1 ≤ U) (hXU : X ≤ U) :
    clippedScale (X/(Ideal.absNorm (selectedPlain D allocation j) : ℝ)) ≤ U := by
  have hN : (1 : ℝ) ≤ Ideal.absNorm (selectedPlain D allocation j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (selectedDivisor_ne_zero D Finset.univ allocation (Sum.inr j)))
  exact max_le hU ((div_le_self hX hN).trans hXU)

/-- Source scale caps and one frequency gate suffice for the actual
allocated data. The full original relative conductor family also covers
every surviving slot. -/
theorem allocatedBufferedData_admissible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {w : NonzeroElement} {n : ℕ} {profileBound : ℕ → ℝ} {a e : ℝ}
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
    (puncture : Ideal O) (hpuncture : puncture ≠ 0)
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P₁ P₂ : BufferedPlainProfile n profileBound a e)
    (Z d X₁ X₂ : ℝ) (P : ι → ℝ) (t : ℝ) (bin : ℕ)
    (η₀ : ι → Character) (A B : ι → ℝ)
    (Rwidth τ ηaux σmin σmax T : ℝ)
    (hbase : 1 < Z^d) (hR : 0 ≤ Rwidth)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hX₁cap : X₁ ≤ (Z^d)^Rwidth) (hX₂cap : X₂ ≤ (Z^d)^Rwidth)
    (hP : ∀ i, 1 ≤ P i ∧ P i ≤ (Z^d)^Rwidth)
    (hσmin : σmin ≤ 0) (hσmax : 0 ≤ σmax)
    (hconductor : ∀ label, (bufferedProductFamily M H hH η₀
      (excluded N.character puncture) label).modulus.absNorm ≤ Z^d)
    (ht₁ : P₁.freq = t) (ht₂ : P₂.freq = t)
    (hfreq : |t|+Z^τ/2 ≤ (3*bin+2 : ℕ)*Z^τ)
    (hfour : (3+(3*bin+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux)
    (htwo : (3+(3*bin+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux)
    (hlog : ∀ i : liveIndices D allocation,
      2*(|Real.log (A i.val)|+|Real.log (B i.val)|)+1 ≤ Real.log (P i.val))
    (hbuffer : 3*(bin+1 : ℕ)*Z^τ ≤ T) :
    (allocatedBufferedData parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂ P t bin).Admissible
      M H hH (fun i : liveIndices D allocation => η₀ i.val)
        (fun i : liveIndices D allocation => A i.val) (fun i : liveIndices D allocation => B i.val)
        Rwidth τ ηaux σmin σmax Z d T := by
  have hscale : 1 ≤ (Z^d)^Rwidth := Real.one_le_rpow hbase.le hR
  have hc (X : ℝ) : 0 < clippedScale X := zero_lt_one.trans_le (clippedScale_ge_one X)
  refine ⟨Real.logb_nonneg hbase (clippedScale_ge_one _),?_,
    Real.logb_nonneg hbase (clippedScale_ge_one _),?_,?_,?_,?_,?_,?_,hfour,htwo,?_,hbuffer⟩
  · exact (Real.logb_le_iff_le_rpow hbase (hc _)).mpr
      (allocated_plain_scale_le D allocation 0 X₁ _ hX₁ hscale hX₁cap)
  · exact (Real.logb_le_iff_le_rpow hbase (hc _)).mpr
      (allocated_plain_scale_le D allocation 1 X₂ _ hX₂ hscale hX₂cap)
  · intro i
    exact ⟨Real.logb_nonneg hbase (hP i.val).1,
      (Real.logb_le_iff_le_rpow hbase (zero_lt_one.trans_le (hP i.val).1)).mpr (hP i.val).2,
      hσmin,hσmax⟩
  · rintro (_ | ⟨i,θ⟩)
    · exact hconductor none
    · exact hconductor (some (i.val,θ))
  · simpa only [allocatedBufferedData, ht₁] using hfreq
  · simpa only [allocatedBufferedData, ht₂] using hfreq
  · intro i
    simpa only [allocatedBufferedData, add_zero] using hfreq
  · intro i
    change _ ≤ Real.log ((Z^d)^Real.logb (Z^d) (P i.val))
    rw [Real.rpow_logb (zero_lt_one.trans hbase) (ne_of_gt hbase)
      (zero_lt_one.trans_le (hP i.val).1)]
    exact hlog i

#print axioms allocatedBufferedData_admissible
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointAllocatedAdmissible -/

/- BEGIN ORIGINAL MODULE Analytic.JointBufferedDominatedFibers ; sha256 22fa381c655d67c140976b401627461d7beebbf71d04bed03c5f9538d7c059b5 -/
section


/-! Select literal source realizations only on the nonempty arithmetic
support. No artificial profile is needed for a zero or empty fiber. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem joint_buffered_product_fibers_of_le
    {α : Type*} [DecidableEq α] {β : α → Type*}
    {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (η : Character) (η₀ : Slot → Character) (V : Slot → ℝ → ℂ) (Bprofile : Slot → ℝ)
    (orders : Finset Slot → ℕ) (profileBound : ℕ → ℝ) (a e Z d : ℝ)
    (labels : Finset α) (w : α → NonzeroElement) (fiber : (v : α) → Finset (β v))
    (weight value : (v : α) → β v → ℝ) (B E Csrc : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E) (hCsrc : 0 ≤ Csrc)
    (gate : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e →
      SurvivingBufferedData η (w v) Slot orders profileBound a e → Prop)
    (hweight : ∀ v ∈ labels, ∀ b ∈ fiber v, 0 ≤ weight v b)
    (hvalue : ∀ v ∈ labels, ∀ b ∈ fiber v, 0 ≤ value v b)
    (hmass : ∀ v ∈ labels, (∑ b ∈ fiber v, weight v b) ≤ B)
    (hdata : ∀ v ∈ labels, ∀ b ∈ fiber v,
      ∃ DL DR : SurvivingBufferedData η (w v) Slot orders profileBound a e,
        value v b ≤ Csrc*(‖DL.value M H η₀ V Bprofile Z d‖*‖DR.value M H η₀ V Bprofile Z d‖) ∧
        gate v DL DR)
    (hmain : ∀ (S : Finset α), S ⊆ labels →
      ∀ FL FR : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e,
      (∀ v ∈ S, gate v (FL v) (FR v)) →
      (∑ v ∈ S, ‖(FL v).value M H η₀ V Bprofile Z d‖ *
        ‖(FR v).value M H η₀ V Bprofile Z d‖) ≤ E) :
    (∑ v ∈ labels, ∑ b ∈ fiber v, weight v b*value v b) ≤ B*(Csrc*E) := by
  apply joint_weighted_fibers labels fiber weight value B (Csrc*E) hB hweight hvalue hmass
  intro S hS pick hpick
  have hreal (v : S) := hdata v (hS v.property) (pick v) (hpick v)
  choose DL DR hnorm hgate using hreal
  by_cases hne : S.Nonempty
  · obtain ⟨v₀,hv₀⟩ := hne
    let left₀ := DL ⟨v₀,hv₀⟩
    let right₀ := DR ⟨v₀,hv₀⟩
    let FL : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e :=
      fun v => if hv : v ∈ S then DL ⟨v,hv⟩ else left₀.rebase (w v)
    let FR : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e :=
      fun v => if hv : v ∈ S then DR ⟨v,hv⟩ else right₀.rebase (w v)
    have hFL (v : S) : FL v = DL v := by dsimp only [FL]; rw [dif_pos v.property]
    have hFR (v : S) : FR v = DR v := by dsimp only [FR]; rw [dif_pos v.property]
    have hb := hmain S hS FL FR (fun v hv => by
      rw [hFL ⟨v,hv⟩,hFR ⟨v,hv⟩]
      exact hgate ⟨v,hv⟩)
    rw [← Finset.sum_coe_sort S (fun v =>
      ‖(FL v).value M H η₀ V Bprofile Z d‖ * ‖(FR v).value M H η₀ V Bprofile Z d‖)] at hb
    have hh : (∑ v : S, value v (pick v)) ≤ Csrc*(∑ v : S,
        ‖(FL v).value M H η₀ V Bprofile Z d‖*‖(FR v).value M H η₀ V Bprofile Z d‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _
      simpa only [hFL,hFR] using hnorm v
    exact hh.trans (mul_le_mul_of_nonneg_left hb hCsrc)
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    simpa using mul_nonneg hCsrc hE

#print axioms joint_buffered_product_fibers_of_le
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointBufferedDominatedFibers -/

/- BEGIN ORIGINAL MODULE Analytic.JointBufferedExistentialFibers ; sha256 dd93352d1a611259758cdd0908ddcf07c5d0e33057ef2b67c71afe66527dd5a2 -/
section


/-! Select literal source realizations only on the nonempty arithmetic
support. No artificial profile is needed for a zero or empty fiber. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem joint_buffered_product_fibers_of_exists
    {α : Type*} [DecidableEq α] {β : α → Type*}
    {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (η : Character) (η₀ : Slot → Character) (V : Slot → ℝ → ℂ) (Bprofile : Slot → ℝ)
    (orders : Finset Slot → ℕ) (profileBound : ℕ → ℝ) (a e Z d : ℝ)
    (labels : Finset α) (w : α → NonzeroElement) (fiber : (v : α) → Finset (β v))
    (weight value : (v : α) → β v → ℝ) (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (gate : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e →
      SurvivingBufferedData η (w v) Slot orders profileBound a e → Prop)
    (hweight : ∀ v ∈ labels, ∀ b ∈ fiber v, 0 ≤ weight v b)
    (hvalue : ∀ v ∈ labels, ∀ b ∈ fiber v, 0 ≤ value v b)
    (hmass : ∀ v ∈ labels, (∑ b ∈ fiber v, weight v b) ≤ B)
    (hdata : ∀ v ∈ labels, ∀ b ∈ fiber v,
      ∃ DL DR : SurvivingBufferedData η (w v) Slot orders profileBound a e,
        value v b = ‖DL.value M H η₀ V Bprofile Z d‖*‖DR.value M H η₀ V Bprofile Z d‖ ∧
        gate v DL DR)
    (hmain : ∀ (S : Finset α), S ⊆ labels →
      ∀ FL FR : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e,
      (∀ v ∈ S, gate v (FL v) (FR v)) →
      (∑ v ∈ S, ‖(FL v).value M H η₀ V Bprofile Z d‖ *
        ‖(FR v).value M H η₀ V Bprofile Z d‖) ≤ E) :
    (∑ v ∈ labels, ∑ b ∈ fiber v, weight v b*value v b) ≤ B*E := by
  apply joint_weighted_fibers labels fiber weight value B E hB hweight hvalue hmass
  intro S hS pick hpick
  have hreal (v : S) := hdata v (hS v.property) (pick v) (hpick v)
  choose DL DR hnorm hgate using hreal
  by_cases hne : S.Nonempty
  · obtain ⟨v₀,hv₀⟩ := hne
    let left₀ := DL ⟨v₀,hv₀⟩
    let right₀ := DR ⟨v₀,hv₀⟩
    let FL : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e :=
      fun v => if hv : v ∈ S then DL ⟨v,hv⟩ else left₀.rebase (w v)
    let FR : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e :=
      fun v => if hv : v ∈ S then DR ⟨v,hv⟩ else right₀.rebase (w v)
    have hFL (v : S) : FL v = DL v := by dsimp only [FL]; rw [dif_pos v.property]
    have hFR (v : S) : FR v = DR v := by dsimp only [FR]; rw [dif_pos v.property]
    have hb := hmain S hS FL FR (fun v hv => by
      rw [hFL ⟨v,hv⟩,hFR ⟨v,hv⟩]
      exact hgate ⟨v,hv⟩)
    rw [← Finset.sum_coe_sort S (fun v =>
      ‖(FL v).value M H η₀ V Bprofile Z d‖ * ‖(FR v).value M H η₀ V Bprofile Z d‖)] at hb
    simpa only [hFL,hFR,← hnorm] using hb
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    simpa using hE

#print axioms joint_buffered_product_fibers_of_exists
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointBufferedExistentialFibers -/

/- BEGIN ORIGINAL MODULE Analytic.JointBufferedSlotShifts ; sha256 c2b2f4237d8d2663684677779a09c72d3fb3cc2c58b2b0ba2f76c8b425e4d84f -/
section


/-! Put the literal prime Mellin shifts in buffered data. The prime
profile used by the high theorem remains the fixed original function;
its constants therefore precede all input heights and real shifts. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

def shiftedPrimeProfiles {Slot : Type*} (V : Slot → ℝ → ℂ)
    (σ freq : Slot → ℝ) : Slot → ℝ → ℂ :=
  fun j y => V j y*(y : ℂ)^(-shift (σ j) (freq j))

theorem annularWeight_shifted_zero {Slot : Type*} (V : Slot → ℝ → ℂ)
    (σ freq : Slot → ℝ) (j : Slot) (P : ℝ) (I : Ideal O) :
    annularWeight (shiftedPrimeProfiles V σ freq j) P 0 0 I =
      annularWeight (V j) P (σ j) (freq j) I := by
  simp only [annularWeight,shiftedPrimeProfiles,HeckeDyadic.shift,Complex.ofReal_zero,
    zero_mul,sub_zero,neg_zero,Complex.cpow_zero,mul_one]

namespace SurvivingBufferedData
variable {η : Character} {w : NonzeroElement} {Slot : Type*}
  [Fintype Slot] [DecidableEq Slot]
  {orders : Finset Slot → ℕ} {profileBound : ℕ → ℝ} {a e : ℝ}

def withSlotShifts (D : SurvivingBufferedData η w Slot orders profileBound a e)
    (σ freq : Slot → ℝ) : SurvivingBufferedData η w Slot orders profileBound a e :=
  { D with data := { D.data with σ := fun j => σ j.val, v := fun j => freq j.val } }

@[simp] theorem withSlotShifts_length
    (D : SurvivingBufferedData η w Slot orders profileBound a e) (σ freq : Slot → ℝ) :
    (D.withSlotShifts σ freq).length = D.length := rfl

theorem withSlotShifts_value
    (D : SurvivingBufferedData η w Slot orders profileBound a e)
    (hσ : ∀ j, D.data.σ j = 0) (hv : ∀ j, D.data.v j = 0)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (η₀ : Slot → Character) (V : Slot → ℝ → ℂ) (B σ freq : Slot → ℝ) (Z d : ℝ) :
    (D.withSlotShifts σ freq).value M H η₀ V B Z d =
      D.value M H η₀ (shiftedPrimeProfiles V σ freq) B Z d := by
  unfold value withSlotShifts JointBufferedProductData.value
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [hσ,hv,annularWeight_shifted_zero]

/-- Conductor, lengths and plain frequencies are unchanged. Only the
literal shifted prime-frequency gates and bounded real shifts are needed. -/
theorem withSlotShifts_short_gates
    (D : SurvivingBufferedData η w Slot orders profileBound a e)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η₀ : Slot → Character)
    (Rwidth τ ηaux lo₀ hi₀ σmin σmax Z d T : ℝ) (σ freq : Slot → ℝ)
    (hD : D.ShortSlotGates M H hH η₀ Rwidth τ ηaux lo₀ hi₀ Z d T)
    (hσ : ∀ j : D.slots, σmin ≤ σ j.val ∧ σ j.val ≤ σmax)
    (hfreq : ∀ j : D.slots,
      |D.data.t+freq j.val|+Z^τ/2 ≤ (3*D.data.bin+2 : ℕ)*Z^τ) :
    (D.withSlotShifts σ freq).ShortSlotGates M H hH η₀
      Rwidth τ ηaux σmin σmax Z d T := by
  exact ⟨hD.r₁_nonneg,hD.r₁_le,hD.r₂_nonneg,hD.r₂_le,
    (fun j => ⟨(hD.slots j).1,(hD.slots j).2.1,(hσ j).1,(hσ j).2⟩),
    hD.conductor,hD.freq₁,hD.freq₂,hfreq,hD.height_four,hD.height_two,hD.buffer_height⟩

end SurvivingBufferedData

#print axioms SurvivingBufferedData.withSlotShifts_value
#print axioms SurvivingBufferedData.withSlotShifts_short_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointBufferedSlotShifts -/

/- BEGIN ORIGINAL MODULE Analytic.JointCommonVolumeSector ; sha256 48e0f5e2f1ed0af1a23623166aebf743c282954b038eb39ec8b908c47a600166 -/
section


/-! A lower common-norm endpoint is enough for the actual residual length.
No exact ideal norm is fixed inside a joint population sector. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildSourceCaps
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

theorem actual_second_common_volume_sector (s : Input Slot) (C R : Ideal O)
    (B : actualAllocations s.pools C)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0)
    (Z A c loss : ℝ) (hZ : 1 < Z)
    (hv : volume s.toData ≤ Z^A) (hC : Z^c ≤ (C.absNorm : ℝ))
    (hprofile : (max 1 s.upper)^Fintype.card Slot ≤ Z^loss) :
    Real.logb Z (secondCommonVolume s C B) ≤ A-c+loss := by
  have hz := zero_lt_one.trans hZ
  have hV := volume_pos s.toData
  have hCpos := Real.rpow_pos_of_pos hz c
  have hbound := actual_second_common_volume_le s C R B hne
  have hh : secondCommonVolume s C B ≤ Z^(A-c+loss) := by
    apply hbound.trans
    calc
      _ ≤ Z^loss*Z^A/Z^c := by gcongr
      _ = _ := by
        rw [←Real.rpow_add hz,←Real.rpow_sub hz]
        congr 1
        ring
  have hl := Real.logb_le_logb_of_le hZ (secondCommonVolume_pos s C B) hh
  simpa only [Real.logb_rpow hz hZ.ne'] using hl

#print axioms actual_second_common_volume_sector
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonVolumeSector -/
