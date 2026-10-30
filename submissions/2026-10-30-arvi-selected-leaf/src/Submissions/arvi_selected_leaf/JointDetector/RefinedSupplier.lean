/- Copyright (c) 2026 Joseph Bebel. -/
/- Copyright (c) 2026 OpenAI. Apache-2.0.
The paired HIGH adapter retains Sil's admitted pointwise supplier. -/
import Submissions.arvi_selected_leaf.JointDetector.RefinedPrice
import Submissions.arvi_selected_leaf.JointDetector.BestSourceGates
import Submissions.sil_density_split_20261026.Density.Leaf
import Submissions.hailey_collet_1252270103.Cycle61.Moment.PositiveRowFactors

/-!
# Analytic interface for the refined packed supplier

The new input below is a count of actual natural rows with the literal prime
slot responses. It is stronger than a core detector count, and is not asserted
here without a provider. LOW and native bounds are inherited from Sil.
-/
namespace Qrh.JointDetector.RefinedSupplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Density
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion
open LocalMoment HeckeDetectorZeros ProbePhysical ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The squared product of the original, unaltered physical prime slots.
The root mask, natural zeros, relative ray characters and frequency signs
remain inside `normalizedSlot`. -/
def slotMass {α : Type} [Fintype α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    {Z bΦ : ℝ} (st : NaturalState Z 0 bΦ) (η₀ : Character)
    (W : ℝ → ℂ) (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ)
    (t : ℝ) (z : O) : ℝ :=
  ∏ k, ‖normalizedSlot st.character st.mask 1 z
    (primePool rayM H 2 (Z^(w k)))
    (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I)
    t (Z^(w k))‖^2

/-- Joint count rate; above the zero slope the same selected norm's unit
column supplies the SC count. The inherited zero count is kept in both cases. -/
def jointRate (ν δ : ℝ) : ℝ :=
  if δ ≤ ν then min (1 - RefinedPrice.k ν) (jointCountExponent ν δ)
  else min (1 - RefinedPrice.k ν) (1-δ)

theorem jointRate_le_one {ν δ : ℝ}
    (hν : ν ∈ Icc (13/20 : ℝ) (3/4)) : jointRate ν δ ≤ 1 := by
  have hk := RefinedPrice.k_range hν
  unfold jointRate
  split_ifs <;> exact (min_le_left _ _).trans (by linarith)

/-- All amplitude branches, including the SC complement, pay the refined
price on the entire nonnegative width range. -/
theorem jointRate_energy {ν δ P s M : ℝ}
    (hν : ν ∈ Icc (13/20 : ℝ) (3/4))
    (hδ : δ ∈ Icc (1001/2000 : ℝ) (3/4))
    (hM : 0 ≤ M) (hs : 0 ≤ s) :
    jointRate ν δ * M + ν*P + min δ ν*s ≤ M + RefinedPrice.g ν P s M := by
  unfold jointRate
  split_ifs with h
  · rw [min_eq_left h]
    exact RefinedPrice.joint_energy_le_g hν ⟨hδ.1, h⟩ hM hs
  · have hvd : ν ≤ δ := le_of_not_ge h
    rw [min_eq_right hvd]
    have hsame : jointCountExponent ν ν = 1-ν := by
      unfold jointCountExponent witnessDen
      have hd : 3*(1-ν) ≠ 0 := by nlinarith [hν.2]
      have he : 3 * (1 - ν) + 2 * (ν - ν) = 3 * (1 - ν) := by ring
      rw [he]
      field_simp
    have hk := RefinedPrice.k_le_nu hν
    have hbase := RefinedPrice.joint_energy_le_g hν
      (show ν ∈ Icc (1001/2000 : ℝ) ν from ⟨by linarith [hν.1], le_rfl⟩) hM hs (P:=P)
    rw [hsame, min_eq_right (by linarith)] at hbase
    have hrate : min (1-RefinedPrice.k ν) (1-δ)*M ≤ (1-ν)*M :=
      mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (by linarith)) hM
    linarith

/-- Exact public count contract required by the packed supplier.

The early mesh is chosen before the slot type, profiles, finite anchor
family, heights, or any selected row set. `J` and `C` are chosen before the
live height and density/amplitude values. The count includes every natural
sixth-root state; a free-core-only count does not satisfy this contract.
The product response must be derived using actual individual-slot prefix
selection when invoking a selected-norm theorem.
-/
def WholeJointCount : Prop :=
  ∀ Mmin Mcap smin loss : ℝ, 0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1:ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50:ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (b δ T' : ℝ), 33/40 ≤ b → b ≤ 7/8 → δ ∈ Icc (1001/2000 : ℝ) (3/4) → 0 ≤ T' →
  ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
    st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
    b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T' ∧
    Z^(δ * ∑ k, w k) ≤ slotMass rayM H hH st η₀ W θ w σ v t z) →
    (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(jointRate (2*b-1) δ + loss)

/-- Literal squared factorization; this is the actual HIGH kernel, with no
replacement of the ordinary factors or of the slots. -/
theorem positiveSlotRow_squared_factors {α : Type} [Fintype α] [DecidableEq α]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : α → Finset (Ideal O)) (β : α → Ideal O → ℂ) (P : α → ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 =
      (‖(Real.sqrt X₁ : ℂ)⁻¹*CenteredMomentHeckeHeight.rowTwistedSum η m A z W₁ t X₁‖^2 *
       ‖(Real.sqrt X₂ : ℂ)⁻¹*CenteredMomentHeckeHeight.rowTwistedSum η m A z W₂ t X₂‖^2) *
      ∏ i, ‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2 := by
  rw [actual_positive_row_factors η m A z W₁ W₂ S β P t X₁ X₂ hX₁ hX₂ hP]
  simp only [norm_mul, mul_pow, norm_prod, Finset.prod_pow]


/-- A finite histogram of the actual slot product. The last class has no
upper amplitude restriction; it is paid by the SC count at slope `3/4`. -/
def amplitudeBin (n : ℕ) (step Z s response : ℝ) : Fin (n+1) :=
  ⟨Nat.findGreatest (fun i => Z^(((1001/2000:ℝ)+(i:ℝ)*step)*s) ≤ response) n,
    Nat.lt_succ_of_le (Nat.findGreatest_le n)⟩

theorem amplitudeBin_lower {n : ℕ} {step Z s response : ℝ}
    (h : (amplitudeBin n step Z s response).val ≠ 0) :
    Z^(((1001/2000:ℝ)+((amplitudeBin n step Z s response).val:ℝ)*step)*s) ≤ response := by
  exact Nat.findGreatest_of_ne_zero rfl h

theorem amplitudeBin_upper {n : ℕ} {step Z s response : ℝ}
    (h : (amplitudeBin n step Z s response).val < n) :
    response < Z^(((1001/2000:ℝ)+((amplitudeBin n step Z s response).val+1:ℕ)*step)*s) := by
  apply lt_of_not_ge
  exact Nat.findGreatest_is_greatest (P := fun i => Z^(((1001/2000:ℝ)+(i:ℝ)*step)*s) ≤ response)
    (Nat.lt_succ_self _) (by simpa only [amplitudeBin] using Nat.succ_le_iff.mpr h)

/-- Exact one-bin HIGH energy summation, tied to the actual natural row and
its original slots. The two pointwise inputs are precisely the inherited
HIGH bound with all slots and with the empty slot set. The only improved
analytic premise is the distributional joint **count**, not an energy or
packed-source estimate. All closed amplitude-bin boundaries are included. -/
theorem finite_joint_bin_energy {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    {Z bΦ : ℝ} (st : NaturalState Z 0 bΦ) (η₀ : Character)
    (W : ℝ → ℂ) (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ)
    (t : ℝ) (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (E : Finset O)
    (ν Pl s M F C err loss step : ℝ) (n : ℕ)
    (hZ : 1 ≤ Z) (hν : ν ∈ Icc (13/20:ℝ) (3/4)) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hF : 0 ≤ F) (hC : 0 ≤ C) (hstep : 0 < step) (hn : 0 < n)
    (htop : (1001/2000:ℝ)+(n:ℝ)*step = 3/4)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hfull : ∀ z ∈ E,
      ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I)
        (fun k => Z^(w k)) t X₁ X₂‖^2 ≤ F*Z^(ν*(Pl+s)+err))
    (hplain : ∀ z ∈ E,
      ‖(Real.sqrt X₁ : ℂ)⁻¹*CenteredMomentHeckeHeight.rowTwistedSum
          st.character st.mask 1 z (p.profile 0) t X₁‖^2 *
      ‖(Real.sqrt X₂ : ℂ)⁻¹*CenteredMomentHeckeHeight.rowTwistedSum
          st.character st.mask 1 z (p.profile 1) t X₂‖^2 ≤ F*Z^(ν*Pl+err))
    (hzero : (E.card:ℝ) ≤ C*Z^((1-RefinedPrice.k ν)*M+loss))
    (hjoint : ∀ δ ∈ Icc (1001/2000:ℝ) (3/4), ∀ rows : Finset O,
      rows ⊆ E → (∀ z ∈ rows, Z^(δ*s) ≤ slotMass rayM H hH st η₀ W θ w σ v t z) →
      (rows.card:ℝ) ≤ C*Z^(jointRate ν δ*M+loss)) :
    (∑ z ∈ E, ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I)
        (fun k => Z^(w k)) t X₁ X₂‖^2) ≤
      (n+1:ℕ)*F*C*Z^(M+RefinedPrice.g ν Pl s M+err+loss+step*s) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let mass : O → ℝ := slotMass rayM H hH st η₀ W θ w σ v t
  let row : O → ℝ := fun z =>
    ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I)
        (fun k => Z^(w k)) t X₁ X₂‖^2
  let cls : O → Fin (n+1) := fun z => amplitudeBin n step Z s (mass z)
  let δ : Fin (n+1) → ℝ := fun i => 1001/2000+(i.val:ℝ)*step
  let rate : Fin (n+1) → ℝ := fun i => if i.val=0 then 1-RefinedPrice.k ν else jointRate ν (δ i)
  let slope : Fin (n+1) → ℝ := fun i => if i.val=0 then 1001/2000 else min (δ i) ν
  have hδ : ∀ i, δ i ∈ Icc (1001/2000:ℝ) (3/4) := by
    intro i
    have hi : (i.val:ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    dsimp [δ]
    constructor <;> nlinarith
  have hpaid : ∀ i, rate i*M+ν*Pl+slope i*s ≤ M+RefinedPrice.g ν Pl s M := by
    intro i
    by_cases hi : i.val=0
    · simp only [rate, slope, ite_eq_left hi]
      exact RefinedPrice.zero_energy_le_g_of_delta_le_cutoff hν le_rfl hs
    · simp only [rate, slope, ite_eq_right hi]
      exact jointRate_energy hν (hδ i) hM hs
  have hcount : ∀ i, ((E.filter (fun z => cls z=i)).card:ℝ) ≤ C*Z^(rate i*M+loss) := by
    intro i
    by_cases hi : i.val=0
    · simpa only [rate, ite_eq_left hi] using
        (Nat.cast_le.mpr (Finset.card_filter_le E (fun z => cls z=i))).trans hzero
    · simp only [rate, ite_eq_right hi]
      apply hjoint (δ i) (hδ i) _ (Finset.filter_subset _ _)
      intro z hz
      have he : cls z=i := (Finset.mem_filter.mp hz).2
      have hb := amplitudeBin_lower (n:=n) (step:=step) (Z:=Z) (s:=s) (response:=mass z)
        (show (cls z).val ≠ 0 by rw [he]; exact hi)
      simpa only [← he, δ, cls] using hb
  have hrow : ∀ i, ∀ z ∈ E.filter (fun z => cls z=i),
      row z ≤ F*Z^(ν*Pl+slope i*s+err+step*s) := by
    intro i z hz
    obtain ⟨hzE, he⟩ := Finset.mem_filter.mp hz
    have hall := hfull z hzE
    by_cases hi : i.val=0
    · have hbin : (cls z).val < n := by rw [he, hi]; exact hn
      have hb := (amplitudeBin_upper (n:=n) (step:=step) (Z:=Z) (s:=s)
        (response:=mass z) hbin).le
      have hb' : mass z ≤ Z^((1001/2000+step)*s) := by
        change mass z ≤ Z^((1001/2000+((cls z).val+1:ℕ)*step)*s) at hb
        rw [he, hi] at hb
        norm_num at hb ⊢
        exact hb
      have hf := positiveSlotRow_squared_factors st.character st.mask 1 z (p.profile 0)
        (p.profile 1) (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I)
        (fun k => Z^(w k)) t X₁ X₂ hX₁ hX₂
        (fun k => Real.rpow_pos_of_pos hZ0 _)
      change row z = _*mass z at hf
      rw [hf]
      have hm0 : 0 ≤ mass z := Finset.prod_nonneg (fun k _ => sq_nonneg _)
      have hp0 : 0 ≤ F*Z^(ν*Pl+err) := by positivity
      have hh := mul_le_mul (hplain z hzE) hb' hm0 hp0
      convert hh using 1
      simp only [slope, ite_eq_left hi]
      rw [mul_assoc, ← Real.rpow_add hZ0]
      congr 2
      ring
    · by_cases hνδ : ν ≤ δ i
      · have hp := Real.rpow_le_rpow_of_exponent_le hZ
          (show ν*(Pl+s)+err ≤ ν*Pl+slope i*s+err+step*s by
            simp only [slope, ite_eq_right hi, min_eq_right hνδ]
            nlinarith)
        exact hall.trans (mul_le_mul_of_nonneg_left hp hF)
      · have hnotTop : i.val < n := by
          have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
          by_contra hc
          have heq : i.val=n := by omega
          have : δ i = 3/4 := by dsimp [δ]; rw [heq]; exact htop
          exact hνδ (this.symm ▸ hν.2)
        have hb := (amplitudeBin_upper (n:=n) (step:=step) (Z:=Z) (s:=s)
          (response:=mass z) (show (cls z).val<n by rw [he]; exact hnotTop)).le
        have hb' : mass z ≤ Z^((δ i+step)*s) := by
          change mass z ≤ Z^((1001/2000+((cls z).val+1:ℕ)*step)*s) at hb
          rw [he] at hb
          simpa only [δ, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using hb
        have hf := positiveSlotRow_squared_factors st.character st.mask 1 z (p.profile 0)
          (p.profile 1) (fun k => primePool rayM H 2 (Z^(w k)))
          (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I)
          (fun k => Z^(w k)) t X₁ X₂ hX₁ hX₂
          (fun k => Real.rpow_pos_of_pos hZ0 _)
        change row z = _*mass z at hf
        rw [hf]
        have hm0 : 0 ≤ mass z := Finset.prod_nonneg (fun k _ => sq_nonneg _)
        have hp0 : 0 ≤ F*Z^(ν*Pl+err) := by positivity
        have hh := mul_le_mul (hplain z hzE) hb' hm0 hp0
        convert hh using 1
        simp only [slope, ite_eq_right hi, min_eq_left (le_of_not_ge hνδ)]
        rw [mul_assoc, ← Real.rpow_add hZ0]
        congr 2
        ring
  change ∑ z ∈ E, row z ≤ _
  rw [← Finset.sum_fiberwise E cls row]
  calc
    _ ≤ ∑ i : Fin (n+1), C*F*Z^(M+RefinedPrice.g ν Pl s M+err+loss+step*s) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ _z ∈ E.filter (fun z => cls z=i), F*Z^(ν*Pl+slope i*s+err+step*s) :=
          Finset.sum_le_sum (hrow i)
        _ = ((E.filter (fun z => cls z=i)).card:ℝ)*(F*Z^(ν*Pl+slope i*s+err+step*s)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (C*Z^(rate i*M+loss))*(F*Z^(ν*Pl+slope i*s+err+step*s)) :=
          mul_le_mul_of_nonneg_right (hcount i) (by positivity)
        _ = C*F*Z^(rate i*M+ν*Pl+slope i*s+err+loss+step*s) := by
          calc
            _ = C*F*(Z^(rate i*M+loss)*Z^(ν*Pl+slope i*s+err+step*s)) := by ring
            _ = _ := by rw [← Real.rpow_add hZ0]; congr 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hpaid i])) (mul_nonneg hC hF)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring


section ActualPointwise
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Both literal pointwise inputs are obtained from the admitted supplier.
The second invocation has the empty original slot set; it does not divide
by any slot response and remains valid when a slot vanishes. -/
theorem actual_high_row_bounds {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ Mcap Lplain τ ε₁ e kap v d : ℝ) (hbΦ : 0 ≤ bΦ) (hL : 0 ≤ Lplain) (hτ : 0 < τ)
    (hε₁ : 0 < ε₁) (he : 0 < e) (he' : e < 1/1000) (hkap : 0 < kap) (hkap' : kap ≤ 1)
    (hv : 0 ≤ v) (hd : 0 < d) (hdsupply : Mcap+0+1 ≤ d)
    (hslotBudget : 8*e*(1/d)+kap ≤ ε₁)
    (hplainBudget : 12*e*(Lplain/d+2)+8*kap+2*v ≤ ε₁) :
    ∃ K : ℝ, 0 < K ∧ ∃ S : Finset (ℕ×ℕ), ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ st : NaturalState Z 0 bΦ, st.puncture = 1 → st.width ≤ Mcap →
    ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
      (b : ℝ) (i : ℕ), 51/100 ≤ b → b ≤ 1 →
    ∀ z : O, ∀ hz : st.radial.keep z,
      st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 →
      Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz
        (3*(i+1 : ℕ)*Z^τ) < b + 2*e →
    ∀ (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ) (t : ℝ),
      (∀ k, 0 ≤ w k) → (∀ k, w k ≤ 1) →
      (∀ k, (33/50:ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
      (∀ k, |t+v' k|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) → |t|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^v →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
      length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
      (‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
        (fun k => Z^(w k)) t X₁ X₂‖^2 ≤
      K * (p.control S)^2 *
        Z^((2*b-1)*(length Z X₁ + length Z X₂ + ∑ k, w k) +
          2*ε₁*d*(Fintype.card α + 1)) ∧
      ‖(Real.sqrt X₁ : ℂ)⁻¹*CenteredMomentHeckeHeight.rowTwistedSum
          st.character st.mask 1 z (p.profile 0) t X₁‖^2 *
      ‖(Real.sqrt X₂ : ℂ)⁻¹*CenteredMomentHeckeHeight.rowTwistedSum
          st.character st.mask 1 z (p.profile 1) t X₂‖^2 ≤
      K * (p.control S)^2 *
        Z^((2*b-1)*(length Z X₁ + length Z X₂) +
          2*ε₁*d*(Fintype.card α + 1))) := by
  obtain ⟨K, hK, S, hev⟩ := high_row_bound rayM H hH (α:=α) W hWs hW
    bΦ Mcap Lplain τ ε₁ e kap v d hbΦ hL hτ hε₁ he he' hkap hkap' hv hd hdsupply
    hslotBudget hplainBudget
  refine ⟨K, hK, S, fun η₀ => ?_⟩
  filter_upwards [hev η₀] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro st hu hwidth hQM hQη b i hb hb1 z hz hp hupper T θ w σ v' t hw hw1 hσ hσ'
    hwin hwinP hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  refine ⟨hZ.2 st hu hwidth hQM hQη b i hb hb1 z hz hp hupper T θ w σ v' t
    hw hw1 hσ hσ' hwin hwinP hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂, ?_⟩
  let T₀ : Finset α := ∅
  let θ₀ : T₀ → RayQuotient.Characters rayM H := fun k => False.elim (Finset.notMem_empty k.val k.property)
  let w₀ : T₀ → ℝ := fun _ => 0
  let σ₀ : T₀ → ℝ := fun _ => 33/50
  let v₀ : T₀ → ℝ := fun _ => 0
  have ho := hZ.2 st hu hwidth hQM hQη b i hb hb1 z hz hp hupper T₀ θ₀ w₀ σ₀ v₀ t
    (fun k => False.elim (Finset.notMem_empty k.val k.property))
    (fun k => False.elim (Finset.notMem_empty k.val k.property))
    (fun k => False.elim (Finset.notMem_empty k.val k.property))
    (fun k => False.elim (Finset.notMem_empty k.val k.property))
    (fun k => False.elim (Finset.notMem_empty k.val k.property))
    hwinP hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  rw [positiveSlotRow_squared_factors st.character st.mask 1 z (p.profile 0) (p.profile 1)
    _ _ (fun k => Z^(w₀ k)) t X₁ X₂ hX₁ hX₂
    (fun k => Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)] at ho
  simpa only [T₀, Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty,
    mul_one, add_zero] using ho

end ActualPointwise


/-- Sum class estimates for the literal compact radial energy. The
hypotheses apply to arbitrary finite subsets, including boundary rows. -/
theorem energy_le_class_sums {α κ : Type} [Fintype α] [Fintype κ]
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (S : α → Finset (Ideal O)) (β : α → Ideal O → ℂ) (P : α → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K b : ℝ)
    (_hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) (hK : 0 < K)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Iic b) (cls : O → κ) (G : ℝ)
    (hclass : ∀ c, ∀ rows : Finset O,
      (∀ z ∈ rows, keep z ∧ Φ (‖eisEmbedding z‖^2/K) ≠ 0 ∧ cls z=c) →
      (∑ z ∈ rows, ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2) ≤ G) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≤
      QuadraticInitialBound.diagonalControl Φ * (Fintype.card κ : ℝ) * G := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (b*K)
  let B := ShortDraftLatticeCount.rowNormBall N₀
  let E := B.filter (fun z => keep z ∧ Φ (‖eisEmbedding z‖^2/K) ≠ 0)
  let r : O → ℝ := fun z => ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2
  let f : O → ℝ := fun z => if keep z then r z*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hout : ∀ z, Φ (‖eisEmbedding z‖^2/K) ≠ 0 → z ∈ B := by
    intro z hn
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    have hh : ‖eisEmbedding z‖^2 ≤ (N₀:ℝ) := ((div_le_iff₀ hK).mp (hs hn)).trans hN₀
    exact_mod_cast (show ((Ideal.span {z}).absNorm:ℝ) ≤ N₀ by
      rwa [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span])
  have he : energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K = ∑ z ∈ E, f z := by
    unfold energy
    apply tsum_eq_sum
    intro z hz
    by_cases hk : keep z
    · have hp : Φ (‖eisEmbedding z‖^2/K) = 0 := by
        by_contra hn
        exact hz (Finset.mem_filter.mpr ⟨hout z hn, hk, hn⟩)
      simp only [hp, Complex.zero_re, mul_zero, ite_self]
    · simp only [hk, ite_eq_right, not_false_eq_true]
  have hpt : ∀ z ∈ E, f z ≤ QuadraticInitialBound.diagonalControl Φ*r z := by
    intro z hz
    obtain ⟨_, hk, _⟩ := Finset.mem_filter.mp hz
    dsimp only [f]
    rw [ite_eq_left hk, mul_comm (r z)]
    exact mul_le_mul_of_nonneg_right (profile_re_le_diag Φ _) (sq_nonneg _)
  have hsum : ∑ z ∈ E, r z ≤ (Fintype.card κ:ℝ)*G := by
    rw [← Finset.sum_fiberwise E cls r]
    calc
      _ ≤ ∑ _c : κ, G := by
        apply Finset.sum_le_sum
        intro c _
        apply hclass c
        intro z hz
        obtain ⟨hzE, hc⟩ := Finset.mem_filter.mp hz
        obtain ⟨_, hk, hp⟩ := Finset.mem_filter.mp hzE
        exact ⟨hk, hp, hc⟩
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [he]
  calc
    _ ≤ ∑ z ∈ E, QuadraticInitialBound.diagonalControl Φ*r z := Finset.sum_le_sum hpt
    _ = QuadraticInitialBound.diagonalControl Φ*∑ z ∈ E, r z := (Finset.mul_sum _ _ _).symm
    _ ≤ QuadraticInitialBound.diagonalControl Φ*((Fintype.card κ:ℝ)*G) :=
      mul_le_mul_of_nonneg_left hsum (QuadraticInitialBound.diagonalControl_nonneg Φ)
    _ = _ := by ring

/-- A finite amplitude grid can be chosen after the slot type, with an
arbitrarily small **absolute** exponent budget, even as widths tend to zero. -/
theorem exists_amplitude_grid (N : ℕ) {budget : ℝ} (hb : 0 < budget) :
    ∃ n : ℕ, 0 < n ∧ ∃ step : ℝ, 0 < step ∧
      (1001/2000:ℝ)+(n:ℝ)*step=3/4 ∧ step*N ≤ budget := by
  obtain ⟨n, hn⟩ := exists_nat_gt (((499/2000:ℝ)*(N+1))/budget)
  have hn0 : 0 < n := by
    have : (0:ℝ) < ((499/2000:ℝ)*(N+1))/budget := by positivity
    exact_mod_cast this.trans hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
  refine ⟨n, hn0, (499/2000:ℝ)/n, div_pos (by norm_num) hnpos, ?_, ?_⟩
  · rw [mul_div_cancel₀ _ hnpos.ne']
    norm_num
  · have hh := (div_lt_iff₀ hb).mp hn
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hnpos).2
    nlinarith

end
end Qrh.JointDetector.RefinedSupplier

#print axioms Qrh.JointDetector.RefinedSupplier.jointRate_energy
#print axioms Qrh.JointDetector.RefinedSupplier.finite_joint_bin_energy
#print axioms Qrh.JointDetector.RefinedSupplier.actual_high_row_bounds
#print axioms Qrh.JointDetector.RefinedSupplier.energy_le_class_sums
#print axioms Qrh.JointDetector.RefinedSupplier.exists_amplitude_grid
