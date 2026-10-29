/- Copyright (c) 2026 Joseph Bebel. -/
/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
The unmarked HIGH adapter retains Sil's literal natural-row/dictionary proof;
the joint histogram preserves both actual pointwise estimates. -/
import Candidate.Local.Qrh.JointDetector.AdaptiveSupplier.Unmarked
import Candidate.Local.Qrh.JointDetector.RefinedSupplier
import Candidate.Local.Qrh.JointDetector.AdaptivePrice

namespace Qrh.JointDetector.AdaptiveSupplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Density
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentRetainedProfile
open LocalMoment HeckeDetectorZeros ProbePhysical ActualEisensteinCubic
open RefinedSupplier
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

section Count
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

theorem high_row_count {κ : Type} [Fintype κ] (anchors : κ → Character) (η₀ : Character)
    (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {Z bΦ : ℝ}, 0 < bΦ → ∀ (j : κ) (st : NaturalState Z 0 bΦ),
      st.character = anchors j → st.puncture = 1 →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
        (b T' : ℝ), 79/100 ≤ b → b ≤ 7/8 → 0 ≤ T' →
      ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
        b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T') →
      (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(unmarkedDensity (2*b-1)+loss) := by
  obtain ⟨J, C, hC, hcount⟩ := Unmarked.fixed_natural_dictionary_raw_density
    (orientedFixedBase (highDictionary rayM H hH anchors η₀)) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro Z bΦ hbΦ j st hchar hu hQM hQη b T' hb hb' hT' rows hrows
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hcard : rows'.card = rows.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro z hz
    obtain ⟨hk, _⟩ := hrows z hz
    exact st.row_ne_zero z hk
  have hZ0 : 0 < Z := zero_lt_one.trans_le st.base_ge_one
  have hH0 : 0 < bΦ*Z^st.rowWidth := mul_pos hbΦ (Real.rpow_pos_of_pos hZ0 _)
  rw [← hcard]
  apply hcount Prod.snd b T' hb hb' hT' _ hH0 rows'
  intro u hu'
  have hz : u.val ∈ rows := Finset.mem_subtype.mp hu'
  obtain ⟨hk, hp, hmax⟩ := hrows u.val hz
  refine ⟨?_, ?_⟩
  · -- the frequency norm
    have hs := st.radial_support hp
    have h1 : ‖eisEmbedding u.val‖^2 ≤ bΦ*st.radial.scale :=
      (div_le_iff₀ st.radial.scale_pos).mp hs
    rw [st.scale_eq, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at h1
    exact h1
  · -- the zero transfer to the fixed dictionary
    have hc0 : ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) I =
        idealCoeff (excluded (naturalRow (anchors j) u.val u.property).character 1) I := by
      intro I
      rw [hu, excluded_ideal _ _ one_ne_zero, excluded_ideal _ _ one_ne_zero,
        NaturalRow.ideal, NaturalRow.ideal, hchar]
    exact physical_family_maximum_to_fixed_dictionary (highDictionary rayM H hH anchors η₀)
      (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ u.val hk) (fun _ => false)
      (Cycle61InitialMass.geometry_row_family_nonprincipal rayM H hH st η₀ hQM hQη u.val hk)
      (fun idx => (j, idx)) (fun _ => 1) u
      (fun idx I => whole_source_family_mask rayM H hH η₀ (anchors j)
        (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) u.val u.property (naturalRow (anchors j) u.val u.property) 1
        one_ne_zero hc0
        (fun idx => naturalRow (wholeSourceBase rayM H hH η₀ (anchors j) idx) u.val
          u.property) idx I)
      b T' (by linarith) hmax


theorem high_row_count_on (νMin : ℝ) (hmin : (57/100:ℝ) ≤ νMin) {κ : Type} [Fintype κ] (anchors : κ → Character) (η₀ : Character)
    (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {Z bΦ : ℝ}, 0 < bΦ → ∀ (j : κ) (st : NaturalState Z 0 bΦ),
      st.character = anchors j → st.puncture = 1 →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
        (b T' : ℝ), (1+νMin)/2 ≤ b → b ≤ 7/8 → 0 ≤ T' →
      ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
        b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T') →
      (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(unmarkedDensity (2*b-1)+loss) := by
  obtain ⟨J, C, hC, hcount⟩ := Unmarked.fixed_natural_dictionary_raw_density_floor785
    (orientedFixedBase (highDictionary rayM H hH anchors η₀)) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro Z bΦ hbΦ j st hchar hu hQM hQη b T' hb hb' hT' rows hrows
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hcard : rows'.card = rows.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    intro z hz
    obtain ⟨hk, _⟩ := hrows z hz
    exact st.row_ne_zero z hk
  have hZ0 : 0 < Z := zero_lt_one.trans_le st.base_ge_one
  have hH0 : 0 < bΦ*Z^st.rowWidth := mul_pos hbΦ (Real.rpow_pos_of_pos hZ0 _)
  rw [← hcard]
  apply hcount Prod.snd b T' (by linarith) hb' hT' _ hH0 rows'
  intro u hu'
  have hz : u.val ∈ rows := Finset.mem_subtype.mp hu'
  obtain ⟨hk, hp, hmax⟩ := hrows u.val hz
  refine ⟨?_, ?_⟩
  · -- the frequency norm
    have hs := st.radial_support hp
    have h1 : ‖eisEmbedding u.val‖^2 ≤ bΦ*st.radial.scale :=
      (div_le_iff₀ st.radial.scale_pos).mp hs
    rw [st.scale_eq, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at h1
    exact h1
  · -- the zero transfer to the fixed dictionary
    have hc0 : ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) I =
        idealCoeff (excluded (naturalRow (anchors j) u.val u.property).character 1) I := by
      intro I
      rw [hu, excluded_ideal _ _ one_ne_zero, excluded_ideal _ _ one_ne_zero,
        NaturalRow.ideal, NaturalRow.ideal, hchar]
    exact physical_family_maximum_to_fixed_dictionary (highDictionary rayM H hH anchors η₀)
      (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ u.val hk) (fun _ => false)
      (Cycle61InitialMass.geometry_row_family_nonprincipal rayM H hH st η₀ hQM hQη u.val hk)
      (fun idx => (j, idx)) (fun _ => 1) u
      (fun idx I => whole_source_family_mask rayM H hH η₀ (anchors j)
        (excluded (naturalRow st.character u.val (st.row_ne_zero u.val hk)).character
          st.puncture) u.val u.property (naturalRow (anchors j) u.val u.property) 1
        one_ne_zero hc0
        (fun idx => naturalRow (wholeSourceBase rayM H hH η₀ (anchors j) idx) u.val
          u.property) idx I)
      b T' (by linarith) hmax

end Count

theorem finite_joint_bin_energy (policy : AdaptivePrice.Policy) {q : ℝ} {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    {Z bΦ : ℝ} (st : NaturalState Z 0 bΦ) (η₀ : Character)
    (W : ℝ → ℂ) (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ)
    (t : ℝ) (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (E : Finset O)
    (ν Pl s M F C err loss step : ℝ) (n : ℕ)
    (hZ : 1 ≤ Z) (hq : q ∈ Icc policy.floor (3/4)) (hν : ν ∈ Icc q (3/4)) (hM : 0 ≤ M) (hs : 0 ≤ s)
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
    (hzero : (E.card:ℝ) ≤ C*Z^((1-AdaptivePrice.k ν)*M+loss))
    (hjoint : ∀ δ ∈ Icc (1001/2000:ℝ) (3/4), ∀ rows : Finset O,
      rows ⊆ E → (∀ z ∈ rows, Z^(δ*s) ≤ slotMass rayM H hH st η₀ W θ w σ v t z) →
      (rows.card:ℝ) ≤ C*Z^(AdaptivePrice.jointRate ν δ*M+loss)) :
    (∑ z ∈ E, ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I)
        (fun k => Z^(w k)) t X₁ X₂‖^2) ≤
      (n+1:ℕ)*F*C*Z^(M+AdaptivePrice.supWith (policy.gain q) q Pl s M+err+loss+step*s) := by
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
  let rate : Fin (n+1) → ℝ := fun i => if i.val=0 then 1-AdaptivePrice.k ν else AdaptivePrice.jointRate ν (δ i)
  let slope : Fin (n+1) → ℝ := fun i => if i.val=0 then 1001/2000 else min (δ i) ν
  have hδ : ∀ i, δ i ∈ Icc (1001/2000:ℝ) (3/4) := by
    intro i
    have hi : (i.val:ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    dsimp [δ]
    constructor <;> nlinarith
  have hpaid : ∀ i, rate i*M+ν*Pl+slope i*s ≤ M+AdaptivePrice.supWith (policy.gain q) q Pl s M := by
    intro i
    by_cases hi : i.val=0
    · simp only [rate, slope, ite_eq_left hi]
      exact AdaptivePrice.policy_zero_energy policy hq hν (by norm_num [AdaptivePrice.amplitudeCutoff]) hs
    · simp only [rate, slope, ite_eq_right hi]
      exact AdaptivePrice.policy_jointRate_energy policy hq hν (hδ i) hM hs
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
    _ ≤ ∑ i : Fin (n+1), C*F*Z^(M+AdaptivePrice.supWith (policy.gain q) q Pl s M+err+loss+step*s) := by
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

end
end Qrh.JointDetector.AdaptiveSupplier

#print axioms Qrh.JointDetector.AdaptiveSupplier.high_row_count
#print axioms Qrh.JointDetector.AdaptiveSupplier.finite_joint_bin_energy

#print axioms Qrh.JointDetector.AdaptiveSupplier.high_row_count_on
