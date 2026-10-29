/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed selected cutoff .500000001, same original-row event and full amplitude supremum.
Inherited notices follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
The unmarked HIGH adapter retains Sil's literal natural-row/dictionary proof;
the joint histogram preserves both actual pointwise estimates. -/
import Candidate.Local.Qrh.JointDetector.WeightedSupplier
import Candidate.Local.Qrh.JointDetector.FrontierRate
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateContinuity
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.UnmarkedHigh
import Candidate.Local.Qrh.JointDetector.FrontierNaturalCount
import Candidate.Local.Qrh.JointDetector.AdaptiveSourceChains.Common

namespace Qrh.JointDetector.FrontierRepeatedWeightedHigh
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


def WholeRepeatedCountOn (νMin B L c : ℝ) : Prop :=
  ∀ Mmin Mcap smin loss dmin : ℝ, 0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss → 0 < dmin →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50 : ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (b δ T' : ℝ), (1+νMin)/2 ≤ b → b ≤ 7/8 →
    δ ∈ Icc dmin (2*b-1) → 0 ≤ T' → |t|+height ≤ T' →
  ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
    st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
    b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T' ∧
    Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t z) →
    (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(RepeatedMarks.rawRepeatedCountRate B L c (2*b-1) δ+loss)

def WholeClippedCountOn (νMin B L c : ℝ) : Prop :=
  ∀ Mmin Mcap smin loss dmin : ℝ, 0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss → 0 < dmin → dmin ≤ νMin →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50 : ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (b δ T' : ℝ), (1+νMin)/2 ≤ b → b ≤ 7/8 →
    δ ∈ Icc dmin (3/4:ℝ) → 0 ≤ T' → |t|+height ≤ T' →
  ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
    st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
    b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T' ∧
    Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t z) →
    (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(RepeatedMarks.rawRepeatedCountRate B L c (2*b-1) (min δ (2*b-1))+loss)

def WholeCombinedCountOn (νMin B L c : ℝ) : Prop :=
  ∀ Mmin Mcap smin loss dmin : ℝ, 0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss → 0 < dmin → dmin ≤ νMin →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50 : ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (b δ T' : ℝ), (1+νMin)/2 ≤ b → b ≤ 7/8 →
    δ ∈ Icc dmin (3/4:ℝ) → 0 ≤ T' → |t|+height ≤ T' →
  ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
    st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
    b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T' ∧
    Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t z) →
    (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(FrontierRepeatedMarks.combineSelected (RepeatedMarks.rawRepeatedCountRate B L c) (2*b-1) (min δ (2*b-1))+loss)

/-- The first class includes amplitudes below the positive counting cutoff.
Its mass is never assumed to be at least one. -/
def amplitudeBinAt (low : ℝ) (n : ℕ) (step Z s response : ℝ) : Fin (n+1) :=
  ⟨Nat.findGreatest (fun i => Z^((low+(i:ℝ)*step)*s) ≤ response) n,
    Nat.lt_succ_of_le (Nat.findGreatest_le n)⟩

theorem amplitudeBinAt_lower {low : ℝ} {n : ℕ} {step Z s response : ℝ}
    (h : (amplitudeBinAt low n step Z s response).val ≠ 0) :
    Z^((low+((amplitudeBinAt low n step Z s response).val:ℝ)*step)*s) ≤ response := by
  exact Nat.findGreatest_of_ne_zero rfl h

theorem amplitudeBinAt_upper {low : ℝ} {n : ℕ} {step Z s response : ℝ}
    (h : (amplitudeBinAt low n step Z s response).val < n) :
    response < Z^((low+((amplitudeBinAt low n step Z s response).val+1:ℕ)*step)*s) := by
  apply lt_of_not_ge
  exact Nat.findGreatest_is_greatest (P := fun i => Z^((low+(i:ℝ)*step)*s) ≤ response)
    (Nat.lt_succ_self _) (by simpa only [amplitudeBinAt] using Nat.succ_le_iff.mpr h)

theorem supplier_finite_energy (floor : ℝ) (high : ℝ → ℝ → ℝ → ℝ → ℝ) (rateFn : ℝ → ℝ → ℝ) (zeroRate low : ℝ) {q : ℝ} {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    {Z bΦ : ℝ} (st : NaturalState Z 0 bΦ) (η₀ : Character)
    (W : ℝ → ℂ) (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ)
    (t : ℝ) (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (E : Finset O)
    (ν Pl s M F C err loss step : ℝ) (n : ℕ)
    (hZ : 1 ≤ Z) (hq : q ∈ Icc floor (3/4)) (hν : ν ∈ Icc q (3/4)) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hF : 0 ≤ F) (hC : 0 ≤ C) (hstep : 0 < step) (hn : 0 < n)
    (htop : (low:ℝ)+(n:ℝ)*step = 3/4)
    (hpayZero : zeroRate*M+ν*Pl+low*s ≤ M+high q Pl s M)
    (hpay : ∀ δ ∈ Icc low (3/4:ℝ),
      rateFn ν δ*M+ν*Pl+min δ ν*s ≤ M+high q Pl s M)
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
    (hzero : (E.card:ℝ) ≤ C*Z^(zeroRate*M+loss))
    (hjoint : ∀ δ ∈ Icc low (3/4), ∀ rows : Finset O,
      rows ⊆ E → (∀ z ∈ rows, Z^(δ*s) ≤ slotMass rayM H hH st η₀ W θ w σ v t z) →
      (rows.card:ℝ) ≤ C*Z^(rateFn ν δ*M+loss)) :
    (∑ z ∈ E, ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I)
        (fun k => Z^(w k)) t X₁ X₂‖^2) ≤
      (n+1:ℕ)*F*C*Z^(M+high q Pl s M+err+loss+step*s) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let mass : O → ℝ := slotMass rayM H hH st η₀ W θ w σ v t
  let row : O → ℝ := fun z =>
    ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v k) I)
        (fun k => Z^(w k)) t X₁ X₂‖^2
  let cls : O → Fin (n+1) := fun z => amplitudeBinAt low n step Z s (mass z)
  let δ : Fin (n+1) → ℝ := fun i => low+(i.val:ℝ)*step
  let rate : Fin (n+1) → ℝ := fun i => if i.val=0 then zeroRate else rateFn ν (δ i)
  let slope : Fin (n+1) → ℝ := fun i => if i.val=0 then low else min (δ i) ν
  have hδ : ∀ i, δ i ∈ Icc (low:ℝ) (3/4) := by
    intro i
    have hi : (i.val:ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    dsimp [δ]
    constructor <;> nlinarith
  have hpaid : ∀ i, rate i*M+ν*Pl+slope i*s ≤ M+high q Pl s M := by
    intro i
    by_cases hi : i.val=0
    · simp only [rate, slope, ite_eq_left hi]
      exact hpayZero
    · simp only [rate, slope, ite_eq_right hi]
      exact hpay _ (hδ i)
  have hcount : ∀ i, ((E.filter (fun z => cls z=i)).card:ℝ) ≤ C*Z^(rate i*M+loss) := by
    intro i
    by_cases hi : i.val=0
    · simpa only [rate, ite_eq_left hi] using
        (Nat.cast_le.mpr (Finset.card_filter_le E (fun z => cls z=i))).trans hzero
    · simp only [rate, ite_eq_right hi]
      apply hjoint (δ i) (hδ i) _ (Finset.filter_subset _ _)
      intro z hz
      have he : cls z=i := (Finset.mem_filter.mp hz).2
      have hb := amplitudeBinAt_lower (n:=n) (step:=step) (Z:=Z) (s:=s) (response:=mass z)
        (show (cls z).val ≠ 0 by rw [he]; exact hi)
      simpa only [← he, δ, cls] using hb
  have hrow : ∀ i, ∀ z ∈ E.filter (fun z => cls z=i),
      row z ≤ F*Z^(ν*Pl+slope i*s+err+step*s) := by
    intro i z hz
    obtain ⟨hzE, he⟩ := Finset.mem_filter.mp hz
    have hall := hfull z hzE
    by_cases hi : i.val=0
    · have hbin : (cls z).val < n := by rw [he, hi]; exact hn
      have hb := (amplitudeBinAt_upper (n:=n) (step:=step) (Z:=Z) (s:=s)
        (response:=mass z) hbin).le
      have hb' : mass z ≤ Z^((low+step)*s) := by
        change mass z ≤ Z^((low+((cls z).val+1:ℕ)*step)*s) at hb
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
        have hb := (amplitudeBinAt_upper (n:=n) (step:=step) (Z:=Z) (s:=s)
          (response:=mass z) (show (cls z).val<n by rw [he]; exact hnotTop)).le
        have hb' : mass z ≤ Z^((δ i+step)*s) := by
          change mass z ≤ Z^((low+((cls z).val+1:ℕ)*step)*s) at hb
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
    _ ≤ ∑ i : Fin (n+1), C*F*Z^(M+high q Pl s M+err+loss+step*s) := by
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


theorem normalize_actual_count {Z bΦ M Mcap ρ loss Cd Csum τ t height : ℝ}
    {J₀ J B c h : ℕ} {card : ℝ}
    (hCd : 0 ≤ Cd) (hCC : Cd ≤ Csum) (hbΦ : 1 ≤ bΦ) (hZ : 1 < Z)
    (hM : M ≤ Mcap) (hρ : ρ ≤ 1) (hl : 0 ≤ loss) (hl1 : loss ≤ 1)
    (hJ : J₀ ≤ J) (hc : c ≤ B) (hh : (h:ℝ) ≤ |t|+height+1)
    (hh0 : 0 ≤ height) (hy : 1 ≤ Z^τ)
    (hcount : card ≤ Cd*(1+((3*c:ℕ):ℝ)*(((h+1:ℕ):ℝ)*Z^τ))^J₀*
      (bΦ*Z^M)^(ρ+loss)) :
    card ≤ (Csum*bΦ^2*(1+6*(B:ℝ))^J*(1+|t|+height)^J*Z^(τ*J))*
      Z^(ρ*M+loss*Mcap) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hCs : 0 ≤ Csum := hCd.trans hCC
  have hb0 : 0 ≤ bΦ := zero_le_one.trans hbΦ
  have hbase : 1 ≤ 1+((3*c:ℕ):ℝ)*(((h+1:ℕ):ℝ)*Z^τ) := by
    have : 0 ≤ ((3*c:ℕ):ℝ)*(((h+1:ℕ):ℝ)*Z^τ) := by positivity
    linarith
  have hH := (pow_le_pow_right₀ hbase hJ).trans
    (height_count_le J hc (show 0 ≤ |t|+height by positivity) hh hy)
  have hpow : (Z^τ)^J=Z^(τ*J) := by rw [← Real.rpow_natCast,← Real.rpow_mul hZ0.le]
  rw [hpow] at hH
  have hD := density_power_le hbΦ hZ.le hM hρ hl hl1
  have hcH : Cd*(1+((3*c:ℕ):ℝ)*(((h+1:ℕ):ℝ)*Z^τ))^J₀ ≤
      Csum*((1+6*(B:ℝ))^J*(1+(|t|+height))^J*Z^(τ*J)) :=
    mul_le_mul hCC hH (by positivity) (hCd.trans hCC)
  refine hcount.trans ((mul_le_mul hcH hD (by positivity) (by positivity)).trans_eq ?_)
  rw [show M*ρ+Mcap*loss=ρ*M+loss*Mcap by ring]
  simp only [← add_assoc]
  ring

/-- Grid precision may depend on the later finite slot count, while its
positive lower endpoint is fixed by the early count contract. -/
theorem exists_amplitude_grid_at (N : ℕ) {low budget : ℝ}
    (hlow : low < (3/4:ℝ)) (hb : 0 < budget) :
    ∃ n : ℕ, 0 < n ∧ ∃ step : ℝ, 0 < step ∧
      low+(n:ℝ)*step=3/4 ∧ step*N ≤ budget := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((((3/4:ℝ)-low)*(N+1))/budget)
  have hn0 : 0 < n := by
    have : (0:ℝ) < (((3/4:ℝ)-low)*(N+1))/budget := by positivity
    exact_mod_cast this.trans hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
  refine ⟨n,hn0,((3/4:ℝ)-low)/n,div_pos (by linarith) hnpos,?_,?_⟩
  · rw [mul_div_cancel₀ _ hnpos.ne']
    ring
  · have hh := (div_lt_iff₀ hb).mp hn
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hnpos).2
    nlinarith

/-- Every same-event density/amplitude count is paid before the amplitude
supremum. The rate may already be the minimum of two arithmetic counts. -/
theorem family_payment (q : ℝ) (hq : q ∈ Ioc (0:ℝ) (3/4))
    (rate : ℝ → ℝ → ℝ)
    (hrate : ∀ ν ∈ Icc q (3/4:ℝ), ∀ v ∈ Icc (0:ℝ) ν,
      rate ν v ∈ Icc (0:ℝ) 1)
    {ν v P s M : ℝ} (hν : ν ∈ Icc q (3/4:ℝ)) (hv : v ∈ Icc (0:ℝ) ν) :
    rate ν v*M+ν*P+v*s ≤
      M+(FrontierRepeatedMarks.familyOfRate q hq rate hrate).high P s M := by
  let i : FrontierRepeatedMarks.DensityAmplitude q := ⟨(ν,v),hν.1,hν.2,hv.1,hv.2⟩
  have hi := (FrontierRepeatedMarks.familyOfRate q hq rate hrate).term_le i P s M
  change ν*P+(rate ν v-1)*M+v*s ≤ _ at hi
  linarith

theorem repeated_payment (B L c q : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 1)
    (hL : (3/2:ℝ) ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ 1/6)
    (hq : q ∈ Ioc (0:ℝ) (3/4)) (combined : Bool)
    {ν amp P s M : ℝ} (hν : ν ∈ Icc q (3/4:ℝ)) (ha : amp ∈ Icc (0:ℝ) ν) :
    (if combined then FrontierRepeatedMarks.combineSelected
      (RepeatedMarks.rawRepeatedCountRate B L c) ν amp
      else RepeatedMarks.rawRepeatedCountRate B L c ν amp)*M+ν*P+amp*s ≤
      M+(FrontierRepeatedMarks.repeatedFamily B L c q hB0 hB hL hc0 hc hq combined).high P s M := by
  let i : FrontierRepeatedMarks.DensityAmplitude q := ⟨(ν,amp),hν.1,hν.2,ha.1,ha.2⟩
  have hi := (FrontierRepeatedMarks.repeatedFamily B L c q hB0 hB hL hc0 hc hq combined).term_le i P s M
  change ν*P+((if combined then FrontierRepeatedMarks.combineSelected
    (RepeatedMarks.rawRepeatedCountRate B L c) ν amp
    else RepeatedMarks.rawRepeatedCountRate B L c ν amp)-1)*M+amp*s ≤ _ at hi
  linarith

theorem amplitude_event_clipping {Z s δ ν mass : ℝ} (hZ : 1 ≤ Z) (hs : 0 ≤ s)
    (h : Z^(δ*s) ≤ mass) : Z^((min δ ν)*s) ≤ mass :=
  (Real.rpow_le_rpow_of_exponent_le hZ
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hs)).trans h

theorem wholeClippedCountOn_of_repeated (floor B L c : ℝ)
    (hrep : WholeRepeatedCountOn floor B L c) : WholeClippedCountOn floor B L c := by
  intro Mmin Mcap smin loss dmin hMmin hMcap hsmin hloss hdmin hdminFloor
  obtain ⟨meshMax,hm,hcount⟩ := hrep Mmin Mcap smin loss dmin hMmin hMcap hsmin hloss hdmin
  refine ⟨meshMax,hm,?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  obtain ⟨J,C,hC,hall⟩ := hcount mesh hmesh α rayM H hH W hW hWs κ anchors η₀ bΦ hbΦ
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hall] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro j st hj hp hM hw hQM hQη T θ w σ v t height hw0 hwm hσ0 hσ1 hh hv hs
    b δ T' hb hb1 hδ hT hheight rows hrows
  have hν : dmin ≤ 2*b-1 := by linarith
  apply hZ.2 j st hj hp hM hw hQM hQη T θ w σ v t height hw0 hwm hσ0 hσ1 hh hv hs
    b (min δ (2*b-1)) T' hb hb1 ⟨le_min hδ.1 hν,min_le_right _ _⟩ hT hheight rows
  intro z hz
  obtain ⟨hk,hprofile,hzero,hamp⟩ := hrows z hz
  refine ⟨hk,hprofile,hzero,?_⟩
  exact amplitude_event_clipping hZ.1.le (Finset.sum_nonneg (fun k _ => hw0 k)) hamp

/-- Taking the better of counts for the same literal event happens
before any sum over amplitude classes. -/
theorem same_event_minimum {Z M C loss r₁ r₂ cardinal : ℝ}
    (h₁ : cardinal ≤ C*Z^(r₁*M+loss))
    (h₂ : cardinal ≤ C*Z^(r₂*M+loss)) :
    cardinal ≤ C*Z^((min r₁ r₂)*M+loss) := by
  rcases le_total r₁ r₂ with h|h
  · simpa only [min_eq_left h] using h₁
  · simpa only [min_eq_right h] using h₂

/-- Low-amplitude and selected suppliers count one event; this theorem
never replaces an event by a selected coefficient marginal. -/
theorem combined_event_count {Z M C loss cardinal ν amp raw : ℝ}
    (hrep : cardinal ≤ C*Z^(raw*M+loss))
    (hsel : (500000001/1000000000:ℝ) ≤ amp →
      cardinal ≤ C*Z^(detectorRate ν amp*M+loss)) :
    cardinal ≤ C*Z^((FrontierRepeatedMarks.combineSelected (fun _ _ => raw) ν amp)*M+loss) := by
  unfold FrontierRepeatedMarks.combineSelected
  split_ifs with h
  · exact same_event_minimum hrep (hsel h)
  · exact hrep

/-- Choosing the positive histogram cutoff before the finite slot type.
The omitted zero-amplitude interval is paid by continuity in count rate,
not by falsely imposing a lower response on its rows. -/
theorem exists_early_amplitude_cutoff {B L c floor loss : ℝ}
    (hL : (3/2:ℝ) ≤ L) (hfloor : 0 < floor) (hloss : 0 < loss) :
    ∃ low : ℝ, 0 < low ∧ low < floor ∧ low < (500000001/1000000000:ℝ) ∧
      ∀ ν ∈ Icc floor (3/4:ℝ),
        RepeatedMarks.rawRepeatedCountRate B L c ν 0 ≤
          RepeatedMarks.rawRepeatedCountRate B L c ν low+loss/4 := by
  obtain ⟨η,hη,hbuffer⟩ := RepeatedMarks.rawRate_buffer
    (B:=B) (c:=c) hL hfloor (show 0 < loss/4 by positivity)
  let low := min (η/2) (min (floor/2) (500000001/2000000000:ℝ))
  have hlo : 0 < low := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hlf : low < floor := (min_le_right _ _).trans_lt
    ((min_le_left _ _).trans_lt (by linarith))
  have hlcut : low < (500000001/1000000000:ℝ) :=
    (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  refine ⟨low,hlo,hlf,hlcut,?_⟩
  intro ν hν
  have hνp : 0 < ν := hfloor.trans_le hν.1
  have hb := hbuffer ν 0 ν low
    ⟨hν.1,hν.2,le_rfl,hνp.le⟩
    ⟨hν.1,hν.2,hlo.le,hlf.le.trans hν.1⟩
    (by simpa using hη)
    (by rw [zero_sub,abs_neg,abs_of_pos hlo]; exact
      (min_le_left _ _).trans_lt (by linarith))
  linarith [le_abs_self (RepeatedMarks.rawRepeatedCountRate B L c ν 0-
    RepeatedMarks.rawRepeatedCountRate B L c ν low)]


private theorem count_factor_mono {C D T X r : ℝ} {J K : ℕ}
    (hC : 0 ≤ C) (hCD : C ≤ D) (hT : 0 ≤ T) (hX : 0 ≤ X) (hJ : J ≤ K) :
    C*(1+T)^J*X^r ≤ D*(1+T)^K*X^r := by
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX _)
  exact mul_le_mul hCD (pow_le_pow_right₀ (by linarith) hJ)
    (by positivity) (hC.trans hCD)

/-- Uniform same-event combination before choosing live height scales. -/
theorem wholeCombinedCountOn_of_repeated_selected (floor B L c : ℝ)
    (hrep : WholeRepeatedCountOn floor B L c)
    (hsel : FrontierSelectedCount.WholeSelectedCountOn floor) :
    WholeCombinedCountOn floor B L c := by
  intro Mmin Mcap smin loss dmin hMmin hMcap hsmin hloss hdmin hdminFloor
  obtain ⟨meshR,hmR,hR⟩ := wholeClippedCountOn_of_repeated floor B L c hrep
    Mmin Mcap smin loss dmin hMmin hMcap hsmin hloss hdmin hdminFloor
  obtain ⟨meshS,hmS,hS⟩ := hsel Mmin Mcap smin loss hMmin hMcap hsmin hloss
  refine ⟨min meshR meshS,lt_min hmR hmS,?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  obtain ⟨Jr,Cr,hCr,hr⟩ := hR mesh (hmesh.trans (min_le_left _ _))
    α rayM H hH W hW hWs κ anchors η₀ bΦ hbΦ
  obtain ⟨Js,Cs,hCs,hs⟩ := hS mesh (hmesh.trans (min_le_right _ _))
    α rayM H hH W hW hWs κ anchors η₀ bΦ hbΦ
  refine ⟨Jr+Js,Cr+Cs,by positivity,?_⟩
  filter_upwards [hr,hs] with Z hZr hZs
  refine ⟨hZr.1,?_⟩
  intro j st hj hp hM hw hQM hQη T θ w σ v t height hw0 hwm hσ0 hσ1 hh hv hsmin'
    b δ T' hb hb1 hδ hT hheight rows hrows
  have hrepeated := hZr.2 j st hj hp hM hw hQM hQη T θ w σ v t height
    hw0 hwm hσ0 hσ1 hh hv hsmin' b δ T' hb hb1 hδ hT hheight rows hrows
  have hZpos : 0 < Z := zero_lt_one.trans hZr.1
  have hbΦpos : 0 < bΦ := zero_lt_one.trans_le hbΦ
  have hr' := hrepeated.trans (count_factor_mono hCr.le
    (show Cr ≤ Cr+Cs by linarith) hT (by positivity) (show Jr ≤ Jr+Js by omega))
  unfold FrontierRepeatedMarks.combineSelected
  split_ifs with hcut
  swap
  · exact hr'
  have hνhi : 2*b-1 ≤ (3/4:ℝ) := by linarith
  have hamp : min δ (2*b-1) ∈ Icc (500000001/1000000000:ℝ) (3/4) :=
    ⟨hcut,(min_le_right _ _).trans hνhi⟩
  have hselected := hZs.2 j st hj hp hM hw hQM hQη T θ w σ v t height
    hw0 hwm hσ0 hσ1 hh hv hsmin' b (min δ (2*b-1)) T' hb hb1 hamp hT rows (by
      intro z hz
      obtain ⟨hk,hp',hz',ha⟩ := hrows z hz
      exact ⟨hk,hp',hz',amplitude_event_clipping hZr.1.le
        (Finset.sum_nonneg (fun k _ => hw0 k)) ha⟩)
  have hs' := hselected.trans (count_factor_mono hCs.le
    (show Cs ≤ Cr+Cs by linarith) hT (by positivity) (show Js ≤ Jr+Js by omega))
  rcases le_total (RepeatedMarks.rawRepeatedCountRate B L c (2*b-1) (min δ (2*b-1)))
      (detectorRate (2*b-1) (min δ (2*b-1))) with h|h
  · simpa only [min_eq_left h] using hr'
  · simpa only [min_eq_right h] using hs'

/-- Whole-amplitude payment, including the genuinely uncounted bottom
class. The gap is fixed before the slot type and pays only a count-rate
continuity error times the natural row width. -/
theorem exists_repeated_payment (B L c floor gap : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ 1) (hL : (3/2:ℝ) ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (hf : 0 < floor) (hg : 0 < gap)
    (combined : Bool) :
    ∃ low : ℝ, 0 < low ∧ low < floor ∧ low < (500000001/1000000000:ℝ) ∧
    ∀ q (hq : q ∈ Ioc (0:ℝ) (3/4)), floor ≤ q →
    ∀ ν ∈ Icc q (3/4:ℝ), ∀ P s M : ℝ, 0 ≤ s → 0 ≤ M →
      let F := FrontierRepeatedMarks.repeatedFamily B L c q hB0 hB hL hc0 hc hq combined
      (RepeatedMarks.unmarkedCountRate ν*M+ν*P+low*s ≤ M+F.high P s M+gap*M) ∧
      (∀ δ ∈ Icc low (3/4:ℝ),
        (if combined then FrontierRepeatedMarks.combineSelected
          (RepeatedMarks.rawRepeatedCountRate B L c) ν (min δ ν)
        else RepeatedMarks.rawRepeatedCountRate B L c ν (min δ ν))*M+
          ν*P+min δ ν*s ≤ M+F.high P s M) ∧
      (RepeatedMarks.unmarkedCountRate ν*M+ν*(P+s) ≤ M+F.high P s M+s) := by
  obtain ⟨low,hlow,hlf,hlcut,hbuffer⟩ := exists_early_amplitude_cutoff
    (B:=B) (c:=c) hL hf (show 0 < 4*gap by positivity)
  refine ⟨low,hlow,hlf,hlcut,?_⟩
  intro q hq hfloor ν hν P s M hs hM
  have hνp : 0 < ν := hq.1.trans_le hν.1
  have hlowν : low ≤ ν := hlf.le.trans (hfloor.trans hν.1)
  have hzero := RepeatedMarks.rawRate_zero_ge_unmarked (B:=B) (L:=L) (c:=c) hνp hν.2
  have hcont := hbuffer ν ⟨hfloor.trans hν.1,hν.2⟩
  have hbottom := repeated_payment B L c q hB0 hB hL hc0 hc hq combined
    hν ⟨hlow.le,hlowν⟩ (P:=P) (s:=s) (M:=M)
  have hnot : ¬(500000001/1000000000:ℝ) ≤ low := not_le_of_gt hlcut
  simp only [FrontierRepeatedMarks.combineSelected,if_neg hnot] at hbottom
  have hbottom' : RepeatedMarks.rawRepeatedCountRate B L c ν low*M+ν*P+low*s ≤
      M+(FrontierRepeatedMarks.repeatedFamily B L c q hB0 hB hL hc0 hc hq combined).high P s M := by
    cases combined <;> simpa using hbottom
  have hρ : RepeatedMarks.unmarkedCountRate ν ≤
      RepeatedMarks.rawRepeatedCountRate B L c ν low+gap := by linarith
  refine ⟨?_,?_,?_⟩
  · have := mul_le_mul_of_nonneg_right hρ hM
    linarith
  · intro δ hδ
    exact repeated_payment B L c q hB0 hB hL hc0 hc hq combined hν
      ⟨le_min (hlow.le.trans hδ.1) hνp.le,min_le_right _ _⟩
  · have hz := repeated_payment B L c q hB0 hB hL hc0 hc hq combined
      hν ⟨le_rfl,hνp.le⟩ (P:=P) (s:=s) (M:=M)
    have hn0 : ¬(500000001/1000000000:ℝ) ≤ 0 := by norm_num
    simp only [FrontierRepeatedMarks.combineSelected,if_neg hn0,zero_mul,add_zero] at hz
    have hz' : RepeatedMarks.rawRepeatedCountRate B L c ν 0*M+ν*P ≤
        M+(FrontierRepeatedMarks.repeatedFamily B L c q hB0 hB hL hc0 hc hq combined).high P s M := by
      cases combined <;> simpa using hz
    have hh := mul_le_mul_of_nonneg_right hzero hM
    have hv := mul_le_mul_of_nonneg_right (show ν ≤ (1:ℝ) by linarith [hν.2]) hs
    linarith

/-- Pure payment laws for a general full-amplitude rate. There is no
separate selected/unweighted maximum, and low is fixed by continuity. -/
structure NaturalPaymentLaw (floor low : ℝ) (rateFn : ℝ → ℝ → ℝ)
    (high : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop where
  floor_ge : (2/5:ℝ) ≤ floor
  low_top : low < (3/4:ℝ)
  zero : ∀ {q ν P s M : ℝ}, q ∈ Icc floor (3/4) → ν ∈ Icc q (3/4) → 0 ≤ s → 0 ≤ M →
    (1-AdaptivePrice.k ν)*M+ν*P+low*s ≤ M+high q P s M
  joint : ∀ {q ν δ P s M : ℝ}, q ∈ Icc floor (3/4) → ν ∈ Icc q (3/4) →
    δ ∈ Icc low (3/4) → 0 ≤ M → 0 ≤ s →
    rateFn ν δ*M+ν*P+min δ ν*s ≤ M+high q P s M
  full : ∀ {q ν P s M : ℝ}, q ∈ Icc floor (3/4) → ν ∈ Icc q (3/4) → 0 ≤ s → 0 ≤ M →
    (1-AdaptivePrice.k ν)*M+ν*(P+s) ≤ M+high q P s M+s
  rate_le_one : ∀ {q ν δ : ℝ}, q ∈ Icc floor (3/4) → ν ∈ Icc q (3/4) →
    δ ∈ Icc low (3/4) → rateFn ν δ ≤ 1

/-- The concrete full-supremum price satisfies the natural energy payment
laws with an arbitrarily small row-width reserve. This is a scalar theorem;
the arithmetic inlet remains the literal repeated count of the same rows. -/
theorem exists_natural_payment_law (B L c floor gap : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ 1) (hL : (3/2:ℝ) ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (hf : (2/5:ℝ) ≤ floor) (hg : 0 < gap)
    (combined : Bool) (high : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hhigh : ∀ q (hq : q ∈ Ioc (0:ℝ) (3/4)), floor ≤ q → ∀ P s M,
      high q P s M=(FrontierRepeatedMarks.repeatedFamily B L c q hB0 hB hL hc0 hc hq combined).high P s M+gap*M) :
    ∃ low : ℝ, 0 < low ∧ low < floor ∧
      NaturalPaymentLaw floor low
        (fun ν δ => if combined then FrontierRepeatedMarks.combineSelected
          (RepeatedMarks.rawRepeatedCountRate B L c) ν (min δ ν)
        else RepeatedMarks.rawRepeatedCountRate B L c ν (min δ ν)) high := by
  have hfp : 0 < floor := by linarith
  obtain ⟨low,hlow,hlf,hlcut,hpay⟩ := exists_repeated_payment B L c floor gap
    hB0 hB hL hc0 hc hfp hg combined
  refine ⟨low,hlow,hlf,⟨hf,?_,?_,?_,?_,?_⟩⟩
  · linarith
  · intro q ν P s M hq hν hs hM
    have hq' : q ∈ Ioc (0:ℝ) (3/4) := ⟨hfp.trans_le hq.1,hq.2⟩
    have hh := (hpay q hq' hq.1 ν hν P s M hs hM).1
    rw [hhigh q hq' hq.1]
    change (1-AdaptivePrice.k ν)*M+ν*P+low*s ≤ _ at hh
    linarith
  · intro q ν δ P s M hq hν hδ hM hs
    have hq' : q ∈ Ioc (0:ℝ) (3/4) := ⟨hfp.trans_le hq.1,hq.2⟩
    have hh := (hpay q hq' hq.1 ν hν P s M hs hM).2.1 δ hδ
    rw [hhigh q hq' hq.1]
    have : 0 ≤ gap*M := mul_nonneg hg.le hM
    linarith
  · intro q ν P s M hq hν hs hM
    have hq' : q ∈ Ioc (0:ℝ) (3/4) := ⟨hfp.trans_le hq.1,hq.2⟩
    have hh := (hpay q hq' hq.1 ν hν P s M hs hM).2.2
    rw [hhigh q hq' hq.1]
    change (1-AdaptivePrice.k ν)*M+ν*(P+s) ≤ _ at hh
    have : 0 ≤ gap*M := mul_nonneg hg.le hM
    linarith
  · intro q ν δ hq hν hδ
    have hn : 0 < ν := (hfp.trans_le hq.1).trans_le hν.1
    have hv : min δ ν ∈ Icc (0:ℝ) ν :=
      ⟨le_min (hlow.le.trans hδ.1) hn.le,min_le_right _ _⟩
    have hb := RepeatedMarks.rawRepeatedCountRate_bounds hB0 hB hL hc0 hc hn hν.2 hv.1 hv.2
    cases combined with
    | false => exact hb.2
    | true =>
      exact (FrontierRepeatedMarks.combineSelected_mem hν.2 hv
        ⟨by linarith [hb.1,hν.2],hb.2⟩).2

def SupplierCountAt (floor low : ℝ) (rateFn : ℝ → ℝ → ℝ) {α κ : Type} [Fintype α] [DecidableEq α] [Fintype κ]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (W : ℝ → ℂ)
    (anchors : κ → Character) (η₀ : Character)
    (Mmin Mcap smin mesh loss bΦ : ℝ) (J : ℕ) (C Z : ℝ) : Prop :=
  1 < Z ∧ ∀ (j : κ) (st : NaturalState Z 0 bΦ),
  st.character=anchors j → st.puncture=1 → Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
  (∀ k,0 ≤ w k) → (∀ k,w k ≤ mesh) →
  (∀ k,(33/50:ℝ) ≤ σ k) → (∀ k,σ k ≤ 33/50) →
  0 ≤ height → (∀ k,|v k| ≤ height) → smin ≤ ∑ k,w k →
  ∀ (b δ T' : ℝ), (1+floor)/2 ≤ b → b ≤ 7/8 →
  δ ∈ Icc low (3/4) → 0 ≤ T' → |t|+height ≤ T' →
  ∀ rows : Finset O, (∀ z ∈ rows,∃ hz : st.radial.keep z,
    st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
    b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T' ∧
    Z^(δ*∑ k,w k) ≤ slotMass rayM H hH st η₀ W θ w σ v t z) →
  (rows.card:ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(rateFn (2*b-1) δ+loss)

section
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Actual large-slot HIGH branch from the explicit whole count. The
counting degree is fixed before the physical height scale τ. -/
theorem supplier_high_branch {α : Type} [Fintype α] [DecidableEq α]
    (floor : ℝ) (high : ℝ → ℝ → ℝ → ℝ → ℝ) (low : ℝ) (rateFn : ℝ → ℝ → ℝ) (hlaw : NaturalPaymentLaw floor low rateFn high)
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ : ℝ) (hbΦ : 1 ≤ bΦ) {κ : Type} [Fintype κ] (anchors : κ → Character)
    (η₀ : Character) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hβ' : HeckeZeroSupremum.beta ≤ 7/8)
    (Mmin Mcap smin mesh Lplain ε₁ e kap v d loss budget : ℝ)
    (hMmin : 0 < Mmin) (hsmin : 0 < smin) (hL : 0 ≤ Lplain) (hε₁ : 0 < ε₁)
    (he : 0 < e) (he' : e < 1/1000) (hkap : 0 < kap) (hkap' : kap ≤ 1)
    (hv : 0 ≤ v) (hd : 0 < d) (hdsupply : Mcap+0+1 ≤ d)
    (hslotBudget : 8*e*(1/d)+kap ≤ ε₁)
    (hplainBudget : 12*e*(Lplain/d+2)+8*kap+2*v ≤ ε₁)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hbudget : 0 < budget)
    (Jc : ℕ) (Cc : ℝ) (hCc : 0 < Cc)
    (hcnt : ∀ᶠ Z : ℝ in atTop,
      SupplierCountAt floor low rateFn (α:=α) rayM H hH W anchors η₀ Mmin Mcap smin mesh loss bΦ Jc Cc Z) :
    ∃ J : ℕ, ∀ τ : ℝ, 0 < τ → ∃ K : ℝ,0 < K ∧ ∃ S : Finset (ℕ×ℕ),
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ 2 < Z^τ ∧
    ∀ (j : κ) (q : ℝ),q ∈ Icc floor (3/4) →
    ∀ st : NaturalState Z 0 bΦ, st.character=anchors j → st.puncture=1 →
      Mmin ≤ st.rowWidth → st.width ≤ Mcap →
    ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus) (h : ℕ)
      (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ) (t height : ℝ),
    (∀ k,0 ≤ w k) → (∀ k,w k ≤ mesh) → (∀ k,w k ≤ 1) →
    (∀ k,(33/50:ℝ) ≤ σ k) → (∀ k,σ k ≤ 33/50) →
    0 ≤ height → (∀ k,|v' k| ≤ height) →
    |t|+height+Z^τ/2 ≤ (3*h+2:ℕ)*Z^τ → (h:ℝ) ≤ |t|+height+1 →
    (3+3*(((bufferCount e+1)*(h+1):ℕ):ℝ)*Z^τ)^4 ≤ (Z^d)^v →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
    length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
    energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun k => primePool rayM H 2 (Z^(w k)))
      (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
      (fun k => Z^(w k)) X₁ X₂
      (fun z => st.radial.keep z ∧ ¬lowRow rayM H hH st η₀ hQM hQη e (((h+1:ℕ):ℝ)*Z^τ) q z)
      st.radial.profile st.radial.scale ≤
    K*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*(1+|t|+height)^J*
      Z^(st.rowWidth+high q (length Z X₁+length Z X₂)
        (∑ k,w k) st.rowWidth+(2*ε₁*d*(Fintype.card α+1)+loss*Mcap+τ*J+budget+smin)) := by
  obtain ⟨Jz,Cz,hCz,hzero⟩ := RepeatedMarks.UnmarkedHigh.high_row_count_on rayM H hH floor hlaw.floor_ge anchors η₀ loss hloss
  let J := Jz+Jc
  obtain ⟨n,hn,step,hstep,htop,hstepN⟩ := exists_amplitude_grid_at (Fintype.card α) hlaw.low_top hbudget
  refine ⟨J,fun τ hτ => ?_⟩
  obtain ⟨Kr,hKr,S,hrow⟩ := actual_high_row_bounds rayM H hH (α:=α) W hWs hW
    bΦ Mcap Lplain τ ε₁ e kap v d (by linarith) hL hτ hε₁ he he' hkap hkap' hv hd hdsupply
    hslotBudget hplainBudget
  let B := bufferCount e
  let baseK := (n+1:ℕ)*Kr*(Cz+Cc)*bΦ^2*(1+6*(B:ℝ))^J
  refine ⟨(Fintype.card (BufferIndex e):ℝ)*baseK,by dsimp [baseK]; positivity,S,?_⟩
  filter_upwards [hcnt,hrow η₀,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop 2)]
    with Z hZc hZr hZτ
  refine ⟨hZc.1,hZτ,?_⟩
  intro j q hq st hchar hu hfloor hwidth hQM hQη h T θ w σ v' t height hw hwm hw1 hσ hσ' hh0 hv'
    hwin hhle hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hZ1 := hZc.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hZτ0 : 0 ≤ Z^τ := Real.rpow_nonneg hZ0.le _
  have hZτ1 : 1 ≤ Z^τ := by linarith
  let T₀ : ℝ := ((h+1:ℕ):ℝ)*Z^τ
  have hT₀ : 2 < T₀ := by
    have : (1:ℝ) ≤ ((h+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos h
    dsimp [T₀]; nlinarith
  let Pl := length Z X₁+length Z X₂
  let s := ∑ k,w k
  let M := st.rowWidth
  have hM0 : 0 ≤ M := hMmin.le.trans hfloor
  have hMc : M ≤ Mcap := by
    have := st.character_nonneg
    have : st.width=st.rowWidth+st.characterWidth := rfl
    linarith
  have hs : 0 ≤ s := Finset.sum_nonneg (fun k _ => hw k)
  have hsN : s ≤ Fintype.card α := by
    calc
      _ ≤ ∑ _k : T,(1:ℝ) := Finset.sum_le_sum (fun k _ => hw1 k)
      _ = (Fintype.card T:ℝ) := by simp
      _ ≤ _ := by exact_mod_cast Fintype.card_le_of_injective _ Subtype.val_injective
  have hstepS : step*s ≤ budget :=
    (mul_le_mul_of_nonneg_left hsN hstep.le).trans hstepN
  let sel := selectBin rayM H hH st η₀ hQM hQη e T₀
  let commonC := (Cz+Cc)*bΦ^2*(1+6*(B:ℝ))^J*(1+|t|+height)^J*Z^(τ*J)
  let G := baseK*(p.control S)^2*(1+|t|+height)^J*
    Z^(M+high q Pl s M+
      (2*ε₁*d*(Fintype.card α+1)+loss*Mcap+τ*J+budget+smin))
  have hG0 : 0 ≤ G := by dsimp [G,baseK]; positivity
  refine (energy_le_class_sums st.character st.mask 1 t (p.profile 0) (p.profile 1)
    (fun k => primePool rayM H 2 (Z^(w k)))
    (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
    (fun k => Z^(w k)) X₁ X₂
    (fun z => st.radial.keep z ∧ ¬lowRow rayM H hH st η₀ hQM hQη e T₀ q z)
    st.radial.profile st.radial.scale bΦ (fun z => st.radial.nonneg z)
    st.radial.scale_pos st.radial_support sel G ?_).trans_eq ?_
  · intro c rows hrows
    by_cases hc : (q+1)/2 ≤ bufferValue e c ∧ bufferValue e c ≤ 7/8
    · let b := bufferValue e c
      let ν := 2*b-1
      have hν : ν ∈ Icc q (3/4) := ⟨by dsimp [ν,b]; linarith [hc.1],by dsimp [ν,b]; linarith [hc.2]⟩
      have hb : (1+floor)/2 ≤ b := by
        have hf := hlaw.floor_ge
        dsimp [b]
        linarith [hq.1,hc.1]
      have hcB : c.1.val ≤ B := Nat.lt_succ_iff.mp c.1.isLt
      have hguards : ∀ z ∈ rows,∃ hz : st.radial.keep z,
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
        b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz
          (((3*c.1.val:ℕ):ℝ)*T₀) := by
        intro z hz
        obtain ⟨⟨hk,_⟩,hp,hsel⟩ := hrows z hz
        have hb := selectBin_spec rayM H hH st η₀ hQM hQη e T₀ he hT₀ hβ hβ' z hk
        change OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
          z hk e T₀ (sel z) at hb
        rw [hsel] at hb
        exact ⟨hk,hp,hb.2.2.2.2.2.1⟩
      have hpair : ∀ z ∈ rows,
          ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
            (fun k => primePool rayM H 2 (Z^(w k)))
            (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
              HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
            (fun k => Z^(w k)) t X₁ X₂‖^2 ≤ Kr*(p.control S)^2*Z^(ν*(Pl+s)+2*ε₁*d*(Fintype.card α+1)) ∧
          ‖(Real.sqrt X₁:ℂ)⁻¹*CenteredMomentHeckeHeight.rowTwistedSum st.character st.mask 1 z (p.profile 0) t X₁‖^2*
          ‖(Real.sqrt X₂:ℂ)⁻¹*CenteredMomentHeckeHeight.rowTwistedSum st.character st.mask 1 z (p.profile 1) t X₂‖^2 ≤
            Kr*(p.control S)^2*Z^(ν*Pl+2*ε₁*d*(Fintype.card α+1)) := by
        intro z hz
        obtain ⟨⟨hk,_⟩,hp,hsel⟩ := hrows z hz
        have hbinfo := selectBin_spec rayM H hH st η₀ hQM hQη e T₀ he hT₀ hβ hβ' z hk
        have hup := hbinfo.2.2.2.2.2.2.2.2
        have hsel' : selectBin rayM H hH st η₀ hQM hQη e T₀ z=c := hsel
        rw [hsel'] at hup
        rw [show T₀=((h+1:ℕ):ℝ)*Z^τ from rfl,binIndex_height] at hup
        have hwinS : ∀ k,|t+v' k|+Z^τ/2 ≤ (3*binIndex c.1.val h+2:ℕ)*Z^τ := by
          intro k
          apply window_binIndex c.1.val h hZτ0
          have := abs_add_le t (v' k)
          have := hv' k
          linarith
        have hwinP : |t|+Z^τ/2 ≤ (3*binIndex c.1.val h+2:ℕ)*Z^τ := by
          apply window_binIndex c.1.val h hZτ0
          linarith
        exact hZr.2 st hu hwidth hQM hQη b (binIndex c.1.val h) (by linarith [hb,hlaw.floor_ge]) (by linarith [hc.2])
          z hk hp hup T θ w σ v' t hw hw1 hσ hσ' hwinS hwinP
          (gate_binIndex c.1.val h B 4 hZτ0 hcB hgate) p X₁ X₂ hX₁ hX₂ hl₁ hl₂
      have hzeroN : (rows.card:ℝ) ≤ commonC*Z^((1-AdaptivePrice.k ν)*M+loss*Mcap) := by
        have hh := hzero (by linarith : 0 < bΦ) j st hchar hu hQM hQη b _ (by linarith [hb]) hc.2 (by positivity) rows hguards
        have hρ : unmarkedDensity ν ≤ 1 :=
          QRH.SilDensitySplit.Density.unmarkedDensity_le_one (by linarith [hlaw.floor_ge,hq.1,hν.1]) hν.2
        have he := normalize_actual_count hCz.le (show Cz ≤ Cz+Cc by linarith) hbΦ hZ1 hMc hρ hloss.le hloss1
          (show Jz ≤ J by dsimp [J]; omega) hcB hhle hh0 hZτ1 hh
        change (rows.card:ℝ) ≤ commonC*Z^(unmarkedDensity ν*M+loss*Mcap) at he
        have hρeq : unmarkedDensity ν=1-AdaptivePrice.k ν := by
          unfold unmarkedDensity AdaptivePrice.k
          rw [show 3*(5-2*ν)=15-6*ν by ring]
        rw [hρeq] at he
        exact he
      by_cases hsmall : smin ≤ ∑ k,w k
      ·
        have hjointN : ∀ δ ∈ Icc low (3/4),∀ sub : Finset O,
            sub ⊆ rows → (∀ z ∈ sub,Z^(δ*s) ≤ slotMass rayM H hH st η₀ W θ w σ v' t z) →
            (sub.card:ℝ) ≤ commonC*Z^(rateFn ν δ*M+loss*Mcap) := by
          intro δ hδ sub hsub hamp
          by_cases hsub0 : sub=∅
          · simp only [hsub0,Finset.card_empty,Nat.cast_zero]
            dsimp [commonC]
            positivity
          have hheightCount : |t|+height ≤ ((3*c.1.val:ℕ):ℝ)*T₀ := by
            obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr hsub0
            obtain ⟨⟨hk,_⟩,_,hselz⟩ := hrows z (hsub hz)
            have hbin := selectBin_spec rayM H hH st η₀ hQM hQη e T₀ he hT₀ hβ hβ' z hk
            change OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
              z hk e T₀ (sel z) at hbin
            rw [hselz] at hbin
            have hcpos : (1:ℝ) ≤ c.1.val := by exact_mod_cast hbin.1
            have hthree : (3:ℝ) ≤ ((3*c.1.val:ℕ):ℝ) := by push_cast; linarith
            have horig : |t|+height ≤ 3*T₀ := by
              dsimp [T₀]
              push_cast at hwin ⊢
              nlinarith
            exact horig.trans (mul_le_mul_of_nonneg_right hthree (by linarith))
          have hh := hZc.2 j st hchar hu hfloor hwidth hQM hQη T θ w σ v' t height hw hwm hσ hσ'
            hh0 hv' hsmall b δ (((3*c.1.val:ℕ):ℝ)*T₀) (by linarith) hc.2 hδ (by positivity) hheightCount sub
            (fun z hz => by
              obtain ⟨hk,hp,hl⟩ := hguards z (hsub hz)
              exact ⟨hk,hp,hl,hamp z hz⟩)
          have hρ : rateFn ν δ ≤ 1 := by
            have hk : 0 ≤ AdaptivePrice.k ν := by
              unfold AdaptivePrice.k
              exact div_nonneg (by linarith [hlaw.floor_ge,hq.1,hν.1]) (by linarith [hν.2])
            exact hlaw.rate_le_one hq hν hδ
          exact normalize_actual_count hCc.le (by linarith : Cc ≤ Cz+Cc) hbΦ hZ1 hMc hρ hloss.le hloss1
            (show Jc ≤ J by dsimp [J]; omega) hcB hhle hh0 hZτ1 hh
        have hf := supplier_finite_energy floor high rateFn (1-AdaptivePrice.k ν) low rayM H hH st η₀ W θ w σ v' t p X₁ X₂ rows
          ν Pl s M (Kr*(p.control S)^2) commonC (2*ε₁*d*(Fintype.card α+1)) (loss*Mcap) step n
          hZ1.le hq hν hM0 hs (by positivity) (by dsimp [commonC]; positivity) hstep hn htop (hlaw.zero hq hν hs hM0) (fun δ hδ => hlaw.joint hq hν hδ hM0 hs) hX₁ hX₂
          (fun z hz => (hpair z hz).1) (fun z hz => (hpair z hz).2) hzeroN hjointN
        refine hf.trans ?_
        dsimp [G,baseK,commonC]
        calc
          _ = ((n+1:ℕ)*Kr*(Cz+Cc)*bΦ^2*(1+6*(B:ℝ))^J)*(p.control S)^2*(1+|t|+height)^J*
            (Z^(τ*J)*Z^(M+high q Pl s M+
              2*ε₁*d*(Fintype.card α+1)+loss*Mcap+step*s)) := by ring
          _ = ((n+1:ℕ)*Kr*(Cz+Cc)*bΦ^2*(1+6*(B:ℝ))^J)*(p.control S)^2*(1+|t|+height)^J*
            Z^(M+high q Pl s M+
              (2*ε₁*d*(Fintype.card α+1)+loss*Mcap+τ*J+step*s)) := by
            rw [← Real.rpow_add hZ0]
            congr 2
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)) (by positivity)
      · have hsmall' : s < smin := lt_of_not_ge hsmall
        have hpay := hlaw.full hq hν hs hM0 (P:=Pl) (M:=M)
        have hsum : (∑ z ∈ rows,‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
            (fun k => primePool rayM H 2 (Z^(w k)))
            (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
              HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
            (fun k => Z^(w k)) t X₁ X₂‖^2) ≤
            (rows.card:ℝ)*(Kr*(p.control S)^2*Z^(ν*(Pl+s)+2*ε₁*d*(Fintype.card α+1))) := by
          calc
            _ ≤ ∑ _z ∈ rows,Kr*(p.control S)^2*Z^(ν*(Pl+s)+2*ε₁*d*(Fintype.card α+1)) :=
              Finset.sum_le_sum (fun z hz => (hpair z hz).1)
            _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
        have hcN : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.succ_pos n
        have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hzeroN (by positivity))
        refine hsum'.trans ?_
        have hp : Z^((1-AdaptivePrice.k ν)*M+loss*Mcap)*
            Z^(ν*(Pl+s)+2*ε₁*d*(Fintype.card α+1)) ≤
            Z^(M+high q Pl s M+2*ε₁*d*(Fintype.card α+1)+loss*Mcap+budget+smin) := by
          rw [← Real.rpow_add hZ0]
          exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
        calc
          _ = commonC*(Kr*(p.control S)^2)*
              (Z^((1-AdaptivePrice.k ν)*M+loss*Mcap)*
                Z^(ν*(Pl+s)+2*ε₁*d*(Fintype.card α+1))) := by ring
          _ ≤ commonC*(Kr*(p.control S)^2)*
              Z^(M+high q Pl s M+2*ε₁*d*(Fintype.card α+1)+loss*Mcap+budget+smin) :=
            mul_le_mul_of_nonneg_left hp (by dsimp [commonC]; positivity)
          _ ≤ (n+1:ℕ)*(commonC*(Kr*(p.control S)^2)*
              Z^(M+high q Pl s M+2*ε₁*d*(Fintype.card α+1)+loss*Mcap+budget+smin)) :=
            le_mul_of_one_le_left (by dsimp [commonC]; positivity) hcN
          _ = G := by
            dsimp only [G,baseK,commonC]
            calc
              _ = ((n+1:ℕ)*Kr*(Cz+Cc)*bΦ^2*(1+6*(B:ℝ))^J)*(p.control S)^2*(1+|t|+height)^J*
                (Z^(τ*J)*Z^(M+high q Pl s M+2*ε₁*d*(Fintype.card α+1)+loss*Mcap+budget+smin)) := by ring
              _ = _ := by rw [← Real.rpow_add hZ0]; congr 2; ring
    · have hempty : rows=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨⟨hk,hnl⟩,hp,hsel⟩ := hrows z hz
        have hb := selectBin_spec rayM H hH st η₀ hQM hQη e T₀ he hT₀ hβ hβ' z hk
        have hh := selectBin_high rayM H hH st η₀ hQM hQη e T₀ q he hT₀ hβ hβ' z hk hnl
        change (q+1)/2 ≤ bufferValue e (sel z) at hh
        have hsel' : selectBin rayM H hH st η₀ hQM hQη e T₀ z=c := hsel
        rw [hsel'] at hb
        rw [hsel] at hh
        exact hc ⟨hh,hb.2.2.2.2.1⟩
      simpa only [hempty,Finset.sum_empty] using hG0
  · change QuadraticInitialBound.diagonalControl st.radial.profile*
      (Fintype.card (BufferIndex e):ℝ)*G =
      (Fintype.card (BufferIndex e):ℝ)*baseK*QuadraticInitialBound.diagonalControl st.radial.profile*
        (p.control S)^2*(1+|t|+height)^J*
        Z^(M+high q Pl s M+
          (2*ε₁*d*(Fintype.card α+1)+loss*Mcap+τ*J+budget+smin))
    dsimp only [G]
    ring

end

/-- Pure repeated-mark HIGH, including all natural bins and all physical
heights. The only analytic count input is the literal whole repeated count;
its supplier is composed here, rather than being added as an assumption. -/
theorem wholeWeightedHigh_of_repeated
    (B L c floor : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 1) (hLsrc : (3/2:ℝ) ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (hf : (2/5:ℝ) ≤ floor)
    (high : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hhigh : ∀ q (hq : q ∈ Ioc (0:ℝ) (3/4)), floor ≤ q → ∀ P s M,
      high q P s M=(FrontierRepeatedMarks.repeatedFamily B L c q hB0 hB hLsrc hc0 hc hq false).high P s M)
    (hwhole : WholeRepeatedCountOn floor B L c) : WeightedSupplier.WholeWeightedHigh floor high := by
  intro Mmin Mcap smin loss hMmin hMcap hsmin hloss
  let gap := loss/4
  let lossC := loss/4
  have hgap : 0 < gap := by dsimp [gap]; positivity
  have hlc : 0 < lossC := by dsimp [lossC]; positivity
  obtain ⟨low,hlow,hlf,hlaw⟩ := exists_natural_payment_law B L c floor gap hB0 hB hLsrc
    hc0 hc hf hgap false (fun q P s M => high q P s M+gap*M)
    (by intro q hq hfloor P s M; rw [hhigh q hq hfloor])
  obtain ⟨meshMax,hm,hcount⟩ := wholeClippedCountOn_of_repeated floor B L c hwhole
    Mmin Mcap smin lossC low hMmin hMcap hsmin hlc hlow hlf.le
  refine ⟨meshMax,hm,?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs bΦ hbΦ κ _ anchors η₀ hβ hβhi
  obtain ⟨Jc,Cc,hCc,hcnt⟩ := hcount mesh hmesh α rayM H hH W hW hWs κ anchors η₀ bΦ hbΦ
  intro Lplain ε₁ kap v d budget hLplain hε₁ hkap hkap1 hv hd hds hbudget
  refine ⟨1,one_pos,?_⟩
  intro e he hecap he1 hslot hplain hloss1
  have hlc1 : lossC ≤ 1 := by dsimp [lossC]; linarith
  have hcnt' : ∀ᶠ Z : ℝ in atTop,
      SupplierCountAt floor low
        (fun ν δ => RepeatedMarks.rawRepeatedCountRate B L c ν (min δ ν))
        (α:=α) rayM H hH W anchors η₀ Mmin Mcap smin mesh lossC bΦ Jc Cc Z := by
    simpa only [WholeClippedCountOn, SupplierCountAt] using hcnt
  obtain ⟨J,hbranch⟩ := supplier_high_branch rayM H hH floor
    (fun q P s M => high q P s M+gap*M) low
    (fun ν δ => RepeatedMarks.rawRepeatedCountRate B L c ν (min δ ν)) hlaw
    W hWs hW bΦ hbΦ anchors η₀ hβ hβhi Mmin Mcap smin mesh Lplain ε₁ e kap v d lossC budget
    hMmin hsmin hLplain hε₁ he hecap hkap hkap1 hv hd hds hslot hplain
    hlc hlc1 hbudget Jc Cc hCc hcnt'
  refine ⟨J,?_⟩
  intro τ hτ
  obtain ⟨K,hK,S,hall⟩ := hbranch τ hτ
  refine ⟨K,hK,S,?_⟩
  filter_upwards [hall] with Z hZ
  refine ⟨hZ.1,hZ.2.1,?_⟩
  intro j q hq st hchar hp hM hw hQM hQη h T θ w σ v' t height hw0 hwm hw1 hσ0 hσ1
    hh hv' hwin hhle hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hhrow := hZ.2.2 j q hq st hchar hp hM hw hQM hQη h T θ w σ v' t height hw0 hwm hw1
    hσ0 hσ1 hh hv' hwin hhle hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hMc : st.rowWidth ≤ Mcap := by
    have := st.character_nonneg
    have : st.width=st.rowWidth+st.characterWidth := rfl
    linarith
  have hM0 : 0 ≤ Mcap := hMmin.le.trans hMcap
  have hpay : gap*st.rowWidth+lossC*Mcap ≤ loss*Mcap := by
    have := mul_le_mul_of_nonneg_left hMc hgap.le
    dsimp [gap,lossC] at *
    nlinarith
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  apply hhrow.trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  positivity

/-- Combined repeated/selected HIGH, including all natural bins and all physical
heights. The only analytic count input is the literal whole repeated count;
its supplier is composed here, rather than being added as an assumption. -/
theorem wholeWeightedHigh_of_combined
    (B L c floor : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 1) (hLsrc : (3/2:ℝ) ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (hf : (2/5:ℝ) ≤ floor)
    (high : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hhigh : ∀ q (hq : q ∈ Ioc (0:ℝ) (3/4)), floor ≤ q → ∀ P s M,
      high q P s M=(FrontierRepeatedMarks.repeatedFamily B L c q hB0 hB hLsrc hc0 hc hq true).high P s M)
    (hwhole : WholeCombinedCountOn floor B L c) : WeightedSupplier.WholeWeightedHigh floor high := by
  intro Mmin Mcap smin loss hMmin hMcap hsmin hloss
  let gap := loss/4
  let lossC := loss/4
  have hgap : 0 < gap := by dsimp [gap]; positivity
  have hlc : 0 < lossC := by dsimp [lossC]; positivity
  obtain ⟨low,hlow,hlf,hlaw⟩ := exists_natural_payment_law B L c floor gap hB0 hB hLsrc
    hc0 hc hf hgap true (fun q P s M => high q P s M+gap*M)
    (by intro q hq hfloor P s M; rw [hhigh q hq hfloor])
  obtain ⟨meshMax,hm,hcount⟩ := hwhole
    Mmin Mcap smin lossC low hMmin hMcap hsmin hlc hlow hlf.le
  refine ⟨meshMax,hm,?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs bΦ hbΦ κ _ anchors η₀ hβ hβhi
  obtain ⟨Jc,Cc,hCc,hcnt⟩ := hcount mesh hmesh α rayM H hH W hW hWs κ anchors η₀ bΦ hbΦ
  intro Lplain ε₁ kap v d budget hLplain hε₁ hkap hkap1 hv hd hds hbudget
  refine ⟨1,one_pos,?_⟩
  intro e he hecap he1 hslot hplain hloss1
  have hlc1 : lossC ≤ 1 := by dsimp [lossC]; linarith
  have hcnt' : ∀ᶠ Z : ℝ in atTop,
      SupplierCountAt floor low
        (fun ν δ => FrontierRepeatedMarks.combineSelected (RepeatedMarks.rawRepeatedCountRate B L c) ν (min δ ν))
        (α:=α) rayM H hH W anchors η₀ Mmin Mcap smin mesh lossC bΦ Jc Cc Z := by
    simpa only [WholeCombinedCountOn, SupplierCountAt] using hcnt
  obtain ⟨J,hbranch⟩ := supplier_high_branch rayM H hH floor
    (fun q P s M => high q P s M+gap*M) low
    (fun ν δ => FrontierRepeatedMarks.combineSelected (RepeatedMarks.rawRepeatedCountRate B L c) ν (min δ ν)) hlaw
    W hWs hW bΦ hbΦ anchors η₀ hβ hβhi Mmin Mcap smin mesh Lplain ε₁ e kap v d lossC budget
    hMmin hsmin hLplain hε₁ he hecap hkap hkap1 hv hd hds hslot hplain
    hlc hlc1 hbudget Jc Cc hCc hcnt'
  refine ⟨J,?_⟩
  intro τ hτ
  obtain ⟨K,hK,S,hall⟩ := hbranch τ hτ
  refine ⟨K,hK,S,?_⟩
  filter_upwards [hall] with Z hZ
  refine ⟨hZ.1,hZ.2.1,?_⟩
  intro j q hq st hchar hp hM hw hQM hQη h T θ w σ v' t height hw0 hwm hw1 hσ0 hσ1
    hh hv' hwin hhle hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hhrow := hZ.2.2 j q hq st hchar hp hM hw hQM hQη h T θ w σ v' t height hw0 hwm hw1
    hσ0 hσ1 hh hv' hwin hhle hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hMc : st.rowWidth ≤ Mcap := by
    have := st.character_nonneg
    have : st.width=st.rowWidth+st.characterWidth := rfl
    linarith
  have hM0 : 0 ≤ Mcap := hMmin.le.trans hMcap
  have hpay : gap*st.rowWidth+lossC*Mcap ≤ loss*Mcap := by
    have := mul_le_mul_of_nonneg_left hMc hgap.le
    dsimp [gap,lossC] at *
    nlinarith
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  apply hhrow.trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  positivity


end
end Qrh.JointDetector.FrontierRepeatedWeightedHigh

#print axioms Qrh.JointDetector.FrontierRepeatedWeightedHigh.supplier_finite_energy
#print axioms Qrh.JointDetector.FrontierRepeatedWeightedHigh.exists_early_amplitude_cutoff
#print axioms Qrh.JointDetector.FrontierRepeatedWeightedHigh.repeated_payment

#print axioms Qrh.JointDetector.FrontierRepeatedWeightedHigh.supplier_high_branch

#print axioms Qrh.JointDetector.FrontierRepeatedWeightedHigh.wholeWeightedHigh_of_repeated

#print axioms Qrh.JointDetector.FrontierRepeatedWeightedHigh.wholeWeightedHigh_of_combined
