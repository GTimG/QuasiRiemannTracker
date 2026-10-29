/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
The unmarked HIGH adapter retains Sil's literal natural-row/dictionary proof;
the joint histogram preserves both actual pointwise estimates. -/
import Candidate.Local.Qrh.JointDetector.AdaptiveSupplier.JointHigh
import Candidate.Local.Qrh.JointDetector.NaturalCount
import Candidate.Local.Qrh.JointDetector.AdaptiveSourceChains.Common

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


/-- Pure scalar payment laws; these carry no count, energy or packed estimate. -/
structure HighLaw (floor : ℝ) (high : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop where
  floor_ge : (57/100:ℝ) ≤ floor
  zero : ∀ {q ν P s M : ℝ},q ∈ Icc floor (3/4) → ν ∈ Icc q (3/4) → 0 ≤ s →
    (1-AdaptivePrice.k ν)*M+ν*P+(1001/2000:ℝ)*s ≤ M+high q P s M
  joint : ∀ {q ν δ P s M : ℝ},q ∈ Icc floor (3/4) → ν ∈ Icc q (3/4) →
    δ ∈ Icc (1001/2000:ℝ) (3/4) → 0 ≤ M → 0 ≤ s →
    AdaptivePrice.jointRate ν δ*M+ν*P+min δ ν*s ≤ M+high q P s M
  full : ∀ {q ν P s M : ℝ},q ∈ Icc floor (3/4) → ν ∈ Icc q (3/4) → 0 ≤ s →
    (1-AdaptivePrice.k ν)*M+ν*(P+s) ≤ M+high q P s M+s

theorem supplier_finite_energy (floor : ℝ) (high : ℝ → ℝ → ℝ → ℝ → ℝ) (hlaw : HighLaw floor high) {q : ℝ} {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    {Z bΦ : ℝ} (st : NaturalState Z 0 bΦ) (η₀ : Character)
    (W : ℝ → ℂ) (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ)
    (t : ℝ) (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (E : Finset O)
    (ν Pl s M F C err loss step : ℝ) (n : ℕ)
    (hZ : 1 ≤ Z) (hq : q ∈ Icc floor (3/4)) (hν : ν ∈ Icc q (3/4)) (hM : 0 ≤ M) (hs : 0 ≤ s)
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
      (n+1:ℕ)*F*C*Z^(M+high q Pl s M+err+loss+step*s) := by
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
  have hpaid : ∀ i, rate i*M+ν*Pl+slope i*s ≤ M+high q Pl s M := by
    intro i
    by_cases hi : i.val=0
    · simp only [rate, slope, ite_eq_left hi]
      exact hlaw.zero hq hν hs
    · simp only [rate, slope, ite_eq_right hi]
      exact hlaw.joint hq hν (hδ i) hM hs
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


def SupplierCountAt {α κ : Type} [Fintype α] [DecidableEq α] [Fintype κ]
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
  ∀ (b δ T' : ℝ), (1+(57/100:ℝ))/2 ≤ b → b ≤ 7/8 →
  δ ∈ Icc (1001/2000:ℝ) (3/4) → 0 ≤ T' →
  ∀ rows : Finset O, (∀ z ∈ rows,∃ hz : st.radial.keep z,
    st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
    b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T' ∧
    Z^(δ*∑ k,w k) ≤ slotMass rayM H hH st η₀ W θ w σ v t z) →
  (rows.card:ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(AdaptivePrice.jointRate (2*b-1) δ+loss)

private theorem normalize_count {Z bΦ M Mcap ρ loss Cd Csum τ t height : ℝ}
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

section
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Actual large-slot HIGH branch from the explicit whole count. The
counting degree is fixed before the physical height scale τ. -/
theorem supplier_high_branch {α : Type} [Fintype α] [DecidableEq α]
    (floor : ℝ) (high : ℝ → ℝ → ℝ → ℝ → ℝ) (hlaw : HighLaw floor high)
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
      SupplierCountAt (α:=α) rayM H hH W anchors η₀ Mmin Mcap smin mesh loss bΦ Jc Cc Z) :
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
  obtain ⟨Jz,Cz,hCz,hzero⟩ := high_row_count_on rayM H hH (57/100) le_rfl anchors η₀ loss hloss
  let J := Jz+Jc
  obtain ⟨n,hn,step,hstep,htop,hstepN⟩ := exists_amplitude_grid (Fintype.card α) hbudget
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
      have hb : (157/200:ℝ) ≤ b := by
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
        exact hZr.2 st hu hwidth hQM hQη b (binIndex c.1.val h) (by linarith) (by linarith [hc.2])
          z hk hp hup T θ w σ v' t hw hw1 hσ hσ' hwinS hwinP
          (gate_binIndex c.1.val h B 4 hZτ0 hcB hgate) p X₁ X₂ hX₁ hX₂ hl₁ hl₂
      have hzeroN : (rows.card:ℝ) ≤ commonC*Z^((1-AdaptivePrice.k ν)*M+loss*Mcap) := by
        have hh := hzero (by linarith : 0 < bΦ) j st hchar hu hQM hQη b _ (by linarith [hb]) hc.2 (by positivity) rows hguards
        have hρ : unmarkedDensity ν ≤ 1 :=
          QRH.SilDensitySplit.Density.unmarkedDensity_le_one (by linarith [hlaw.floor_ge,hq.1,hν.1]) hν.2
        have he := normalize_count hCz.le (show Cz ≤ Cz+Cc by linarith) hbΦ hZ1 hMc hρ hloss.le hloss1
          (show Jz ≤ J by dsimp [J]; omega) hcB hhle hh0 hZτ1 hh
        change (rows.card:ℝ) ≤ commonC*Z^(unmarkedDensity ν*M+loss*Mcap) at he
        have hρeq : unmarkedDensity ν=1-AdaptivePrice.k ν := by
          unfold unmarkedDensity AdaptivePrice.k
          rw [show 3*(5-2*ν)=15-6*ν by ring]
        rw [hρeq] at he
        exact he
      by_cases hsmall : smin ≤ ∑ k,w k
      ·
        have hjointN : ∀ δ ∈ Icc (1001/2000:ℝ) (3/4),∀ sub : Finset O,
            sub ⊆ rows → (∀ z ∈ sub,Z^(δ*s) ≤ slotMass rayM H hH st η₀ W θ w σ v' t z) →
            (sub.card:ℝ) ≤ commonC*Z^(AdaptivePrice.jointRate ν δ*M+loss*Mcap) := by
          intro δ hδ sub hsub hamp
          have hh := hZc.2 j st hchar hu hfloor hwidth hQM hQη T θ w σ v' t height hw hwm hσ hσ'
            hh0 hv' hsmall b δ (((3*c.1.val:ℕ):ℝ)*T₀) (by linarith) hc.2 hδ (by positivity) sub
            (fun z hz => by
              obtain ⟨hk,hp,hl⟩ := hguards z (hsub hz)
              exact ⟨hk,hp,hl,hamp z hz⟩)
          have hρ : AdaptivePrice.jointRate ν δ ≤ 1 := by
            have hk : 0 ≤ AdaptivePrice.k ν := by
              unfold AdaptivePrice.k
              exact div_nonneg (by linarith [hlaw.floor_ge,hq.1,hν.1]) (by linarith [hν.2])
            unfold AdaptivePrice.jointRate
            split_ifs <;> exact (min_le_left _ _).trans (by linarith)
          exact normalize_count hCc.le (by linarith : Cc ≤ Cz+Cc) hbΦ hZ1 hMc hρ hloss.le hloss1
            (show Jc ≤ J by dsimp [J]; omega) hcB hhle hh0 hZτ1 hh
        have hf := supplier_finite_energy floor high hlaw rayM H hH st η₀ W θ w σ v' t p X₁ X₂ rows
          ν Pl s M (Kr*(p.control S)^2) commonC (2*ε₁*d*(Fintype.card α+1)) (loss*Mcap) step n
          hZ1.le hq hν hM0 hs (by positivity) (by dsimp [commonC]; positivity) hstep hn htop hX₁ hX₂
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
        have hpay := hlaw.full hq hν hs (P:=Pl) (M:=M)
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

theorem priced_source_of_whole_count
    (hwhole : NaturalCount.WholeJointCountOn (57/100))
    (floor : ℝ) (high : ℝ → ℝ → ℝ → ℝ → ℝ) (hlaw : HighLaw floor high)
    (B₀ L₀ c₀ Mmin Mmax Lplain : ℝ) (hL : 0 < L₀)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hface : 0 < B₀ ∧ B₀ ≤ 1 ∧ 0 < c₀) (h0 : 0 < Mmin) (h1 : Mmin ≤ Mmax)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀)
    (qfun : ℝ → ℝ) (hqfun : ∀ w,qfun w ∈ Icc floor (3/4))
    (price : Price)
    (hprice : ∀ w P s M,price.f w P s M=
      max (qfun w*deletionNeed B₀ L₀ c₀ P s M) (high (qfun w) P s M)) :
    PricedPackedSource price Mmin Mmax Lplain := by
  intro ε hε
  have hβ' : HeckeZeroSupremum.beta ≤ 7/8 := by
    have := Candidate.FourthPower.IncumbentInput.native_kappa_bound
    linarith
  obtain ⟨meshN, hmeshN, hnat⟩ := native_priced_source hβ Mmin Mmax Lplain h0 h1 ε hε
  have hMmax : 0 < Mmax := h0.trans_le h1
  have hden : 0 < max (1:ℝ) Mmax := zero_lt_one.trans_le (le_max_left _ _)
  have hue : 0 < (ε/4)/(max 1 Mmax) := div_pos (by positivity) hden
  obtain ⟨unitMesh, hum, hu⟩ := hparent ((ε/4)/(max 1 Mmax)) hue
  have he4 : Mmax*((ε/4)/(max 1 Mmax)) ≤ ε/4 := by
    calc Mmax*((ε/4)/(max 1 Mmax)) ≤ (max 1 Mmax)*((ε/4)/(max 1 Mmax)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hue.le
      _ = ε/4 := mul_div_cancel₀ _ hden.ne'
  have hmeshPos : 0 < min (min (unitMesh*Mmin) meshN) (min (ε/8) 1) :=
    lt_min (lt_min (mul_pos hum h0) hmeshN) (lt_min (by positivity) one_pos)
  let Mcap₀ : ℝ := Mmax+ε/8
  let loss₀ : ℝ := min (ε/(8*(Mcap₀+1))) 1
  have hMc₀ : Mmin ≤ Mcap₀ := by dsimp [Mcap₀]; linarith
  have hl₀ : 0 < loss₀ := by dsimp [loss₀,Mcap₀]; positivity
  obtain ⟨meshC,hmeshC,hcounts⟩ := hwhole Mmin Mcap₀ (ε/16) loss₀ h0 hMc₀ (by positivity) hl₀
  refine ⟨min (min (min (unitMesh*Mmin) meshN) (min (ε/8) 1)) meshC,
    lt_min hmeshPos hmeshC,?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs bΦ hbΦ κ _ anchors η₀ Q hQ hQ0 hQt hQ72
  have hmeshOld : mesh ≤ min (min (unitMesh*Mmin) meshN) (min (ε/8) 1) :=
    hmesh.trans (min_le_left _ _)
  have hmeshCount : mesh ≤ meshC := hmesh.trans (min_le_right _ _)
  have hm' : max 0 mesh ≤ min (min (unitMesh*Mmin) meshN) (min (ε/8) 1) :=
    max_le hmeshPos.le hmeshOld
  have hmU : max 0 mesh ≤ unitMesh*Mmin := hm'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hmN : mesh ≤ meshN := hmeshOld.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hmE : max 0 mesh ≤ ε/8 := hm'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm1 : max 0 mesh ≤ 1 := hm'.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Jc,Cc,hCc,hcounts⟩ := hcounts mesh hmeshCount α rayM H hH W hW hWs κ anchors η₀ bΦ (by linarith)
  -- native (large heights) and parent constants
  obtain ⟨degN, SN, CN, hCN, hevN⟩ := hnat mesh hmN α rayM H hH W hW hWs bΦ hbΦ κ anchors η₀ Q
    hQ hQ0 hQt hQ72
  obtain ⟨degP, SP, CP, hCP, hevP⟩ :=
    QRH.Record1252270103Source.PhysicalParentSources.unit_source_finite_anchors (α:=α) hu
      rayM H hH W hW hWs bΦ (max 0 mesh) Mmin Mmax (ε/4) hbΦ h0 hum.le hmU hue.le he4
      anchors η₀ Q hQ hQ0 hQt hQ72
  -- scalars
  set N : ℕ := Fintype.card α with hNdef
  set Mcap : ℝ := Mmax + ε/8 with hMcap
  set d : ℝ := Mcap + 1 with hddef
  set Lp : ℝ := max Lplain 0 with hLp
  have hd : 0 < d := by rw [hddef, hMcap]; positivity
  have hLp0 : 0 ≤ Lp := le_max_right _ _
  have hN1 : (0:ℝ) < (N:ℝ) + 1 := by positivity
  set ε₁ : ℝ := ε/(16*d*((N:ℝ)+1)) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  have hε₁d : 2*ε₁*d*((N:ℝ)+1) = ε/8 := by
    rw [hε₁def]; field_simp; ring
  set kap : ℝ := min (ε₁/32) (1/2) with hkapdef
  have hkap : 0 < kap := lt_min (by positivity) (by norm_num)
  have hkap1 : kap ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hkapε : kap ≤ ε₁/32 := min_le_left _ _
  set vg : ℝ := ε₁/8 with hvg
  have hvg0 : 0 < vg := by positivity
  set e : ℝ := min (1/2000) (ε₁/(100*(Lp/d + 2 + 1/d))) with hedef
  have hden2 : 0 < 100*(Lp/d + 2 + 1/d) := by positivity
  have he : 0 < e := lt_min (by norm_num) (div_pos hε₁ hden2)
  have he' : e < 1/1000 := (min_le_left _ _).trans_lt (by norm_num)
  have heε : e*(100*(Lp/d + 2 + 1/d)) ≤ ε₁ := by
    have := min_le_right (1/2000:ℝ) (ε₁/(100*(Lp/d + 2 + 1/d)))
    rw [← hedef] at this
    rwa [le_div_iff₀ hden2] at this
  have hLd : 0 ≤ Lp/d := div_nonneg hLp0 hd.le
  have hdinv : 0 ≤ 1/d := by positivity
  have heL : 0 ≤ e*(Lp/d) := mul_nonneg he.le hLd
  have hed : 0 ≤ e*(1/d) := mul_nonneg he.le hdinv
  have hslotB : 8*e*(1/d)+kap ≤ ε₁ := by linarith
  have hplainB : 12*e*(Lp/d+2)+8*kap+2*vg ≤ ε₁ := by linarith
  set loss : ℝ := min (ε/(8*(Mcap+1))) 1 with hlossdef
  have hMcap0 : 0 ≤ Mcap := by rw [hMcap]; positivity
  have hloss : 0 < loss := lt_min (by positivity) one_pos
  have hloss1 : loss ≤ 1 := min_le_right _ _
  have hlossM : loss*Mcap ≤ ε/8 := by
    have h1 : loss ≤ ε/(8*(Mcap+1)) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  -- zero-slot energy (all slots erased)
  haveI : NeZero (internalQ Q η₀) := ⟨hQ0⟩
  obtain ⟨degZ, SZ, hceZ⟩ := Candidate.FourthPower.NativeNonfixedEnergy.canonical_energy
    rayM H hH (∅ : Finset α) W 1 2 (1/4) (9/4) bΦ Mcap Lplain 1 (ε/4)
    (33/50) (33/50) (3/4) one_pos hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by positivity) zero_le_one (by positivity) hβ
    Candidate.FourthPower.IncumbentInput.native_kappa_bound (internalQ Q η₀) hQt hQ72
    (inf_le_left.trans hQ)
  obtain ⟨CZ, hCZ, hevZ⟩ := hceZ η₀ inf_le_right
  -- HIGH: the density degree, then the height scale
  have hcounts' : ∀ᶠ Z : ℝ in atTop,
      SupplierCountAt (α:=α) rayM H hH W anchors η₀ Mmin Mcap (ε/16) mesh loss bΦ Jc Cc Z := hcounts
  obtain ⟨J,hJ⟩ := supplier_high_branch rayM H hH (α:=α) floor high hlaw
    W hWs hW bΦ (by linarith) anchors η₀ hβ hβ'
    Mmin Mcap (ε/16) mesh Lp ε₁ e kap vg d loss (ε/16)
    h0 (by positivity) hLp0 hε₁ he he' hkap hkap1 hvg0.le hd (by linarith)
    hslotB hplainB hloss hloss1 (by positivity) Jc Cc hCc hcounts'
  set τ : ℝ := min (ε/(16*((J:ℝ)+1))) (d*vg/16) with hτdef
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτJ : τ*J ≤ ε/16 := by
    have h1 : τ ≤ ε/(16*((J:ℝ)+1)) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    have : (0:ℝ) ≤ J := Nat.cast_nonneg _
    linarith
  obtain ⟨KH, hKH, SH, hevH⟩ := hJ τ hτ
  -- LOW: uniform in the cut
  obtain ⟨CL, hCL, hevL⟩ := low_branch rayM H hH (α := α) W hWs hW (1/d) d τ ε₁ e kap vg
    (33/50) (33/50) bΦ Mcap d hdinv hd.le hτ hε₁ he he' hkap hvg0.le hslotB (by linarith)
    hd (by linarith) le_rfl
  -- large heights
  set c : ℝ := d*vg/16 with hcdef
  have hc0 : 0 < c := by positivity
  have hcτ : 4*c + 4*τ ≤ d*vg/2 := by
    have : τ ≤ d*vg/16 := min_le_right _ _
    rw [hcdef]; linarith
  set k : ℕ := ⌈(3/4*(N:ℝ))/c⌉₊ with hkdef
  have hck : 3/4*(N:ℝ) ≤ c*k := by
    have := Nat.le_ceil ((3/4*(N:ℝ))/c)
    rw [← hkdef, div_le_iff₀ hc0] at this
    linarith
  set B : ℕ := bufferCount e with hBdef
  refine ⟨degN + k + degP + degZ + J, SN ∪ SP ∪ SZ ∪ SH,
    CN + (max 1 CL)^N*(CP + CZ) + KH, by positivity, ?_⟩
  have hanch : ∀ᶠ Z : ℝ in atTop, ∀ j, ((anchors j).modulus.absNorm : ℝ) ≤ Z^(ε/8) :=
    eventually_all.mpr (fun j =>
      (tendsto_rpow_atTop (by positivity : (0:ℝ) < ε/8)).eventually (eventually_ge_atTop _))
  have hgateE : ∀ᶠ Z : ℝ in atTop, (9*((B:ℝ)+1))^4 ≤ Z^(d*vg/2) :=
    (tendsto_rpow_atTop (by positivity : (0:ℝ) < d*vg/2)).eventually (eventually_ge_atTop _)
  filter_upwards [hevN, hevP, hevZ, hevL η₀, hevH, hanch, hgateE]
    with Z hZN hZP hZZ hZL hZH hZa hZg
  clear hevN hevP hevZ hevL hevH hanch hgateE hJ hceZ hnat hu hparent
  have hmaxN : 0 ≤ (max 1 CL)^N := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hAP : 0 ≤ (max 1 CL)^N*CP := mul_nonneg hmaxN hCP.le
  have hAZ : 0 ≤ (max 1 CL)^N*CZ := mul_nonneg hmaxN hCZ.le
  have hAsplit : (max 1 CL)^N*(CP + CZ) = (max 1 CL)^N*CP + (max 1 CL)^N*CZ := mul_add _ _ _
  have hε₁dN : 2*ε₁*d*(N:ℝ) ≤ ε/8 := by
    have h2 : 0 ≤ 2*ε₁*d := by positivity
    have : 2*ε₁*d*((N:ℝ)+1) = 2*ε₁*d*N + 2*ε₁*d := by ring
    linarith
  intro j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂
    hX₁ hX₂ hl₁ hl₂
  rw [hprice]
  have hZ1 : 1 < Z := hZL.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hbase : 1 ≤ 1+|t|+height := by linarith [abs_nonneg t]
  have hdg := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hs0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  set S := SN ∪ SP ∪ SZ ∪ SH with hSdef
  have hcN : p.control SN ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p
      (Finset.subset_union_left.trans (Finset.subset_union_left.trans
        Finset.subset_union_left))
  have hcP : p.control SP ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p
      (Finset.subset_union_right.trans (Finset.subset_union_left.trans
        Finset.subset_union_left))
  have hcZ : p.control SZ ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p
      (Finset.subset_union_right.trans Finset.subset_union_left)
  have hcH : p.control SH ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p Finset.subset_union_right
  set M := Real.logb Z (((Ideal.span {V}).absNorm : ℝ) * K) with hMdef
  set q : ℝ := qfun w₀ with hqdef
  have hq : q ∈ Icc floor (3/4) := hqfun w₀
  have hq0 : (57/100:ℝ) ≤ q := hlaw.floor_ge.trans hq.1
  have hq1 : q ≤ 3/4 := hq.2
  set Pl : ℝ := length Z X₁ + length Z X₂ with hPl
  set need := deletionNeed B₀ L₀ c₀ Pl (∑ i, w i) M with hneed
  have hlowle : q*need ≤ max (q*need) (high q Pl (∑ i, w i) M) := le_max_left _ _
  have hhighle : high q Pl (∑ i, w i) M ≤ max (q*need) (high q Pl (∑ i, w i) M) :=
    le_max_right _ _
  have hneed0 : 0 ≤ need := deletionNeed_nonneg _ _ _ _ _ _
  have hprice0 : 0 ≤ max (q*need) (high q Pl (∑ i, w i) M) :=
    (mul_nonneg (by linarith) hneed0).trans hlowle
  have hCtot : 0 ≤ CN + (max 1 CL)^N*(CP + CZ) + KH := by positivity
  by_cases hlarge : Z^c < 1+|t|+height
  · ---------------- large heights: native bound with the height factor
    have hn := hZN j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos
      p X₁ X₂ hX₁ hX₂ hl₁ hl₂
    rw [nativePrice_f, max_eq_right hs0, ← hMdef] at hn
    refine hn.trans ?_
    have hsN : ∑ i, w i ≤ N := by
      calc ∑ i, w i ≤ ∑ _i : T, (1:ℝ) :=
            Finset.sum_le_sum (fun i _ => (hwm i).trans ((le_max_right 0 mesh).trans hm1))
        _ = (Fintype.card T : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        _ ≤ N := by exact_mod_cast Fintype.card_le_of_injective _ Subtype.val_injective
    have hZk : Z^(3/4*∑ i, w i) ≤ (1+|t|+height)^k := by
      calc Z^(3/4*∑ i, w i) ≤ Z^(c*k) :=
            Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
        _ = (Z^c)^k := by rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
        _ ≤ (1+|t|+height)^k :=
            pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) hlarge.le k
    have hsplitZ : Z^(M + 3/4*∑ i, w i + ε) = Z^(3/4*∑ i, w i) * Z^(M + ε) := by
      rw [← Real.rpow_add hZ0]; ring_nf
    rw [hsplitZ]
    have hZ2 : Z^(M+ε) ≤ Z^(M + max (q*need) (high q Pl (∑ i, w i) M) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
    have hpc := p.control_nonneg SN
    calc CN*QuadraticInitialBound.diagonalControl Φ*(p.control SN)^2*(1+|t|+height)^degN*
          (Z^(3/4*∑ i, w i) * Z^(M + ε))
        ≤ CN*QuadraticInitialBound.diagonalControl Φ*(p.control SN)^2*(1+|t|+height)^degN*
          ((1+|t|+height)^k * Z^(M + ε)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hZk (Real.rpow_nonneg hZ0.le _)
      _ = CN*QuadraticInitialBound.diagonalControl Φ*(p.control SN)^2*
          (1+|t|+height)^(degN+k)*Z^(M + ε) := by rw [pow_add]; ring
      _ ≤ _ := scale_le hCN.le (by linarith) hdg (p.control_nonneg SN) hcN hbase
          (by omega) hZ1.le (by linarith)
  · ---------------- bounded heights: LOW/HIGH split
    replace hlarge := not_lt.mp hlarge
    have hM0 : 0 ≤ M := h0.le.trans hM₁
    have hUpos := packed_scale_pos V hV hK
    have hUM : ((Ideal.span {V}).absNorm : ℝ) * K = Z^M := packed_scale_eq hZ1 V hV hK
    have hZτ1 : 1 ≤ Z^τ := Real.one_le_rpow hZ1.le hτ.le
    set x : ℝ := |t| + height with hxdef
    have hx0 : 0 ≤ x := by rw [hxdef]; positivity
    set h : ℕ := ⌈x/Z^τ⌉₊ with hhdef
    have hwin : |t| + height + Z^τ/2 ≤ (3*h+2 : ℕ)*Z^τ := by
      have h1 : x/Z^τ ≤ h := Nat.le_ceil _
      rw [div_le_iff₀ (zero_lt_one.trans_le hZτ1)] at h1
      push_cast
      have : 0 ≤ (h:ℝ)*Z^τ := by positivity
      rw [← hxdef]
      linarith
    have hhle : (h:ℝ) ≤ |t| + height + 1 := by
      have h1 := Nat.ceil_lt_add_one (div_nonneg hx0 (zero_lt_one.trans_le hZτ1).le)
      rw [← hhdef] at h1
      have h2 : x/Z^τ ≤ x := div_le_self hx0 hZτ1
      linarith
    have hgate4 : (3 + 3*(((B+1)*(h+1) : ℕ) : ℝ)*Z^τ)^4 ≤ (Z^d)^vg :=
      height_gate hZ1.le hτ.le hc0.le hcτ hZg (base := x) (by linarith) (by linarith)
    have hgate2 : (3 + 3*(((B+1)*(h+1) : ℕ) : ℝ)*Z^τ)^2 ≤ (Z^d)^vg := by
      have h1 : (1:ℝ) ≤ 3 + 3*(((B+1)*(h+1) : ℕ) : ℝ)*Z^τ := by
        have : (0:ℝ) ≤ 3*(((B+1)*(h+1) : ℕ) : ℝ)*Z^τ := by positivity
        linarith
      exact (pow_le_pow_right₀ h1 (by norm_num)).trans hgate4
    -- the natural state at scale `N(V)K = Z^M`
    let st := packedState (anchors j) (internalQ Q η₀) Φ bΦ Z
      (((Ideal.span {V}).absNorm : ℝ) * K) M (ε/8) hZ1.le hM0 (by positivity) hUpos hUM hΦ
      hΦpos (hZa j)
    have hwidth : st.width ≤ Mcap := by
      change M + ε/8 ≤ Mmax + ε/8
      linarith
    have hQM : st.fixedModulus ≤ rayM := inf_le_left.trans hQ
    have hQη : st.fixedModulus ≤ η₀.modulus := inf_le_right
    -- sublattice packing
    have hpack := Packet.packed_energy_le (anchors j) (fixedBadMask*idealGenerator 1) V hV t
      (p.profile 0) (p.profile 1) (9/4) (9/4) X₁ X₂
      ((p.support 0).trans Set.Icc_subset_Iic_self) ((p.support 1).trans Set.Icc_subset_Iic_self)
      hX₁ hX₂ (fun i => primePool rayM H 2 (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) (initialKeep (anchors j) (internalQ Q η₀)) Φ hΦpos K hK
    let Lw := lowRow rayM H hH st η₀ hQM hQη e (((h+1 : ℕ) : ℝ)*Z^τ) q
    have hsplit := energy_split st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayM H 2 (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) X₁ X₂ st.radial.keep Lw st.radial.profile st.radial.scale bΦ
      st.radial.scale_pos st.radial_support
    -- HIGH rows
    have hl₁' : length Z X₁ ≤ Lp := hl₁.trans (le_max_left _ _)
    have hl₂' : length Z X₂ ≤ Lp := hl₂.trans (le_max_left _ _)
    have hhigh := hZH.2.2 j q hq st rfl rfl hM₁ hwidth hQM hQη h T θ w σ v t height hw hwm
      (fun i => (hwm i).trans (hmeshOld.trans ((min_le_right _ _).trans (min_le_right _ _))))
      hσ₁ hσ₂ hh hv hwin hhle hgate4 p X₁ X₂ hX₁ hX₂ hl₁' hl₂'
    have hhighB : energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => primePool rayM H 2 (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i => Z^(w i)) X₁ X₂ (fun z => st.radial.keep z ∧ ¬ Lw z)
        st.radial.profile st.radial.scale ≤
        KH*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
          (1+|t|+height)^(degN + k + degP + degZ + J)*
          Z^(M + max (q*need) (high q Pl (∑ i, w i) M) + ε) := by
      refine hhigh.trans (scale_le hKH.le (by linarith) hdg (p.control_nonneg SH) hcH hbase
        (by omega) hZ1.le ?_)
      have : (2*ε₁*d*(Fintype.card α + 1) + loss*Mcap + τ*J+ε/16+ε/16) ≤ ε/8+ε/8+ε/16+ε/16+ε/16 := by
        have e1 : 2*ε₁*d*((Fintype.card α : ℝ) + 1) = ε/8 := hε₁d
        linarith
      change M + high q Pl (∑ i, w i) M +
        (2*ε₁*d*(Fintype.card α + 1) + loss*Mcap + τ*J+ε/16+ε/16) ≤ _
      linarith
    -- LOW rows
    have hw' : ∀ i, 0 ≤ extend T w 0 i := extend_forall T w 0 (fun x => 0 ≤ x) hw le_rfl
    have hwm' : ∀ i, extend T w 0 i ≤ max 0 mesh :=
      extend_forall T w 0 (fun x => x ≤ max 0 mesh) (fun i => (hwm i).trans (le_max_right _ _))
        (le_max_left _ _)
    have hwr' : ∀ i, extend T w 0 i / d ≤ 1/d :=
      fun i => div_le_div_of_nonneg_right ((hwm' i).trans hm1) hd.le
    have hσ₁' : ∀ i, (33/50:ℝ) ≤ extend T σ (33/50) i :=
      extend_forall T σ (33/50) (fun x => 33/50 ≤ x) hσ₁ le_rfl
    have hσ₂' : ∀ i, extend T σ (33/50) i ≤ 33/50 :=
      extend_forall T σ (33/50) (fun x => x ≤ 33/50) hσ₂ le_rfl
    have hv' : ∀ i, |extend T v 0 i| ≤ height :=
      extend_forall T v 0 (fun x => |x| ≤ height) hv (by simpa using hh)
    have hwinL : ∀ i, |t + extend T v 0 i| + Z^τ/2 ≤ (3*h+2 : ℕ)*Z^τ := by
      intro i
      have := abs_add_le t (extend T v 0 i)
      have := hv' i
      linarith
    have hsT : ∑ i ∈ T, extend T w 0 i = ∑ i, w i := sum_extend T w 0
    have hlowB : energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => primePool rayM H 2 (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i => Z^(w i)) X₁ X₂ (fun z => st.radial.keep z ∧ Lw z)
        st.radial.profile st.radial.scale ≤
        ((max 1 CL)^N*(CP + CZ))*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
          (1+|t|+height)^(degN + k + degP + degZ + J)*
          Z^(M + max (q*need) (high q Pl (∑ i, w i) M) + ε) := by
      by_cases hfall : B₀ * M < Pl
      · -- the ordinary lengths alone leave the face: erase every slot
        have hneedS : need = ∑ i, w i := deletionNeed_eq_self_of_lengths hL hs0 hfall
        have hlow := hZL.2 q (by linarith) (by linarith) st rfl hwidth hQM hQη h
          (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t T ∅
          (Finset.empty_subset _) (fun i _ => hw' i) (fun i _ => hwr' i)
          (fun i _ => hσ₁' i) (fun i _ => hσ₂' i) (fun i _ => hwinL i) hgate2
          (p.profile 0) (p.profile 1) X₁ X₂ (mul_pos hX₁ hX₂).le
        simp only [extend_coe] at hlow
        have hz := hZZ.2 (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t
          height (fun i hi => absurd hi (Finset.notMem_empty i))
          (fun i hi => absurd hi (Finset.notMem_empty i))
          (fun i hi => absurd hi (Finset.notMem_empty i))
          (fun i hi => absurd hi (Finset.notMem_empty i)) hh
          (fun i hi => absurd hi (Finset.notMem_empty i)) st rfl rfl hwidth ∅
          (Finset.Subset.refl _) p X₁ X₂ hX₁ hX₂ (le_rpow_of_length_le hZ1 hl₁)
          (le_rpow_of_length_le hZ1 hl₂)
        rw [Finset.sum_empty, mul_zero, add_zero] at hz
        have hcard : (T \ ∅).card ≤ N := (Finset.card_le_univ _)
        have hsum : ∑ i ∈ T \ ∅, extend T w 0 i = ∑ i, w i := by
          rw [Finset.sdiff_empty, hsT]
        rw [hsum] at hlow
        refine hlow.trans ?_
        have hE0 := energy_nonneg st.character st.mask 1 t (p.profile 0) (p.profile 1)
          (fun i : (∅ : Finset α) => primePool rayM H 2 (Z^(extend T w 0 i)))
          (fun (i : (∅ : Finset α)) I =>
            idealCoeff (relativeCharacter rayM H hH η₀ (extend T θ 1 i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(extend T w 0 i))
              (extend T σ (33/50) i) (extend T v 0 i) I)
          (fun i : (∅ : Finset α) => Z^(extend T w 0 i)) X₁ X₂
          st.radial.keep st.radial.profile st.radial.scale (fun z => st.radial.nonneg z)
        refine low_total_le hCL hCZ.le hZ1.le (by positivity) hcard hdg (p.control_nonneg SZ)
          hcZ hbase (by omega) (by linarith) ?_ hE0 hz
        change 2*ε₁*d*N + q*∑ i, w i + (M + ε/8 + ε/4) ≤ _
        have e2 : q*∑ i, w i = q*need := by rw [hneedS]
        linarith
      · -- paid partial deletion into the parent face
        replace hfall := not_lt.mp hfall
        have hneeds : need ≤ ∑ i, w i := deletionNeed_le_self hs0
        obtain ⟨F, hFT, hlo, hhi⟩ := greedy_deletion T (extend T w 0) (max 0 mesh) need
          (le_max_left _ _) hneed0 (fun i _ => hw' i) (fun i _ => hwm' i)
          (by rw [hsT]; exact hneeds)
        have hsplitT : ∑ i ∈ F, extend T w 0 i + ∑ i ∈ T \ F, extend T w 0 i = ∑ i, w i :=
          (sum_retained_add_deleted T F hFT (extend T w 0)).trans hsT
        have hF0 : 0 ≤ ∑ i ∈ F, extend T w 0 i := Finset.sum_nonneg (fun i _ => hw' i)
        have hface' := retained_in_face (del := ∑ i ∈ T \ F, extend T w 0 i) hL
          hface.2.2.le hM0 hfall hlo (by linarith)
        have hsF : ∑ i : F, extend T w 0 i = ∑ i ∈ F, extend T w 0 i :=
          Finset.sum_coe_sort F (extend T w 0)
        have hadm : (QRH.Record1252270103Source.globalFace B₀ L₀ c₀).Admissible
            (length Z X₁) (length Z X₂) (∑ i : F, extend T w 0 i) M := by
          rw [QRH.Record1252270103Source.globalFace_admissible_iff (length_nonneg Z X₁ hZ1)
            (length_nonneg Z X₂ hZ1) (by rw [hsF]; exact hF0) hL.le, hsF]
          have e : ∑ i ∈ F, extend T w 0 i = (∑ i, w i) - ∑ i ∈ T \ F, extend T w 0 i := by
            linarith
          rw [e]
          exact hface'
        have hlow := hZL.2 q (by linarith) (by linarith) st rfl hwidth hQM hQη h
          (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t T F hFT
          (fun i _ => hw' i) (fun i _ => hwr' i) (fun i _ => hσ₁' i) (fun i _ => hσ₂' i)
          (fun i _ => hwinL i) hgate2 (p.profile 0) (p.profile 1) X₁ X₂ (mul_pos hX₁ hX₂).le
        simp only [extend_coe] at hlow
        have hp := hZP j F (fun i : F => extend T θ 1 i) (fun i : F => extend T w 0 i)
          (fun i : F => extend T σ (33/50) i) (fun i : F => extend T v 0 i) t height
          (fun i => hw' i) (fun i => hwm' i) (fun i => hσ₁' i) (fun i => hσ₂' i) hh
          (fun i => hv' i) M hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
        rw [← hUM] at hp
        have hcard : (T \ F).card ≤ N := Finset.card_le_univ _
        have hE0 := energy_nonneg st.character st.mask 1 t (p.profile 0) (p.profile 1)
          (fun i : F => primePool rayM H 2 (Z^(extend T w 0 i)))
          (fun (i : F) I =>
            idealCoeff (relativeCharacter rayM H hH η₀ (extend T θ 1 i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(extend T w 0 i))
              (extend T σ (33/50) i) (extend T v 0 i) I)
          (fun i : F => Z^(extend T w 0 i)) X₁ X₂
          st.radial.keep st.radial.profile st.radial.scale (fun z => st.radial.nonneg z)
        refine hlow.trans (low_total_le hCL hCP.le hZ1.le (by positivity) hcard hdg
          (p.control_nonneg SP) hcP hbase (by omega) (by linarith) ?_ hE0 hp)
        have e2 : q*∑ i ∈ T \ F, extend T w 0 i ≤ q*need + q*max 0 mesh := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left hhi (by linarith)
        have e3 : q*max 0 mesh ≤ ε/8 := by
          have : q*max 0 mesh ≤ 1*max 0 mesh :=
            mul_le_mul_of_nonneg_right (by linarith) (le_max_left _ _)
          linarith
        linarith
    -- assembly
    have hY0 : 0 ≤ QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
        (1+|t|+height)^(degN + k + degP + degZ + J)*
        Z^(M + max (q*need) (high q Pl (∑ i, w i) M) + ε) := by
      have := p.control_nonneg S
      have := Real.rpow_nonneg hZ0.le (M + max (q*need) (high q Pl (∑ i, w i) M) + ε)
      positivity
    refine hpack.trans (hsplit.trans_le ?_)
    calc _ ≤ ((max 1 CL)^N*(CP + CZ))*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
          (1+|t|+height)^(degN + k + degP + degZ + J)*
          Z^(M + max (q*need) (high q Pl (∑ i, w i) M) + ε) +
        KH*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
          (1+|t|+height)^(degN + k + degP + degZ + J)*
          Z^(M + max (q*need) (high q Pl (∑ i, w i) M) + ε) := add_le_add hlowB hhighB
      _ = ((max 1 CL)^N*(CP + CZ) + KH)*(QuadraticInitialBound.diagonalControl Φ*
          (p.control S)^2*(1+|t|+height)^(degN + k + degP + degZ + J)*
          Z^(M + max (q*need) (high q Pl (∑ i, w i) M) + ε)) := by ring
      _ ≤ (CN + (max 1 CL)^N*(CP + CZ) + KH)*(QuadraticInitialBound.diagonalControl Φ*
          (p.control S)^2*(1+|t|+height)^(degN + k + degP + degZ + J)*
          Z^(M + max (q*need) (high q Pl (∑ i, w i) M) + ε)) :=
          mul_le_mul_of_nonneg_right (by linarith) hY0
      _ = _ := by ring


/-- Each retained adaptive policy satisfies the scalar laws used by the actual histogram. -/
theorem adaptive_high_law (policy : AdaptivePrice.Policy) :
    HighLaw policy.floor (fun q => AdaptivePrice.supWith (policy.gain q) q) where
  floor_ge := by linarith [policy.floor_mem.1]
  zero hq hν hs := AdaptivePrice.policy_zero_energy policy hq hν le_rfl hs
  joint hq hν hδ hM hs := AdaptivePrice.policy_jointRate_energy policy hq hν hδ hM hs
  full := by
    intro q ν P s M hq hν hs
    have hνg : ν ∈ Icc (29/50:ℝ) (3/4) :=
      ⟨policy.floor_mem.1.trans (hq.1.trans hν.1), hν.2⟩
    have hκ := policy.retained_bounds hq hν
    have hk0 : 0 ≤ AdaptivePrice.retainedSlope (policy.gain q) ν :=
      (AdaptivePrice.retainedSlope_pos (policy.gain_mem q hq) hνg).le
    have hext : 0 ≤ (ν-AdaptivePrice.k ν+policy.gain q)*max (s-M/10) 0 :=
      mul_nonneg (by dsimp [AdaptivePrice.retainedSlope] at hκ; linarith [hκ.2]) (le_max_right _ _)
    have hslot := mul_le_mul_of_nonneg_right
      (show ν-AdaptivePrice.retainedSlope (policy.gain q) ν ≤ 1 by linarith [hν.2]) hs
    have hb := AdaptivePrice.le_supWith (policy.gain_mem q hq)
      (policy.floor_mem.1.trans hq.1) hν P s M
    unfold AdaptivePrice.gWith at hb
    nlinarith

/-- Actual LOW/HIGH assembly for every policy used by the finite source chains. -/
theorem policyPackedProvider_of_whole_count
    (hwhole : NaturalCount.WholeJointCountOn (57/100)) :
    AdaptiveSourceChains.PolicyPackedProvider := by
  intro policy φ B₀ L₀ c₀ B L c A D hL hφ hβ hB hB1 hc hp
  exact priced_source_of_whole_count hwhole policy.floor
    (fun q => AdaptivePrice.supWith (policy.gain q) q) (adaptive_high_law policy)
    B₀ L₀ c₀ (9/10) 4 4 hL hβ ⟨hB,hB1,hc⟩ (by norm_num) (by norm_num) hp
    (AdaptiveLedger.densQ policy φ B₀ L₀ L A D (QRH.SilDensitySplit.Hybrid.cross B₀ L₀ B L))
    (AdaptiveLedger.densQ_mem policy φ B₀ L₀ L A D (QRH.SilDensitySplit.Hybrid.cross B₀ L₀ B L))
    (AdaptiveLedger.stepData policy φ B₀ L₀ c₀ B L c A D hL).price
    (fun _ _ _ _ => rfl)

/-- The remaining analytic premise is the literal selected all-source operator bound. -/
theorem policyPackedProvider (hnorm : NaturalCount.ActualSelectedSlotNorm) :
    AdaptiveSourceChains.PolicyPackedProvider :=
  policyPackedProvider_of_whole_count
    (NaturalCount.wholeJointCountOn_of_actualSelectedSlotNorm hnorm (57/100) le_rfl)

end
end Qrh.JointDetector.AdaptiveSupplier

#print axioms Qrh.JointDetector.AdaptiveSupplier.supplier_high_branch

#print axioms Qrh.JointDetector.AdaptiveSupplier.priced_source_of_whole_count

#print axioms Qrh.JointDetector.AdaptiveSupplier.policyPackedProvider
