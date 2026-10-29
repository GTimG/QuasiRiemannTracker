/- Copyright (c) 2026 Joseph Bebel. -/
/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
The unmarked HIGH adapter retains Sil's literal natural-row/dictionary proof;
the joint histogram preserves both actual pointwise estimates. -/
import Candidate.Local.Qrh.JointDetector.AdaptiveSupplier.High

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


/-- One-scale form of the literal whole natural joint count. It is used only
as a count in the HIGH summation, and will be instantiated from WholeJointCountOn. -/
def JointCountAt {α κ : Type} [Fintype α] [DecidableEq α] [Fintype κ]
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
  ∀ (b δ T' : ℝ), (1+(29/50:ℝ))/2 ≤ b → b ≤ 7/8 →
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
theorem joint_high_branch {α : Type} [Fintype α] [DecidableEq α]
    (policy : AdaptivePrice.Policy)
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ : ℝ) (hbΦ : 1 ≤ bΦ) {κ : Type} [Fintype κ] (anchors : κ → Character)
    (η₀ : Character) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hβ' : HeckeZeroSupremum.beta ≤ 7/8)
    (Mmin Mcap smin mesh Lplain ε₁ e kap v d loss budget : ℝ)
    (hMmin : 0 < Mmin) (hL : 0 ≤ Lplain) (hε₁ : 0 < ε₁)
    (he : 0 < e) (he' : e < 1/1000) (hkap : 0 < kap) (hkap' : kap ≤ 1)
    (hv : 0 ≤ v) (hd : 0 < d) (hdsupply : Mcap+0+1 ≤ d)
    (hslotBudget : 8*e*(1/d)+kap ≤ ε₁)
    (hplainBudget : 12*e*(Lplain/d+2)+8*kap+2*v ≤ ε₁)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hbudget : 0 < budget)
    (Jc : ℕ) (Cc : ℝ) (hCc : 0 < Cc)
    (hcnt : ∀ᶠ Z : ℝ in atTop,
      JointCountAt (α:=α) rayM H hH W anchors η₀ Mmin Mcap smin mesh loss bΦ Jc Cc Z) :
    ∃ J : ℕ, ∀ τ : ℝ, 0 < τ → ∃ K : ℝ,0 < K ∧ ∃ S : Finset (ℕ×ℕ),
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ 2 < Z^τ ∧
    ∀ (j : κ) (q : ℝ),q ∈ Icc policy.floor (3/4) →
    ∀ st : NaturalState Z 0 bΦ, st.character=anchors j → st.puncture=1 →
      Mmin ≤ st.rowWidth → st.width ≤ Mcap →
    ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus) (h : ℕ)
      (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ) (t height : ℝ),
    (∀ k,0 ≤ w k) → (∀ k,w k ≤ mesh) → (∀ k,w k ≤ 1) →
    (∀ k,(33/50:ℝ) ≤ σ k) → (∀ k,σ k ≤ 33/50) →
    0 ≤ height → (∀ k,|v' k| ≤ height) → smin ≤ ∑ k,w k →
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
      Z^(st.rowWidth+AdaptivePrice.supWith (policy.gain q) q (length Z X₁+length Z X₂)
        (∑ k,w k) st.rowWidth+(2*ε₁*d*(Fintype.card α+1)+loss*Mcap+τ*J+budget)) := by
  obtain ⟨Jz,Cz,hCz,hzero⟩ := high_row_count rayM H hH anchors η₀ loss hloss
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
    hsmall hwin hhle hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
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
    Z^(M+AdaptivePrice.supWith (policy.gain q) q Pl s M+
      (2*ε₁*d*(Fintype.card α+1)+loss*Mcap+τ*J+budget))
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
      have hb : (79/100:ℝ) ≤ b := by
        have hf := policy.floor_mem.1
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
        have hh := hzero (by linarith : 0 < bΦ) j st hchar hu hQM hQη b _ hb hc.2 (by positivity) rows hguards
        have hρ : unmarkedDensity ν ≤ 1 :=
          QRH.SilDensitySplit.Density.unmarkedDensity_le_one (by linarith [policy.floor_mem.1,hq.1,hν.1]) hν.2
        have he := normalize_count hCz.le (show Cz ≤ Cz+Cc by linarith) hbΦ hZ1 hMc hρ hloss.le hloss1
          (show Jz ≤ J by dsimp [J]; omega) hcB hhle hh0 hZτ1 hh
        change (rows.card:ℝ) ≤ commonC*Z^(unmarkedDensity ν*M+loss*Mcap) at he
        have hρeq : unmarkedDensity ν=1-AdaptivePrice.k ν := by
          unfold unmarkedDensity AdaptivePrice.k
          rw [show 3*(5-2*ν)=15-6*ν by ring]
        rw [hρeq] at he
        exact he
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
          have hk := (AdaptivePrice.k_range ⟨policy.floor_mem.1.trans (hq.1.trans hν.1),hν.2⟩).1
          unfold AdaptivePrice.jointRate
          split_ifs <;> exact (min_le_left _ _).trans (by linarith)
        exact normalize_count hCc.le (by linarith : Cc ≤ Cz+Cc) hbΦ hZ1 hMc hρ hloss.le hloss1
          (show Jc ≤ J by dsimp [J]; omega) hcB hhle hh0 hZτ1 hh
      have hf := finite_joint_bin_energy policy rayM H hH st η₀ W θ w σ v' t p X₁ X₂ rows
        ν Pl s M (Kr*(p.control S)^2) commonC (2*ε₁*d*(Fintype.card α+1)) (loss*Mcap) step n
        hZ1.le hq hν hM0 hs (by positivity) (by dsimp [commonC]; positivity) hstep hn htop hX₁ hX₂
        (fun z hz => (hpair z hz).1) (fun z hz => (hpair z hz).2) hzeroN hjointN
      refine hf.trans ?_
      dsimp [G,baseK,commonC]
      calc
        _ = ((n+1:ℕ)*Kr*(Cz+Cc)*bΦ^2*(1+6*(B:ℝ))^J)*(p.control S)^2*(1+|t|+height)^J*
          (Z^(τ*J)*Z^(M+AdaptivePrice.supWith (policy.gain q) q Pl s M+
            2*ε₁*d*(Fintype.card α+1)+loss*Mcap+step*s)) := by ring
        _ = ((n+1:ℕ)*Kr*(Cz+Cc)*bΦ^2*(1+6*(B:ℝ))^J)*(p.control S)^2*(1+|t|+height)^J*
          Z^(M+AdaptivePrice.supWith (policy.gain q) q Pl s M+
            (2*ε₁*d*(Fintype.card α+1)+loss*Mcap+τ*J+step*s)) := by
          rw [← Real.rpow_add hZ0]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)) (by positivity)
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
        Z^(M+AdaptivePrice.supWith (policy.gain q) q Pl s M+
          (2*ε₁*d*(Fintype.card α+1)+loss*Mcap+τ*J+budget))
    dsimp only [G]
    ring

end
end
end Qrh.JointDetector.AdaptiveSupplier

#print axioms Qrh.JointDetector.AdaptiveSupplier.joint_high_branch
