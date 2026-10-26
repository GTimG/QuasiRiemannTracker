/- The four-way split of a LOW child of the first step at its natural state: the old moment (branch O), the reflection
of a plain factor (branch R), the second step with its HIGH part in count form (branch L2) and the direct deletion
into the old region (branch D). Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.LowBranch.DirectMain
import Candidate.Cycle63.Moment.LowBranch.Reflection
import Candidate.Cycle63.Moment.LowBranch.SecondStepReturn
import Candidate.Cycle63.Moment.LowBranch.WidenedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentEnergyPaidBands

/-- The first test of the split: after the fixed deletion of the slot length `del` from the slot length `zJ`, the
plain lengths `x₁`, `x₂` and the slots at the price `κ` fit in the width `W`. -/
def OldRegionTest (x₁ x₂ κ zJ del W : ℝ) : Prop := x₁ + x₂ + 6*κ*(zJ - del) ≤ W

/-- The second test of the split: after the fixed deletion the state exceeds the old capacity by at most `δR`, and
one plain factor, reflected with the slack `ξ`, leaves the state in the old region with the margin `δR`. -/
def ReflectionTest (x₁ x₂ κ zJ del W δR ξ : ℝ) : Prop :=
  x₁ + x₂ + 6*κ*(zJ - del) ≤ W + δR ∧
    (max 0 (W - x₂ + ξ) + x₁ + 6*κ*(zJ - del) + δR ≤ W ∨
      max 0 (W - x₁ + ξ) + x₂ + 6*κ*(zJ - del) + δR ≤ W)

/-- The control of the profiles grows with the set of the sources. -/
theorem profiles_control_mono {a b : ℝ} {S S' : Finset (ℕ × ℕ)} (h : S ⊆ S') (p : Profiles a b) :
    p.control S ≤ p.control S' :=
  mul_le_mul (control_mono h (p.profile 0)) (control_mono h (p.profile 1)) (sourceControl_nonneg _ _)
    (sourceControl_nonneg _ _)

/-- A bound with a larger constant, profile control, height exponent and base exponent. -/
theorem dispatch_mono {Z K K' D c c' h Ret E E' : ℝ} {m m' : ℕ} (hZ : 1 ≤ Z) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hKK : K ≤ K') (hc : 0 ≤ c) (hcc : c ≤ c') (hh : 1 ≤ h) (hmm : m ≤ m') (hE : E ≤ E') (hRet : 0 ≤ Ret) :
    K * D * c ^ 2 * h ^ m * (Z ^ E + Ret) ≤ K' * D * c' ^ 2 * h ^ m' * (Z ^ E' + Ret) := by
  have hc' : 0 ≤ c' := hc.trans hcc
  have hK' : 0 ≤ K' := hK.trans hKK
  have hZE : Z ^ E ≤ Z ^ E' := Real.rpow_le_rpow_of_exponent_le hZ hE
  have hZ0 : 0 ≤ Z ^ E := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hpow : h ^ m ≤ h ^ m' := pow_le_pow_right₀ hh hmm
  have hh0 : 0 ≤ h ^ m := by positivity
  have h1 : K * D ≤ K' * D := mul_le_mul_of_nonneg_right hKK hD
  have h2 : K * D * c ^ 2 ≤ K' * D * c' ^ 2 :=
    mul_le_mul h1 (pow_le_pow_left₀ hc hcc 2) (sq_nonneg c) (mul_nonneg hK' hD)
  have h3 : K * D * c ^ 2 * h ^ m ≤ K' * D * c' ^ 2 * h ^ m' :=
    mul_le_mul h2 hpow hh0 (mul_nonneg (mul_nonneg hK' hD) (sq_nonneg c'))
  exact mul_le_mul h3 (add_le_add hZE le_rfl) (add_nonneg hZ0 hRet)
    (mul_nonneg (mul_nonneg (mul_nonneg hK' hD) (sq_nonneg c')) (by positivity))


/-- The energy of a state after the fixed deletion is at most the factor of the deleted slots times the energy of the
remaining state; a bound of the remaining state with a returned part gives the bound with the returned part scaled by
the factor of the deleted slots. -/
theorem dispatch_assemble {EJ Erem Fa Pf Z e0 Kr D c h V E1 : ℝ} {m : ℕ} (hZ : 0 < Z) (hPf : 0 ≤ Pf)
    (hFa : Fa ≤ Pf * Z ^ e0) (hfix : EJ ≤ Fa * Erem)
    (hrem : Erem ≤ Kr * D * c ^ 2 * h ^ m * (Z ^ E1 + V)) (hErem : 0 ≤ Erem) :
    EJ ≤ Pf * Kr * D * c ^ 2 * h ^ m * (Z ^ (e0 + E1) + Z ^ e0 * V) := by
  have hZe : 0 ≤ Z ^ e0 := Real.rpow_nonneg hZ.le _
  calc EJ ≤ Fa * Erem := hfix
    _ ≤ (Pf * Z ^ e0) * Erem := mul_le_mul_of_nonneg_right hFa hErem
    _ ≤ (Pf * Z ^ e0) * (Kr * D * c ^ 2 * h ^ m * (Z ^ E1 + V)) :=
        mul_le_mul_of_nonneg_left hrem (mul_nonneg hPf hZe)
    _ = Pf * Kr * D * c ^ 2 * h ^ m * (Z ^ (e0 + E1) + Z ^ e0 * V) := by
        rw [Real.rpow_add hZ]; ring

/-- The constants of the four branches are at most their combination. -/
theorem dispatch_constants {Pf KD Cr C₀ C₁ C₂ : ℝ} (hPf : 0 ≤ Pf) (hKD : 0 ≤ KD) (hCr : 0 ≤ Cr) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    Pf * (C₀ + C₁) ≤ Pf * (C₀ + C₁ + Cr * (C₁ + 1) + C₂) + KD ∧
    Pf * (C₀ + Cr * (C₁ + 1)) ≤ Pf * (C₀ + C₁ + Cr * (C₁ + 1) + C₂) + KD ∧
    Pf * C₂ ≤ Pf * (C₀ + C₁ + Cr * (C₁ + 1) + C₂) + KD ∧
    KD ≤ Pf * (C₀ + C₁ + Cr * (C₁ + 1) + C₂) + KD := by
  have hCr1 : 0 ≤ Cr * (C₁ + 1) := mul_nonneg hCr (by linarith)
  have hP : 0 ≤ Pf * (C₀ + C₁ + Cr * (C₁ + 1) + C₂) := mul_nonneg hPf (by linarith)
  refine ⟨?_, ?_, ?_, le_add_of_nonneg_left hP⟩
  · exact (mul_le_mul_of_nonneg_left (by linarith) hPf).trans (le_add_of_nonneg_right hKD)
  · exact (mul_le_mul_of_nonneg_left (by linarith) hPf).trans (le_add_of_nonneg_right hKD)
  · exact (mul_le_mul_of_nonneg_left (by linarith) hPf).trans (le_add_of_nonneg_right hKD)

variable {α : Type*} [Fintype α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The four-way split of a LOW child at its natural state. For a state of width at most `nominal + δ`, slots of
total length `Σ_J w` from which the length `del` is deleted at the price `q` on the LOW rows, the energy over the LOW
rows is at most the old moment at the width `nominal + δ`, raised by the reflection loss `εR`, the amplifier `amp`
less the reserve, the allowance `X`, and the padding at the rate of the direct deletion, plus the returned part `Ret`,
which is zero unless the state is wide and the second step is run, and is then the count form of the HIGH part of the
second step, which pays at the row width of the state and has at most `Kclass` classes. The tests are the old-region
test, the reflection test, `wide` (the width of the child is at least the least width of the second step) and,
otherwise, the direct deletion into the old region. The facts of the branches are hypotheses: `q * del ≤ amp - reserve`
pays the fixed deletion, `hD` gives the overshoot of the direct deletion and `hgate` that the second step applies.
The lengths `w j` of the slots are at most the slot bound `Lslot` of the second step, which is a parameter below the
common mesh of the old moment (`hLslot : Lslot ≤ commonMesh Mcap Bmask L εold`): the old moment, the reflection and the
direct deletion hold for every smaller slot bound (`positiveAt_of_le`). -/
theorem low_state_dispatch {Base : Type}
    (W : ℝ → ℂ) (A B ap bp bΦ Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hLslot : Lslot ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (ξ δR εR : ℝ) (hξ : 0 < ξ) (hδR : 0 ≤ δR) (hεR : 0 < εR)
    (base : Character → Base → Character) (Bnorm : ℝ)
    (Applicable : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (stepTwo : SecondStepReturnAt (α := α) M H hH base W B ap bp bΦ Bmask L Lslot lo hi Mcap εold Bnorm Applicable) :
    ∀ η₀ : Character, ∀ Q : Ideal O,
      ∀ hQM : Q ≤ M, internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ Kclass : ℝ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height mesh a : ℝ) (i : ℕ),
      (∀ j, 0 ≤ w j) →
      (∀ j, w j ≤ Lslot) →
      (∀ j ∈ J, w j/d ≤ Rwidth) →
      0 ≤ mesh → (∀ j ∈ J, w j ≤ mesh) →
      (∀ j, lo ≤ σ j) → (∀ j, σ j ≤ hi) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
      51/100 ≤ a → a ≤ (1+q)/2 →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ s : NaturalState Z Bmask bΦ, ∀ hQ : s.fixedModulus = internalQ Q η₀, s.width ≤ Mcap →
      ∀ p : Profiles ap bp, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      ∀ (nominal δ padding amp reserve del X G : ℝ) (wide : Prop) (v₁ : O) (T Wl lengthL ampL lossL : ℝ),
      s.width - nominal ≤ δ → 0 ≤ δ → 0 ≤ padding → 0 ≤ del → 0 ≤ X → q * del ≤ amp - reserve →
      nominal + δ ≤ Mcap → nominal + δ ≤ L →
      (¬ wide → 0 ≤ G ∧
        length Z X₁ + length Z X₂ + (6*Cycle63.Optimization.slotPrice)*(∑ j ∈ J, w j) - nominal ≤ G + padding ∧
        q/(6*Cycle63.Optimization.slotPrice)*G ≤ amp + X - reserve) →
      (wide → ∀ (hsW : s.width ≤ nominal + δ) (R : Finset α), R ⊆ J → R ≠ J → (∑ j ∈ R, w j) ≤ del + mesh →
        del ≤ ∑ j ∈ R, w j →
        ¬ OldRegionTest (length Z X₁) (length Z X₂) Cycle63.Optimization.slotPrice (∑ j ∈ J, w j) (∑ j ∈ R, w j)
          (nominal + δ) →
        ¬ ReflectionTest (length Z X₁) (length Z X₂) Cycle63.Optimization.slotPrice (∑ j ∈ J, w j)
          (∑ j ∈ R, w j) (nominal + δ) δR ξ →
        Applicable η₀ Z (widenState s (nominal + δ) hsW) v₁ (length Z X₁) (length Z X₂) (∑ j ∈ J \ R, w j) Wl T
          lengthL ampL lossL) →
      let hQM : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
      let hQη : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
      let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      ∃ Ret : ℝ, 0 ≤ Ret ∧
        (Ret = 0 ∨ ∃ (unit₂ : Bool → FirstSourceLabel → O)
            (Hb : (b : Bool) → SecondStepHighCount M H hH (base η₀) η₀ Z Bnorm T b v₁ (unit₂ b)),
            (∀ b, (Hb b).Pays Cycle63.Optimization.secondJunction s.rowWidth lengthL ampL lossL) ∧
            (∀ b, (Fintype.card (Hb b).Class : ℝ) ≤ Kclass) ∧
            Ret = Z^(2*ε*d*(Fintype.card α : ℝ) + q*(del + mesh)) * ∑ b, (Hb b).value) ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I *
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
          s.radial.profile s.radial.scale ≤
        K * diagonalControl s.radial.profile * (p.control S) ^ 2 * (1 + |t| + height) ^ degree *
          (Z^(nominal + δ + amp - reserve + X + εold + εR + 2*ε*d*(Fintype.card α : ℝ) +
            q/(6*Cycle63.Optimization.slotPrice)*padding + q*mesh) + Ret) := by
  obtain ⟨degI, SI, hinc⟩ := original_incumbent (α := α) M H hH W A B ap bp bΦ Bmask L lo hi Mcap εold
    hA hWs hW hB hap hap' hbp hbΦ hBmask hMcap hεold hbeta
  obtain ⟨Cs, hCs, hslots⟩ := actual_low_slots M H hH W A B hA hWs hW Rwidth dmax τ ε e κ η lo hi bΦ Mcap Bmask
    margin d hRw hdmax hτ hε he he' hκ hη hbudget hbΦ.le hmargin hd hdsupply hdm q hq₀ hq₁
  have hκs : (1:ℝ)/6 ≤ Cycle63.Optimization.slotPrice := by
    linarith [Cycle63.Optimization.slotPrice_mem.1]
  obtain ⟨Cr, Jexp, UR, hCr, hSU, hdJ, hrefl⟩ := reflected_remaining_energy_bound (α := α) M H hH W A B ap bp
    bΦ Bmask L Lslot lo hi Mcap εold Cycle63.Optimization.slotPrice
    δR ξ εR degI SI hA hWs hW.continuous hap hap' hbp hbΦ hBmask hMcap.le hεold.le hκs hδR hξ hεR
  obtain ⟨degD, SD, hdirect⟩ := actual_direct_low_main (α := α) M H hH W A B ap bp bΦ Bmask L lo hi Mcap εold
    hA hWs hW hB hap hap' hbp hbΦ hBmask hMcap hεold hbeta Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he
    he' hκ hη hbudget hmargin hd hdsupply hdm q hq₀ hq₁
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨degT, ST, Kc, C₂, hC₂, hstep'⟩ := stepTwo η₀ Q hQM hQ0 hQt hQ72
  refine ⟨max (max Jexp degT) degD, UR ∪ ST ∪ SD, Kc, ?_⟩
  obtain ⟨C₀, C₁, hC₀, hC₁, hold⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CD, C₀D, C₁D, hCD, hC₀D, hC₁D, hD⟩ := hdirect η₀ Q hQM hQ0 hQt hQ72
  have hCD0 : 0 < CD := by linarith
  have hmax0 : 0 < max 1 Cs := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hPf0 : 0 ≤ (max 1 Cs) ^ (Fintype.card α) := by positivity
  have hKD0 : 0 ≤ CD ^ (Fintype.card α) * (C₀D + C₁D) := by positivity
  have hKO0 : 0 ≤ (max 1 Cs) ^ (Fintype.card α) * (C₀ + C₁ + Cr * (C₁ + 1) + C₂) := by positivity
  refine ⟨(max 1 Cs) ^ (Fintype.card α) * (C₀ + C₁ + Cr * (C₁ + 1) + C₂) +
    CD ^ (Fintype.card α) * (C₀D + C₁D), by positivity, ?_⟩
  filter_upwards [hold, hslots η₀, hrefl, hstep', hD] with Z hZold hslot hZr hZs hZd
  refine ⟨hZold.1, ?_⟩
  intro J θ w σ v t height mesh a i hw hwL hwr hmesh hwm hσlo hσhi hheight hv ha ha' hfreq hhigh s hQ hs p X₁
    X₂ hX₁ hX₂ hc₁ hc₂ nominal δ padding amp reserve del X G wide v₁ T Wl lengthL ampL lossL hwidth hδ hpad hdel
    hX hqdel hWMcap hWL hDfacts hgate
  dsimp only
  have hZ0 : 0 < Z := zero_lt_one.trans hZold.1
  have hZ1 : 1 ≤ Z := hZold.1.le
  have hposL := positiveAt_of_le M H hH hZold.2.2 hLslot
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hbase1 : 1 ≤ 1 + |t| + height := by linarith [abs_nonneg t]
  have hκpos := Cycle63.Optimization.slotPrice_pos
  have hrate0 : 0 ≤ q / (6 * Cycle63.Optimization.slotPrice) := by positivity
  have hratepad : 0 ≤ q / (6 * Cycle63.Optimization.slotPrice) * padding := mul_nonneg hrate0 hpad
  have hNnn : 0 ≤ 2 * ε * d * (Fintype.card α : ℝ) := by positivity
  have hmesh0 := hmesh
  -- the constants
  obtain ⟨hKO, hKR, hKL, hKD⟩ := dispatch_constants hPf0 hKD0 hCr.le hC₀.le hC₁.le hC₂.le
  have hUR : UR ⊆ UR ∪ ST ∪ SD := Finset.subset_union_left.trans Finset.subset_union_left
  have hST : ST ⊆ UR ∪ ST ∪ SD := Finset.subset_union_right.trans Finset.subset_union_left
  have hSD : SD ⊆ UR ∪ ST ∪ SD := Finset.subset_union_right
  have hdegR : Jexp ≤ max (max Jexp degT) degD := (le_max_left _ _).trans (le_max_left _ _)
  have hdegI : degI ≤ max (max Jexp degT) degD := hdJ.trans hdegR
  have hdegT : degT ≤ max (max Jexp degT) degD := (le_max_right _ _).trans (le_max_left _ _)
  have hdegD : degD ≤ max (max Jexp degT) degD := le_max_right _ _
  have hctlI : p.control SI ≤ p.control (UR ∪ ST ∪ SD) := profiles_control_mono (hSU.trans hUR) p
  have hctlR : p.control UR ≤ p.control (UR ∪ ST ∪ SD) := profiles_control_mono hUR p
  have hctlT : p.control ST ≤ p.control (UR ∪ ST ∪ SD) := profiles_control_mono hST p
  have hctlD : p.control SD ≤ p.control (UR ∪ ST ∪ SD) := profiles_control_mono hSD p
  -- the slots
  let hQM' : s.fixedModulus ≤ M := by rw [hQ]; exact inf_le_left.trans hQM
  let hQη' : s.fixedModulus ≤ η₀.modulus := by rw [hQ]; exact inf_le_right
  let low := ActualLow M H hH s η₀ hQM' hQη' a e (3 * (i + 1 : ℕ) * Z ^ τ)
  let pay : ℝ := max 1 Cs * Z ^ (2 * ε * d)
  have hpay : 1 ≤ pay := by
    have hpow : 1 ≤ Z ^ (2 * ε * d) := Real.one_le_rpow hZ1 (by positivity)
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) hpow
  by_cases hwd : wide
  · -- the fixed deletion of the LOW slots of the wide child
    have hpayslot : ∀ z, s.radial.keep z → low z → ∀ j ∈ J,
        ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z ^ (w j)))
          (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I *
            annularWeight W (Z ^ (w j)) (σ j) (v j) I) t (Z ^ (w j))‖ ^ 2 ≤ pay * Z ^ (q * w j) := by
      intro z hz hl j hj
      have hf : |t + v j| + Z ^ τ / 2 ≤ (3 * i + 2 : ℕ) * Z ^ τ := by
        have hh := abs_add_le t (v j)
        linarith [hv j]
      exact (hslot.2 s hs hQM' hQη' a i ha ha' (w j) (σ j) t (v j) (hw j) (hwr j hj) (hσlo j) (hσhi j) hf
        hhigh z hz hl (θ j)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 Cs)
          (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hZ0.le _))
    obtain ⟨R, hR, hsum, hcover, hfix⟩ := fixed_low_energy s low J (p.profile 0) (p.profile 1)
      (fun j => primePool M H B (Z ^ (w j)))
      (fun j I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I *
        annularWeight W (Z ^ (w j)) (σ j) (v j) I)
      t X₁ X₂ q del mesh hX₁ hX₂ hq₀ hdel hmesh w (fun _ => pay) (fun j _ => hw j) hwm
      (fun _ _ => zero_le_one.trans hpay) hpayslot
    have hprod : (∏ j ∈ R, pay) ≤ pay ^ (Fintype.card α) := by
      simp only [Finset.prod_const]
      exact pow_le_pow_right₀ hpay ((Finset.card_le_card hR).trans (Finset.card_le_univ J))
    have hpayN : pay ^ (Fintype.card α) =
        (max 1 Cs) ^ (Fintype.card α) * Z ^ (2 * ε * d * (Fintype.card α : ℝ)) :=
      buffer_power_identity (max 1 Cs) Z ε d (Fintype.card α) hZ0
    have hFa : (∏ j ∈ R, pay) * Z ^ (q * (del + mesh)) ≤
        (max 1 Cs) ^ (Fintype.card α) * Z ^ (2 * ε * d * (Fintype.card α : ℝ) + q * (del + mesh)) := by
      calc (∏ j ∈ R, pay) * Z ^ (q * (del + mesh)) ≤ pay ^ (Fintype.card α) * Z ^ (q * (del + mesh)) :=
            mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hZ0.le _)
        _ = (max 1 Cs) ^ (Fintype.card α) * Z ^ (2 * ε * d * (Fintype.card α : ℝ) + q * (del + mesh)) := by
            rw [hpayN, Real.rpow_add hZ0]; ring
    by_cases hRJ : R = J
    · -- no slot remains: the zero-slot moment
      have hrem := remaining_energy_bound M H hH W B ap bp bΦ Bmask L Lslot lo hi Mcap εold
        Cycle63.Optimization.slotPrice Z η₀ Q degI SI
        C₀ C₁ hC₀.le hC₁.le hZold.2.1 hposL J R θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
        hX₁ hX₂ hc₁ hc₂ (Or.inl hRJ)
      have key := dispatch_assemble (V := 0) (Kr := C₀ + C₁) (D := diagonalControl s.radial.profile)
        (c := p.control SI) (h := 1 + |t| + height) (m := degI) (E1 := s.width + εold) hZ0 hPf0 hFa hfix
        (by rw [add_zero]; exact hrem) (natural_energy_nonneg s _ _ _ _ _ _ _ _ _)
      refine ⟨0, le_rfl, Or.inl rfl, ?_⟩
      refine key.trans ?_
      rw [mul_zero]
      exact dispatch_mono hZ1 hdiag (mul_nonneg hPf0 (by positivity)) hKO (p.control_nonneg SI) hctlI hbase1
        hdegI (by linarith only [hqdel, hX, hεR, hratepad, hwidth]) le_rfl
    · have hdR : del ≤ ∑ j ∈ R, w j := hcover.resolve_left hRJ
      have hsplit := Finset.sum_sdiff hR (f := w)
      by_cases hO : OldRegionTest (length Z X₁) (length Z X₂) Cycle63.Optimization.slotPrice (∑ j ∈ J, w j)
          (∑ j ∈ R, w j) (nominal + δ)
      · -- branch (O): the remaining state is in the old region
        have hsW : s.width ≤ nominal + δ := by linarith only [hwidth]
        let s' := widenState s (nominal + δ) hsW
        have hs'w : s'.width = nominal + δ := widenState_width s _ hsW
        have hcap : R = J ∨ length Z X₁ + length Z X₂ + 6 * Cycle63.Optimization.slotPrice *
            (∑ j ∈ J \ R, w j) ≤ s'.width := by
          right
          unfold OldRegionTest at hO
          rw [hs'w]
          have h6 : 6 * Cycle63.Optimization.slotPrice * (∑ j ∈ J \ R, w j) =
              6 * Cycle63.Optimization.slotPrice * ((∑ j ∈ J, w j) - ∑ j ∈ R, w j) := by
            congr 1; linarith only [hsplit]
          linarith only [hO, h6]
        have hrem := remaining_energy_bound M H hH W B ap bp bΦ Bmask L Lslot lo hi Mcap εold
          Cycle63.Optimization.slotPrice Z η₀ Q degI
          SI C₀ C₁ hC₀.le hC₁.le hZold.2.1 hposL J R θ w σ v t height hw hwL hσlo hσhi hheight hv s' hQ
          (by rw [hs'w]; exact hWMcap) p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap
        have key := dispatch_assemble (V := 0) (Kr := C₀ + C₁) (D := diagonalControl s.radial.profile)
          (c := p.control SI) (h := 1 + |t| + height) (m := degI) (E1 := nominal + δ + εold) hZ0 hPf0 hFa hfix
          (by rw [add_zero, ← hs'w]; exact hrem) (natural_energy_nonneg s _ _ _ _ _ _ _ _ _)
        refine ⟨0, le_rfl, Or.inl rfl, ?_⟩
        refine key.trans ?_
        rw [mul_zero]
        exact dispatch_mono hZ1 hdiag (mul_nonneg hPf0 (by positivity)) hKO (p.control_nonneg SI) hctlI hbase1
          hdegI (by linarith only [hqdel, hX, hεR, hratepad]) le_rfl
      by_cases hRt : ReflectionTest (length Z X₁) (length Z X₂) Cycle63.Optimization.slotPrice (∑ j ∈ J, w j)
          (∑ j ∈ R, w j) (nominal + δ) δR ξ
      · -- branch (R): one plain factor of the remaining state is reflected into the old region
        have hsW : s.width ≤ nominal + δ := by linarith only [hwidth]
        let s' := widenState s (nominal + δ) hsW
        have hs'w : s'.width = nominal + δ := widenState_width s _ hsW
        have hreflect : R = J ∨
            (length Z X₁ + length Z X₂ + 6 * Cycle63.Optimization.slotPrice * (∑ i ∈ J \ R, w i) ≤
                s'.width + δR ∧
              (max 0 (s'.width - length Z X₂ + ξ) + length Z X₁ + 6 * Cycle63.Optimization.slotPrice *
                  (∑ i ∈ J \ R, w i) + δR ≤ s'.width ∨
                max 0 (s'.width - length Z X₁ + ξ) + length Z X₂ + 6 * Cycle63.Optimization.slotPrice *
                  (∑ i ∈ J \ R, w i) + δR ≤ s'.width)) := by
          right
          have h6 : 6 * Cycle63.Optimization.slotPrice * (∑ j ∈ J \ R, w j) =
              6 * Cycle63.Optimization.slotPrice * ((∑ j ∈ J, w j) - ∑ j ∈ R, w j) := by
            congr 1; linarith only [hsplit]
          obtain ⟨hov, hr⟩ := hRt
          rw [hs'w]
          refine ⟨by linarith only [hov, h6], ?_⟩
          rcases hr with h | h
          · exact Or.inl (by linarith only [h, h6])
          · exact Or.inr (by linarith only [h, h6])
        have hrem := hZr.2 η₀ Q C₀ C₁ hC₀.le hC₁.le hZold.2.1 hposL J R θ w σ v t height hw hwL hσlo hσhi
          hheight hv s' hQ (by rw [hs'w]; exact hWMcap) (by rw [hs'w]; exact hWL) p X₁ X₂ hX₁ hX₂ hc₁ hc₂
          hreflect
        have key := dispatch_assemble (V := 0) (Kr := C₀ + Cr * (C₁ + 1)) (D := diagonalControl s.radial.profile)
          (c := p.control UR) (h := 1 + |t| + height) (m := Jexp) (E1 := nominal + δ + εold + εR) hZ0 hPf0 hFa
          hfix (by rw [add_zero, ← hs'w]; exact hrem) (natural_energy_nonneg s _ _ _ _ _ _ _ _ _)
        refine ⟨0, le_rfl, Or.inl rfl, ?_⟩
        refine key.trans ?_
        rw [mul_zero]
        exact dispatch_mono hZ1 hdiag (mul_nonneg hPf0 (by positivity)) hKR (p.control_nonneg UR) hctlR hbase1
          hdegR (by linarith only [hqdel, hX, hratepad]) le_rfl
      · -- branch (L2): the second step is run on the remaining state of the widened state
        have hsW : s.width ≤ nominal + δ := by linarith only [hwidth]
        let s' := widenState s (nominal + δ) hsW
        have hs'w : s'.width = nominal + δ := widenState_width s _ hsW
        have happ := hgate hwd hsW R hR hRJ hsum hdR hO hRt
        obtain ⟨unit₂, Hb, hpays, hcls, hrem⟩ := hZs.2 J R θ w σ v t height hw hwL hσlo hσhi hheight hv s' hQ
          (by rw [hs'w]; exact hWMcap) p X₁ X₂ hX₁ hX₂ hc₁ hc₂ v₁ T Wl lengthL ampL lossL happ
        have hV : 0 ≤ ∑ b, (Hb b).value := Finset.sum_nonneg (fun b _ => (Hb b).value_nonneg hZ0.le)
        have hRet : 0 ≤ Z ^ (2 * ε * d * (Fintype.card α : ℝ) + q * (del + mesh)) * ∑ b, (Hb b).value :=
          mul_nonneg (Real.rpow_nonneg hZ0.le _) hV
        have key := dispatch_assemble (Kr := C₂) (D := diagonalControl s.radial.profile) (c := p.control ST)
          (h := 1 + |t| + height) (m := degT) (V := ∑ b, (Hb b).value) (E1 := nominal + δ + εold) hZ0 hPf0 hFa
          hfix (by rw [← hs'w]; exact hrem) (natural_energy_nonneg s _ _ _ _ _ _ _ _ _)
        refine ⟨Z ^ (2 * ε * d * (Fintype.card α : ℝ) + q * (del + mesh)) * ∑ b, (Hb b).value, hRet,
          Or.inr ⟨unit₂, Hb, hpays, hcls, rfl⟩, ?_⟩
        refine key.trans ?_
        exact dispatch_mono hZ1 hdiag (mul_nonneg hPf0 hC₂.le) hKL (p.control_nonneg ST) hctlT hbase1 hdegT
          (by linarith only [hqdel, hX, hεR, hratepad]) hRet
  · -- branch (D): the deletion into the old region is paid by the allowance
    obtain ⟨hG0, htot, hpayD⟩ := hDfacts hwd
    obtain ⟨R', hR', hcap', hbound⟩ := hZd.2 J θ w σ v t height mesh a i hw (fun j => (hwL j).trans hLslot) hwr
      hmesh hwm hσlo hσhi hheight
      hv ha ha' hfreq hhigh s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ nominal δ padding amp reserve X G hwidth hδ hpad hG0
      htot hpayD
    refine ⟨0, le_rfl, Or.inl rfl, ?_⟩
    calc _ ≤ _ := hbound
      _ = (CD ^ (Fintype.card α) * (C₀D + C₁D)) * diagonalControl s.radial.profile * (p.control SD) ^ 2 *
          (1 + |t| + height) ^ degD * (Z ^ (nominal + δ + amp - reserve + X + εold +
            2 * ε * d * (Fintype.card α : ℝ) + q / (6 * Cycle63.Optimization.slotPrice) * padding + q * mesh) +
            0) := by ring
      _ ≤ _ := dispatch_mono hZ1 hdiag hKD0 hKD (p.control_nonneg SD) hctlD
          hbase1 hdegD (by linarith only [hεR]) le_rfl

end
end OAI.SevenEighths.Cycle63Moment.LowBranch
