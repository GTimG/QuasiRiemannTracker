/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- Copyright (c) 2026 Sil and OpenAI. Apache-2.0.
The unmarked HIGH adapter retains Sil's literal natural-row/dictionary proof;
the joint histogram preserves both actual pointwise estimates. -/
import Candidate.Local.Qrh.JointDetector.FineAdaptiveSupplier
import Candidate.Local.Qrh.JointDetector.FineNaturalCount
import Candidate.Local.Qrh.JointDetector.AdaptiveSourceChains.Common

namespace Qrh.JointDetector.WeightedSupplier
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


/-- The direct weighted HIGH inlet. Its early mesh precedes the finite
slot type, and its height degree precedes the live physical height. This
interface does not demand the old separately maximized HighLaw estimates. -/
def WholeWeightedHigh (floor : ℝ) (high : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ Mmin Mcap smin loss : ℝ, 0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss →
  ∃ meshC : ℝ, 0 < meshC ∧ ∀ mesh : ℝ, mesh ≤ meshC →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1:ℝ) 2 →
  ∀ bΦ : ℝ, 1 ≤ bΦ → ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character),
  (51/100:ℝ) ≤ HeckeZeroSupremum.beta → HeckeZeroSupremum.beta ≤ 7/8 →
  ∀ Lplain ε₁ kap v d budget : ℝ,
    0 ≤ Lplain → 0 < ε₁ → 0 < kap → kap ≤ 1 →
    0 ≤ v → 0 < d → Mcap+0+1 ≤ d → 0 < budget →
  ∃ eMax : ℝ, 0 < eMax ∧ ∀ e : ℝ, 0 < e → e < 1/1000 → e ≤ eMax →
    8*e*(1/d)+kap ≤ ε₁ → 12*e*(Lplain/d+2)+8*kap+2*v ≤ ε₁ → loss ≤ 1 →
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
        (∑ k,w k) st.rowWidth+(2*ε₁*d*(Fintype.card α+1)+loss*Mcap+τ*J+budget+smin))

theorem priced_source_of_weighted_high
    (floor : ℝ) (high : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hfloor : (1/50:ℝ) ≤ floor) (hwhole : WholeWeightedHigh floor high)
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
  have hhighInput := hcounts mesh hmeshCount α rayM H hH W hW hWs bΦ (by linarith) κ anchors η₀ hβ hβ'
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
  obtain ⟨eMax,heMax,hhighBuffer⟩ := hhighInput Lp ε₁ kap vg d (ε/16)
    hLp0 hε₁ hkap hkap1 hvg0.le hd (by linarith) (by positivity)
  set e : ℝ := min eMax (min (1/2000) (ε₁/(100*(Lp/d + 2 + 1/d)))) with hedef
  have hden2 : 0 < 100*(Lp/d + 2 + 1/d) := by positivity
  have he : 0 < e := lt_min heMax (lt_min (by norm_num) (div_pos hε₁ hden2))
  have he' : e < 1/1000 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have heε : e*(100*(Lp/d + 2 + 1/d)) ≤ ε₁ := by
    have : e ≤ ε₁/(100*(Lp/d + 2 + 1/d)) := (min_le_right _ _).trans (min_le_right _ _)
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
  obtain ⟨J,hJ⟩ := hhighBuffer e he he' (min_le_left _ _) hslotB hplainB hloss1
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
  have hq0 : (1/50:ℝ) ≤ q := hfloor.trans hq.1
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



end
end Qrh.JointDetector.WeightedSupplier

#print axioms Qrh.JointDetector.WeightedSupplier.priced_source_of_weighted_high
