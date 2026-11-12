/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, label half: the `RootLabelData` of a residual split from the root input.

* `dvd_rad_sq`: an ideal with all factor multiplicities `≤ 2` divides `rad(I)²`.
* `lab_cubeFree`, `lab_cube_rad`: the second labels of any source are cube-free
  (`label_cube_free` on the residual) and divide the square of their radical.
* `lab_norm_le`: the second-label columns are bounded by the residual column cap.
* `residFin_columns`, `residFin_coefficient`, `residFin_S0`: the reindexed renormalized residual
  is the literal residual `restOf`.
* `residFin_canonical`: the canonical form of the residual from `d.hcanonical`.
* `rootLabelData_of`: every field of `RootLabelData` except the four geometric ones (`hbox`,
  `hdyad`, `hcapC`, `hcapD`, from `GeometryAt`) and the multiplicities (`hmultC`, `hmultD`).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderResidual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second QRH.SilDensitySplit.CubeFree.Second.Provider
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentNaturalFixedRaySource CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedCompletedRows CenteredMomentSectorLocalization
open MixedFirstActualNonexceptional MixedPrincipalPoolCaps MixedInnerExceptionalBlock
open RepairedRawContext RepairedSourceSideSupply RepairedSourceRootGeometry
open Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open RayFourExpansion CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeProviderLD {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-! ### Cube-free second labels -/

theorem dvd_rad_sq {I : Id} (hI : I ≠ 0)
    (h2 : ∀ Q, Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors I) ≤ 2) :
    I ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport I, P)^2 := by
  calc I = (UniqueFactorizationMonoid.normalizedFactors I).prod :=
        (Ideal.prod_normalizedFactors_eq_self hI).symm
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
          P ^ (Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I)) :=
        Finset.prod_multiset_count _
    _ ∣ ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P^2 :=
        Finset.prod_dvd_prod_of_dvd _ _ (fun P _ => pow_dvd_pow P (h2 P))
    _ = (∏ P ∈ IdealMobiusDivisorSum.primeSupport I, P)^2 := Finset.prod_pow _ _ _

variable {ι : Type*} [Fintype ι] {a b : ℝ}

theorem lab_cubeFree (s : Source ι a b) (ha : 0 < a) (l : Lab (S0 s ha)) :
    Packet.CubeFreeCommon l.1.val.1 l.1.val.2 :=
  first_label_cubeFree s ha l.1

theorem lab_cube_rad (s : Source ι a b) (ha : 0 < a) (l : Lab (S0 s ha)) :
    l.1.val.1 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1, P)^2 ∧
      l.1.val.2 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2, P)^2 := by
  have hd := commonLabels_data _ _ l.1.val.1 l.1.val.2 l.1.property
  have hcf := lab_cubeFree s ha l
  have hcount : ∀ (left : Bool) (Q : Id), Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors
      (if left then l.1.val.1 else l.1.val.2)) ≤ 2 := by
    intro left Q
    by_cases hQ : Q ∈ CenteredMomentCompleteCommon.commonSupport l.1.val.1 l.1.val.2
    · have h := hcf ⟨Q, hQ⟩
      cases left
      · have hv : Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors l.1.val.2) = 1 ∨
            Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors l.1.val.2) = 2 := h.2
        simp only [Bool.false_eq_true, ite_false]
        omega
      · have hv : Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors l.1.val.1) = 1 ∨
            Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors l.1.val.1) = 2 := h.1
        simp only [ite_true]
        omega
    · have hz : Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors
          (if left then l.1.val.1 else l.1.val.2)) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        apply hQ
        unfold CenteredMomentCompleteCommon.commonSupport
        have hs : (QRH.Record1252270103KernelMass.primeSupport l.1.val.1 : Finset Id) =
            QRH.Record1252270103KernelMass.primeSupport l.1.val.2 := hd.2.2
        cases left
        · simp only [Bool.false_eq_true, ite_false] at hmem
          have h2 : Q ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2 := Multiset.mem_toFinset.mpr hmem
          have h1 : Q ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1 := by
            have : Q ∈ (QRH.Record1252270103KernelMass.primeSupport l.1.val.2 : Finset Id) := h2
            rw [← hs] at this; exact this
          exact Finset.mem_inter.mpr ⟨h1, h2⟩
        · simp only [ite_true] at hmem
          have h1 : Q ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1 := Multiset.mem_toFinset.mpr hmem
          have h2 : Q ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2 := by
            have : Q ∈ (QRH.Record1252270103KernelMass.primeSupport l.1.val.1 : Finset Id) := h1
            rw [hs] at this; exact this
          exact Finset.mem_inter.mpr ⟨h1, h2⟩
      rw [hz]; omega
  exact ⟨dvd_rad_sq hd.1 (hcount true), dvd_rad_sq hd.2.1 (hcount false)⟩

/-- Second-label columns are bounded by any bound on the source columns. -/
theorem lab_norm_le (s : Source ι a b) (ha : 0 < a) (X : ℝ)
    (hX : ∀ I ∈ sourceColumns s, (Ideal.absNorm I : ℝ) ≤ X) (l : Lab (S0 s ha)) :
    (Ideal.absNorm l.1.val.1 : ℝ) ≤ X ∧ (Ideal.absNorm l.1.val.2 : ℝ) ≤ X := by
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp l.1.property
  have hI := Finset.mem_filter.mp (Finset.mem_product.mp hq).1
  have hJ := Finset.mem_filter.mp (Finset.mem_product.mp hq).2
  have hIs : q.1 ∈ sourceColumns s := by
    have := hI.1; unfold S0 at this; rw [CenteredMomentActiveSource.mem_activeSource] at this
    exact this.1
  have hJs : q.2 ∈ sourceColumns s := by
    have := hJ.1; unfold S0 at this; rw [CenteredMomentActiveSource.mem_activeSource] at this
    exact this.1
  have e1 : l.1.val.1 = CenteredMomentCompleteCommon.commonPart q.1 q.2 := by rw [← he]
  have e2 : l.1.val.2 = CenteredMomentCompleteCommon.commonPart q.2 q.1 := by rw [← he]
  rw [e1, e2]
  constructor
  · exact (by exact_mod_cast CenteredMomentCompleteCommon.absNorm_commonPart_le _ _ hI.2.1 :
      (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart q.1 q.2) : ℝ) ≤ Ideal.absNorm q.1).trans
      (hX _ hIs)
  · exact (by exact_mod_cast CenteredMomentCompleteCommon.absNorm_commonPart_le _ _ hJ.2.1 :
      (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart q.2 q.1) : ℝ) ≤ Ideal.absNorm q.2).trans
      (hX _ hJs)

/-! ### The residual split is the literal residual -/

section resid
variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

theorem residFin_columns (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    sourceColumns (residFin d C B J) = sourceColumns (restOf d.root (by norm_num) d.cover C B J) := by
  unfold residFin residOf
  rw [sourceColumns_reindex, sourceColumns_renorm]

theorem residFin_coefficient (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (ha : (0:ℝ) < 1/4) (seed : Id) :
    sourceCoefficient (residFin d C B J) ha seed =
      sourceCoefficient (restOf d.root (by norm_num) d.cover C B J) ha seed := by
  unfold residFin residOf
  rw [sourceCoefficient_reindex, sourceCoefficient_renorm]

theorem residFin_S0 (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (ha : (0:ℝ) < 1/4) :
    S0 (residFin d C B J) ha = S0 (restOf d.root (by norm_num) d.cover C B J) ha := by
  unfold S0; rw [residFin_columns, residFin_coefficient]

/-- **`labelAvgT` is the `splitLabel` of the residual split.** -/
theorem labelAvgT_eq_split (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (JB : (B : actualAllocations (tuplePools d.root) C) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K : ℝ)
    (T : actualAllocations (tuplePools d.root) C → ℝ) (Zs ξr : ℝ)
    (Wd : actualAllocations (tuplePools d.root) C → ℝ)
    (B : actualAllocations (tuplePools d.root) C) (ξ : RayCharacter) (ha : (0:ℝ) < 1/4) :
    labelAvgT d.root ha (by norm_num) d.cover C JB τ χ₀ Q m t K T Zs ξr Wd B ξ =
      splitLabel (S0 (residFin d C B (JB B)) ha) (sourceCoefficient (residFin d C B (JB B)) ha 1)
        (childCharacter τ ξ) χ₀ Q m t (16 * K * Wd B^4) (frequencyRadius (T B) Zs ξr)
        (sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
          (restOf d.root (by norm_num) d.cover C B (JB B)).T
          (restOf d.root (by norm_num) d.cover C B (JB B)).d) := by
  have h1 : labelAvgT d.root ha (by norm_num) d.cover C JB τ χ₀ Q m t K T Zs ξr Wd B ξ =
      splitLabel (S0 (restOf d.root (by norm_num) d.cover C B (JB B)) ha)
        (sourceCoefficient (restOf d.root (by norm_num) d.cover C B (JB B)) ha 1)
        (childCharacter τ ξ) χ₀ Q m t (16 * K * Wd B^4) (frequencyRadius (T B) Zs ξr)
        (sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
          (restOf d.root (by norm_num) d.cover C B (JB B)).T
          (restOf d.root (by norm_num) d.cover C B (JB B)).d) := by
    unfold labelAvgT labelAvg splitLabel
    rfl
  rw [h1, residFin_S0, residFin_coefficient]

theorem residFin_pool_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    ∀ I ∈ sourceColumns (residFin d C B J), (Ideal.absNorm I : ℝ) ≤ Z^(8:ℝ) := by
  intro I hI
  rw [residFin_columns] at hI
  exact ((source_column_pool_norm _ (by norm_num) I hI).trans
    (restOf_pool_le d.root (by norm_num) d.cover C B J)).trans d.hpool

/-! ### The second-step frequency -/

theorem cap_eq_vol (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    capRes d C B J = (9/4:ℝ)^2 * 2^(Fintype.card (Rest J)) * sourceVolume (residOf d C B J) := by
  unfold capRes
  rw [← sourceNormCap_renorm]
  set r := restOf d.root (by norm_num) d.cover C B J
  have n1 := (nrm_pos r.hd.1).ne'
  have n2 := (nrm_pos r.hd.2).ne'
  have hp : QRH.Record1252270103KernelMass.pairNorm ((1:Id), (1:Id)) = 1 := by
    simp [QRH.Record1252270103KernelMass.pairNorm]
  unfold sourceNormCap sourceVolume
  change (9/4:ℝ)^2 * ((r.T / (nrm r.d.1 * nrm r.d.2)) /
      QRH.Record1252270103KernelMass.pairNorm ((1:Id), (1:Id))) * ∏ i, 2 * r.P i =
    (9/4:ℝ)^2 * 2^(Fintype.card (Rest J)) * (r.X₁ / nrm r.d.1 * (r.X₂ / nrm r.d.2) * ∏ i, r.P i)
  rw [hp, div_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← r.hpX]
  field_simp
  simp only [Fintype.card_eq_nat_card]
  ring_nf
  congr

theorem frame_vol_eq (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh)
    (C : Id) (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (V₀ : O) (hV₀ : V₀ ≠ 0) (kLog : ℝ) :
    (frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh V₀ hV₀ kLog).vol =
      sourceVolume (residOf d C B J) := by
  obtain ⟨-, -, -, -, hP⟩ := d.hcanonical
  unfold GSrc.vol sourceVolume
  change (residOf d C B J).X₁ * (residOf d C B J).X₂ *
      ∏ k, Z^(d.w (residSlot (d := d) k)) = _
  congr 1
  rw [← Equiv.prod_comp (Fintype.equivFin (Rest J)).symm (fun i => (residOf d C B J).P i)]
  apply Finset.prod_congr rfl
  intro k _
  exact (congrFun hP _).symm

/-- **The label Poisson condition from the frequency choice.** -/
theorem hdyad_of_freq (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh)
    (C : Id) (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (V₀ : O) (hV₀ : V₀ ≠ 0) (Kc ξr : ℝ) (hKc : 0 < Kc) (hcap : 1 ≤ capRes d C B J)
    (hZc : 32 * ((9/4:ℝ)^2 * 2^(Fintype.card (Rest J)))^2 * Z^(ξr/2) ≤ Z^mesh) :
    32 * frequencyRadius (Tfreq d C B J Kc) Z ξr ≤
      Z ^ cutoffLog (frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh
        V₀ hV₀ (Real.logb Z Kc)) := by
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  set rs := frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh V₀ hV₀
    (Real.logb Z Kc)
  have hvol : rs.vol = sourceVolume (residOf d C B J) := frame_vol_eq d hW hWs bΦ hbΦ Q hQM hQ0
    hQt hQ72 hε Bmask hBmask mesh hmesh C B J V₀ hV₀ _
  have hv0 : 0 < rs.vol := by rw [hvol]; exact sourceVolume_pos _
  have hcut : Z ^ cutoffLog rs = rs.vol^2 / Kc * Z^mesh := by
    unfold cutoffLog GSrc.colLog
    rw [Real.rpow_add hZ0, Real.rpow_sub hZ0, mul_comm (2:ℝ), Real.rpow_mul hZ0.le,
      Real.rpow_logb hZ0 hZ1.ne' hv0, Real.rpow_two]
    change rs.vol ^ 2 / Z ^ (Real.logb Z Kc) * Z^mesh = _
    rw [Real.rpow_logb hZ0 hZ1.ne' hKc]
  rw [hcut]
  unfold frequencyRadius Tfreq
  rw [max_eq_right hcap, cap_eq_vol, ← hvol]
  have hc0 : 0 ≤ ((9/4:ℝ)^2 * 2^(Fintype.card (Rest J)))^2 := by positivity
  have hZξ : 0 ≤ Z^(ξr/2) := Real.rpow_nonneg hZ0.le _
  have e : 32 * (((9/4:ℝ)^2 * 2^(Fintype.card (Rest J)) * rs.vol)^2 / Kc * Z^(ξr/2)) =
      (32 * ((9/4:ℝ)^2 * 2^(Fintype.card (Rest J)))^2 * Z^(ξr/2)) * (rs.vol^2 / Kc) := by ring
  rw [e, mul_comm (rs.vol^2 / Kc)]
  exact mul_le_mul_of_nonneg_right hZc (by positivity)

/-- **The root label data of a residual split** from the root input, the side data and the
geometric fields (`GeometryAt`) and the multiplicities. -/
theorem rootLabelData_of (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh)
    (C : Id) (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (P : SidePack η) (hPC : P.Cs ∣ C) (Kc R Hc : ℝ) (hKc : 0 < Kc) (Mbox : ℤ) (Mm : ℕ)
    (ha : (0:ℝ) < 1/4)
    (hbox : ∀ l n, inRange (S0 (residFin d C B J) ha) Kc R Hc l n → n ∈ box Mbox)
    (hdyad : 32 * R ≤ Z ^ cutoffLog (frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask
      hBmask mesh hmesh P.V P.hV (Real.logb Z Kc)))
    (hcapC : ∀ l : Lab (S0 (residFin d C B J) ha), ∀ Lp ∈ labelPool (S0 (residFin d C B J) ha) l,
      (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport
        (((residFin d C B J).R * l.1.val.1) * Lp) ∪ holes (residFin d C B J).H, I) : ℝ) ≤ Z^Bmask)
    (hcapD : ∀ l : Lab (S0 (residFin d C B J) ha), ∀ Lp ∈ labelPool (S0 (residFin d C B J) ha) l,
      (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport
        (((residFin d C B J).R * l.1.val.2) * Lp) ∪ holes (residFin d C B J).H, I) : ℝ) ≤ Z^Bmask)
    (hmultC : ∀ (G' : Id) (A : O), ((Finset.univ : Finset (Lab (S0 (residFin d C B J) ha))).filter
      (fun l => l.1.val.1 = G' ∧ lA (S0 (residFin d C B J) ha) l = A)).card ≤ Mm)
    (hmultD : ∀ (G' : Id) (A : O), ((Finset.univ : Finset (Lab (S0 (residFin d C B J) ha))).filter
      (fun l => l.1.val.2 = G' ∧ lA (S0 (residFin d C B J) ha) l = A)).card ≤ Mm) :
    RootLabelData (θ := thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM hQ0 hQt hQ72 Holes N ε hε Bmask
        hBmask (Fintype.card (Rest J))) P (internalQ Q η₀) CenteredMomentSecondHeightFamily.fixedBadMask
      (residFin d C B J) ha
      (frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh P.V P.hV
        (Real.logb Z Kc)) Kc R Hc Mbox Mm ((1/4:ℝ)^2) := by
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hcan := d.hcanonical
  obtain ⟨hS, hpool, hν, hWsl, hP⟩ := hcan
  refine
    { hW₁ := rfl
      hW₂ := rfl
      ht₁ := rfl
      ht₂ := rfl
      hX₁ := rfl
      hX₂ := rfl
      hY₁ := rfl
      hY₂ := rfl
      hV₀ := rfl
      hCR := ?_
      hcan := ?_
      hQ := rfl
      hQ72 := hQ72
      hm0 := CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero
      hml := dvd_mul_right _ _
      hm2 := dvd_mul_left _ _
      hkLog := Real.rpow_logb hZ0 hZ1.ne' hKc
      hKc := hKc
      hholes_sub := ?_
      hholes_R₀ := ?_
      hcapC := hcapC
      hcapD := hcapD
      hcubeExp := ?_
      hcubeRadC := fun l => (lab_cube_rad _ ha l).1
      hcubeRadD := fun l => (lab_cube_rad _ ha l).2
      hbox := hbox
      hdyad := hdyad
      hclow_pos := by norm_num
      hcol := ?_
      hspanInj := spanInj_holds _
      hmultC := hmultC
      hmultD := hmultD }
  · change P.Cs ∣ d.root.R * C
    exact hPC.trans (dvd_mul_left _ _)
  · refine ⟨hS, rfl, fun i => congrFun hpool _, fun i => congrFun hν _, fun i => congrFun hWsl _,
      fun i => congrFun hP _, rfl, rfl⟩
  · change d.root.H ⊆ _
    rw [d.hH]; exact Finset.empty_subset _
  · intro i P' hP'
    change P' ∈ d.root.H at hP'
    rw [d.hH] at hP'
    exact absurd hP' (Finset.notMem_empty _)
  · intro l P'
    rcases lab_cubeFree _ ha l P' with ⟨h1 | h1, h2 | h2⟩ <;> omega
  · exact hcol_of_canonical _ ha _ rfl rfl (fun i => congrFun hP _)

end resid

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
