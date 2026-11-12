/- Copyright (c) 2026 Sil. Apache-2.0.
Provider: polynomial scale bounds of the first blocks and the allocation count.

* `first_label_norm`: first-label norms are at most any column bound (`Z^8` at the root).
* `rootVolume_le`: `V(root) ≤ Z^7`.
* `primeSet_norm_le`, `active_norm_le`: `N(∏_E P) ≤ N C`, `N(r_{C,D}) ≤ N C`.
* `firstRadius_le`: the first frequency radius is at most `Z^{31}`.
* `childScale_le_of_block`: the child scale of a retained block is at most `4·Z^{32}`.
* `alloc_card_le`: `#actual allocations of C ≤ τ(C)^{#slots}`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderLabelRoot

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
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentActiveSource ActualEisensteinCubic
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock MixedFirstCommonSum
open MixedFirstRetainedFixed MixedFirstExceptionalWindow MixedPrincipalPoolCaps
open RepairedRawContext Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeProviderSc {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {ι : Type*} [Fintype ι] {a b : ℝ}

theorem first_label_norm (s : Source ι a b) (ha : 0 < a) (X : ℝ)
    (hX : ∀ I ∈ sourceColumns s, (Ideal.absNorm I : ℝ) ≤ X) (p : Labels s ha 1) :
    (Ideal.absNorm p.val.1 : ℝ) ≤ X ∧ (Ideal.absNorm p.val.2 : ℝ) ≤ X := by
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp p.property
  have hI := Finset.mem_filter.mp (Finset.mem_product.mp hq).1
  have hJ := Finset.mem_filter.mp (Finset.mem_product.mp hq).2
  have hIs : q.1 ∈ sourceColumns s := ((mem_activeSource _ _ _).mp hI.1).1
  have hJs : q.2 ∈ sourceColumns s := ((mem_activeSource _ _ _).mp hJ.1).1
  have e1 : p.val.1 = CenteredMomentCompleteCommon.commonPart q.1 q.2 := by rw [← he]
  have e2 : p.val.2 = CenteredMomentCompleteCommon.commonPart q.2 q.1 := by rw [← he]
  rw [e1, e2]
  constructor
  · exact (by exact_mod_cast CenteredMomentCompleteCommon.absNorm_commonPart_le _ _ hI.2.1 :
      (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart q.1 q.2) : ℝ) ≤ Ideal.absNorm q.1).trans
      (hX _ hIs)
  · exact (by exact_mod_cast CenteredMomentCompleteCommon.absNorm_commonPart_le _ _ hJ.2.1 :
      (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart q.2 q.1) : ℝ) ≤ Ideal.absNorm q.2).trans
      (hX _ hJs)

theorem primeSet_norm_le (C D : Id) (hC : C ≠ 0) (E : Finset (CommonIndex C D)) :
    (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) ≤ Ideal.absNorm C := by
  have hsub : E.map (Function.Embedding.subtype _) ⊆ IdealMobiusDivisorSum.primeSupport C := by
    intro P hP
    obtain ⟨Q, _, rfl⟩ := Finset.mem_map.mp hP
    exact (Finset.mem_inter.mp Q.property).1
  have hd := IdealMobiusDivisorSum.support_product_dvd hC hsub
  rw [Finset.prod_map] at hd
  exact norm_le_of_dvd hC hd

theorem active_norm_le (C D : Id) (hC : C ≠ 0) :
    (Ideal.absNorm (Ideal.span {activeConductor C D}) : ℝ) ≤ Ideal.absNorm C := by
  unfold activeConductor
  rw [span_finitePrimeModulus]
  have hsub : (Finset.univ : Finset (ActiveIndex C D)).map
      ((Function.Embedding.subtype _).trans (Function.Embedding.subtype _)) ⊆
      IdealMobiusDivisorSum.primeSupport C := by
    intro P hP
    obtain ⟨Q, _, rfl⟩ := Finset.mem_map.mp hP
    exact (Finset.mem_inter.mp Q.val.property).1
  have hd := IdealMobiusDivisorSum.support_product_dvd hC hsub
  rw [Finset.prod_map] at hd
  exact norm_le_of_dvd hC hd

theorem firstNominal_le (C D : Id) (hC : C ≠ 0) (E : Finset (CommonIndex C D)) (K V : ℝ)
    (hK : 1 ≤ K) :
    firstNominalScale C D (∏ P ∈ E, P.val) K V ≤ (Ideal.absNorm C : ℝ)^2 * V^2 := by
  unfold firstNominalScale
  have h1 := primeSet_norm_le C D hC E
  have h2 := active_norm_le C D hC
  have hc1 := nrm_one_le (CenteredMomentCompleteCommon.commonPart_ne_zero C D)
  have hc2 := nrm_one_le (CenteredMomentCompleteCommon.commonPart_ne_zero D C)
  unfold nrm at hc1 hc2
  have hden : 1 ≤ K * (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart C D) : ℝ) *
      (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart D C) : ℝ) := by
    have := one_le_mul_of_one_le_of_one_le hK hc1
    exact one_le_mul_of_one_le_of_one_le this hc2
  have hnum : 0 ≤ (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) *
      (Ideal.absNorm (Ideal.span {activeConductor C D}) : ℝ) * V^2 := by positivity
  rw [div_le_iff₀ (by linarith)]
  calc (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) * (Ideal.absNorm (Ideal.span {activeConductor C D}) : ℝ) *
        V^2 ≤ (Ideal.absNorm C : ℝ) * (Ideal.absNorm C : ℝ) * V^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (Ideal.absNorm C : ℝ)^2 * V^2 * (K *
        (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart C D) : ℝ) *
        (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart D C) : ℝ)) := by
        have e : (Ideal.absNorm C : ℝ) * (Ideal.absNorm C : ℝ) * V^2 =
            (Ideal.absNorm C : ℝ)^2 * V^2 := by ring
        rw [e]
        exact le_mul_of_one_le_right (by positivity) hden

theorem dyad_le_of_retained (R : ℝ) (n : ℤ) (hn : n ∈ retainedIndices R) : dyadicScale n ≤ 4 * R :=
  retained_scale_le R n ((mem_retainedIndices R n).mp hn).1

theorem childScale_eq (Z κ : ℝ) (hZ : 1 < Z) (n : ℤ) :
    childScale Z κ n = dyadicScale n * Z^κ := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  unfold childScale
  rw [Real.rpow_add hZ0, Real.rpow_logb hZ0 hZ.ne' (dyadicScale_pos n)]

/-- The number of actual allocations of `C` is at most `τ(C)` to the number of slots. -/
theorem alloc_card_le (S : ι ⊕ Fin 2 → Finset Id) (C : Id) (hC : C ≠ 0) :
    (actualAllocations S C).card ≤
      (IdealMobiusDivisorSum.idealDivisors C).card ^ Fintype.card (ι ⊕ Fin 2) := by
  set e := Fintype.equivFin (ι ⊕ Fin 2)
  let f : (ι ⊕ Fin 2 → Id) → (Fin (Fintype.card (ι ⊕ Fin 2)) → Id) := fun B i => B (e.symm i)
  have hinj : Function.Injective f := by
    intro B B' h
    funext j
    have := congrFun h (e j)
    simpa [f] using this
  rw [← Finset.card_image_of_injective _ hinj]
  have hC' : C ≠ ⊥ := hC
  apply Packet.Fibre.card_le_of_components_dvd hC'
  intro g hg i
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hg
  have hprod := (Finset.mem_filter.mp hB).2
  rw [← hprod]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)

/-! ### Root scales -/

section root
variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

theorem root_prodP (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) :
    (∏ i, d.root.P i) ≤ Z^(1:ℝ) := by
  obtain ⟨-, -, -, -, hP⟩ := d.hcanonical
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  rw [show (∏ i, d.root.P i) = ∏ i, Z^(d.w i) from Finset.prod_congr rfl (fun i _ => congrFun hP i),
    ← Real.rpow_sum_of_pos hZ0]
  apply Real.rpow_le_rpow_of_exponent_le hZ1.le
  have h := d.width_bounds.2
  have hc := G.face.2.2.2.2.2.1
  linarith

theorem rootVolume_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) :
    sourceVolume d.root ≤ Z^(7:ℝ) := by
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hx1 := (d.root.hL.trans_le d.root.hX₁).le
  have hx2 := (d.root.hL.trans_le d.root.hX₂).le
  have hp0 : 0 ≤ ∏ i, d.root.P i := Finset.prod_nonneg fun i _ => by linarith [d.root.hP i]
  unfold sourceVolume
  calc d.root.X₁ * d.root.X₂ * ∏ i, d.root.P i ≤ Z^(3:ℝ) * Z^(3:ℝ) * Z^(1:ℝ) :=
        mul_le_mul (mul_le_mul d.hX₁ d.hX₂ hx2 (by positivity)) (root_prodP d) hp0 (by positivity)
    _ = Z^(7:ℝ) := by rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]; norm_num

theorem root_columns_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) :
    ∀ I ∈ sourceColumns d.root, (Ideal.absNorm I : ℝ) ≤ Z^(8:ℝ) :=
  fun I hI => (source_column_pool_norm d.root (by norm_num) I hI).trans d.hpool

theorem firstRadius_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (ha : (0:ℝ) < 1/4)
    (p : Labels d.root ha 1) (E : Finset (CommonIndex p.val.1 p.val.2)) (ξ : ℝ) (hξ : ξ ≤ 2) :
    firstRadius d.root p.val.1 p.val.2 E d.Kroot Z ξ ≤ Z^(31:ℝ) := by
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hK1 : 1 ≤ d.Kroot := hZ1.le.trans d.hKlow
  have hC0 := (commonLabels_data _ _ p.val.1 p.val.2 p.property).1
  have hN := (first_label_norm d.root ha _ (root_columns_le d) p).1
  have hV := rootVolume_le d
  have hV0 := (sourceVolume_pos d.root).le
  unfold firstRadius frequencyRadius
  have h1 := firstNominal_le p.val.1 p.val.2 hC0 E d.Kroot (sourceVolume d.root) hK1
  have hF0 : 0 ≤ firstNominalScale p.val.1 p.val.2 (∏ P ∈ E, P.val) d.Kroot (sourceVolume d.root) := by
    unfold firstNominalScale; have := d.radial_pos; positivity
  have h2 : (Ideal.absNorm p.val.1 : ℝ)^2 * sourceVolume d.root^2 ≤ (Z^(8:ℝ))^2 * (Z^(7:ℝ))^2 :=
    mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2) (pow_le_pow_left₀ hV0 hV 2)
      (sq_nonneg _) (by positivity)
  have h3 : Z^(ξ/2) ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  calc firstNominalScale p.val.1 p.val.2 (∏ P ∈ E, P.val) d.Kroot (sourceVolume d.root) * Z^(ξ/2)
      ≤ ((Z^(8:ℝ))^2 * (Z^(7:ℝ))^2) * Z^(1:ℝ) :=
        mul_le_mul (h1.trans h2) h3 (by positivity) (by positivity)
    _ = Z^(31:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le,
          ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
        norm_num

theorem slotWidth_root_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) J ≤
      2^(Fintype.card κ) * Z^(1:ℝ) := by
  refine (prod_comp_le (fun j : J => j.val.val) (Subtype.val_injective.comp Subtype.val_injective)
    (fun i => 2 * d.root.P i) (fun i => by linarith [d.root.hP i])).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  exact mul_le_mul_of_nonneg_left (root_prodP d) (by positivity)

/-- **The Gauss scale of every residual split of a retained block is polynomial.** -/
theorem block_Kc_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (ha : (0:ℝ) < 1/4)
    (p : Labels d.root ha 1) (E : Finset (CommonIndex p.val.1 p.val.2)) (κs : ℝ) (hκ0 : 0 ≤ κs)
    (hκ : κs ≤ 1) (n : ℤ)
    (hn : n ∈ retainedIndices (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z κs))
    (C : Id) (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (hZbig : 64 * (16:ℝ)^(Fintype.card κ) ≤ Z^(4:ℝ)) :
    16 * childScale Z κs n *
      (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) J)^4 ≤ Z^(40:ℝ) := by
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hR := firstRadius_le d ha p E κs (by linarith)
  have hd := dyad_le_of_retained _ n hn
  have hW := slotWidth_root_le d C B J
  have hW0 := (slotWidth_pos (allocatedLiveSource d.root (by norm_num) d.cover C B) J).le
  rw [childScale_eq Z κs hZ1 n]
  have hK : dyadicScale n * Z^κs ≤ (4 * Z^(31:ℝ)) * Z^(1:ℝ) :=
    mul_le_mul (hd.trans (by linarith)) (Real.rpow_le_rpow_of_exponent_le hZ1.le hκ)
      (Real.rpow_nonneg hZ0.le _) (by positivity)
  have hW4 : (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) J)^4 ≤
      (2^(Fintype.card κ) * Z^(1:ℝ))^4 := pow_le_pow_left₀ hW0 hW 4
  have hd0 := (dyadicScale_pos n).le
  calc 16 * (dyadicScale n * Z^κs) *
        (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) J)^4
      ≤ 16 * ((4 * Z^(31:ℝ)) * Z^(1:ℝ)) * (2^(Fintype.card κ) * Z^(1:ℝ))^4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num)) hW4 (by positivity)
          (by positivity)
    _ = (64 * (16:ℝ)^(Fintype.card κ)) * Z^(36:ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (Z^(1:ℝ)), ← Real.rpow_mul hZ0.le,
          show ((2:ℝ)^(Fintype.card κ))^4 = (16:ℝ)^(Fintype.card κ) by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        have e : 16 * (4 * Z ^ (31:ℝ) * Z ^ (1:ℝ)) * ((16:ℝ) ^ Fintype.card κ * Z ^ ((1:ℝ) * ↑(4:ℕ)))
            = 64 * (16:ℝ) ^ Fintype.card κ * (Z ^ (31:ℝ) * Z ^ (1:ℝ) * Z ^ ((1:ℝ) * ↑(4:ℕ))) := by ring
        rw [e, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
        norm_num
    _ ≤ Z^(4:ℝ) * Z^(36:ℝ) := mul_le_mul_of_nonneg_right hZbig (by positivity)
    _ = Z^(40:ℝ) := by rw [← Real.rpow_add hZ0]; norm_num

end root

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
