/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 8: the label part of one residual split at one scale.

* `frame_mult`: the frame labels of a column hit each frame label at most `Mm` times;
* `frame_group_raised`: the frame group of a class is the RAISED group of the unraised labels;
* `frame_group_fibre`: its restricted fibre (codes `(G, (A₂))`, `G ∣ (A₂)²`);
* `split_label_at`: at one scale `Z`, a height-uniform Seam B bound `B₀` for the admissible
  groups of the frame source (supplied by `split_label_bound`) gives
  `splitLabel(t) ≤ #box · Cg · (vol/c · Mm · B₀) · pm_J² · (1+2π)^{4J} · (1+|t|)^{2J}`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly7

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows
open QRH.SilDensitySplit.CubeFree.Packet

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalBlock CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSectorLocalization CenteredMomentSecondActiveDyadic CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice RayFourExpansion CenteredMomentSecondWindowBudget
open CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The restricted fibre statement at one scale (the conclusion of `fibre_rows_sq`). -/
def FibreAt (Z Cexp B ε : ℝ) (k : ℕ) : Prop :=
  ∀ (L : ℝ) (θ : GData L) (mesh : ℝ)
    (labels : Finset (GLabel θ mesh Z)) (code : GLabel θ mesh Z → Fin k → Ideal O),
    (∀ x ∈ labels, ‖x.prefactor‖ ≤ 1) →
    (∀ x ∈ labels, x.common ∣ (Ideal.span {x.twist})^2) →
    (∀ x ∈ labels, x.D ≠ 0 ∧ (x.D.absNorm : ℝ) ≤ Z^B) →
    (∀ x ∈ labels, ∀ i, code x i ∣ (Ideal.span {x.twist})^2) →
    Set.InjOn (fun x => (code x, x.D)) labels →
    ∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm : ℝ) ≤ Z^Cexp →
      ∑ x ∈ labels.filter (fun x => x.twist ∣ y), gWeight x ≤ Z^(ε/8)

theorem eventually_fibreAt (k : ℕ) (Cexp B ε : ℝ) (hC : 0 ≤ Cexp) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, FibreAt Z Cexp B ε k :=
  fibre_rows_sq k Cexp B ε hC hB hε

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

section
variable {η : Character} {P : SidePack η} {Q : Id} {m : O}
  {s : Source (Fin θ.N) θ.a θ.b} {ha : 0 < θ.a} {rs : GSrc θ mesh Z} {Kc R H : ℝ} {M : ℤ}
  {Mm : ℕ} {clow : ℝ}

/-- The frame label of a column. -/
abbrev frameX (ξ : RayCharacter) (g : Lab (S0 s ha) → Id) (n : Fin 4 → ℤ) (χ : RayCharacter)
    (k : Σ _ : Lab (S0 s ha), Id) : GLabel θ mesh Z :=
  (frameData P.j₀ ξ s rs (S0 s ha) g n χ k).toLabel η

/-- **Multiplicity of the frame labels.** -/
theorem frame_mult (ξ : RayCharacter) (g : Lab (S0 s ha) → Id) (n : Fin 4 → ℤ)
    (χ : RayCharacter) (Ks : Finset (Σ _ : Lab (S0 s ha), Id))
    (hm : ∀ (G : Id) (A : O), ((Finset.univ : Finset (Lab (S0 s ha))).filter
      (fun l => g l = G ∧ lA (S0 s ha) l = A)).card ≤ Mm) :
    ∀ y ∈ Ks.image (frameX (η := η) (P := P) (s := s) (ha := ha) (rs := rs)
        ξ g n χ),
      (Ks.filter (fun k => frameX (η := η) (P := P) (s := s) (ha := ha)
        (rs := rs) ξ g n χ k = y)).card ≤ Mm := by
  intro y _
  refine le_trans ?_ (hm y.G y.twist)
  apply Finset.card_le_card_of_injOn (fun k => k.1)
  · intro k hk
    have hX := (Finset.mem_filter.mp hk).2
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and]
    rw [← hX]
    exact ⟨rfl, rfl⟩
  · intro k hk k' hk' h
    have hX := (Finset.mem_filter.mp hk).2
    have hX' := (Finset.mem_filter.mp hk').2
    have hD : k.2 = k'.2 := by
      have e1 : (frameX (η := η) (P := P) (s := s) (ha := ha) (rs := rs)
        ξ g n χ k).D = k.2 := rfl
      have e2 : (frameX (η := η) (P := P) (s := s) (ha := ha) (rs := rs)
        ξ g n χ k').D = k'.2 := rfl
      rw [← e1, ← e2, hX, hX']
    exact Sigma.ext h (heq_of_eq hD)

/-- **The frame group is a raised group.** -/
theorem frame_group_raised (ξ : RayCharacter) (g : Lab (S0 s ha) → Id) (n : Fin 4 → ℤ)
    (χ : RayCharacter) (Ks : Finset (Σ _ : Lab (S0 s ha), Id)) :
    Ks.image (frameX (η := η) (P := P) (s := s) (ha := ha) (rs := rs)
        ξ g n χ) =
      (Ks.image (fun k => setN (frameX (η := η) (P := P) (s := s)
        (ha := ha) (rs := rs) ξ g n χ k) n)).image (raised rs) := by
  rw [Finset.image_image]
  rfl

/-- **The restricted fibre of a frame group.** -/
theorem frame_group_fibre (hR : RootLabelData (θ := θ) P Q m s ha rs Kc R H M Mm clow)
    (ξ : RayCharacter) (g : Lab (S0 s ha) → Id) (hg : IsColumn (S0 s ha) g)
    (hgdvd : ∀ l, g l ∣ (Ideal.span {lA (S0 s ha) l})^2) (n : Fin 4 → ℤ)
    (χ : RayCharacter) (Ks : Finset (Σ _ : Lab (S0 s ha), Id))
    (hKs : ∀ k ∈ Ks, k.2 ∈ labelPool (S0 s ha) k.1) (Cexp ε : ℝ)
    (hfib : FibreAt Z Cexp θ.Bmask ε 2) :
    ∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm : ℝ) ≤ Z^Cexp →
      ∑ x ∈ (Ks.image (frameX (η := η) (P := P) (s := s) (ha := ha)
        (rs := rs) ξ g n χ)).filter (fun x => x.twist ∣ y), gWeight x ≤ Z^(ε/8) := by
  apply hfib L θ mesh _ (fun x => ![x.G, Ideal.span {x.twist}])
  · intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    show ‖(1:ℂ)‖ ≤ 1
    rw [norm_one]
  · intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact hgdvd k.1
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hgood := frame_good hR ξ g hg n χ k (hKs k hk)
    have hfits := toLabel_fits (θ := θ) (mesh := mesh) (Z := Z) η rs _ hgood
    exact ⟨hfits.D_sq.ne_zero, hfits.D_cap⟩
  · intro x hx i
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    fin_cases i
    · exact hgdvd k.1
    · exact dvd_pow_self _ two_ne_zero
  · intro x hx x' hx' h
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k', _, rfl⟩ := Finset.mem_image.mp hx'
    simp only [Prod.mk.injEq] at h
    obtain ⟨hc, hD⟩ := h
    have hG : g k.1 = g k'.1 := congrFun hc 0
    have hsp : Ideal.span {lA (S0 s ha) k.1} = Ideal.span {lA (S0 s ha) k'.1} := congrFun hc 1
    have hA := hR.hspanInj k.1 k'.1 hsp
    show (frameData P.j₀ ξ s rs (S0 s ha) g n χ k).toLabel η =
      (frameData P.j₀ ξ s rs (S0 s ha) g n χ k').toLabel η
    rw [frameData_eq P.j₀ ξ s rs (S0 s ha) g n χ k k' hG hA hD]

end

/-! ### The label part of one split at one scale -/

theorem windowBudget_sq (J : ℕ) (t E : ℝ) (hE : 0 ≤ E) :
    windowBudget J t E * windowBudget J t E = E * (heightEnvelope t ^ J * profileMoment J)^2 := by
  unfold windowBudget
  have := Real.mul_self_sqrt hE
  calc Real.sqrt E * heightEnvelope t ^ J * profileMoment J *
        (Real.sqrt E * heightEnvelope t ^ J * profileMoment J)
      = (Real.sqrt E * Real.sqrt E) * (heightEnvelope t ^ J * profileMoment J)^2 := by ring
    _ = _ := by rw [this]

theorem heightEnvelope_le (t : ℝ) : heightEnvelope t ≤ (1 + 2*Real.pi)^2 * (1 + ‖t‖) := by
  unfold heightEnvelope
  have hp := Real.pi_pos
  have ht := norm_nonneg t
  have : 1 + ‖t‖ + 2*Real.pi ≤ (1 + 2*Real.pi) * (1 + ‖t‖) := by nlinarith
  nlinarith

theorem heightEnvelope_pow_le (t : ℝ) (J : ℕ) :
    (heightEnvelope t ^ J * profileMoment J)^2 ≤
      (profileMoment J^2 * (1 + 2*Real.pi)^(4*J)) * (1 + ‖t‖)^(2*J) := by
  have h0 := (heightEnvelope_pos t).le
  have h1 : heightEnvelope t ^ J ≤ ((1 + 2*Real.pi)^2 * (1 + ‖t‖))^J :=
    pow_le_pow_left₀ h0 (heightEnvelope_le t) J
  have hpm := profileMoment_nonneg J
  calc (heightEnvelope t ^ J * profileMoment J)^2 = (heightEnvelope t ^ J)^2 * profileMoment J^2 := by
        ring
    _ ≤ (((1 + 2*Real.pi)^2 * (1 + ‖t‖))^J)^2 * profileMoment J^2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg h0 _) h1 2) (sq_nonneg _)
    _ = _ := by
        rw [mul_pow, ← pow_mul, mul_pow, ← pow_mul, ← pow_mul,
          show 2 * J * 2 = 4 * J by ring, show J * 2 = 2 * J by ring]
        ring

/-- **The label part of one split at one scale.** -/
theorem split_label_at (J : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
    ∀ {L : ℝ} {θ : GData L} {mesh Z : ℝ} {η : Character} (P : SidePack η)
      (ξ : RayCharacter) (Q : Id) (m : O) (χ₀ : RayCharacter)
      (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z) (Kc R H : ℝ) (M : ℤ)
      (Mm : ℕ) (clow : ℝ) (hR : RootLabelData P Q m s ha rs Kc R H M Mm clow)
      (Mmin Mmax ε' B₀ : ℝ) (hB₀ : 0 ≤ B₀) (hHr : Mmin ≤ commonH rs ∧ commonH rs ≤ Mmax)
      (hlog : Real.logb Z 2 ≤ mesh) (hfib : FibreAt Z (Mmax + 2) θ.Bmask ε' 2)
      (hseam : ∀ labels : Finset (GLabel θ mesh Z),
        AdmissibleGroup (gFrame L θ mesh η Z) Mmin Mmax mesh ε' Z rs labels (commonH rs) →
        ∀ v : ℝ, ∑ x ∈ labels, gWeight x * gEnergy η rs x v ≤ B₀ * (1 + ‖v‖)^(2*J))
      (t : ℝ),
      splitLabel (S0 s ha) (sourceCoefficient s ha 1) (childCharacter P.base ξ) χ₀ Q m t Kc R H ≤
        (((box M).card : ℝ) * Cg * ((rs.vol / clow) * Mm * B₀) *
          (profileMoment J^2 * (1 + 2*Real.pi)^(4*J))) * (1 + ‖t‖)^(2*J) := by
  obtain ⟨Cg, hCg, hcl⟩ := class_label_bound ballProfile 0 J
  refine ⟨Cg, hCg, ?_⟩
  intro L θ mesh Z η P ξ Q m χ₀ s ha rs Kc R H M Mm clow hR Mmin Mmax ε' B₀ hB₀
    hHr hlog hfib hseam t
  set S := S0 s ha with hSdef
  set β := sourceCoefficient s ha 1 with hβdef
  set ψ := childCharacter P.base ξ with hψ
  have hZ0 : 0 < Z := zero_lt_one.trans rs.hZ
  have hvol := rs.vol_pos hZ0
  have hcl0 := hR.hclow_pos
  set Λc := rs.vol / clow with hΛc
  have hΛ : 0 ≤ Λc := by positivity
  set Ecl := Λc * Mm * B₀ with hEcl
  have hE0 : 0 ≤ Ecl := by positivity
  -- columns
  let gC : Lab S → Id := fun l => l.1.val.1
  let gD : Lab S → Id := fun l => l.1.val.2
  have hgC : IsColumn S gC := fun l => Or.inl rfl
  have hgD : IsColumn S gD := fun l => Or.inr rfl
  have hdC : ∀ l, gC l ∣ (Ideal.span {lA S l})^2 := fun l =>
    left_dvd_twist_sq _ _ (lab_data S l).1 (lab_data S l).2.2 l.2 (fun P => (hR.hcubeExp l P).1)
  have hdD : ∀ l, gD l ∣ (Ideal.span {lA S l})^2 := fun l =>
    right_dvd_twist_sq _ _ (lab_data S l).1 (lab_data S l).2.1 (lab_data S l).2.2 l.2
      (fun P => (hR.hcubeExp l P).2)
  -- the per-class bound
  have hclass : ∀ n ∈ box M,
      (∑ l ∈ (Finset.univ : Finset (Lab S)).filter
          (fun l => inRange S Kc R H l n ∧ classBlock S β ψ χ₀ Q m t Kc R l n ≠ 0),
        classWeight S Kc l n * ‖classBlock S β ψ χ₀ Q m t Kc R l n‖) ≤
      Cg * (Ecl * (heightEnvelope t ^ J * profileMoment J)^2) := by
    intro n _
    set Ls := (Finset.univ : Finset (Lab S)).filter
      (fun l => inRange S Kc R H l n ∧ classBlock S β ψ χ₀ Q m t Kc R l n ≠ 0) with hLs
    have hmem : ∀ k ∈ Ls.sigma (fun l => (classLabel ψ χ₀ Q m Kc R S n l).pool),
        k.1 ∈ Ls ∧ k.2 ∈ labelPool S k.1 := fun k hk => Finset.mem_sigma.mp hk
    have hLmem : ∀ l ∈ Ls, inRange S Kc R H l n ∧ classBlock S β ψ χ₀ Q m t Kc R l n ≠ 0 :=
      fun l hl => (Finset.mem_filter.mp hl).2
    have hwt : ∀ l : Lab S, 0 ≤ classWeight S Kc l n := by
      intro l
      unfold classWeight
      have := (normalizer_pos _ _ (lab_data S l).1 l.2).le
      have hK := hR.hKc
      have : 0 ≤ outerScalar l.1.val.1 l.1.val.2 Kc n := by unfold outerScalar; positivity
      positivity
    have hseamG : ∀ (g : Lab S → Id), IsColumn S g → (∀ l, g l ∣ (Ideal.span {lA S l})^2) →
        ∀ χ v, ∑ y ∈ (Ls.sigma (fun l => (classLabel ψ χ₀ Q m Kc R S n l).pool)).image
          (fun k => (frameData P.j₀ ξ s rs S g n χ k).toLabel (θ := θ) (mesh := mesh)
            (Z := Z) η), gWeight y * gEnergy η rs y v ≤ B₀ * (1 + ‖v‖)^(2*J) := by
      intro g hg hgd χ
      apply hseam
      rw [frame_group_raised (η := η) (P := P) (s := s) (ha := ha)
        (rs := rs) ξ g n χ]
      apply raised_admissible η Mmin Mmax ε' rs _ _ hlog hHr
      · rw [← frame_group_raised (η := η) (P := P) (s := s) (ha := ha)
          (rs := rs) ξ g n χ]
        exact frame_group_fibre hR ξ g hg hgd n χ _ (fun k hk => (hmem k hk).2) (Mmax + 2) ε' hfib
      · intro x hx
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
        exact lA_ne S k.1
    have h := hcl P ξ Q m hR.hm0 hR.hml hR.hm2 hR.hQ72 hR.hQ χ₀ s ha rs hR.hW₁ hR.hW₂ hR.ht₁
      hR.ht₂ hR.hX₁ hR.hX₂ hR.hY₁ hR.hY₂ hR.hV₀ hR.hCR S (S0_subset s ha) (S0_zero s ha) Ls
      (classLabel ψ χ₀ Q m Kc R S n) (fun l => famSpec ψ S l) (fun l => classWeight S Kc l n) hwt
      (dyadicScale (n 0) * dyadicScale (n 1) / (dyadicScale (n 2) * dyadicScale (n 3)))
      (by have := dyadicScale_pos (n 0); have := dyadicScale_pos (n 1);
          have := dyadicScale_pos (n 2); have := dyadicScale_pos (n 3); positivity)
      t (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
      (dyadicScale (n 1)) (dyadicScale_pos _)
      (fun l _ => rows_major _ _ (dyadicScale_pos _))
      Λc B₀ B₀ hΛ hB₀ hB₀ Mm
      (frameData P.j₀ ξ s rs S gC n) (frameData P.j₀ ξ s rs S gD n)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun χ k hk => frame_good hR ξ gC hgC n χ k (hmem k hk).2)
      (fun χ k hk => frame_good hR ξ gD hgD n χ k (hmem k hk).2)
      (fun _ _ => hR.hcan) (fun _ _ => hR.hcan)
      (fun χ k hk => frame_dyad hR ξ ψ χ₀ t gC n χ k (hLmem k.1 (hmem k hk).1).1
        (hLmem k.1 (hmem k hk).1).2)
      (fun χ k hk => frame_dyad hR ξ ψ χ₀ t gD n χ k (hLmem k.1 (hmem k hk).1).1
        (hLmem k.1 (hmem k hk).1).2)
      (fun χ k hk => class_frame_ratio hR ξ ψ χ₀ t gC hgC n χ k (hLmem k.1 (hmem k hk).1).2)
      (fun χ k hk => class_frame_ratio hR ξ ψ χ₀ t gD hgD n χ k (hLmem k.1 (hmem k hk).1).2)
      (fun χ => frame_mult (η := η) (P := P) (s := s) (ha := ha) (rs := rs)
        ξ gC n χ _ hR.hmultC)
      (fun χ => frame_mult (η := η) (P := P) (s := s) (ha := ha) (rs := rs)
        ξ gD n χ _ hR.hmultD)
      (hseamG gC hgC hdC) (hseamG gD hgD hdD)
    rw [pow_zero, one_mul, windowBudget_sq J t _ hE0] at h
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl
    intro l _
    rw [classBlock_eq]
  calc splitLabel S β ψ χ₀ Q m t Kc R H
      ≤ ∑ n ∈ box M, ∑ l ∈ (Finset.univ : Finset (Lab S)).filter
          (fun l => inRange S Kc R H l n ∧ classBlock S β ψ χ₀ Q m t Kc R l n ≠ 0),
        classWeight S Kc l n * ‖classBlock S β ψ χ₀ Q m t Kc R l n‖ :=
        splitLabel_le_classes S β ψ χ₀ Q m t Kc R H hR.hKc M hR.hbox
    _ ≤ ∑ _n ∈ box M, Cg * (Ecl * (heightEnvelope t ^ J * profileMoment J)^2) :=
        Finset.sum_le_sum hclass
    _ = ((box M).card : ℝ) * Cg * Ecl * (heightEnvelope t ^ J * profileMoment J)^2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ((box M).card : ℝ) * Cg * Ecl *
          ((profileMoment J^2 * (1 + 2*Real.pi)^(4*J)) * (1 + ‖t‖)^(2*J)) :=
        mul_le_mul_of_nonneg_left (heightEnvelope_pow_le t J) (by positivity)
    _ = _ := by ring

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
