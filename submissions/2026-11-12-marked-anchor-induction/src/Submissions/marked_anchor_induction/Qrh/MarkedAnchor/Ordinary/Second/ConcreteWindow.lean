/- Copyright (c) 2026 Sil. Apache-2.0.
The window form of the second split.

MISMATCH. `Second.SecondSplit.hcross` asks, for each nonfixed second label `x` and EACH
height `v`, `cross x v ≤ √(energy rL x v) · √(energy rR x v)` with the two one-sided label
energies at the SAME height `v`. The concrete nonfixed second physical block of a label
(OAI `physicalBlock … (partRows false …)`) is not of that form: its kernel
`physicalKernel … (A z) I J` is separated by the whole-kernel Fourier transform
(`physical_kernel_dyadic`, `wholeKernel`), which shifts the column heights by the window
variable `θ` (`N(I)^{iθ}`). The only available per-label estimate, OAI
`CenteredMomentSecondSupportedChildren.actual_block_from_supported_envelopes` (used by FP
`MixedPhysicalEnvelopes.actual_canonical_source_envelopes` and the forked
`MixedActualRetained`), bounds the block by `C0·Z^δ·windowBudget J₁ t E₁ · windowBudget J₂ t E₂`
from one-sided budgets `E₁, E₂` that are UNIFORM IN THE HEIGHT
(`∀ v, energy(v) ≤ E/N(t₂) · (1+|v|)^{2J}`). A pointwise-in-`v` cross bound is false for a
general bilinear form with a non-diagonal kernel, and taking per-label suprema over `v`
cannot be fed by Seam B (Seam B bounds `∑_x w_x e_x(v)` for each `v`, not
`∑_x w_x sup_v e_x(v)/(1+|v|)^{2J}`). So `SecondSplit` cannot be instantiated by the
literal blocks.

FIX (proved here, abstract). Replace `hcross` by the window hypothesis `hwindow`: for every
degree `J` and all `EL, ER ≥ 0`, if the WEIGHTED LABEL SUMS of the one-sided energies satisfy
`∀ v', ∑_x w_x e(rL, x, v') ≤ EL (1+|v'|)^{2J}` (and the same for `rR`), then
`total v ≤ zero v + fixedPart v + tail v + Cwin J · windowBudget J v EL · windowBudget J v ER`.
This is exactly the shape Seam B can feed (its bound holds at every height), and
`summed_sides_window` proves the skeleton conclusion from it, with the same quantifier order
as `Second.summed_sides`; the only change in the output is the height factor
`(heightEnvelope v ^ d · profileMoment d)²` (polynomial in `v`) and the window constant
`Cwin d`, fixed with the structural data before `Z`.

What `hwindow` needs concretely (NOT proved here): a GROUPED version of OAI
`actual_block_from_supported_envelopes`, i.e. the second-step whole-kernel estimate applied
once on the joint row type (labels × rows) — the analogue for the second step of
`First.JointKernel.summed_kernel_from_raw`. Within one dyadic class `n` the kernel ratio is
common; the classes number `O(log² Z)`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.Side
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.Second.Concrete
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
noncomputable section
open scoped BigOperators Classical
open Filter
open OAI.SevenEighths.CenteredMomentSecondWindowBudget

/-- The second split of one side in WINDOW form (replaces `SecondSplit.hcross`). `Cwin J` is
the window constant at degree `J` (fixed with the structural data, before `Z`). -/
structure SecondSplitW (F : SideFrame) (Cwin : ℕ → ℝ) where
  total : ℝ → ℝ
  zero : ℝ → ℝ
  fixedPart : ℝ → ℝ
  tail : ℝ → ℝ
  rL : F.Src
  rR : F.Src
  labels : Finset F.Label
  hweight : ∀ x ∈ labels, 0 ≤ F.weight x
  hwindow : ∀ (J : ℕ) (v EL ER : ℝ), 0 ≤ EL → 0 ≤ ER →
    (∀ v' : ℝ, ∑ x ∈ labels, F.weight x * F.energy rL x v' ≤ EL * (1 + ‖v'‖)^(2*J)) →
    (∀ v' : ℝ, ∑ x ∈ labels, F.weight x * F.energy rR x v' ≤ ER * (1 + ‖v'‖)^(2*J)) →
    total v ≤ zero v + fixedPart v + tail v +
      Cwin J * (windowBudget J v EL * windowBudget J v ER)

/-- The skeleton conclusion for window-form splits. -/
def SideSupplyW (D : StepData) (G : StepGates D) {Θ : Type}
    (Frame : Θ → ℝ → OAI.SevenEighths.HeckeFamily.Character → ℝ → SideFrame)
    (amp : AmpFamily Frame) (Cwin : Θ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, 0 < mesh → mesh ≤ meshMax →
  ∀ (θ : Θ) (η : OAI.SevenEighths.HeckeFamily.Character),
  ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
  ∀ (S : SecondSplitW (Frame θ mesh η Z) (Cwin θ)) (A c qC H : ℝ),
    AdmissibleGroup (Frame θ mesh η Z) D.Hmin D.Hmax mesh (ε/2) Z S.rL S.labels H →
    AdmissibleGroup (Frame θ mesh η Z) D.Hmin D.Hmax mesh (ε/2) Z S.rR S.labels H →
    BranchData D G (Frame θ mesh η Z) ε mesh S.rL A c qC H →
    BranchData D G (Frame θ mesh η Z) ε mesh S.rR A c qC H →
    ∀ v Z0 Zf Zt : ℝ, S.zero v ≤ Z0 → S.fixedPart v ≤ Zf → S.tail v ≤ Zt →
      S.total v ≤ Z0 + Zf + Zt +
        Cwin θ degree * (C * Real.sqrt (amp θ mesh η Z S.rL degree control *
          amp θ mesh η Z S.rR degree control) * Z^(A - c + qC + ε)) *
          (heightEnvelope v ^ degree * profileMoment degree)^2

/-- One column in either branch: Seam B output at exponent `≤ A - c + q_C + ε`
(as `Second.Side.column_exponent`). -/
theorem column_exponent' {D : StepData} (G : StepGates D) {F : SideFrame} {ε mesh : ℝ}
    (hε : 0 < ε) (hm0 : 0 ≤ mesh) (hmL : mesh ≤ G.meshL ε) {r : F.Src} {A c qC H : ℝ}
    (hb : BranchData D G F ε mesh r A c qC H) :
    (∃ w₀ : ℝ, F.logScale r + D.price.f w₀ (F.P r) (F.s r) H + ε/2 ≤ A - c + qC + ε) ∨
    (F.logScale r + (nativePrice (3/4) (by norm_num)).f 0 (F.P r) (F.s r) H + ε/2 ≤
      A - c + qC + ε) := by
  rcases hb with ⟨tl, g, htl0, htl, hfl, hH, hlog, hP, hs⟩ | ⟨hlog, hs⟩
  · left
    refine ⟨g.w, ?_⟩
    obtain ⟨hex, -, -⟩ := large_side_exponent (G.ledger_spec hε) hm0 hmL htl0 htl g hfl A c qC
    have hmono := D.price.mono g.w g.PC (F.P r) g.s (F.s r) g.H hP hs
    rw [hlog, hH]
    linarith
  · right
    have h := small_side_exponent G hε hs A c qC 0 (F.P r) H
    rw [hlog]
    linarith

theorem raise_bound' {X C C' a a' e e' Z : ℝ} {d d' : ℕ} (hX : 1 ≤ X) (hZ : 1 ≤ Z)
    (hC : 0 ≤ C) (hCC : C ≤ C') (ha : 0 ≤ a) (haa : a ≤ a') (hdd : d ≤ d') (hee : e ≤ e') :
    C * a * X^(2*d) * Z^e ≤ (C' * a' * Z^e') * X^(2*d') := by
  have h1 : X^(2*d) ≤ X^(2*d') := pow_le_pow_right₀ hX (by omega)
  have h2 : Z^e ≤ Z^e' := Real.rpow_le_rpow_of_exponent_le hZ hee
  have hZe : 0 ≤ Z^e := Real.rpow_nonneg (by linarith) _
  have hC' : 0 ≤ C' := hC.trans hCC
  have ha' : 0 ≤ a' := ha.trans haa
  calc C * a * X^(2*d) * Z^e ≤ C' * a' * X^(2*d') * Z^e' := by
        apply mul_le_mul _ h2 hZe (by positivity)
        exact mul_le_mul (mul_le_mul hCC haa ha hC') h1 (by positivity) (by positivity)
    _ = _ := by ring

/-- The window product of two Seam B column budgets `K·a·Z^E`. -/
theorem window_product (d : ℕ) (v K aL aR E Z : ℝ) (hK : 0 ≤ K) (haL : 0 ≤ aL) (hZ : 0 < Z) :
    windowBudget d v (K * aL * Z^E) * windowBudget d v (K * aR * Z^E) =
      (K * Real.sqrt (aL * aR) * Z^E) * (heightEnvelope v ^ d * profileMoment d)^2 := by
  unfold windowBudget
  have hZE : 0 ≤ Z^E := (Real.rpow_pos_of_pos hZ E).le
  have hs : Real.sqrt (K * aL * Z^E) * Real.sqrt (K * aR * Z^E) =
      K * Real.sqrt (aL * aR) * Z^E := by
    have e1 : K * aL * Z^E = (K * Z^E) * aL := by ring
    have e2 : K * aR * Z^E = (K * Z^E) * aR := by ring
    rw [e1, e2, ← Real.sqrt_mul (mul_nonneg (mul_nonneg hK hZE) haL),
      show K * Z^E * aL * (K * Z^E * aR) = (K * Z^E)^2 * (aL * aR) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hK hZE)]
    ring
  calc Real.sqrt (K * aL * Z^E) * heightEnvelope v ^ d * profileMoment d *
        (Real.sqrt (K * aR * Z^E) * heightEnvelope v ^ d * profileMoment d)
      = (Real.sqrt (K * aL * Z^E) * Real.sqrt (K * aR * Z^E)) *
          (heightEnvelope v ^ d * profileMoment d)^2 := by ring
    _ = _ := by rw [hs]

/-- **Skeleton theorem in window form**: Seam B for the step price and for the native price
give the summed side bound of every window-form second split. -/
theorem summed_sides_window (D : StepData) (G : StepGates D) {Θ : Type}
    (Frame : Θ → ℝ → OAI.SevenEighths.HeckeFamily.Character → ℝ → SideFrame)
    (amp : AmpFamily Frame) (hamp : AmpMono amp) (Cwin : Θ → ℕ → ℝ)
    (hlarge : GroupedSideBound Frame amp D.price D.Hmin D.Hmax)
    (hsmall : GroupedSideBound Frame amp (nativePrice (3/4) (by norm_num)) D.Hmin D.Hmax) :
    SideSupplyW D G Frame amp Cwin := by
  intro ε hε
  have hε2 : 0 < ε/2 := by linarith
  obtain ⟨mL, hmL, hL⟩ := hlarge (ε/2) hε2
  obtain ⟨mS, hmS, hS⟩ := hsmall (ε/2) hε2
  obtain ⟨-, -, hmeshL, -, -⟩ := G.ledger_spec hε
  refine ⟨min (min mL mS) (G.meshL ε), lt_min (lt_min hmL hmS) hmeshL, ?_⟩
  intro mesh hmesh hmm θ η
  have hm1 : mesh ≤ mL := hmm.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hm2 : mesh ≤ mS := hmm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hm3 : mesh ≤ G.meshL ε := hmm.trans (min_le_right _ _)
  obtain ⟨dL, SL, CL, hCL, hZL⟩ := hL mesh hmesh hm1 θ η
  obtain ⟨dS, SS, CS, hCS, hZS⟩ := hS mesh hmesh hm2 θ η
  refine ⟨max dL dS, SL ∪ SS, max CL CS, lt_max_of_lt_left hCL, ?_⟩
  filter_upwards [hZL, hZS, eventually_ge_atTop (1:ℝ)] with Z hZL hZS hZ1
  intro S A c qC H hadmL hadmR hbL hbR v Z0 Zf Zt h0 hf ht
  have hcol : ∀ r : (Frame θ mesh η Z).Src,
      AdmissibleGroup (Frame θ mesh η Z) D.Hmin D.Hmax mesh (ε/2) Z r S.labels H →
      BranchData D G (Frame θ mesh η Z) ε mesh r A c qC H →
      ∀ v' : ℝ,
      ∑ x ∈ S.labels, (Frame θ mesh η Z).weight x * (Frame θ mesh η Z).energy r x v' ≤
        (max CL CS * amp θ mesh η Z r (max dL dS) (SL ∪ SS) * Z^(A - c + qC + ε)) *
          (1 + ‖v'‖)^(2*max dL dS) := by
    intro r hadm hb v'
    have hX1 : (1:ℝ) ≤ 1 + ‖v'‖ := by linarith [norm_nonneg v']
    obtain ⟨hnn, hmono⟩ := hamp θ mesh η Z r
    rcases column_exponent' G hε hmesh.le hm3 hb with ⟨w₀, hex⟩ | hex
    · exact (hZL r S.labels w₀ H hadm v').trans (raise_bound' hX1 hZ1 hCL.le (le_max_left _ _)
        (hnn _ _) (hmono _ _ _ _ (le_max_left _ _) Finset.subset_union_left)
        (le_max_left _ _) hex)
    · exact (hZS r S.labels 0 H hadm v').trans (raise_bound' hX1 hZ1 hCS.le (le_max_right _ _)
        (hnn _ _) (hmono _ _ _ _ (le_max_right _ _) Finset.subset_union_right)
        (le_max_right _ _) hex)
  have hK : 0 ≤ max CL CS := le_max_of_le_left hCL.le
  have hZ0 : 0 < Z := by linarith
  have haL := (hamp θ mesh η Z S.rL).1 (max dL dS) (SL ∪ SS)
  have haR := (hamp θ mesh η Z S.rR).1 (max dL dS) (SL ∪ SS)
  have hZE : 0 ≤ Z^(A - c + qC + ε) := (Real.rpow_pos_of_pos hZ0 _).le
  have h := S.hwindow (max dL dS) v _ _ (mul_nonneg (mul_nonneg hK haL) hZE)
    (mul_nonneg (mul_nonneg hK haR) hZE) (hcol S.rL hadmL hbL) (hcol S.rR hadmR hbR)
  rw [window_product (max dL dS) v (max CL CS) _ _ _ Z hK haL hZ0] at h
  linarith

end
end Qrh.MarkedAnchor.Ordinary.Second.Concrete
