/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The second-step side bound of the cube-free step (CF Section 6), with Seam B as hypothesis.

Scalars (CF (3.1), (6.1)-(6.3)). On the C-side of a first common pair `(C, D)` with log
norms `c, d`, common radical/Möbius width `q`, total width `A = P + S` and first dual scale
`K₀ = 2A - c - d + q - 1`, an actual Gauss dyad `K = K₀ - t` and selected width `u` give,
after the D⁴ transfer, column width `a = A - c - u`, Gauss scale `k = K + 4u` and twist width
`q_C = q + c - d`, hence the packed envelope `H = 2a - k + q_C = 1 + t - 6u`
(`envelope_identity`). Seam B bounds the side at `Z^{a + q_C + price + ε}`; the step ledger
(`StepGates.ledger`, CF (6.2)-(6.3)) pays the price by the selected width,
`price ≤ u + ε/16`, so the side exponent is `A - c + q_C` up to `ε` (`large_side_exponent`).
Below the floor no block is selected (`u = 0`) and the native price `κ·s ≤ ε/16` is used
(`small_side_exponent`). The two sides balance by `q_C + q_D = 2q` (`twist_balance`), which
gives the cancellation (6.4) in the first Cauchy product.

`summed_sides`: from Seam B for the step price (large branch) and for the native price
(small branch), every second split of a side (`SecondSplit`) whose two physical columns form
admissible label groups satisfies
  `total ≤ zero + fixed + tail + C √(amp_L amp_R) (1+|v|)^{2·degree} Z^{A - c + q_C + ε}`,
with constants chosen after `ε`, the mesh, the structural data and `η`, and before `Z`. The
zero-frequency, fixed-inducing and tail bounds are inputs (supplied by the diagonal modules).
The D-Cauchy normalisation `Z^{u}` and the transfer factor `Z^{-u}` have cancelled in
`SecondSplit.total` (CF Section 4).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.sil_density_split_20261026.CubeFree.Second.Poisson
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.StepData

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.Second
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
noncomputable section
open scoped BigOperators Classical
open Filter

/-! ### Scalar identities -/

/-- CF (6.1): the packed envelope after the D⁴ transfer. -/
theorem envelope_identity (A c d q t u : ℝ) :
    let K₀ := 2*A - c - d + q - 1
    let a := A - c - u
    let k := (K₀ - t) + 4*u
    let qC := q + c - d
    2*a - k + qC = 1 + t - 6*u := by
  intro K₀ a k qC
  simp only [K₀, a, k, qC]
  ring

/-- CF (3.1): the two twist widths balance, `q_C + q_D = 2q`; hence the two side exponents
`A - c + q_C` and `A - d + q_D` add up to `2(A + q) - c - d`. -/
theorem twist_balance (A c d q : ℝ) :
    (A - c + (q + c - d)) + (A - d + (q + d - c)) = 2*(A + q) - c - d := by
  ring

/-- Large branch, CF (6.2)-(6.3): the leaf price at the side is paid by the selected width. -/
theorem large_side_exponent {D : StepData} {ε floor meshL tlL mesh tl : ℝ}
    (hL : LedgerAt D ε floor meshL tlL) (hm0 : 0 ≤ mesh) (hm : mesh ≤ meshL)
    (htl0 : 0 ≤ tl) (htl : tl ≤ tlL) (g : SideGeometry D ε mesh tl) (hw : floor ≤ g.w)
    (A c qC : ℝ) :
    (A - c - g.u) + qC + D.price.f g.w g.PC g.s g.H ≤ (A - c + qC) + ε/16 ∧
      D.Hmin ≤ g.H ∧ g.H ≤ D.Hmax := by
  obtain ⟨-, -, -, -, h⟩ := hL
  obtain ⟨h1, h2, h3⟩ := h mesh hm0 hm tl htl0 htl g hw
  exact ⟨by linarith, h1, h2⟩

/-- Small branch: no selection, native price `κ·max 0 s ≤ ε/16` below the floor. -/
theorem small_side_exponent {D : StepData} (G : StepGates D) {ε s : ℝ} (hε : 0 < ε)
    (hs : s ≤ G.floor ε) (A c qC w P M : ℝ) :
    (A - c) + qC + (nativePrice (3/4) (by norm_num)).f w P s M ≤ (A - c + qC) + ε/16 := by
  rw [nativePrice_f]
  have := G.small_price hε hs
  linarith

/-! ### Seam B on both physical columns -/

private theorem sqrt_mul_mul (K p q : ℝ) (hK : 0 ≤ K) (hp : 0 ≤ p) :
    Real.sqrt (K*p) * Real.sqrt (K*q) = K * Real.sqrt (p*q) := by
  rw [← Real.sqrt_mul (mul_nonneg hK hp), show K*p*(K*q) = K^2*(p*q) by ring,
    Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]

/-- The two one-sided Seam B bounds at a common exponent `E` give the nonfixed part. -/
theorem split_bound_of_sides {F : SideFrame} (S : SecondSplit F) (v Z0 Zf Zt K E Z aL aR : ℝ)
    (hK : 0 ≤ K) (hZ : 0 < Z) (haL : 0 ≤ aL)
    (h0 : S.zero v ≤ Z0) (hf : S.fixedPart v ≤ Zf) (ht : S.tail v ≤ Zt)
    (hL : ∑ x ∈ S.labels, F.weight x * F.energy S.rL x v ≤ K * aL * Z^E)
    (hR : ∑ x ∈ S.labels, F.weight x * F.energy S.rR x v ≤ K * aR * Z^E) :
    S.total v ≤ Z0 + Zf + Zt + K * Real.sqrt (aL * aR) * Z^E := by
  have h := S.total_le v Z0 Zf Zt _ _ h0 hf ht hL hR
  have hZE : 0 ≤ Z^E := (Real.rpow_pos_of_pos hZ E).le
  have he : Real.sqrt (K * aL * Z^E) * Real.sqrt (K * aR * Z^E) =
      K * Real.sqrt (aL * aR) * Z^E := by
    have e1 : K * aL * Z^E = (K * Z^E) * aL := by ring
    have e2 : K * aR * Z^E = (K * Z^E) * aR := by ring
    rw [e1, e2, sqrt_mul_mul _ _ _ (mul_nonneg hK hZE) haL]
    ring
  linarith

/-! ### The skeleton theorem -/

/-- Branch data of one side. Large branch: a side geometry `g` above the floor whose
selected width is the source's selected width (`logScale = A - c - u + q_C`) and whose
widths dominate the source's; the group envelope is `g.H`. Small branch: no selection
(`logScale = A - c + q_C`) and retained width below the floor. -/
def BranchData (D : StepData) (G : StepGates D) (F : SideFrame) (ε mesh : ℝ)
    (r : F.Src) (A c qC H : ℝ) : Prop :=
  (∃ tl : ℝ, ∃ g : SideGeometry D ε mesh tl, 0 ≤ tl ∧ tl ≤ G.tlL ε ∧ G.floor ε ≤ g.w ∧
      H = g.H ∧ F.logScale r = A - c - g.u + qC ∧ F.P r ≤ g.PC ∧ F.s r ≤ g.s) ∨
    (F.logScale r = A - c + qC ∧ F.s r ≤ G.floor ε)

/-- The conclusion of the second-step skeleton for one side frame family with amplitudes
`amp`: the supply of summed side bounds at exponent `A - c + q_C`. -/
def SideSupply (D : StepData) (G : StepGates D) {Θ : Type}
    (Frame : Θ → ℝ → OAI.SevenEighths.HeckeFamily.Character → ℝ → SideFrame)
    (amp : AmpFamily Frame) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, 0 < mesh → mesh ≤ meshMax →
  ∀ (θ : Θ) (η : OAI.SevenEighths.HeckeFamily.Character),
  ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
  ∀ (S : SecondSplit (Frame θ mesh η Z)) (A c qC H : ℝ),
    AdmissibleGroup (Frame θ mesh η Z) D.Hmin D.Hmax mesh (ε/2) Z S.rL S.labels H →
    AdmissibleGroup (Frame θ mesh η Z) D.Hmin D.Hmax mesh (ε/2) Z S.rR S.labels H →
    BranchData D G (Frame θ mesh η Z) ε mesh S.rL A c qC H →
    BranchData D G (Frame θ mesh η Z) ε mesh S.rR A c qC H →
    ∀ v Z0 Zf Zt : ℝ, S.zero v ≤ Z0 → S.fixedPart v ≤ Zf → S.tail v ≤ Zt →
      S.total v ≤ Z0 + Zf + Zt +
        C * Real.sqrt (amp θ mesh η Z S.rL degree control * amp θ mesh η Z S.rR degree control) *
          (1 + ‖v‖)^(2*degree) * Z^(A - c + qC + ε)

/-- One column: the Seam B output in either branch is at most `Z^{A - c + q_C + ε}`. -/
private theorem column_exponent {D : StepData} (G : StepGates D) {F : SideFrame} {ε mesh : ℝ}
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

/-- One Seam B output, raised to the common degree, seminorm set, constant and exponent. -/
private theorem raise_bound {X C C' a a' e e' Z : ℝ} {d d' : ℕ} (hX : 1 ≤ X) (hZ : 1 ≤ Z)
    (hC : 0 ≤ C) (hCC : C ≤ C') (ha : 0 ≤ a) (haa : a ≤ a') (hdd : d ≤ d') (hee : e ≤ e') :
    C * a * X^(2*d) * Z^e ≤ (C' * X^(2*d')) * a' * Z^e' := by
  have h1 : X^(2*d) ≤ X^(2*d') := pow_le_pow_right₀ hX (by omega)
  have h2 : Z^e ≤ Z^e' := Real.rpow_le_rpow_of_exponent_le hZ hee
  have hZe : 0 ≤ Z^e := Real.rpow_nonneg (by linarith) _
  have hX0 : 0 ≤ X := by linarith
  have hC' : 0 ≤ C' := hC.trans hCC
  have ha' : 0 ≤ a' := ha.trans haa
  calc C * a * X^(2*d) * Z^e ≤ C' * a' * X^(2*d') * Z^e' := by
        apply mul_le_mul _ h2 hZe (by positivity)
        exact mul_le_mul (mul_le_mul hCC haa ha hC') h1 (by positivity) (by positivity)
    _ = _ := by ring

/-- **The skeleton side theorem** (CF Sections 4-6): Seam B for the step price and for the
native price give the summed side bounds of every second split at exponent `A - c + q_C`.
The common degree is the larger degree and the common seminorm set the union. -/
theorem summed_sides (D : StepData) (G : StepGates D) {Θ : Type}
    (Frame : Θ → ℝ → OAI.SevenEighths.HeckeFamily.Character → ℝ → SideFrame)
    (amp : AmpFamily Frame) (hamp : AmpMono amp)
    (hlarge : GroupedSideBound Frame amp D.price D.Hmin D.Hmax)
    (hsmall : GroupedSideBound Frame amp (nativePrice (3/4) (by norm_num)) D.Hmin D.Hmax) :
    SideSupply D G Frame amp := by
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
  have hX1 : (1:ℝ) ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  have hcol : ∀ r : (Frame θ mesh η Z).Src,
      AdmissibleGroup (Frame θ mesh η Z) D.Hmin D.Hmax mesh (ε/2) Z r S.labels H →
      BranchData D G (Frame θ mesh η Z) ε mesh r A c qC H →
      ∑ x ∈ S.labels, (Frame θ mesh η Z).weight x * (Frame θ mesh η Z).energy r x v ≤
        (max CL CS * (1 + ‖v‖)^(2*max dL dS)) * amp θ mesh η Z r (max dL dS) (SL ∪ SS) *
          Z^(A - c + qC + ε) := by
    intro r hadm hb
    obtain ⟨hnn, hmono⟩ := hamp θ mesh η Z r
    rcases column_exponent G hε hmesh.le hm3 hb with ⟨w₀, hex⟩ | hex
    · exact (hZL r S.labels w₀ H hadm v).trans (raise_bound hX1 hZ1 hCL.le (le_max_left _ _)
        (hnn _ _) (hmono _ _ _ _ (le_max_left _ _) Finset.subset_union_left)
        (le_max_left _ _) hex)
    · exact (hZS r S.labels 0 H hadm v).trans (raise_bound hX1 hZ1 hCS.le (le_max_right _ _)
        (hnn _ _) (hmono _ _ _ _ (le_max_right _ _) Finset.subset_union_right)
        (le_max_right _ _) hex)
  have hK : 0 ≤ max CL CS * (1 + ‖v‖)^(2*max dL dS) :=
    mul_nonneg (le_max_of_le_left hCL.le) (by positivity)
  have h := split_bound_of_sides S v Z0 Zf Zt _ (A - c + qC + ε) Z _ _ hK (by linarith)
    ((hamp θ mesh η Z S.rL).1 _ _) h0 hf ht (hcol S.rL hadmL hbL) (hcol S.rR hadmR hbR)
  refine h.trans (le_of_eq ?_)
  ring

end
end Qrh.MarkedAnchor.Ordinary.Second
