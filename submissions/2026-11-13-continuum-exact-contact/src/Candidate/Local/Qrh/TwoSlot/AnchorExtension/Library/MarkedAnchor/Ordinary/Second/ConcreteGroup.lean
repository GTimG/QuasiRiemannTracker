/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Envelope grouping of the concrete second-step labels (CF §§5-6).

* Dyad raising (`raiseL`, `gEnergy_raise_le`): replacing a label's row dyad `n 1` by a
  dyad `k` with `2·2^{n 1} ≤ 2^k` does not decrease its frame energy, since
  `ballProfile (x/K) ≤ ballProfile (x/K')` for `2K ≤ K'` (OAI `ballProfile_radius_le`); the
  keep set of `canonicalRadial` does not depend on the dyads. Weight, twist and row relation
  are unchanged.
* The top dyad (`topDyad`): for the Poisson cutoff `E = 2a - k + mesh` the raised dyad is
  `k = ⌊log₂ (Z^E / N(A₂))⌋`, so the raised label still satisfies `Fits.dual` and its
  ORIGINAL envelope `log_Z (N(V₀A₂)·2^k)` lies in `(H - log_Z 2, H]` with the SOURCE-ONLY
  value `H = 2a - k + q₀ + mesh` (`raised_envelope`). Hence all raised labels of a source lie
  within one mesh of the common `H` once `log_Z 2 ≤ mesh` (`raised_admissible`).
* BranchData (`branch_large`, `branch_small`): the selection (Selection.lean), the side
  geometry and the scalar identity (6.1) `2a - k + q_C = 1 + t - 6u` (`Side.envelope_identity`)
  give `BranchData` for the raised group with `H = g.H`, the frequency defect of the side
  geometry being `t + mesh` (the mesh of the Poisson cutoff).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedFrame
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.Side
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.Selection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Packet.Reduce

noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
local notation "O" => HeckeFamily.O

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-! ### Monotonicity of a ball-profile energy in the radius -/

theorem restrictedEnergy_radius_le {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (K K' : ℝ) (hK : 0 < K) (hK' : 0 < K')
    (hKK : 2 * K ≤ K') :
    restrictedEnergy keep S a c ballProfile K ≤ restrictedEnergy keep S a c ballProfile K' := by
  unfold restrictedEnergy
  apply Summable.tsum_le_tsum _ (restricted_summable keep S a ha c ballProfile K hK)
    (restricted_summable keep S a ha c ballProfile K' hK')
  intro z
  by_cases hz : keep z
  · simp only [hz, ite_true]
    exact mul_le_mul_of_nonneg_left
      (CenteredMomentAmplifiedRetainedRadius.ballProfile_radius_le _ _ _ (sq_nonneg _) hK hK' hKK)
      (sq_nonneg _)
  · simp only [hz, ite_false, le_refl]

theorem sourceRestrictedEnergy_radius_le (keep : O → Prop) (Q : Finset (Ideal O))
    (c f : Ideal O → ℂ) (K K' : ℝ) (hK : 0 < K) (hK' : 0 < K') (hKK : 2 * K ≤ K') :
    sourceRestrictedEnergy keep Q c f ballProfile K ≤
      sourceRestrictedEnergy keep Q c f ballProfile K' :=
  restrictedEnergy_radius_le keep _ _ (CenteredMomentSourceRow.sourceGenerator_supported Q)
    _ K K' hK hK' hKK

/-! ### Dyad raising -/

/-- The label with its row dyad `n 1` replaced by `k`. -/
def raiseL (x : GLabel θ mesh Z) (k : ℤ) : GLabel θ mesh Z :=
  { x with n := Function.update x.n 1 k }

@[simp] theorem raiseL_n1 (x : GLabel θ mesh Z) (k : ℤ) : (raiseL x k).n 1 = k := by
  simp [raiseL]

@[simp] theorem raiseL_twist (x : GLabel θ mesh Z) (k : ℤ) : (raiseL x k).twist = x.twist :=
  rfl

theorem gWeight_raise (x : GLabel θ mesh Z) (k : ℤ) : gWeight (raiseL x k) = gWeight x := rfl

/-- `Fits` survives raising when the raised dyad satisfies the Poisson cutoff. -/
theorem fits_raise {η : Character} {r : GSrc θ mesh Z} {x : GLabel θ mesh Z} (h : Fits η r x)
    (k : ℤ)
    (hk : Real.logb Z (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale k) ≤
      2 * r.colLog - r.kLog + mesh) :
    Fits η r (raiseL x k) where
  twist_ne := h.twist_ne
  mask_ne := h.mask_ne
  coef := h.coef
  R_ne := h.R_ne
  G_ne := h.G_ne
  seed_dvd := h.seed_dvd
  D_sq := h.D_sq
  G_cap := h.G_cap
  D_cap := h.D_cap
  G_mask := h.G_mask
  holes_sub := h.holes_sub
  cap := h.cap
  holes_R₀ := h.holes_R₀
  d₁ := h.d₁
  d₂ := h.d₂
  dual := by simpa only [raiseL_n1, raiseL_twist] using hk

/-- **Raising does not decrease the literal energy.** -/
theorem rawEnergy_raise_le (η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z)
    (h : Fits η r x) (k : ℤ) (h' : Fits η r (raiseL x k))
    (hk : 2 * dyadicScale (x.n 1) ≤ dyadicScale k) (v : ℝ) :
    rawEnergy η r x h v ≤ rawEnergy η r (raiseL x k) h' v := by
  unfold rawEnergy labelEnergy
  have e : (raiseL x k).n 1 = k := raiseL_n1 x k
  rw [e]
  exact sourceRestrictedEnergy_radius_le _ _ _ _ _ _ (dyadicScale_pos _) (dyadicScale_pos _) hk

/-- **Raising does not decrease the frame energy.** -/
theorem gEnergy_raise_le (η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (k : ℤ)
    (hk : 2 * dyadicScale (x.n 1) ≤ dyadicScale k)
    (hdual : Real.logb Z (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale k) ≤
      2 * r.colLog - r.kLog + mesh) (v : ℝ) :
    gEnergy η r x v ≤ gEnergy η r (raiseL x k) v := by
  by_cases h : Fits η r x
  · have h' := fits_raise h k hdual
    unfold gEnergy
    rw [dif_pos h, dif_pos h']
    have hZ : 0 ≤ r.norm :=
      div_nonneg (Real.rpow_nonneg (zero_le_one.trans r.hZ.le) _) (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left (rawEnergy_raise_le η r x h k h' hk v) (by positivity)
  · have h0 : gEnergy η r x v = 0 := by unfold gEnergy; rw [dif_neg h]
    rw [h0]
    exact (gFrame L θ mesh η Z).energy_nonneg r (raiseL x k) v

/-! ### The top dyad -/

/-- The largest dyad `k` with `N·2^k ≤ T`. -/
def topDyad (T N : ℝ) : ℤ := ⌊Real.logb 2 (T / N)⌋

theorem topDyad_spec (T N : ℝ) (hT : 0 < T) (hN : 0 < N) :
    N * dyadicScale (topDyad T N) ≤ T ∧ T < 2 * (N * dyadicScale (topDyad T N)) := by
  have hq : 0 < T / N := div_pos hT hN
  have h1 : (2:ℝ) ^ (topDyad T N : ℝ) ≤ T / N := by
    have := Int.floor_le (Real.logb 2 (T / N))
    calc (2:ℝ) ^ (topDyad T N : ℝ) ≤ (2:ℝ) ^ (Real.logb 2 (T / N)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = T / N := Real.rpow_logb (by norm_num) (by norm_num) hq
  have h2 : T / N < (2:ℝ) ^ ((topDyad T N : ℝ) + 1) := by
    have := Int.lt_floor_add_one (Real.logb 2 (T / N))
    calc T / N = (2:ℝ) ^ (Real.logb 2 (T / N)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hq).symm
      _ < (2:ℝ) ^ ((topDyad T N : ℝ) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) this
  have hd : dyadicScale (topDyad T N) = (2:ℝ) ^ (topDyad T N : ℝ) := by
    unfold dyadicScale; rw [Real.rpow_intCast]
  rw [hd]
  rw [Real.rpow_add (by norm_num), Real.rpow_one] at h2
  constructor
  · rw [le_div_iff₀ hN] at h1; linarith
  · rw [div_lt_iff₀ hN] at h2; linarith

/-- A dyad whose double fits below `T` is at least one step below the top dyad. -/
theorem dyad_lt_top (T N : ℝ) (hT : 0 < T) (hN : 0 < N) (n : ℤ)
    (hn : 2 * (N * dyadicScale n) ≤ T) : 2 * dyadicScale n ≤ dyadicScale (topDyad T N) := by
  obtain ⟨-, h2⟩ := topDyad_spec T N hT hN
  have hlt : dyadicScale (n + 1) < 2 * dyadicScale (topDyad T N) := by
    rw [dyadicScale_add]
    have : N * (2 * dyadicScale n) < N * (2 * dyadicScale (topDyad T N)) := by nlinarith
    exact lt_of_mul_lt_mul_left this hN.le
  have hle : n + 1 ≤ topDyad T N := by
    by_contra hc
    push_neg at hc
    have h3 : topDyad T N + 1 ≤ n + 1 := by omega
    have h4 : dyadicScale (topDyad T N + 1) ≤ dyadicScale (n + 1) := by
      unfold dyadicScale; exact zpow_le_zpow_right₀ (by norm_num) h3
    rw [dyadicScale_add] at h4
    linarith
  have h5 : dyadicScale (n + 1) ≤ dyadicScale (topDyad T N) := by
    unfold dyadicScale; exact zpow_le_zpow_right₀ (by norm_num) hle
  rw [dyadicScale_add] at h5
  exact h5

/-- The Poisson cutoff `Z^{2a - k + mesh}` of a source. -/
def cutoffLog (r : GSrc θ mesh Z) : ℝ := 2 * r.colLog - r.kLog + mesh

/-- The source-only common envelope `H = 2a - k + q₀ + mesh` of the raised labels. -/
def commonH (r : GSrc θ mesh Z) : ℝ := cutoffLog r + r.twistLog

/-- The raised dyad of a label on a source. -/
def raisedDyad (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) : ℤ :=
  topDyad (Z ^ cutoffLog r) ((Ideal.span {x.twist}).absNorm : ℝ)

/-- The raised label. -/
def raised (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) : GLabel θ mesh Z :=
  raiseL x (raisedDyad r x)

theorem raised_twist (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) : (raised r x).twist = x.twist :=
  rfl

theorem gWeight_raised (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) :
    gWeight (raised r x) = gWeight x := rfl

private theorem logb_le_of_le {Z u T : ℝ} (hZ : 1 < Z) (hu : 0 < u) (h : u ≤ Z ^ T) :
    Real.logb Z u ≤ T := by
  rw [Real.logb_le_iff_le_rpow hZ hu]; exact h

/-- The raised dyad satisfies the Poisson cutoff (`Fits.dual`). -/
theorem raised_dual (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (hx : x.twist ≠ 0) :
    Real.logb Z (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (raisedDyad r x)) ≤
      2 * r.colLog - r.kLog + mesh := by
  have hZ0 : 0 < Z := zero_lt_one.trans r.hZ
  have hN := absNorm_span_pos x.twist hx
  obtain ⟨h1, -⟩ := topDyad_spec (Z ^ cutoffLog r) _ (Real.rpow_pos_of_pos hZ0 _) hN
  exact logb_le_of_le r.hZ (mul_pos hN (dyadicScale_pos _)) h1

theorem fits_raised {η : Character} {r : GSrc θ mesh Z} {x : GLabel θ mesh Z} (h : Fits η r x) :
    Fits η r (raised r x) :=
  fits_raise h _ (raised_dual r x h.twist_ne)

/-- Labels whose doubled dyad is below the cutoff are dominated by their raised labels. -/
theorem gEnergy_le_raised (η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z)
    (hx : x.twist ≠ 0)
    (hlow : Real.logb Z (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (x.n 1)) +
      Real.logb Z 2 ≤ 2 * r.colLog - r.kLog + mesh) (v : ℝ) :
    gEnergy η r x v ≤ gEnergy η r (raised r x) v := by
  have hZ0 : 0 < Z := zero_lt_one.trans r.hZ
  have hN := absNorm_span_pos x.twist hx
  refine gEnergy_raise_le η r x _ ?_ (raised_dual r x hx) v
  show 2 * dyadicScale (x.n 1) ≤ dyadicScale (topDyad (Z ^ cutoffLog r) _)
  apply dyad_lt_top _ _ (Real.rpow_pos_of_pos hZ0 _) hN
  have hpos : 0 < ((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (x.n 1) :=
    mul_pos hN (dyadicScale_pos _)
  have h2 : Real.logb Z (2 * (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (x.n 1))) ≤
      cutoffLog r := by
    rw [Real.logb_mul (by norm_num) hpos.ne']
    unfold cutoffLog; linarith
  rwa [Real.logb_le_iff_le_rpow r.hZ (by positivity)] at h2

/-- **The raised envelope.** `H - log_Z 2 < env ≤ H` with the source-only `H`. -/
theorem raised_envelope (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (hx : x.twist ≠ 0) :
    commonH r - Real.logb Z 2 < gEnvelope r (raised r x) ∧
      gEnvelope r (raised r x) ≤ commonH r := by
  have hZ0 : 0 < Z := zero_lt_one.trans r.hZ
  have hN := absNorm_span_pos x.twist hx
  obtain ⟨h1, h2⟩ := topDyad_spec (Z ^ cutoffLog r) _ (Real.rpow_pos_of_pos hZ0 _) hN
  have hpos : 0 < ((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (raisedDyad r x) :=
    mul_pos hN (dyadicScale_pos _)
  have henv : gEnvelope r (raised r x) = r.twistLog +
      Real.logb Z (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (raisedDyad r x)) := by
    rw [gEnvelope_eq r (raised r x) hx]
    rfl
  have hup := logb_le_of_le r.hZ hpos h1
  have hlo : cutoffLog r < Real.logb Z 2 +
      Real.logb Z (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (raisedDyad r x)) := by
    rw [← Real.logb_mul (by norm_num) hpos.ne', Real.lt_logb_iff_rpow_lt r.hZ (by positivity)]
    exact h2
  rw [henv]
  unfold commonH
  constructor <;> linarith

/-- **The admissible group after raising** (envelope and weight clauses of
`Second.AdmissibleGroup`, together with a fibre bound supplied by the caller). -/
theorem raised_admissible (η : Character) (Mmin Mmax ε : ℝ) (r : GSrc θ mesh Z)
    (labels : Finset (GLabel θ mesh Z)) (hne : ∀ x ∈ labels, x.twist ≠ 0)
    (hlog : Real.logb Z 2 ≤ mesh) (hH : Mmin ≤ commonH r ∧ commonH r ≤ Mmax)
    (hfib : ∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm : ℝ) ≤ Z^(Mmax + 2) →
      ∑ x ∈ (labels.image (raised r)).filter (fun x => x.twist ∣ y), gWeight x ≤ Z^(ε/8)) :
    AdmissibleGroup (gFrame L θ mesh η Z) Mmin Mmax mesh ε Z r (labels.image (raised r))
      (commonH r) := by
  refine ⟨hH.1, hH.2, ?_, fun x _ => gWeight_nonneg x, hfib⟩
  intro x hx
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨h1, h2⟩ := raised_envelope r x₀ (hne x₀ hx₀)
  change |gEnvelope r (raised r x₀) - commonH r| ≤ mesh
  rw [abs_le]
  constructor <;> linarith

/-- Resetting the dyad vector. -/
def setN (x : GLabel θ mesh Z) (n : Fin 4 → ℤ) : GLabel θ mesh Z := { x with n := n }

theorem setN_raiseL (x : GLabel θ mesh Z) (k : ℤ) : setN (raiseL x k) x.n = x := by
  cases x; rfl

/-- On a set of labels with a common dyad vector the raising is injective. -/
theorem raised_injOn (r : GSrc θ mesh Z) (labels : Finset (GLabel θ mesh Z)) (n₀ : Fin 4 → ℤ)
    (hn : ∀ x ∈ labels, x.n = n₀) : Set.InjOn (raised r) labels := by
  intro x hx y hy hxy
  calc x = setN (raised r x) x.n := (setN_raiseL x _).symm
    _ = setN (raised r x) n₀ := by rw [hn x hx]
    _ = setN (raised r y) n₀ := by rw [hxy]
    _ = setN (raised r y) y.n := by rw [hn y hy]
    _ = y := setN_raiseL y _

/-- **The raised group dominates the original group** (common dyad vector, every doubled
dyad below the Poisson cutoff). -/
theorem sum_le_raised (η : Character) (r : GSrc θ mesh Z) (labels : Finset (GLabel θ mesh Z))
    (n₀ : Fin 4 → ℤ) (hn : ∀ x ∈ labels, x.n = n₀) (hne : ∀ x ∈ labels, x.twist ≠ 0)
    (hlow : ∀ x ∈ labels,
      Real.logb Z (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (x.n 1)) +
        Real.logb Z 2 ≤ 2 * r.colLog - r.kLog + mesh) (v : ℝ) :
    ∑ x ∈ labels, gWeight x * gEnergy η r x v ≤
      ∑ x ∈ labels.image (raised r), gWeight x * gEnergy η r x v := by
  rw [Finset.sum_image (raised_injOn r labels n₀ hn)]
  apply Finset.sum_le_sum
  intro x hx
  rw [gWeight_raised]
  exact mul_le_mul_of_nonneg_left (gEnergy_le_raised η r x (hne x hx) (hlow x hx) v)
    (gWeight_nonneg x)

/-! ### Branch data -/

section Branch
open QRH.SilDensitySplit.CubeFree Qrh.MarkedAnchor.Ordinary

/-- The scalar side data of a raised source: CF (6.1) with `a = A - c - u`, `k = K₀ - t + 4u`,
`q₀ = q_C = q + c - d`. -/
structure SideScalars (r : GSrc θ mesh Z) (A c d q t u : ℝ) : Prop where
  col : r.colLog = A - c - u
  gauss : r.kLog = (2*A - c - d + q - 1 - t) + 4*u
  twist : r.twistLog = q + c - d

theorem SideScalars.commonH_eq {r : GSrc θ mesh Z} {A c d q t u : ℝ}
    (h : SideScalars r A c d q t u) : commonH r = 1 + (t + mesh) - 6*u := by
  unfold commonH cutoffLog
  rw [h.col, h.gauss, h.twist]
  ring

theorem SideScalars.logScale {r : GSrc θ mesh Z} {A c d q t u : ℝ}
    (h : SideScalars r A c d q t u) :
    r.colLog + r.twistLog = A - c - u + (q + c - d) := by
  rw [h.col, h.twist]

/-- **Large-branch BranchData** for a raised group: the side geometry with frequency defect
`t + mesh`, selected width `u` (one upward mesh error, Selection.lean), retained width
`∑ wᵢ ≤ S - f - u` and ordinary width `P ≤ P_C`. -/
theorem branch_large (D : StepData) (G : StepGates D) (η : Character) (ε tl : ℝ)
    (r : GSrc θ mesh Z) (A c d q t u : ℝ) (hsc : SideScalars r A c d q t u)
    (S f cg PC : ℝ) (hS : D.s₀ ≤ S ∧ S ≤ D.c) (hf : 0 ≤ f ∧ f ≤ cg) (hPC : 0 ≤ PC)
    (hroot : PC + (cg - f) + D.L*S ≤ D.B + tl)
    (hsel : D.sel ε (S - f) ≤ u ∧ u ≤ D.sel ε (S - f) + mesh)
    (hs : (∑ i, r.w i) ≤ S - f - u) (hP : gP r ≤ PC)
    (htl0 : 0 ≤ tl) (htl : tl ≤ G.tlL ε) (ht : -tl ≤ t + mesh ∧ t + mesh ≤ 1 + 6*u + tl)
    (hfloor : G.floor ε ≤ S - f) :
    BranchData D G (gFrame L θ mesh η Z) ε mesh r A c (q + c - d) (commonH r) := by
  left
  let g : SideGeometry D ε mesh tl :=
    { S := S, f := f, cg := cg, PC := PC, u := u, s := ∑ i, r.w i, t := t + mesh
      hS := hS, hf := hf, hPC := hPC, hroot := hroot, hsel := hsel
      hs := ⟨Finset.sum_nonneg fun i _ => r.hw i, hs⟩, ht := ht }
  refine ⟨tl, g, htl0, htl, hfloor, ?_, ?_, hP, le_rfl⟩
  · rw [hsc.commonH_eq]; rfl
  · change r.colLog + r.twistLog = A - c - u + (q + c - d)
    exact hsc.logScale

/-- **Small-branch BranchData**: nothing selected (`u = 0`) and the retained width below the
floor. -/
theorem branch_small (D : StepData) (G : StepGates D) (η : Character) (ε : ℝ)
    (r : GSrc θ mesh Z) (A c d q t : ℝ) (hsc : SideScalars r A c d q t 0)
    (hs : (∑ i, r.w i) ≤ G.floor ε) :
    BranchData D G (gFrame L θ mesh η Z) ε mesh r A c (q + c - d) (commonH r) := by
  right
  refine ⟨?_, hs⟩
  change r.colLog + r.twistLog = A - c + (q + c - d)
  rw [hsc.logScale]; ring

/-- Envelope range on the large branch (the ledger, CF (6.2)). -/
theorem commonH_range_large (D : StepData) (G : StepGates D) {ε : ℝ} (hε : 0 < ε) (tl : ℝ)
    (r : GSrc θ mesh Z) (A c d q t u : ℝ) (hsc : SideScalars r A c d q t u)
    (S f cg PC : ℝ) (hS : D.s₀ ≤ S ∧ S ≤ D.c) (hf : 0 ≤ f ∧ f ≤ cg) (hPC : 0 ≤ PC)
    (hroot : PC + (cg - f) + D.L*S ≤ D.B + tl)
    (hsel : D.sel ε (S - f) ≤ u ∧ u ≤ D.sel ε (S - f) + mesh)
    (s : ℝ) (hs : 0 ≤ s ∧ s ≤ S - f - u)
    (hm0 : 0 ≤ mesh) (hm : mesh ≤ G.meshL ε)
    (htl0 : 0 ≤ tl) (htl : tl ≤ G.tlL ε) (ht : -tl ≤ t + mesh ∧ t + mesh ≤ 1 + 6*u + tl)
    (hfloor : G.floor ε ≤ S - f) :
    D.Hmin ≤ commonH r ∧ commonH r ≤ D.Hmax := by
  let g : SideGeometry D ε mesh tl :=
    { S := S, f := f, cg := cg, PC := PC, u := u, s := s, t := t + mesh
      hS := hS, hf := hf, hPC := hPC, hroot := hroot, hsel := hsel, hs := hs, ht := ht }
  obtain ⟨-, h1, h2⟩ := large_side_exponent (G.ledger_spec hε) hm0 hm htl0 htl g hfloor A c 0
  rw [hsc.commonH_eq]
  exact ⟨h1, h2⟩

/-- Envelope range on the small branch (`StepGates.small_envelope`). -/
theorem commonH_range_small (D : StepData) (G : StepGates D) (tl : ℝ)
    (r : GSrc θ mesh Z) (A c d q t : ℝ) (hsc : SideScalars r A c d q t 0)
    (htl : tl ≤ 1 - D.Hmin) (ht : -tl ≤ t + mesh ∧ t + mesh ≤ 1 + tl) :
    D.Hmin ≤ commonH r ∧ commonH r ≤ D.Hmax := by
  rw [hsc.commonH_eq, show 1 + (t + mesh) - 6*(0:ℝ) = 1 + (t + mesh) by ring]
  exact G.small_envelope htl ht

/-- The selection of the large branch in the form of the side geometry: the chosen block of
the live slots has width `u ∈ [sel S, sel S + mesh]` and leaves the live width `S - u`
(`Selection.chosen_large`). -/
theorem selection_scalars (D : StepData) (ε : ℝ) {ι : Type*} [Fintype ι] (Lv : Finset ι)
    (w : ι → ℝ) (rho : ℝ) (hm : 0 ≤ mesh) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hsel : 0 ≤ D.sel ε (Selection.liveWidth Lv w) ∧
      D.sel ε (Selection.liveWidth Lv w) ≤ Selection.liveWidth Lv w)
    (hlarge : rho < Selection.liveWidth Lv w) :
    let J := Selection.chosenSlots Lv w (D.sel ε) rho mesh hm hw hwm hsel
    D.sel ε (Selection.liveWidth Lv w) ≤ (∑ j ∈ J, w j.val) ∧
      (∑ j ∈ J, w j.val) ≤ D.sel ε (Selection.liveWidth Lv w) + mesh ∧
      (∑ j ∈ Finset.univ \ J, w j.val) = Selection.liveWidth Lv w - (∑ j ∈ J, w j.val) :=
  Selection.chosen_large Lv w (D.sel ε) rho mesh hm hw hwm hsel hlarge

/-- The raising depends on the source only through its Poisson cutoff (so the two physical
columns of a split, with equal `2a - k`, raise every label identically). -/
theorem raised_congr {r r' : GSrc θ mesh Z} (h : cutoffLog r = cutoffLog r') :
    raised r = raised r' := by
  funext x
  unfold raised raisedDyad
  rw [h]

theorem commonH_congr {r r' : GSrc θ mesh Z} (h : cutoffLog r = cutoffLog r')
    (h' : r.twistLog = r'.twistLog) : commonH r = commonH r' := by
  unfold commonH; rw [h, h']

/-- **Large branch, assembled**: the raised group of a source is admissible at the source-only
envelope `H = 1 + (t + mesh) - 6u` and carries the branch data at the same `H`
(given the fibre bound). -/
theorem raised_group_large (D : StepData) (G : StepGates D) (η : Character) {ε : ℝ} (hε : 0 < ε)
    (tl : ℝ) (r : GSrc θ mesh Z) (labels : Finset (GLabel θ mesh Z))
    (hne : ∀ x ∈ labels, x.twist ≠ 0) (hlog : Real.logb Z 2 ≤ mesh)
    (A c d q t u : ℝ) (hsc : SideScalars r A c d q t u)
    (S f cg PC : ℝ) (hS : D.s₀ ≤ S ∧ S ≤ D.c) (hf : 0 ≤ f ∧ f ≤ cg) (hPC : 0 ≤ PC)
    (hroot : PC + (cg - f) + D.L*S ≤ D.B + tl)
    (hsel : D.sel ε (S - f) ≤ u ∧ u ≤ D.sel ε (S - f) + mesh)
    (hs : (∑ i, r.w i) ≤ S - f - u) (hP : gP r ≤ PC)
    (hm0 : 0 ≤ mesh) (hm : mesh ≤ G.meshL ε)
    (htl0 : 0 ≤ tl) (htl : tl ≤ G.tlL ε) (ht : -tl ≤ t + mesh ∧ t + mesh ≤ 1 + 6*u + tl)
    (hfloor : G.floor ε ≤ S - f)
    (hfib : ∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm : ℝ) ≤ Z^(D.Hmax + 2) →
      ∑ x ∈ (labels.image (raised r)).filter (fun x => x.twist ∣ y), gWeight x ≤
        Z^((ε/2)/8)) :
    AdmissibleGroup (gFrame L θ mesh η Z) D.Hmin D.Hmax mesh (ε/2) Z r (labels.image (raised r))
        (commonH r) ∧
      BranchData D G (gFrame L θ mesh η Z) ε mesh r A c (q + c - d) (commonH r) := by
  have hrange := commonH_range_large D G hε tl r A c d q t u hsc S f cg PC hS hf hPC hroot hsel
    (∑ i, r.w i) ⟨Finset.sum_nonneg fun i _ => r.hw i, hs⟩ hm0 hm htl0 htl ht hfloor
  exact ⟨raised_admissible η D.Hmin D.Hmax (ε/2) r labels hne hlog hrange hfib,
    branch_large D G η ε tl r A c d q t u hsc S f cg PC hS hf hPC hroot hsel hs hP htl0 htl ht
      hfloor⟩

/-- **Small branch, assembled.** -/
theorem raised_group_small (D : StepData) (G : StepGates D) (η : Character) (ε tl : ℝ)
    (r : GSrc θ mesh Z) (labels : Finset (GLabel θ mesh Z))
    (hne : ∀ x ∈ labels, x.twist ≠ 0) (hlog : Real.logb Z 2 ≤ mesh)
    (A c d q t : ℝ) (hsc : SideScalars r A c d q t 0) (hs : (∑ i, r.w i) ≤ G.floor ε)
    (htl : tl ≤ 1 - D.Hmin) (ht : -tl ≤ t + mesh ∧ t + mesh ≤ 1 + tl)
    (hfib : ∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm : ℝ) ≤ Z^(D.Hmax + 2) →
      ∑ x ∈ (labels.image (raised r)).filter (fun x => x.twist ∣ y), gWeight x ≤
        Z^((ε/2)/8)) :
    AdmissibleGroup (gFrame L θ mesh η Z) D.Hmin D.Hmax mesh (ε/2) Z r (labels.image (raised r))
        (commonH r) ∧
      BranchData D G (gFrame L θ mesh η Z) ε mesh r A c (q + c - d) (commonH r) :=
  ⟨raised_admissible η D.Hmin D.Hmax (ε/2) r labels hne hlog
      (commonH_range_small D G tl r A c d q t hsc htl ht) hfib,
    branch_small D G η ε r A c d q t hsc hs⟩

/-- `log_Z 2 ≤ mesh` eventually. -/
theorem eventually_logb_two_le (mesh : ℝ) (hm : 0 < mesh) :
    ∀ᶠ Z : ℝ in atTop, Real.logb Z 2 ≤ mesh := by
  have h := (tendsto_rpow_atTop (show (0:ℝ) < mesh by positivity)).eventually_ge_atTop (2:ℝ)
  filter_upwards [h, eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  rw [Real.logb_le_iff_le_rpow hZ1 (by norm_num)]
  exact hZ

end Branch

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
