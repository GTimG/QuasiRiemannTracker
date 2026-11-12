/- Copyright (c) 2026 Sil. Apache-2.0.
Provider: the concrete residual splits handed to the label stack, and the exact geometric Prop
`GeometryAt` delivered by the provider geometry (`ProviderGeometry*.lean`).

For a root input `d`, an allocation `B` of the first common factor `G` and a selected block `J`:
* `residOf d … B J := renorm (restOf d.root … B J)` (the extracted residual, `d = (1,1)`);
* `residFin d … B J : Source (Fin n) (1/4) (9/4)`, `n = #(Rest J)`: `residOf` reindexed;
* `thetaOf … n : GData 3`: the frame data (`rayM = M`, `Hray = H`, `W`, `bΦ`, `η₀`, `Q`,
  `Holes`, `a = 1/4`, `b = 9/4`, `Lcap = windowCap`, `Cap = 16`, `Bmask`);
* `frameOf d … B J mesh … V₀ kLog : GSrc (thetaOf … n) mesh Z`: the frame source (`srcOf`) of
  `residFin` with the root slot data restricted to the residual slots;
* `GeometryAt`: the box, the Poisson-cutoff dyad condition, the radical caps, the branch data with
  the exponent identity `A - c + q_C ≤ colLog + twistLog + u`, and the envelope range, for one
  split.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.Provider
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly12
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceRootGeometry

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
open CenteredMomentNaturalFixedRaySource
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedCompletedRows CenteredMomentSectorLocalization
open RepairedRawContext RepairedSourceSideSupply RepairedSourceRootGeometry
open Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeProviderResid {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-! ### The frame data -/

/-- **The frame data `θ` of the residual splits with `n` slots.** -/
def thetaOf {D : StepData} (G : StepGates D) (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ) (η₀ : Character)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (Holes N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Bmask : ℝ) (hBmask : 0 ≤ Bmask) (n : ℕ) : GData 3 where
  N := n
  rayM := M
  Hray := H
  hH := hH
  W := W
  hW := hW
  hWs := hWs
  bΦ := bΦ
  hbΦ := hbΦ
  η₀ := η₀
  Q := Q
  hQ := hQM
  hQ0 := hQ0
  hQt := hQt
  hQ72 := hQ72
  Holes := Holes
  a := 1/4
  b := 9/4
  Lcap := windowCap G N ε
  Cap := 16
  Bmask := Bmask
  ha := le_rfl
  hb1 := by norm_num
  hb := le_rfl
  hLcap := by have := windowCap_ge_eight G N ε hε; linarith
  hLL := by have := windowCap_ge_eight G N ε hε; linarith
  hCap := by norm_num
  hCapb := by norm_num
  hBmask := hBmask

/-! ### The residual splits -/

variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

/-- The extracted residual of an allocation and a selected block. -/
abbrev residOf (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    Source (Rest J) (1/4) (9/4) :=
  renorm (restOf d.root (by norm_num) d.cover C B J)

/-- The root slot of a residual slot. -/
def residSlot {d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀} {C : Id}
    {B : actualAllocations (tuplePools d.root) C} {J : Finset (liveIndices B.val)}
    (k : Fin (Fintype.card (Rest J))) : κ :=
  ((Fintype.equivFin (Rest J)).symm k).val.val

/-- **The residual split on `Fin n`.** -/
def residFin (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    Source (Fin (Fintype.card (Rest J))) (1/4) (9/4) :=
  reindexSource (residOf d C B J) (Fintype.equivFin (Rest J))

theorem residFin_X_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    (residFin d C B J).X₁ ≤ Z^(3:ℝ) ∧ (residFin d C B J).X₂ ≤ Z^(3:ℝ) ∧
      (residFin d C B J).Y₁ ≤ Z^(3:ℝ) ∧ (residFin d C B J).Y₂ ≤ Z^(3:ℝ) := by
  set r := restOf d.root (by norm_num) d.cover C B J
  have h1 := nrm_one_le r.hd.1
  have h2 := nrm_one_le r.hd.2
  have hx1 : 0 ≤ r.X₁ := (r.hL.trans_le r.hX₁).le
  have hx2 : 0 ≤ r.X₂ := (r.hL.trans_le r.hX₂).le
  have hy1 : 0 ≤ r.Y₁ := (r.hL.trans_le r.hY₁).le
  have hy2 : 0 ≤ r.Y₂ := (r.hL.trans_le r.hY₂).le
  have eX1 : r.X₁ = d.root.X₁ := rfl
  have eX2 : r.X₂ = d.root.X₂ := rfl
  have eY1 : r.Y₁ = d.root.Y₁ := rfl
  have eY2 : r.Y₂ = d.root.Y₂ := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change r.X₁ / nrm r.d.1 ≤ _
    exact (div_le_self hx1 h1).trans (eX1 ▸ d.hX₁)
  · change r.X₂ / nrm r.d.2 ≤ _
    exact (div_le_self hx2 h2).trans (eX2 ▸ d.hX₂)
  · change r.Y₁ / nrm r.d.1 ≤ _
    exact (div_le_self hy1 h1).trans (eY1 ▸ d.hY₁)
  · change r.Y₂ / nrm r.d.2 ≤ _
    exact (div_le_self hy2 h2).trans (eY2 ▸ d.hY₂)

/-- **The frame source of a residual split.** `mesh` is the slot-width bound of the root
(`min (mesh G ε) meshCap` in the provider), `V₀` the packed first twist of the side, `kLog`
the Gauss log-scale `log_Z Kc`. -/
def frameOf (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh) (V₀ : O) (hV₀ : V₀ ≠ 0) (kLog : ℝ) :
    GSrc (thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM hQ0 hQt hQ72 Holes N ε hε Bmask hBmask
      (Fintype.card (Rest J))) mesh Z :=
  srcOf (θ := thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM hQ0 hQt hQ72 Holes N ε hε Bmask hBmask
      (Fintype.card (Rest J))) (residFin d C B J) d.one_lt_Z
    (fun k => d.chars (residSlot (d := d) k)) (fun k => d.w (residSlot (d := d) k))
    (fun _ => 33/50) (fun k => d.freq (residSlot (d := d) k)) d.t₀ d.V
    (fun k => d.R₀ (residSlot (d := d) k))
    (fun k => d.hw _) (fun k => hmesh _) (fun _ => rfl) d.hV (fun k => d.hfreq _)
    (fun k => d.hholes _)
    (residFin_X_le d C B J).1 (residFin_X_le d C B J).2.1 (residFin_X_le d C B J).2.2.1
    (residFin_X_le d C B J).2.2.2 V₀ hV₀ kLog

/-! ### The second-step frequency of an allocation -/

/-- The residual norm cap `sourceNormCap(rest_B)` (`= (9/4)²·2^{#rest}·vol_B`, `cap_eq_vol`). -/
def capRes (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) : ℝ :=
  sourceNormCap (restOf d.root (by norm_num) d.cover C B J).P (9/4)
    (restOf d.root (by norm_num) d.cover C B J).T (restOf d.root (by norm_num) d.cover C B J).d

/-- **The second-step frequency `T B := Y_B²/Kc_B`**, `Y_B = max 1 (capRes)`: the diagonal
requirement `Y_B²/(16 K W_B⁴) ≤ T B` holds with equality, and with `ξr = mesh` the label
condition `32·R ≤ Z^{cutoffLog}` reduces to `32·(81/16)²·4^{#rest}·Z^{mesh/2} ≤ Z^{mesh}`
(`hdyad_of_freq`); allocations with `capRes < 1` have no nonzero residual column. -/
def Tfreq (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) (Kc : ℝ) : ℝ :=
  (max 1 (capRes d C B J))^2 / Kc

/-! ### The geometric Prop -/

/-- **The geometry of one residual split**: the dyadic box of radius
`M ≤ c_b log₂ Z + 2`, every label row below the frame Poisson cutoff (`hdyad`), the radical caps
of both genuine columns, branch data whose exponent `A - c + q_C` is at most
`colLog + twistLog + u` (`u` the selected width of the allocation), and the envelope range. -/
def GeometryAt {L : ℝ} (D : StepData) (G : StepGates D) {θ : GData L} {mesh Z : ℝ} (ε : ℝ)
    (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z)
    (Kc R H u cb : ℝ) : Prop :=
  ∃ Mbox : ℤ, (0 ≤ Mbox ∧ (Mbox : ℝ) ≤ cb * Real.logb 2 Z + 2) ∧
    (∀ l n, inRange (S0 s ha) Kc R H l n → n ∈ box Mbox) ∧
    (32 * R ≤ Z ^ cutoffLog rs) ∧
    (∀ l : Lab (S0 s ha), ∀ Lp ∈ labelPool (S0 s ha) l,
      (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport ((s.R * l.1.val.1) * Lp) ∪
        holes s.H, I) : ℝ) ≤ Z^θ.Bmask) ∧
    (∀ l : Lab (S0 s ha), ∀ Lp ∈ labelPool (S0 s ha) l,
      (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport ((s.R * l.1.val.2) * Lp) ∪
        holes s.H, I) : ℝ) ≤ Z^θ.Bmask) ∧
    (∃ A c qC : ℝ, BranchData D G (gFrame L θ mesh η Z) ε mesh rs A c qC (commonH rs) ∧
      A - c + qC ≤ rs.colLog + rs.twistLog + u) ∧
    (D.Hmin ≤ commonH rs ∧ commonH rs ≤ D.Hmax)

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
