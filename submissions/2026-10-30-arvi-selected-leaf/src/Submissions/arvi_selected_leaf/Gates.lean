/-
Scalar step data and gates of the selected-leaf native step.

Same geometry as Sil's native cube-free step (`CubeFree.nativeData`), with the leaf price
`e5Price K = max (K · deletionNeed) selExcess` in place of `(3/4) · deletionNeed`. The ledger has
two branches:
* deletion at the cut `K`: Sil's native retention/overshoot argument with `3/4 → K`;
* the selected large sieve: `selExcess PC s H ≤ u + ε/16`, which follows from the principal gate
  `L > 2 + 9a/2` alone (it gives both `4a ≤ L - 1` and `14a/5 ≤ 4L/5 - 1`).
-/
import Submissions.sil_density_split_20261026.CubeFree.StepData
import Submissions.arvi_selected_leaf.Price

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree

/-- Scalar gates of one selected-leaf native step from parent `p` to child `n`, selected fraction
`a`, deletion cut `K`. -/
structure E5Gates (p n : Face) (a K : ℝ) : Prop where
  retention : 0 < a - K * (p.L - n.L + (6*p.B - p.L)*a) / p.L
  cap : 0 < p.c*(1 - 6*a*n.c) - (1-a)*n.c
  principal : 0 < n.L - 2 - 9/2*a
  diagonal : 0 < n.L - 1 - 4*a
  secondRef : 0 < 3/2*n.L - 5/2 - 9/2*a
  refPos : 0 < 1/6 - (1+3/2*a)*n.c
  H : 0 < 1 - 6*a*n.c
  overshoot : 0 < 1 - K*(6*p.B - p.L)/p.L
  B_le : n.B ≤ p.B
  B_lt : p.B < 1
  cap_lt : p.c < 1/6
  cap_pos : 0 < n.c
  a_pos : 0 < a
  a_lt : a < 1
  L_lt : n.L < p.L
  K_pos : 0 < K
  K_le : K ≤ 3/4

namespace E5Gates
variable {p n : Face} {a K : ℝ}

theorem L₀_pos (h : E5Gates p n a K) : 0 < p.L := by
  have := h.principal; have := h.L_lt; have := h.a_pos; linarith

theorem c_lt (h : E5Gates p n a K) : n.c < 1/6 := by
  have := h.refPos; have := h.cap_pos; have := h.a_pos; nlinarith

end E5Gates

/-- Step data of the selected-leaf native step. -/
def e5Data (p n : Face) (a K : ℝ) (h : E5Gates p n a K) : StepData where
  B₀ := p.B
  L₀ := p.L
  c₀ := p.c
  B := n.B
  L := n.L
  c := n.c
  κ := 3/4
  s₀ := 0
  Hmin := (1 - 6*a*n.c)/2
  Hmax := 3
  sel := fun _ w => a * w
  price := e5Price K p.B p.L p.c h.K_pos.le h.L₀_pos

section ledger
variable {p n : Face} {a K : ℝ}

/-- Retention and overshoot at the cut `K` (Sil's `native_retention_aux` with `3/4 → K ≤ 3/4`). -/
theorem cut_retention_aux {B₀ L L₀ w u tl ε : ℝ} (hL₀ : 0 < L₀) (hB₀ : 0 ≤ B₀)
    (hB₁ : B₀ < 1) (hw : 0 ≤ w) (hu0 : a*w ≤ u) (htl : 0 ≤ tl) (htlε : tl ≤ L₀*ε/24)
    (hK1 : K ≤ 3/4)
    (hret : 0 < a - K*(L₀ - L + (6*B₀ - L₀)*a)/L₀)
    (hov : 0 < 1 - K*(6*B₀ - L₀)/L₀) :
    K*(((L₀ - L)*w + (6*B₀ - L₀)*u + (B₀*tl + tl))/L₀) ≤ u + ε/16 := by
  have e1 : K*(((L₀ - L)*w + (6*B₀ - L₀)*u + (B₀*tl + tl))/L₀) =
      u - (a - K*(L₀ - L + (6*B₀ - L₀)*a)/L₀)*w
        - (1 - K*(6*B₀ - L₀)/L₀)*(u - a*w) + K*((B₀*tl + tl)/L₀) := by
    field_simp; ring
  rw [e1]
  have h1 := mul_nonneg hret.le hw
  have h2 := mul_nonneg hov.le (show 0 ≤ u - a*w by linarith)
  have h3 : (B₀*tl + tl)/L₀ ≤ ε/12 := by
    rw [div_le_iff₀ hL₀]
    linarith [mul_nonneg (show 0 ≤ 1 - B₀ by linarith) htl]
  have h4 : K*((B₀*tl + tl)/L₀) ≤ ε/16 := by
    have h5 : 0 ≤ (B₀*tl + tl)/L₀ := div_nonneg (by positivity) hL₀.le
    calc K*((B₀*tl + tl)/L₀) ≤ 3/4*((B₀*tl + tl)/L₀) := mul_le_mul_of_nonneg_right hK1 h5
      _ ≤ 3/4*(ε/12) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = ε/16 := by ring
  linarith

/-- **The selected branch of the ledger.** On every side geometry the reflected selected large
sieve is paid by the selected width. -/
theorem sel_branch_aux {B L PC cg f S u s t tl mesh ε : ℝ}
    (hB : B < 1) (hL : 2 + 9/2*a < L) (ha : 0 ≤ a)
    (hS : 0 ≤ S) (hf : 0 ≤ f) (hfcg : f ≤ cg)
    (hroot : PC + (cg - f) + L*S ≤ B + tl)
    (hu0 : 0 ≤ u) (hu1 : u ≤ a*(S - f) + mesh) (hs : s ≤ S - f - u) (ht : -tl ≤ t)
    (hε : 0 < ε) (hmesh : 4*mesh + 2*tl ≤ ε/16) (hmesh' : 14/5*mesh + 8/5*tl ≤ ε/16) :
    selExcess PC s (1 + t - 6*u) ≤ u + ε/16 := by
  have haS : a*(S - f) ≤ a*S := mul_le_mul_of_nonneg_left (by linarith) ha
  unfold selExcess
  apply max_le
  · linarith
  · rcases le_total (1 + t - 6*u - PC) 0 with hH | hH
    · rw [max_eq_left (by linarith)]
      have h1 := mul_nonneg (show 0 ≤ L - 1 - 4*a by linarith) hS
      nlinarith
    · rw [max_eq_right (by linarith)]
      have h1 := mul_nonneg (show 0 ≤ 4/5*L - 1 - 14/5*a by linarith) hS
      nlinarith

end ledger

variable {p n : Face} {a K : ℝ}

/-- The selected-leaf ledger: Sil's native ledger at the cut `K`, plus the selected branch. -/
theorem e5_ledger (h : E5Gates p n a K) {ε : ℝ} (hε : 0 < ε) :
    LedgerAt (e5Data p n a K h) ε (ε/16)
      (min (min ((1 - 6*a*n.c)/24) ((p.c*(1 - 6*a*n.c) - (1-a)*n.c)/2)) (ε/128))
      (min (min ((1 - 6*a*n.c)/4) 1)
        (min (3*(p.c*(1 - 6*a*n.c) - (1-a)*n.c)) (min (p.L*ε/24) (ε/128)))) := by
  have hh0 : 0 < 1 - 6*a*n.c := h.H
  have hcap : 0 < p.c*(1 - 6*a*n.c) - (1-a)*n.c := h.cap
  have hL₀ := h.L₀_pos
  refine ⟨by positivity, ?_, lt_min (lt_min (by positivity) (by positivity)) (by positivity),
    lt_min (lt_min (by positivity) one_pos) (lt_min (by positivity) (lt_min (by positivity)
      (by positivity))), ?_⟩
  · show ε/16 ≤ ε/(16*(3/4))
    apply div_le_div_of_nonneg_left hε.le (by norm_num) (by norm_num)
  intro mesh hmesh hmeshL tl htl htlL g hfloor
  have hm1 : mesh ≤ (1 - 6*a*n.c)/24 := hmeshL.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hm2 : mesh ≤ (p.c*(1 - 6*a*n.c) - (1-a)*n.c)/2 :=
    hmeshL.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hm3 : mesh ≤ ε/128 := hmeshL.trans (min_le_right _ _)
  have ht1 : tl ≤ (1 - 6*a*n.c)/4 :=
    htlL.trans ((min_le_left _ _).trans (min_le_left _ _))
  have ht2 : tl ≤ 1 := htlL.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht3 : tl ≤ 3*(p.c*(1 - 6*a*n.c) - (1-a)*n.c) :=
    htlL.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht4 : tl ≤ p.L*ε/24 :=
    htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht5 : tl ≤ ε/128 :=
    htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hS := g.hS
  have hf := g.hf
  have hPC := g.hPC
  have hroot := g.hroot
  have hsel := g.hsel
  have hs := g.hs
  have ht := g.ht
  simp only [e5Data] at hS hroot hsel
  have hw : g.w = g.S - g.f := rfl
  have hH : g.H = 1 + g.t - 6*g.u := rfl
  have hwpos : 0 < g.w := lt_of_lt_of_le (by positivity) hfloor
  have ha := h.a_pos
  have ha1 := h.a_lt
  have hc := h.cap_pos
  have hLn : 2 < n.L := by have := h.principal; linarith
  have hu0 : a * g.w ≤ g.u := hsel.1
  have hu1 : g.u ≤ a * g.w + mesh := hsel.2
  have hwc : g.w ≤ n.c := by rw [hw]; linarith
  have hupos : 0 ≤ g.u := le_trans (mul_nonneg ha.le hwpos.le) hu0
  refine ⟨?_, ?_, ?_⟩
  · show (1 - 6*a*n.c)/2 ≤ g.H
    have : a*g.w ≤ a*n.c := mul_le_mul_of_nonneg_left hwc ha.le
    rw [hH]; linarith
  · show g.H ≤ 3
    have : a*g.w ≤ a*n.c := mul_le_mul_of_nonneg_left hwc ha.le
    rw [hH]; linarith
  show max (K * deletionNeed p.B p.L p.c g.PC g.s g.H) (selExcess g.PC g.s g.H) ≤ g.u + ε/16
  apply max_le
  · -- deletion at the cut `K`
    rcases le_or_gt g.s 0 with hsle | hspos
    · rw [deletionNeed_of_nonpos hsle]; linarith
    have hBB := h.B_le
    have hB₁ := h.B_lt
    have hB₀ : 0 < p.B := by
      have hSf : ε/16 ≤ g.S := by rw [hw] at hfloor; linarith
      have : 2*(ε/16) ≤ n.L*g.S := mul_le_mul hLn.le hSf (by positivity) (by linarith)
      linarith
    have hc₀ : 0 < p.c := by
      have h1 : 0 < (1-a)*n.c := mul_pos (by linarith) hc
      by_contra hneg
      have : p.c*(1 - 6*a*n.c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hh0.le
      linarith
    have hc₀6 := h.cap_lt
    have hcapH : g.s - p.c*g.H ≤ 0 := by
      rw [hH]
      refine native_cap_aux h.a_pos ha1 hc₀ hwc hu0 hu1 (by rw [hw]; linarith) ht.1 ?_
      linarith [mul_le_mul_of_nonneg_right hc₀6.le (show 0 ≤ tl + 6*mesh by positivity)]
    have hneed := deletionNeed_le_defect (B₀:=p.B) (L₀:=p.L) (P:=g.PC) hcapH
    have hdef : g.PC + p.L*g.s - p.B*g.H ≤
        (p.L - n.L)*g.w + (6*p.B - p.L)*g.u + (p.B*tl + tl) := by
      rw [hH]
      exact native_defect_aux hBB hB₀.le (by linarith) hL₀.le hf.1 hf.2 hw hroot
        (by rw [hw]; linarith) ht.1
    have hkey := cut_retention_aux (a:=a) (K:=K) (L:=n.L) hL₀ hB₀.le hB₁ hwpos.le hu0 htl ht4
      h.K_le h.retention h.overshoot
    calc K * deletionNeed p.B p.L p.c g.PC g.s g.H
        ≤ K * max 0 ((g.PC + p.L*g.s - p.B*g.H)/p.L) :=
          mul_le_mul_of_nonneg_left hneed h.K_pos.le
      _ ≤ K * max 0 (((p.L - n.L)*g.w + (6*p.B - p.L)*g.u + (p.B*tl + tl))/p.L) := by
          apply mul_le_mul_of_nonneg_left _ h.K_pos.le
          exact max_le_max le_rfl (div_le_div_of_nonneg_right hdef hL₀.le)
      _ ≤ g.u + ε/16 := by
          rw [mul_max_of_nonneg _ _ h.K_pos.le]
          refine max_le (by linarith) hkey
  · -- the selected branch
    rw [hH]
    refine sel_branch_aux (a:=a) (B:=n.B) (L:=n.L) (cg:=g.cg) (S:=g.S) (f:=g.f) (tl:=tl)
      (mesh:=mesh) (lt_of_le_of_lt h.B_le h.B_lt) (by linarith [h.principal]) ha.le hS.1 hf.1 hf.2
      hroot hupos (by rw [← hw]; exact hu1) (by rw [← hw]; exact hs.2) ht.1 hε ?_ ?_
    · linarith
    · linarith

/-- The reference reserves (Sil's `native_reference`, selection `a·w`). -/
theorem e5_reference (h : E5Gates p n a K) :
    ReferenceAt (e5Data p n a K h) (min (1 - n.B) (1/3 - (2 + 3*a)*n.c)) := by
  have hB : n.B < 1 := lt_of_le_of_lt h.B_le h.B_lt
  have hr := h.refPos
  have hpr := h.principal
  have hsr := h.secondRef
  have hdg := h.diagonal
  have ha := h.a_pos
  have hc := h.cap_pos
  refine ⟨lt_min (by linarith) (by linarith), ?_⟩
  intro ε _ S hS0 hSc
  simp only [e5Data] at hS0 hSc ⊢
  have hm1 : min (1 - n.B) (1/3 - (2 + 3*a)*n.c) ≤ 1 - n.B := min_le_left _ _
  have hm2 : min (1 - n.B) (1/3 - (2 + 3*a)*n.c) ≤ 1/3 - (2 + 3*a)*n.c := min_le_right _ _
  have e1 : 0 ≤ (n.L - 2 - 9/2*a)*S := mul_nonneg (by linarith) hS0
  have e2 : 0 ≤ (3/2*n.L - 5/2 - 9/2*a)*S := mul_nonneg (by linarith) hS0
  have e3 : 0 ≤ (n.L - 1 - 4*a)*S := mul_nonneg (by linarith) hS0
  have e4 : (2 + 3*a)*S ≤ (2 + 3*a)*n.c :=
    mul_le_mul_of_nonneg_left hSc (by linarith)
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- **The selected-leaf scalar chain certificate gives the generic step gates.** -/
theorem stepGates_of_e5 (h : E5Gates p n a K) : StepGates (e5Data p n a K h) where
  face := by
    have := h.principal; have := h.a_pos
    exact ⟨h.B_le, h.B_lt, h.L_lt, show 1 < n.L by linarith, h.cap_pos, h.c_lt, h.cap_lt⟩
  kappa := rfl
  crossing := by
    refine ⟨le_rfl, ?_, fun h0 => absurd h0 (lt_irrefl 0)⟩
    show (p.L - n.L)*0 ≤ p.B - n.B
    have := h.B_le; simp; linarith
  envelope := by
    have := h.H
    refine ⟨by show 0 < (1 - 6*a*n.c)/2; positivity, ?_, by norm_num [e5Data]⟩
    show (1 - 6*a*n.c)/2 < 1
    have := h.a_pos; have := h.cap_pos; nlinarith
  sel_spec := by
    intro ε _
    have ha := h.a_pos
    have ha1 := h.a_lt
    refine ⟨fun x _ y _ hxy => mul_le_mul_of_nonneg_left hxy ha.le, fun w hw _ => ?_⟩
    exact ⟨mul_nonneg ha.le hw, show a * w ≤ w by nlinarith⟩
  ledger := fun ε hε => ⟨(_, _, _), e5_ledger h hε⟩
  reference := ⟨_, e5_reference h⟩

end
end QRH.ArviSelectedLeaf
