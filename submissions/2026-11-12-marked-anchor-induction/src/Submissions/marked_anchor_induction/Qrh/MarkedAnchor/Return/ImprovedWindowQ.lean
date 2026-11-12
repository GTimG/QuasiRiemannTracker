/- Copyright (c) 2026 Sil. Apache-2.0.
The improved count window of the return and its exact rational certificates. The polynomial
certificates use ArviFoxy's `Poly2`/`posBox`/`bernCheck` (arvi_selected_leaf, Apache-2.0); the window
cover extends Joseph Bebel's `CoverQ.lean` (PR103, Apache-2.0); the monotonicity proof follows
Collet's `CountMonotonicity.lean` (Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.PositiveGap.Return.Tuning.CoverQ
import Submissions.marked_anchor_induction.Qrh.PositiveGap.Return.CountWidth
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Return.ImprovedScheme

/-!
# Return.ImprovedWindowQ

The improved window on `δ ∈ [189/512, 15/32]`, `p ∈ [15/32, 1/2]` at the line
`(g0, g1) = (lineG0, lineG1)`. With `k = 1 - p(1+2 g1)`, `a = p(1+2 g0)`, `V = 5/6 - δ`:
`J = 3V + 2δk`, `U = 1 - p(1 + 6 g0 - 4 g1)`, `N = (1-δ) J + V δ U`, `T = J + δ U`;
value `N/J`, cutoff `T/J`, improved inverse crossing `2T/(3J)` (the plain threshold is `T/(3J)`).
The identities `1 - δ(a + k·2T/(3J)) = N/J` and `1 - δ + V(T/J - 1) = N/J` are polynomial;
ten guards (`g0`-`g9`) are checked by `posBox` in the kernel. `coverOK2` is `coverOK` with the
improved row as a further leaf alternative.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qrh.MarkedAnchor.Return.ImprovedQ
noncomputable section

open Set QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning QRH.ArviReturnTuning
open QRH.Record1252270103Return (plainCurve)
open Qrh.MarkedAnchor.Interface

/-! ### Real formulas -/

def kI (p : ℝ) : ℝ := 1-p*(1+2*lineG1)
def aI (p : ℝ) : ℝ := p*(1+2*lineG0)
def UI (p : ℝ) : ℝ := 1-p*(1+6*lineG0-4*lineG1)
def JI (δ p : ℝ) : ℝ := 3*(5/6-δ)+2*δ*kI p
def NI (δ p : ℝ) : ℝ := (1-δ)*JI δ p+(5/6-δ)*δ*UI p
def TI (δ p : ℝ) : ℝ := JI δ p+δ*UI p
def valueI (δ p : ℝ) : ℝ := NI δ p/JI δ p
def cutoffI (δ p : ℝ) : ℝ := TI δ p/JI δ p
def crossingI (δ p : ℝ) : ℝ := 2*TI δ p/(3*JI δ p)
def dUI : ℝ := -(1+6*lineG0-4*lineG1)
def dJI (δ : ℝ) : ℝ := -2*δ*(1+2*lineG1)

theorem JI_pos {δ p : ℝ} (hδ : δ∈Icc (0:ℝ) (3/4)) (hp : p∈Icc (0:ℝ) (1/2)) : 0<JI δ p := by
  have h1 : 0≤δ*p := mul_nonneg hδ.1 hp.1
  have h2 : δ*p≤3/4*(1/2) := mul_le_mul hδ.2 hp.2 hp.1 (by norm_num)
  unfold JI kI lineG1
  nlinarith [hδ.1, hδ.2, hp.1, hp.2]

/-! ### Rational polynomials -/

def g0Q : ℚ := 552429/10000000
def g1Q : ℚ := 7227847/100000000
def leftQ : ℚ := 1467/2000
def topQ : ℚ := 311/400

open Q2 in
def kQ : Q2 := sub (C 1) (smul (1+2*g1Q) Y)
open Q2 in
def VQ : Q2 := sub (C (5/6)) X
open Q2 in
def JQ : Q2 := add (smul 3 VQ) (smul 2 (mul X kQ))
open Q2 in
def UQ : Q2 := sub (C 1) (smul (1+6*g0Q-4*g1Q) Y)
open Q2 in
def NQ : Q2 := add (mul (sub (C 1) X) JQ) (mul (mul VQ X) UQ)
open Q2 in
def TQ : Q2 := add JQ (mul X UQ)

open Q2 in
/-- `N - (1 - δ L(p)) J` for an affine `L(p) = c0 + c1 p`. -/
def belowQ (c0 c1 : ℚ) : Q2 := sub NQ (mul (sub (C 1) (mul X (add (C c0) (smul c1 Y)))) JQ)

open Q2 in
def gQ : Fin 10 → Q2 := ![kQ, JQ, sub TQ JQ, sub (smul (12499/10000) JQ) TQ,
  sub (smul 2 TQ) (smul (3*(leftQ+1/1000000)) JQ),
  belowQ topQ (1-topQ),
  belowQ topQ (2*(countBQ-topQ)/countLQ),
  belowQ topQ (2*(countCapQ-1/10000000)),
  sub NQ (mul (sub (sub (C 1) (smul (2*naturalMQ) X)) (smul (2*sMinusQ) (mul X Y))) JQ),
  sub (mul UQ (smul (-2*(1+2*g1Q)) X)) (smul (-(1+6*g0Q-4*g1Q)) JQ)]

theorem cast_g0 : ((g0Q:ℚ):ℝ)=lineG0 := by norm_num [g0Q,lineG0]
theorem cast_g1 : ((g1Q:ℚ):ℝ)=lineG1 := by norm_num [g1Q,lineG1]
theorem cast_left : ((leftQ:ℚ):ℝ)=anchorLeft := by norm_num [leftQ,anchorLeft]
theorem cast_top : ((topQ:ℚ):ℝ)=anchorTop := by norm_num [topQ,anchorTop]
theorem cast_countB : ((countBQ:ℚ):ℝ)=countCB := by norm_num [countBQ,countCB]
theorem cast_countL : ((countLQ:ℚ):ℝ)=countCL := by norm_num [countLQ,countCL]
theorem cast_countCap : ((countCapQ:ℚ):ℝ)=countCap := by norm_num [countCapQ,countCap]
theorem cast_sMinus : ((sMinusQ:ℚ):ℝ)=sMinus := by norm_num [sMinusQ,sMinus]

section
variable (δ p : ℝ)

theorem ev_kQ : Q2.ev kQ δ p=kI p := by
  simp only [kQ,Q2.ev_sub,Q2.ev_smul,Q2.ev_C,Q2.ev_Y]; push_cast; rw [cast_g1]; unfold kI; ring
theorem ev_VQ : Q2.ev VQ δ p=5/6-δ := by
  simp only [VQ,Q2.ev_sub,Q2.ev_C,Q2.ev_X]; push_cast; ring
theorem ev_JQ : Q2.ev JQ δ p=JI δ p := by
  simp only [JQ,Q2.ev_add,Q2.ev_smul,Q2.ev_mul,Q2.ev_X,ev_VQ,ev_kQ]; push_cast; unfold JI; ring
theorem ev_UQ : Q2.ev UQ δ p=UI p := by
  simp only [UQ,Q2.ev_sub,Q2.ev_smul,Q2.ev_C,Q2.ev_Y]; push_cast; rw [cast_g0,cast_g1]; unfold UI; ring
theorem ev_NQ : Q2.ev NQ δ p=NI δ p := by
  simp only [NQ,Q2.ev_add,Q2.ev_sub,Q2.ev_mul,Q2.ev_C,Q2.ev_X,ev_VQ,ev_JQ,ev_UQ]; push_cast
  unfold NI; ring
theorem ev_TQ : Q2.ev TQ δ p=TI δ p := by
  simp only [TQ,Q2.ev_add,Q2.ev_mul,Q2.ev_X,ev_JQ,ev_UQ]; unfold TI; ring
theorem ev_belowQ (c0 c1 : ℚ) :
    Q2.ev (belowQ c0 c1) δ p=NI δ p-(1-δ*((c0:ℝ)+(c1:ℝ)*p))*JI δ p := by
  simp only [belowQ,Q2.ev_add,Q2.ev_sub,Q2.ev_mul,Q2.ev_smul,Q2.ev_C,Q2.ev_X,Q2.ev_Y,ev_NQ,ev_JQ]
  push_cast; ring

end

/-! ### The kernel checks of the ten guards on the window -/

def dloQ : ℚ := 189/512
def dhiQ : ℚ := 15/32
def ploQ : ℚ := 15/32

theorem guards_ok : (List.finRange 10).all (fun j => posBox (gQ j) 0 dloQ dhiQ ploQ (1/2)) = true := by
  decide +kernel

theorem guard_pos (j : Fin 10) {δ p : ℝ} (hδ : δ∈Icc (189/512:ℝ) (15/32)) (hp : p∈Icc (15/32:ℝ) (1/2)) :
    0<Q2.ev (gQ j) δ p := by
  have h := guards_ok
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact posBox_sound _ 0 dloQ dhiQ ploQ (1/2) (h j) (by simpa [dloQ] using hδ.1)
    (by simpa [dhiQ] using hδ.2) (by simpa [ploQ] using hp.1) (by simpa using hp.2)

/-! ### The improved window -/

section
variable {δ p : ℝ} (hδ : δ∈Icc (189/512:ℝ) (15/32)) (hp : p∈Icc (15/32:ℝ) (1/2))
include hδ hp

theorem hk : 0<kI p := by have := guard_pos 0 hδ hp; rwa [show gQ 0=kQ from rfl,ev_kQ] at this
theorem hJ : 0<JI δ p := by have := guard_pos 1 hδ hp; rwa [show gQ 1=JQ from rfl,ev_JQ] at this
theorem hT1 : JI δ p<TI δ p := by
  have := guard_pos 2 hδ hp
  rw [show gQ 2=Q2.sub TQ JQ from rfl,Q2.ev_sub,ev_TQ,ev_JQ] at this; linarith
theorem hT2 : TI δ p<12499/10000*JI δ p := by
  have := guard_pos 3 hδ hp
  rw [show gQ 3=Q2.sub (Q2.smul (12499/10000) JQ) TQ from rfl,Q2.ev_sub,Q2.ev_smul,ev_TQ,ev_JQ] at this
  push_cast at this; linarith
theorem hcross : (anchorLeft+1/1000000)*(3*JI δ p)<2*TI δ p := by
  have := guard_pos 4 hδ hp
  rw [show gQ 4=Q2.sub (Q2.smul 2 TQ) (Q2.smul (3*(leftQ+1/1000000)) JQ) from rfl,Q2.ev_sub,
    Q2.ev_smul,Q2.ev_smul,ev_TQ,ev_JQ] at this
  push_cast at this; rw [cast_left] at this; linarith
theorem hnat : (1-δ*(p+(1-p)*anchorTop))*JI δ p<NI δ p := by
  have := guard_pos 5 hδ hp
  rw [show gQ 5=belowQ topQ (1-topQ) from rfl,ev_belowQ] at this
  push_cast at this; rw [cast_top] at this; linarith
theorem hplain1 : (1-δ*(anchorTop+2*(countCB-anchorTop)/countCL*p))*JI δ p<NI δ p := by
  have := guard_pos 6 hδ hp
  rw [show gQ 6=belowQ topQ (2*(countBQ-topQ)/countLQ) from rfl,ev_belowQ] at this
  push_cast at this; rw [cast_top,cast_countB,cast_countL] at this; linarith
theorem hplain0 : (1-δ*(anchorTop+2*(countCap-1/10000000)*p))*JI δ p<NI δ p := by
  have := guard_pos 7 hδ hp
  rw [show gQ 7=belowQ topQ (2*(countCapQ-1/10000000)) from rfl,ev_belowQ] at this
  push_cast at this; rw [cast_top,cast_countCap] at this; linarith
theorem htail : (1-2*δ*naturalM-2*δ*p*sMinus)*JI δ p<NI δ p := by
  have := guard_pos 8 hδ hp
  rw [show gQ 8=Q2.sub NQ (Q2.mul (Q2.sub (Q2.sub (Q2.C 1) (Q2.smul (2*naturalMQ) Q2.X))
    (Q2.smul (2*sMinusQ) (Q2.mul Q2.X Q2.Y))) JQ) from rfl] at this
  simp only [Q2.ev_sub,Q2.ev_mul,Q2.ev_smul,Q2.ev_C,Q2.ev_X,Q2.ev_Y,ev_NQ,ev_JQ] at this
  push_cast at this; rw [cast_naturalMQ,cast_sMinus] at this; linarith
theorem hanti : 0<UI p*dJI δ-dUI*JI δ p := by
  have := guard_pos 9 hδ hp
  rw [show gQ 9=Q2.sub (Q2.mul UQ (Q2.smul (-2*(1+2*g1Q)) Q2.X)) (Q2.smul (-(1+6*g0Q-4*g1Q)) JQ)
    from rfl] at this
  simp only [Q2.ev_sub,Q2.ev_mul,Q2.ev_smul,Q2.ev_X,ev_UQ,ev_JQ] at this
  push_cast at this; rw [cast_g0,cast_g1] at this; unfold dJI dUI; linarith

end

theorem crossing_eq (δ p : ℝ) (hJ : JI δ p≠0) :
    2*(cutoffI δ p-crossingI δ p)=crossingI δ p := by
  unfold cutoffI crossingI; field_simp; ring

theorem inverse_identity (δ p : ℝ) (hJ : JI δ p≠0) :
    1-δ*(p*(1+2*lineG0)+(1-p*(1+2*lineG1))*crossingI δ p)=valueI δ p := by
  unfold crossingI valueI; field_simp; unfold NI TI JI UI kI; ring

theorem long_identity (δ p : ℝ) (hJ : JI δ p≠0) :
    1-δ+(5/6-δ)*(cutoffI δ p-1)=valueI δ p := by
  unfold cutoffI valueI; field_simp; unfold NI TI; ring

theorem UI_hasDerivAt (p : ℝ) : HasDerivAt UI dUI p := by
  have h := ((hasDerivAt_id p).mul_const (1+6*lineG0-4*lineG1)).const_sub 1
  convert h using 1
  · funext z; simp only [UI,id]
  · unfold dUI; ring

theorem JI_hasDerivAt (δ p : ℝ) : HasDerivAt (JI δ) (dJI δ) p := by
  have h := ((((hasDerivAt_id p).mul_const (1+2*lineG1)).const_sub 1).const_mul (2*δ)).const_add
    (3*(5/6-δ))
  convert h using 1
  · funext z; simp only [JI,kI,id]
  · unfold dJI; ring

theorem valueI_ratio {δ p : ℝ} (hj : JI δ p≠0) :
    valueI δ p=1-δ+(5/6-δ)*δ*(UI p/JI δ p) := by
  unfold valueI NI; field_simp; try ring

theorem valueI_hasDerivAt {δ p : ℝ} (hj : JI δ p≠0) :
    HasDerivAt (valueI δ) ((5/6-δ)*δ*(-(UI p*dJI δ-dUI*JI δ p))/(JI δ p)^2) p := by
  have hq := (UI_hasDerivAt p).div (JI_hasDerivAt δ p) hj
  have hn := (JI_hasDerivAt δ p).continuousAt.eventually_ne hj
  have he : valueI δ =ᶠ[nhds p] (fun z=>1-δ+(5/6-δ)*δ*(UI z/JI δ z)) :=
    hn.mono (fun z hz=>valueI_ratio hz)
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert (hasDerivAt_const p (1-δ)).add (hq.const_mul ((5/6-δ)*δ)) using 1 <;> (try funext z) <;> ring

theorem valueI_antitoneOn {δ : ℝ} (hδ : δ∈Icc (189/512:ℝ) (15/32)) :
    AntitoneOn (valueI δ) (Icc (15/32:ℝ) (1/2)) := by
  have hj (p : ℝ) (hp : p∈Icc (15/32:ℝ) (1/2)) : 0<JI δ p := hJ hδ hp
  have hh (p : ℝ) (hp : p∈Icc (15/32:ℝ) (1/2)) := valueI_hasDerivAt (hj p hp).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro p hp; exact (hh p hp).continuousAt.continuousWithinAt
  · intro p hp; exact (hh p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hh p (interior_subset hp)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith [hδ.2]) (by linarith [hδ.1]))
        (neg_nonpos.mpr (hanti hδ (interior_subset hp)).le)
    · exact sq_nonneg _

/-- **The improved window** `[189/512, 15/32] × [15/32, 1/2]` (line `(lineG0, lineG1)`, native
plain fallback on the count face `C`). -/
def window : ImprovedWindow (naturalK/6) where
  B := countCB
  lam := countCL
  cap := countCap-1/10000000
  sourceCap := countCap
  mHi := naturalM
  lam_gt_one := by norm_num [countCL]
  mHi_lo := natural_join_bounds.1
  mHi_hi := natural_join_bounds.2
  cap_le_source := by linarith
  cap_small := by norm_num [countCap]
  value := valueI
  cutoff := cutoffI
  crossing := crossingI
  deltaLo := 189/512
  deltaHi := 15/32
  pLo := 15/32
  deltaBounds := by norm_num
  pBounds := by norm_num
  cutoff_bounds := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    exact ⟨(le_div_iff₀ hJ').mpr (by linarith [hT1 hd hp]),
      (div_le_iff₀ hJ').mpr (by linarith [hT2 hd hp])⟩
  crossing_left := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    unfold crossingI
    rw [le_div_iff₀ (by linarith)]
    have := hcross hd hp
    unfold anchorLeft at this ⊢
    linarith
  plain_left := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    rw [crossing_eq δ p hJ'.ne']
    unfold crossingI
    rw [le_div_iff₀ (by linarith)]
    have := hcross hd hp
    linarith
  slope_nonneg := by intro δ p hd hp; exact (hk hd hp).le
  inverse_crossing := by intro δ p hd hp; exact inverse_identity δ p (hJ hd hp).ne'
  ordinary_crossing := by
    intro δ p hd hp
    rw [crossing_eq δ p (hJ hd hp).ne']
    have e := inverse_identity δ p (hJ hd hp).ne'
    apply le_of_eq
    rw [← e]; ring
  native_top := by
    intro δ p hd hp
    unfold valueI
    rw [le_div_iff₀ (hJ hd hp)]
    linarith [hnat hd hp]
  plain_top := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    unfold valueI plainCurve
    apply max_le
    · rw [le_div_iff₀ hJ']
      have h := hplain0 hd hp
      linarith
    · rw [le_div_iff₀ hJ']
      have h := hplain1 hd hp
      have e : (1-2*δ*(anchorTop/2)-2*δ*p*(countCB-2*(anchorTop/2))/countCL)*JI δ p=
          (1-δ*(anchorTop+2*(countCB-anchorTop)/countCL*p))*JI δ p := by ring
      rw [e]; exact h.le
  natural_tail := by
    intro δ p hd hp
    have he : (1-2*naturalM)/(6*(naturalK/6))=sMinus := by norm_num [naturalM,naturalK,sMinus]
    rw [mul_div_assoc,he]
    unfold valueI
    rw [le_div_iff₀ (hJ hd hp)]
    have := htail hd hp
    linarith
  widths := by
    intro ν hν m hm1 hm2
    have hM : naturalM=(1-naturalK*sMinus)/2 := rfl
    apply lt_min
    · unfold countCap; linarith
    · rw [hM] at hm2
      norm_num [naturalK,sMinus] at hm2
      rw [lt_div_iff₀ (by norm_num [countCL])]
      norm_num [countCB,countCL]
      linarith
  long_crossing := by intro δ p hd hp; exact long_identity δ p (hJ hd hp).ne'
  antitone := by intro δ hd; exact valueI_antitoneOn hd

/-! ### The edge cover with the improved alternative -/

/-- The row margin of the improved window at the edge `e`. -/
def rowImpQ (e : Edge) : Q2 := rowQ (edgeDQ e) (edgeCQ e) JQ NQ

/-- A leaf: Collet's old count, a native window, or an improved window `(dlo, dhi, plo)`. -/
def leafOK2 (e : Edge) (ws : List WinQ) (imps : List (ℚ×ℚ×ℚ)) (a b c d : ℚ) : Bool :=
  leafOK e ws a b c d ||
    imps.any fun w => decide (w.1≤a) && decide (b≤w.2.1) && decide (w.2.2≤c) &&
      bernCheck (rowImpQ e) a b c d

/-- `coverOK` with the improved alternative. -/
def coverOK2 (e : Edge) (ws : List WinQ) (imps : List (ℚ×ℚ×ℚ)) : ℕ → ℚ → ℚ → ℚ → ℚ → Bool
  | 0, a, b, c, d => leafOK2 e ws imps a b c d
  | k + 1, a, b, c, d =>
    leafOK2 e ws imps a b c d ||
      (if 3 * (d - c) ≤ 2 * (b - a) then
        coverOK2 e ws imps k a ((a + b) / 2) c d && coverOK2 e ws imps k ((a + b) / 2) b c d
      else coverOK2 e ws imps k a b c ((c + d) / 2) && coverOK2 e ws imps k a b ((c + d) / 2) d)

theorem exponent_lt_of_rowImp {e : Edge} {δ p R : ℝ}
    (hJ' : 0<JI δ p) (hF : 0<Q2.ev (rowImpQ e) δ p) (hR : R≤NI δ p/JI δ p) :
    Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*R<theta-reserve := by
  unfold rowImpQ at hF
  rw [ev_rowQ,ev_JQ,ev_NQ] at hF
  have hd : 0≤3/4*edgeD e := by positivity [edgeD_nonneg e]
  have hRN := mul_le_mul_of_nonneg_left ((le_div_iff₀ hJ').mp hR) hd
  have hlt : JI δ p*(Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*R)<JI δ p*(theta-reserve) := by
    nlinarith only [hF,hRN]
  exact (mul_lt_mul_iff_right₀ hJ').mp hlt

section
variable (e : Edge) (ws : List WinQ) (imps : List (ℚ×ℚ×ℚ)) (env : ℝ → ℝ → ℝ)
  (hold : ∀ δ p, δ ∈ Icc (0 : ℝ) (3 / 4) → p ∈ Icc (0 : ℝ) (1 / 2) →
    env δ p ≤ countN .old δ p / countJ .old δ p)
  (hwin : ∀ w ∈ ws, w.branch ≠ .old → ∀ δ p, δ ∈ Icc (w.dlo : ℝ) w.dhi →
    p ∈ Icc (w.plo : ℝ) (1 / 2) → env δ p ≤ countN w.branch δ p / countJ w.branch δ p)
  (himp : ∀ w ∈ imps, ∀ δ p, δ ∈ Icc (w.1 : ℝ) w.2.1 → p ∈ Icc (w.2.2 : ℝ) (1 / 2) →
    env δ p ≤ NI δ p / JI δ p)
include hold hwin himp

theorem leafOK2_sound (a b c d : ℚ) (h : leafOK2 e ws imps a b c d = true) {δ p : ℝ}
    (hd0 : (a : ℝ) ≤ δ) (hd1 : δ ≤ b) (hp0 : (c : ℝ) ≤ p) (hp1 : p ≤ d)
    (hδ : δ ∈ Icc (0 : ℝ) (3 / 4)) (hp : p ∈ Icc (0 : ℝ) (1 / 2)) :
    Ebase (edgeD e) (edgeC e) δ p + 3 / 4 * edgeD e * env δ p < theta - reserve := by
  simp only [leafOK2, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨w, hw, ⟨⟨⟨ha, hbd⟩, hc⟩, hrow⟩⟩
  · exact leafOK_sound e ws env hold hwin a b c d h hd0 hd1 hp0 hp1 hδ hp
  · have hF : 0 < Q2.ev (rowImpQ e) δ p := bernCheck_sound _ a b c d hrow hd0 hd1 hp0 hp1
    have ha' : (w.1 : ℝ) ≤ a := by exact_mod_cast ha
    have hbd' : (b : ℝ) ≤ w.2.1 := by exact_mod_cast hbd
    have hc' : (w.2.2 : ℝ) ≤ c := by exact_mod_cast hc
    exact exponent_lt_of_rowImp (JI_pos hδ hp) hF
      (himp w hw δ p ⟨ha'.trans hd0, hd1.trans hbd'⟩ ⟨hc'.trans hp0, hp.2⟩)

theorem coverOK2_sound (k : ℕ) : ∀ (a b c d : ℚ), coverOK2 e ws imps k a b c d = true →
    ∀ {δ p : ℝ}, (a : ℝ) ≤ δ → δ ≤ b → (c : ℝ) ≤ p → p ≤ d → δ ∈ Icc (0 : ℝ) (3 / 4) →
      p ∈ Icc (0 : ℝ) (1 / 2) →
      Ebase (edgeD e) (edgeC e) δ p + 3 / 4 * edgeD e * env δ p < theta - reserve := by
  induction k with
  | zero =>
    intro a b c d h δ p hd0 hd1 hp0 hp1 hδ hp
    exact leafOK2_sound e ws imps env hold hwin himp a b c d h hd0 hd1 hp0 hp1 hδ hp
  | succ k ih =>
    intro a b c d h δ p hd0 hd1 hp0 hp1 hδ hp
    simp only [coverOK2, Bool.or_eq_true] at h
    rcases h with h | h
    · exact leafOK2_sound e ws imps env hold hwin himp a b c d h hd0 hd1 hp0 hp1 hδ hp
    · split_ifs at h with hs
      · simp only [Bool.and_eq_true] at h
        rcases le_total δ (((a + b) / 2 : ℚ) : ℝ) with hm | hm
        · exact ih _ _ _ _ h.1 hd0 hm hp0 hp1 hδ hp
        · exact ih _ _ _ _ h.2 hm hd1 hp0 hp1 hδ hp
      · simp only [Bool.and_eq_true] at h
        rcases le_total p (((c + d) / 2 : ℚ) : ℝ) with hm | hm
        · exact ih _ _ _ _ h.1 hd0 hd1 hp0 hm hδ hp
        · exact ih _ _ _ _ h.2 hd0 hd1 hm hp1 hδ hp

/-- A passed check of the whole root box `[0, 3/4] × [0, 1/2]`. -/
theorem edge_of_coverOK2 (k : ℕ) (h : coverOK2 e ws imps k 0 (3 / 4) 0 (1 / 2) = true) {δ p : ℝ}
    (hδ : δ ∈ Icc (0 : ℝ) (3 / 4)) (hp : p ∈ Icc (0 : ℝ) (1 / 2)) :
    Ebase (edgeD e) (edgeC e) δ p + 3 / 4 * edgeD e * env δ p < theta - reserve :=
  coverOK2_sound e ws imps env hold hwin himp k 0 (3 / 4) 0 (1 / 2) h (by simpa using hδ.1)
    (by simpa using hδ.2) (by simpa using hp.1) (by simpa using hp.2) hδ hp

end

end
end Qrh.MarkedAnchor.Return.ImprovedQ
