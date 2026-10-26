/- Repeated marks: the HIGH gate of the repeated-mark gain as a finite certificate.

For a branch `k = (i,j)` the class root is `gateN / gateM`, where the inverse piece is
`(x - β_i)/d_i` (`i = 0`: `x - 2pKS`; `i = 1`: `(x - pF)/(1-p)`) and the plain piece is
`(γ_j x - η_j)/e_j` (`j = 0`: `x - 2pS`; `j = 1`: `x - 2p h F`; `j = 2`: `(Lx - 2pBF)/(L-2p)`).
The cleared gate

  `gateG = gateM ((a - νT)(15-6ν) + (10-60a)ν + (15-6ν)(1-2p)νS - 10νF - fee(15-6ν))
           + ν (15-6ν) gateN`

equals `gateM (15-6ν) (1 - sourceBase + facetVal_k - fee)`. It is a polynomial of bidegree
`(3,3)` in `(ν,p)`, affine in the width `b`. Its positivity is certified by bicubic Bernstein
bisection (`checkBox`) at the two width endpoints. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalScalar
import Submissions.hailey_collet_1252270103.Record1252270103StepScalar.UniformMargins
import Submissions.arvi_repeated_marks_20261024.Gain.Bernstein2
import Submissions.arvi_repeated_marks_20261024.Gain.Gain
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.RepeatedMarks.Finite
noncomputable section
open Record1252270103Finite QRH.RepeatedMarks

section generic
variable {R : Type*} [CommRing R]
def dI (p : R) : Fin 2 → R := ![1, 1 - p]
def eP (p L : R) : Fin 3 → R := ![1, 1, L - 2*p]
def gP (L : R) : Fin 3 → R := ![1, 1, L]
def bI (p K S F : R) : Fin 2 → R := ![2*p*K*S, p*F]
def hP (p B hc S F : R) : Fin 3 → R := ![2*p*S, 2*p*hc*F, 2*p*B*F]

def gateM (ν p L : R) (k : Branch) : R :=
  12*ν*(dI p k.1*eP p L k.2) + (5 - 6*ν)*(2*eP p L k.2 + dI p k.1*gP L k.2)
def gateN (ν p K B L hc S F : R) (k : Branch) : R :=
  10*F*(dI p k.1*eP p L k.2) +
    (5 - 6*ν)*(2*eP p L k.2*bI p K S F k.1 + dI p k.1*hP p B hc S F k.2)
def gateG (a T S F fee K B L hc ν p : R) (k : Branch) : R :=
  gateM ν p L k*((a - ν*T)*(15 - 6*ν) + (10 - 60*a)*ν + (15 - 6*ν)*(1 - 2*p)*ν*S
      - 10*ν*F - fee*(15 - 6*ν)) + ν*(15 - 6*ν)*gateN ν p K B L hc S F k
end generic

/-- Power coefficients of the cubic through `f 0, f 1, f (-1), f 2` (as Collet's `cubicCoeffs`). -/
def cubic4 (f : ℚ → ℚ) : Fin 4 → ℚ :=
  ![f 0, (-f 2 + 6*f 1 - 3*f 0 - 2*f (-1))/6, (f 1 + f (-1) - 2*f 0)/2,
    (f 2 - 3*f 1 + 3*f 0 - f (-1))/6]

/-- Bicubic power coefficients by tensor interpolation. -/
def bicubic (f : ℚ → ℚ → ℚ) : Fin 4 → Fin 4 → ℚ :=
  fun i j => cubic4 (fun x => cubic4 (fun y => f x y) j) i

/-- The rational gate of a node at width `b`. -/
def highGate (n low h : Source) (copies b ν p : ℚ) (k : Branch) : ℚ :=
  gateG (sourceA n low b) (sourceT n b + b) (b - 2*n.allowance) (sourceF n low b - n.allowance)
    n.highFee copies h.B h.L h.cap ν p k

def highCoeffs (n low h : Source) (copies b : ℚ) (k : Branch) : Fin 4 → Fin 4 → ℚ :=
  bicubic (fun ν p => highGate n low h copies b ν p k)

/-- The real gate at a real width. -/
def highGateReal (n low h : Source) (copies : ℚ) (b ν p : ℝ) (k : Branch) : ℝ :=
  gateG (sourceAReal n low b) (sourceTReal n b + b) (b - 2*(n.allowance:ℝ))
    (sourceFReal n low b - (n.allowance:ℝ)) (n.highFee:ℝ) (copies:ℝ) (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ)
    ν p k

theorem gateG_bicubic (A T S F fee K B L hc : ℚ) (k : Branch) (ν p : ℝ) :
    gateG (A:ℝ) (T:ℝ) (S:ℝ) (F:ℝ) (fee:ℝ) (K:ℝ) (B:ℝ) (L:ℝ) (hc:ℝ) ν p k =
      ∑ i : Fin 4, ∑ j : Fin 4,
        ((bicubic (fun x y => gateG A T S F fee K B L hc x y k) i j : ℚ) : ℝ) *
          ν^(i:ℕ) * p^(j:ℕ) := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [gateG, gateM, gateN, dI, eP, gP, bI, hP, bicubic, cubic4, Fin.sum_univ_four] <;>
    push_cast <;> ring

theorem highGateReal_rat (n low h : Source) (copies b : ℚ) (ν p : ℝ) (k : Branch) :
    highGateReal n low h copies (b:ℝ) ν p k =
      ∑ i : Fin 4, ∑ j : Fin 4, ((highCoeffs n low h copies b k i j : ℚ) : ℝ) *
        ν^(i:ℕ) * p^(j:ℕ) := by
  have e := gateG_bicubic (sourceA n low b) (sourceT n b + b) (b - 2*n.allowance)
    (sourceF n low b - n.allowance) n.highFee copies h.B h.L h.cap k ν p
  rw [highGateReal, sourceAReal_rat, sourceTReal_rat, sourceFReal_rat]
  push_cast at e ⊢
  simpa only [highCoeffs, highGate] using e

theorem highGateReal_affine (n low h : Source) (copies : ℚ) (ν p : ℝ) (k : Branch) :
    WidthAffine (fun b => highGateReal n low h copies b ν p k) := by
  intro x y t
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp only [highGateReal, gateG, gateM, gateN, dI, eP, gP, bI, hP, sourceAReal, sourceTReal,
      sourceFReal] <;> simp <;> ring

theorem highGateReal_continuous (n low h : Source) (copies : ℚ) (k : Branch) :
    Continuous (fun x : ℝ × ℝ × ℝ => highGateReal n low h copies x.1 x.2.1 x.2.2 k) := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [highGateReal, gateG, gateM, gateN, dI, eP, gP, bI, hP, sourceAReal, sourceTReal,
      sourceFReal] <;> fun_prop

/-- The certificate of one node at one width: one bisection tree per branch. -/
def HighCertAt (n low h : Source) (copies b : ℚ) (T : Branch → Split) : Prop :=
  ∀ k : Branch, checkBox (highCoeffs n low h copies b k) (T k) n.q (3/4 - n.q) 0 (1/2) = true

instance (n low h : Source) (copies b : ℚ) (T : Branch → Split) :
    Decidable (HighCertAt n low h copies b T) := by
  unfold HighCertAt; infer_instance

theorem high_endpoint_pos (n low h : Source) (copies b : ℚ) (T : Branch → Split)
    (hq : n.q < 3/4) (hc : HighCertAt n low h copies b T)
    {ν p : ℝ} (hν : ν ∈ Set.Icc (n.q:ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) (k : Branch) :
    0 < highGateReal n low h copies (b:ℝ) ν p k := by
  rw [highGateReal_rat]
  apply checkBox_sound (highCoeffs n low h copies b k) (T k) n.q (3/4 - n.q) 0 (1/2)
    (by linarith) (by norm_num) (hc k) ν p hν.1 (by push_cast; linarith [hν.2]) (by simpa using hp.1)
    (by push_cast; linarith [hp.2])

/-! ## The cleared gate is a positive multiple of the HIGH gate -/

theorem dI_invSlope {p : ℝ} (hp : p < 1) (i : Fin 2) : dI p i*invSlope p i = 1 := by
  have h1 : (1 - p) ≠ 0 := by linarith
  fin_cases i
  · show (1:ℝ)*1 = 1; ring
  · show (1 - p)*(1/(1-p)) = 1; field_simp

theorem eP_plainSlope {p L : ℝ} (hL : 2*p < L) (hL0 : 0 < L) (j : Fin 3) :
    eP p L j*plainSlope p L j = gP L j := by
  have h2 : (L - 2*p) ≠ 0 := by linarith
  have h5 : L ≠ 0 := by linarith
  fin_cases j
  · show (1:ℝ)*1 = 1; ring
  · show (1:ℝ)*1 = 1; ring
  · show (L - 2*p)*(1/(1 - 2*p/L)) = L
    rw [show (1:ℝ) - 2*p/L = (L - 2*p)/L by field_simp]
    field_simp

theorem dI_invOffset {p : ℝ} (K S F : ℝ) (hp : p < 1) (i : Fin 2) :
    dI p i*invOffset p K S F i = -bI p K S F i := by
  have h1 : (1 - p) ≠ 0 := by linarith
  fin_cases i
  · show (1:ℝ)*(-(2*p*K*S)) = -(2*p*K*S); ring
  · show (1 - p)*(-(p*F)/(1-p)) = -(p*F); field_simp

theorem eP_plainOffset {p L : ℝ} (B hc S F : ℝ) (hL : 2*p < L) (hL0 : 0 < L) (j : Fin 3) :
    eP p L j*plainOffset p B L hc S F j = -hP p B hc S F j := by
  have h2 : (L - 2*p) ≠ 0 := by linarith
  have h5 : L ≠ 0 := by linarith
  fin_cases j
  · show (1:ℝ)*(-(2*p*S)) = -(2*p*S); ring
  · show (1:ℝ)*(-(2*p*hc*F)) = -(2*p*hc*F); ring
  · show (L - 2*p)*(-(2*p*B*F/L)/(1 - 2*p/L)) = -(2*p*B*F)
    rw [show (1:ℝ) - 2*p/L = (L - 2*p)/L by field_simp]
    field_simp

theorem gateM_eq (ν p L : ℝ) (hp : p < 1) (hL : 2*p < L) (hL0 : 0 < L) (k : Branch) :
    gateM ν p L k = 2*(dI p k.1*eP p L k.2)*branchSlope ν p L k := by
  have h1 := dI_invSlope hp k.1
  have h2 := eP_plainSlope hL hL0 k.2
  simp only [gateM, branchSlope, w]
  linear_combination (-2*(5-6*ν)*eP p L k.2) * h1 + (-(5-6*ν)*dI p k.1) * h2

theorem gateN_eq (ν p K B L hc S F : ℝ) (hp : p < 1) (hL : 2*p < L) (hL0 : 0 < L) (k : Branch) :
    gateN ν p K B L hc S F k =
      2*(dI p k.1*eP p L k.2)*(5*F - branchOffset ν p K B L hc S F k) := by
  have h3 := dI_invOffset K S F hp k.1
  have h4 := eP_plainOffset B hc S F hL hL0 k.2
  simp only [gateN, branchOffset, w]
  linear_combination (2*(5-6*ν)*eP p L k.2) * h3 + ((5-6*ν)*dI p k.1) * h4

theorem dIeP_pos {p L : ℝ} (hp : p < 1) (hL : 2*p < L) (k : Branch) :
    0 < dI p k.1*eP p L k.2 := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [dI, eP] <;> nlinarith

theorem gateM_pos {ν p L : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 3/4) (hp : p < 1) (hL : 2*p < L)
    (hL0 : 0 < L) (k : Branch) : 0 < gateM ν p L k := by
  rw [gateM_eq ν p L hp hL hL0 k]
  have := dIeP_pos hp hL k
  have := branchSlope_pos hν0 hν1 hp hL hL0 k
  positivity

theorem gateM_le {ν p L : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 3/4) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hL : 1 < L) (k : Branch) : gateM ν p L k ≤ 15*L := by
  have hde : 0 ≤ dI p k.1*eP p L k.2 ∧ dI p k.1*eP p L k.2 ≤ L := by
    rcases k with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [dI, eP] <;> (try constructor) <;> nlinarith
  have hs : 0 ≤ 2*eP p L k.2 + dI p k.1*gP L k.2 ∧ 2*eP p L k.2 + dI p k.1*gP L k.2 ≤ 3*L := by
    rcases k with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [dI, eP, gP] <;> (try constructor) <;> nlinarith
  have hw : 0 ≤ 5 - 6*ν := by linarith
  have h1 := mul_le_mul_of_nonneg_left hde.2 (show 0 ≤ 12*ν by linarith)
  have h2 := mul_le_mul_of_nonneg_left hs.2 hw
  simp only [gateM]
  nlinarith

theorem gateG_eq (a T S F fee K B L hc ν p : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 3/4) (hp : p < 1)
    (hL : 2*p < L) (hL0 : 0 < L) (k : Branch) :
    gateG a T S F fee K B L hc ν p k =
      gateM ν p L k*(15 - 6*ν)*
        (1 - QRH.Record1252270103Source.PhysicalScalar.physicalBase ν a T +
          facetVal ν p K B L hc S F k - fee) := by
  have hM := gateM_pos hν0 hν1 hp hL hL0 k
  have hM' : gateM ν p L k ≠ 0 := ne_of_gt hM
  have ht : (15 - 6*ν) ≠ 0 := by linarith
  have ht' : (15 - ν*6) ≠ 0 := by linarith
  have hde := dIeP_pos hp hL k
  have hroot : branchRoot ν p K B L hc S F k = gateN ν p K B L hc S F k/gateM ν p L k := by
    rw [branchRoot, gateN_eq ν p K B L hc S F hp hL hL0 k, gateM_eq ν p L hp hL hL0 k]
    rw [mul_div_mul_left _ _ (by positivity : (2*(dI p k.1*eP p L k.2)) ≠ 0)]
  have hfv : facetVal ν p K B L hc S F k =
      (1-2*p)*ν*S + ν*(gateN ν p K B L hc S F k/gateM ν p L k - 10*F/(15 - 6*ν)) := by
    rw [facetVal, hroot, baseXi, densityDenom]; ring
  have hpb : QRH.Record1252270103Source.PhysicalScalar.physicalBase ν a T =
      (1 - 10*ν/(15 - 6*ν)) + ν*T + a*(5 - 6*(1 - 10*ν/(15 - 6*ν))) := by
    simp only [QRH.Record1252270103Source.PhysicalScalar.physicalBase,
      QRH.Record1252270103Source.High.rho, QRH.Record1252270103Source.High.baseXi,
      QRH.Record1252270103Source.High.densityDenom]
    ring
  rw [hfv, hpb, gateG]
  field_simp
  ring

/-! ## From the certificates to a uniform reserve for the repeated-mark gain -/

/-- The HIGH certificates of a node: one bisection tree per branch at each width endpoint. -/
def HighValid (n low : Source) (high : Option Source) (copies : ℚ) : Prop :=
  ∀ h ∈ high, ∀ b ∈ [crossing n low, n.cap], ∃ T : Branch → Split, HighCertAt n low h copies b T

theorem high_gate_pos (n low h : Source) (copies : ℚ) (hq : n.q < 3/4)
    (hv : ∀ b ∈ [crossing n low, n.cap], ∃ T : Branch → Split, HighCertAt n low h copies b T)
    {b ν p : ℝ} (hb : b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hν : ν ∈ Set.Icc (n.q:ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) (k : Branch) :
    0 < highGateReal n low h copies b ν p k := by
  obtain ⟨Tl, hl⟩ := hv (crossing n low) (by simp)
  obtain ⟨Tr, hr⟩ := hv n.cap (by simp)
  exact width_affine_positive (highGateReal_affine n low h copies ν p k) hb
    (high_endpoint_pos n low h copies _ Tl hq hl hν hp k)
    (high_endpoint_pos n low h copies _ Tr hq hr hν hp k)

/-- The HIGH gate is positive on the whole cell (the semantic form of `HighValid`). -/
def HighPos (n low : Source) (high : Option Source) (copies : ℚ) : Prop :=
  ∀ h ∈ high, ∀ b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ), ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
    ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ k, 0 < highGateReal n low h copies b ν p k

theorem highPos_of_valid (n low : Source) (high : Option Source) (copies : ℚ) (hq : n.q < 3/4)
    (hv : HighValid n low high copies) : HighPos n low high copies :=
  fun h hh _ hb _ hν _ hp k => high_gate_pos n low h copies hq (hv h hh) hb hν hp k

/-- A positive reserve for the HIGH gate with the repeated-mark gain, uniform in the width and
the density. The amplitude class `p = 0` gives the facet `ν S`; every class is covered. -/
theorem high_uniform_reserve (n low h : Source) (copies : ℚ) (hcopies : 0 ≤ copies)
    (hq0 : 1/2 ≤ n.q) (hq : n.q < 3/4) (hB0 : 22/23 ≤ (h.B:ℝ)) (hB1 : (h.B:ℝ) ≤ 1)
    (hL : 1 < (h.L:ℝ)) (hh0 : 0 ≤ (h.cap:ℝ)) (hh1 : (h.cap:ℝ) ≤ 1)
    (hv : ∀ b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ), ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
      ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ k, 0 < highGateReal n low h copies b ν p k) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
      0 ≤ b - 2*(n.allowance:ℝ) → 0 ≤ sourceFReal n low b - (n.allowance:ℝ) →
      reserve ≤ 1 - QRH.Record1252270103Source.PhysicalScalar.sourceBase n low b ν +
        gainK ν copies h.B h.L h.cap (b - 2*(n.allowance:ℝ)) (sourceFReal n low b - (n.allowance:ℝ)) -
        (n.highFee:ℝ) := by
  let D := Set.Icc (crossing n low:ℝ) (n.cap:ℝ) ×ˢ
    (Set.Icc (n.q:ℝ) (3/4) ×ˢ Set.Icc (0:ℝ) (1/2))
  have hD : IsCompact D := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨δ, hδ, hall⟩ := QRH.Record1252270103StepScalar.compact_finite_margin D hD
    (fun k : Branch => fun x : ℝ × ℝ × ℝ => highGateReal n low h copies x.1 x.2.1 x.2.2 k)
    (fun k => (highGateReal_continuous n low h copies k).continuousOn)
    (fun k x hx => hv x.1 hx.1 x.2.1 hx.2.1 x.2.2 hx.2.2 k)
  have hLpos : 0 < (h.L:ℝ) := by linarith
  refine ⟨δ/(180*(h.L:ℝ)), by positivity, ?_⟩
  intro b hb ν hν hS hF
  have hq0' : (1/2:ℝ) ≤ (n.q:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hq0
    norm_num at hh
    exact hh
  have hν0 : 1/2 ≤ ν := le_trans hq0' hν.1
  have hPP : ParentParams ν copies h.B h.L h.cap :=
    ⟨by linarith, hν.2, by exact_mod_cast hcopies, hB0, hB1, hL, hh0, hh1⟩
  -- every class and branch clears the reserve
  have hfacet : ∀ p ∈ classes, ∀ k : Branch,
      δ/(180*(h.L:ℝ)) ≤ 1 - QRH.Record1252270103Source.PhysicalScalar.sourceBase n low b ν +
        facetVal ν p copies h.B h.L h.cap (b - 2*(n.allowance:ℝ))
          (sourceFReal n low b - (n.allowance:ℝ)) k - (n.highFee:ℝ) := by
    intro p hp k
    have hp1 : p < 1 := by linarith [hp.2]
    have hpL : 2*p < (h.L:ℝ) := by linarith [hp.2]
    have hg := hall k (b, ν, p) ⟨hb, hν, hp⟩
    simp only at hg
    rw [highGateReal, gateG_eq _ _ _ _ _ _ _ _ _ ν p (by linarith) hν.2 hp1 hpL hLpos k] at hg
    have hM := gateM_pos (ν:=ν) (p:=p) (L:=(h.L:ℝ)) (by linarith) hν.2 hp1 hpL hLpos k
    have hMle := gateM_le (ν:=ν) (p:=p) (L:=(h.L:ℝ)) (by linarith) hν.2 hp.1 hp.2 hL k
    have ht0 : 0 < 15 - 6*ν := by linarith [hν.2]
    have ht1 : 15 - 6*ν ≤ 12 := by linarith
    set G := 1 - QRH.Record1252270103Source.PhysicalScalar.physicalBase ν (sourceAReal n low b)
      (sourceTReal n b + b) + facetVal ν p copies h.B h.L h.cap (b - 2*(n.allowance:ℝ))
        (sourceFReal n low b - (n.allowance:ℝ)) k - (n.highFee:ℝ) with hGdef
    have hGpos : 0 < G := by
      by_contra hcon; push Not at hcon
      have : gateM ν p (h.L:ℝ) k*(15 - 6*ν)*G ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
      linarith
    have hbound : gateM ν p (h.L:ℝ) k*(15 - 6*ν) ≤ 180*(h.L:ℝ) := by nlinarith
    have : δ ≤ 180*(h.L:ℝ)*G := le_trans hg (by nlinarith)
    rw [div_le_iff₀ (by positivity)]
    simp only [QRH.Record1252270103Source.PhysicalScalar.sourceBase]
    linarith
  -- pass to the infimum over classes
  have hgain : δ/(180*(h.L:ℝ)) - (1 - QRH.Record1252270103Source.PhysicalScalar.sourceBase n low b ν -
      (n.highFee:ℝ)) ≤ gainK ν copies h.B h.L h.cap (b - 2*(n.allowance:ℝ))
        (sourceFReal n low b - (n.allowance:ℝ)) := by
    have hne : ((fun p => gainP ν p (copies:ℝ) (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ) (b - 2*(n.allowance:ℝ))
        (sourceFReal n low b - (n.allowance:ℝ))) '' classes).Nonempty :=
      ⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
    show _ ≤ sInf _
    apply le_csInf hne
    rintro _ ⟨p, hp, rfl⟩
    dsimp only
    rw [gainP_eq_inf _ _ _ _ _ _ _ _ (by linarith)]
    apply Finset.le_inf'
    intro k _
    linarith [hfacet p hp k]
  linarith

end
end QRH.RepeatedMarks.Finite
