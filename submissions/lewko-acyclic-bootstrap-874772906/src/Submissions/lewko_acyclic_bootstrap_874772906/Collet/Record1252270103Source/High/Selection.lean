/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.Thresholds

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section

abbrev Branch := Fin 2 × Fin 3
def w (nu : ℝ) := 5-6*nu
def densityDenom (nu : ℝ) := 15-6*nu
def baseXi (nu : ℝ) := 10/densityDenom nu
def rho (nu : ℝ) := 1-nu*baseXi nu
def inverseSlope : Fin 2 → ℝ := ![1,2]
def inverseOffset (S Q : ℝ) : Fin 2 → ℝ := ![-S,-Q]
def plainSlope (lam : ℝ) : Fin 3 → ℝ := ![1,1,lam/(lam-1)]
def plainOffset (B lam h S Q : ℝ) : Fin 3 → ℝ := ![-S,-h*Q,-B*Q/(lam-1)]
def branchSlope (nu lam : ℝ) (k : Branch) :=
  6*nu+w nu*(inverseSlope k.1+plainSlope lam k.2/2)
def branchOffset (nu B lam h S Q : ℝ) (k : Branch) :=
  w nu*(inverseOffset S Q k.1+plainOffset B lam h S Q k.2/2)
def branchValue (nu B lam h S Q x : ℝ) (k : Branch) :=
  branchSlope nu lam k*x+branchOffset nu B lam h S Q k
def branchRoot (nu B lam h S Q : ℝ) (k : Branch) :=
  (5*Q-branchOffset nu B lam h S Q k)/branchSlope nu lam k
def xi (nu B lam h S Q : ℝ) :=
  Finset.univ.inf' Finset.univ_nonempty (branchRoot nu B lam h S Q)
def cutoff (nu B lam h S Q : ℝ) :=
  inverseThreshold (xi nu B lam h S Q) S Q+
    plainThreshold B lam h (xi nu B lam h S Q) S Q/2
def gain (nu B lam h S Q : ℝ) := nu*(xi nu B lam h S Q-baseXi nu*Q)
def detector (nu B lam h S Q x : ℝ) :=
  6*nu*x+w nu*(inverseThreshold x S Q+plainThreshold B lam h x S Q/2)

theorem branchSlope_pos {nu lam : ℝ} (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4)
    (hlam : 1<lam) (k : Branch) : 0<branchSlope nu lam k := by
  have hn : 0<nu := by linarith
  have hw : 0<w nu := by dsimp [w]; linarith
  have hi0 (i : Fin 2) : 0 < inverseSlope i := by fin_cases i <;> norm_num [inverseSlope]
  have hi := hi0 k.1
  have hp0 (j : Fin 3) : 0 < plainSlope lam j := by
    fin_cases j <;> simp [plainSlope] <;> positivity
  have hp := hp0 k.2
  dsimp [branchSlope]
  positivity

theorem branchValue_le_detector {nu B lam h S Q x : ℝ}
    (hnu : nu≤3/4) (k : Branch) :
    branchValue nu B lam h S Q x k ≤ detector nu B lam h S Q x := by
  have hw : 0≤w nu := by dsimp [w]; linarith
  have hi0 (i : Fin 2) : inverseSlope i*x+inverseOffset S Q i ≤ inverseThreshold x S Q := by
    fin_cases i
    · convert le_max_left (x-S) (2*x-Q) using 1 <;> simp [inverseSlope,inverseOffset,inverseThreshold] <;> ring
    · convert le_max_right (x-S) (2*x-Q) using 1 <;> simp [inverseSlope,inverseOffset,inverseThreshold] <;> ring
  have hi := hi0 k.1
  have hp0 (j : Fin 3) : plainSlope lam j*x+plainOffset B lam h S Q j ≤
      plainThreshold B lam h x S Q := by
    fin_cases j
    · convert le_max_left (x-S) (max (x-h*Q) ((lam*x-B*Q)/(lam-1))) using 1 <;>
        simp [plainSlope,plainOffset,plainThreshold] <;> ring
    · convert (le_max_left (x-h*Q) ((lam*x-B*Q)/(lam-1))).trans
        (le_max_right (x-S) _) using 1 <;> simp [plainSlope,plainOffset,plainThreshold] <;> ring
    · convert (le_max_right (x-h*Q) ((lam*x-B*Q)/(lam-1))).trans
        (le_max_right (x-S) _) using 1 <;> simp [plainSlope,plainOffset,plainThreshold] <;> ring
  have hp := hp0 k.2
  have hh := mul_le_mul_of_nonneg_left (show
    inverseSlope k.1*x+inverseOffset S Q k.1+
      (plainSlope lam k.2*x+plainOffset B lam h S Q k.2)/2 ≤
      inverseThreshold x S Q+plainThreshold B lam h x S Q/2 by linarith) hw
  dsimp [branchValue,branchSlope,branchOffset,detector]
  nlinarith

theorem detector_eq_branch (nu B lam h S Q x : ℝ) :
    ∃ k : Branch, detector nu B lam h S Q x=branchValue nu B lam h S Q x k := by
  have hi : ∃i : Fin 2,inverseThreshold x S Q=inverseSlope i*x+inverseOffset S Q i := by
    rcases le_total (x-S) (2*x-Q) with hh|hh
    · exact ⟨1,by rw [inverseThreshold,max_eq_right hh]; norm_num [inverseSlope,inverseOffset]; ring⟩
    · exact ⟨0,by rw [inverseThreshold,max_eq_left hh]; norm_num [inverseSlope,inverseOffset]; ring⟩
  have hp : ∃j : Fin 3,plainThreshold B lam h x S Q=plainSlope lam j*x+plainOffset B lam h S Q j := by
    rcases le_total (x-S) (max (x-h*Q) ((lam*x-B*Q)/(lam-1))) with hh|hh
    · rcases le_total (x-h*Q) ((lam*x-B*Q)/(lam-1)) with hc|hc
      · refine ⟨2,?_⟩
        rw [plainThreshold,max_eq_right hh,max_eq_right hc]
        norm_num [plainSlope,plainOffset]
        ring
      · exact ⟨1,by rw [plainThreshold,max_eq_right hh,max_eq_left hc]; norm_num [plainSlope,plainOffset]; ring⟩
    · exact ⟨0,by rw [plainThreshold,max_eq_left hh]; norm_num [plainSlope,plainOffset]; ring⟩
  obtain ⟨i,hi⟩ := hi
  obtain ⟨j,hj⟩ := hp
  refine ⟨(i,j),?_⟩
  dsimp [detector,branchValue,branchSlope,branchOffset]
  rw [hi,hj]
  ring

theorem detector_le_iff {nu B lam h S Q x : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hlam : 1<lam) :
    detector nu B lam h S Q x≤5*Q ↔ x≤xi nu B lam h S Q := by
  have hb (k : Branch) : branchValue nu B lam h S Q x k≤5*Q ↔
      x≤branchRoot nu B lam h S Q k := by
    rw [branchRoot,le_div_iff₀ (branchSlope_pos hnu0 hnu1 hlam k)]
    dsimp [branchValue]
    constructor <;> intro hh <;> nlinarith
  constructor
  · intro hd
    apply Finset.le_inf'
    intro k _
    exact (hb k).mp ((branchValue_le_detector hnu1 k).trans hd)
  · intro hx
    obtain ⟨k,hk⟩ := detector_eq_branch nu B lam h S Q x
    rw [hk]
    exact (hb k).mpr (hx.trans (Finset.inf'_le _ (Finset.mem_univ k)))

theorem cutoff_balance {nu B lam h S Q : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hlam : 1<lam) :
    6*nu*xi nu B lam h S Q+w nu*cutoff nu B lam h S Q=5*Q := by
  have hle := (detector_le_iff hnu0 hnu1 hlam).mpr (le_refl (xi nu B lam h S Q))
  have hex : ∃k : Branch,branchRoot nu B lam h S Q k≤xi nu B lam h S Q := by
    have hh := (Finset.inf'_le_iff (f:=branchRoot nu B lam h S Q)
      Finset.univ_nonempty).mp (le_refl (xi nu B lam h S Q))
    simpa only [Finset.mem_univ,true_and] using hh
  obtain ⟨k,hk⟩ := hex
  have hk' : xi nu B lam h S Q=branchRoot nu B lam h S Q k :=
    le_antisymm (Finset.inf'_le _ (Finset.mem_univ k)) hk
  have he : branchValue nu B lam h S Q (xi nu B lam h S Q) k=5*Q := by
    rw [hk']
    dsimp [branchValue,branchRoot]
    rw [mul_div_cancel₀ _ (ne_of_gt (branchSlope_pos hnu0 hnu1 hlam k))]
    ring
  have hge := branchValue_le_detector (B:=B) (lam:=lam) (h:=h) (S:=S) (Q:=Q)
    (x:=xi nu B lam h S Q) hnu1 k
  rw [he] at hge
  exact le_antisymm hle hge

theorem gain_count_identity (nu B lam h S Q : ℝ) :
    Q-nu*xi nu B lam h S Q=rho nu*Q-gain nu B lam h S Q := by
  dsimp [rho,gain]
  ring

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.detector_le_iff
#print axioms QRH.Record1252270103Source.High.cutoff_balance
