/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.RefinedPrice

/-! The widened density interval and the adaptive price hold the live cut q
fixed while the running zero slope ν varies. These are scalar results and
actual global Price objects, not an analytic packed supplier. -/
namespace Qrh.JointDetector.AdaptivePrice
noncomputable section
set_option autoImplicit false
open QRH.SilDensitySplit.CubeFree

def k (ν : ℝ) : ℝ := 10*ν/(15-6*ν)
def amplitudeFloor : ℝ := 10011/20000
def amplitudeCutoff : ℝ := 1001/2000
def gain (q : ℝ) : ℝ := min (9/100) (k q-amplitudeFloor)
def retainedSlope (c ν : ℝ) : ℝ := k ν-c
def extendedMSlope (c ν : ℝ) : ℝ := k ν+(ν-k ν+c)/10

theorem k_den_pos {ν : ℝ} (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) : 0 < 15-6*ν := by
  linarith [hν.2]
theorem k_range {ν : ℝ} (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) :
    (145/288:ℝ) ≤ k ν ∧ k ν ≤ 5/7 := by
  constructor
  · rw [k, le_div_iff₀ (k_den_pos hν)]; linarith [hν.1]
  · rw [k, div_le_iff₀ (k_den_pos hν)]; linarith [hν.2]
theorem k_mono {a b : ℝ} (ha : a ∈ Set.Icc (29/50:ℝ) (3/4))
    (hb : b ∈ Set.Icc (29/50:ℝ) (3/4)) (hab : a ≤ b) : k a ≤ k b := by
  rw [k, k, div_le_div_iff₀ (k_den_pos ha) (k_den_pos hb)]
  nlinarith
theorem k_le_nu {ν : ℝ} (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) : k ν ≤ ν := by
  have hn : 0 ≤ ν := by linarith [hν.1]
  have hp : 0 ≤ 5-6*ν := by linarith [hν.2]
  rw [k, div_le_iff₀ (k_den_pos hν)]
  nlinarith [mul_nonneg hn hp]
theorem retainedSlope_bounds {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) :
    (2977/7200:ℝ) ≤ retainedSlope c ν ∧ retainedSlope c ν ≤ ν := by
  have hk := k_range hν
  have hkn := k_le_nu hν
  dsimp [retainedSlope]
  constructor <;> linarith [hc.1, hc.2]
theorem retainedSlope_pos {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) : 0 < retainedSlope c ν := by
  linarith [(retainedSlope_bounds hc hν).1]
theorem extensionCoeff_pos {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) : 0 ≤ ν-k ν+c := by
  linarith [k_le_nu hν, hc.1]
theorem extendedMSlope_bounds {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) :
    0 ≤ extendedMSlope c ν ∧ extendedMSlope c ν ≤ 636/875 := by
  have hk := k_range hν
  have he := extensionCoeff_pos hc hν
  dsimp [extendedMSlope]
  constructor <;> linarith [hν.2, hc.2]
def gWith (c ν P s M : ℝ) : ℝ :=
  ν*P-k ν*M+retainedSlope c ν*s+(ν-k ν+c)*max (s-M/10) 0
theorem g_eq_max {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100)) (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (P s M : ℝ) :
    gWith c ν P s M = max
      (ν * P - k ν * M + retainedSlope c ν * s)
      (ν * P - extendedMSlope c ν * M + ν * s) := by
  have hc := (extensionCoeff_pos hc hν)
  by_cases hs : s - M/10 ≤ 0
  · rw [gWith, max_eq_right hs, mul_zero, add_zero, max_eq_left]
    dsimp [retainedSlope, extendedMSlope]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hs]
  · have hs' : 0 ≤ s - M/10 := (le_of_not_ge hs)
    rw [gWith, max_eq_left hs', max_eq_right]
    · dsimp [retainedSlope, extendedMSlope]
      ring
    · dsimp [retainedSlope, extendedMSlope]
      nlinarith [mul_nonneg hc hs']

private theorem max_le_max_add {a b a' b' e : ℝ}
    (ha : a' ≤ a + e) (hb : b' ≤ b + e) :
    max a' b' ≤ max a b + e := by
  apply max_le
  · linarith [le_max_left a b]
  · linarith [le_max_right a b]

private theorem linear_increment_le {a L : ℝ} (ha : |a| ≤ L) (δ : ℝ) :
    a * δ ≤ L * |δ| := by
  calc
    a * δ ≤ |a * δ| := le_abs_self _
    _ = |a| * |δ| := abs_mul _ _
    _ ≤ L * |δ| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)

theorem g_mono {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100)) (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    {P P' s s' M : ℝ} (hP : P' ≤ P) (hs : s' ≤ s) :
    gWith c ν P' s' M ≤ gWith c ν P s M := by
  rw [g_eq_max hc hν, g_eq_max hc hν]
  have hn : 0 ≤ ν := by linarith [hν.1]
  have hκ := (retainedSlope_pos hc hν).le
  apply max_le_max
  · linarith [mul_le_mul_of_nonneg_left hP hn,
      mul_le_mul_of_nonneg_left hs hκ]
  · linarith [mul_le_mul_of_nonneg_left hP hn,
      mul_le_mul_of_nonneg_left hs hn]

/-- Arbitrary real ordinary-width increments, including negative increments. -/
theorem g_lipP_all {c ν : ℝ} (_hc : c ∈ Set.Icc (0:ℝ) (9/100)) (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (P s M δ : ℝ) :
    gWith c ν (P + δ) s M ≤ gWith c ν P s M + (3/4 : ℝ) * |δ| := by
  have hn : 0 ≤ ν := by linarith [hν.1]
  have ha : |ν| ≤ (3/4 : ℝ) := by simpa only [abs_of_nonneg hn] using hν.2
  have hδ := linear_increment_le ha δ
  have he : gWith c ν (P + δ) s M = gWith c ν P s M + ν * δ := by
    dsimp [gWith]
    ring
  rw [he]
  linarith

/-- Arbitrary real slot-width increments, including negative increments. -/
theorem g_lipS_all {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100)) (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (P s M δ : ℝ) :
    gWith c ν P (s + δ) M ≤ gWith c ν P s M + (3/4 : ℝ) * |δ| := by
  rw [g_eq_max hc hν, g_eq_max hc hν]
  have hn : 0 ≤ ν := by linarith [hν.1]
  have hκ := retainedSlope_bounds hc hν
  have ha : |ν| ≤ (3/4 : ℝ) := by simpa only [abs_of_nonneg hn] using hν.2
  have hb : |retainedSlope c ν| ≤ (3/4 : ℝ) := by
    rw [abs_of_nonneg (retainedSlope_pos hc hν).le]
    exact hκ.2.trans hν.2
  apply max_le_max_add
  · linarith [linear_increment_le hb δ]
  · linarith [linear_increment_le ha δ]

/-- The ordinary-width field of the generic `Price` interface. -/
theorem g_lipP {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100)) (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    gWith c ν (P + δ) s M ≤ gWith c ν P s M + (3/4 : ℝ) * δ := by
  simpa only [abs_of_nonneg hδ] using g_lipP_all hc hν P s M δ

/-- The slot-width field of the generic `Price` interface. -/
theorem g_lipS {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100)) (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    gWith c ν P (s + δ) M ≤ gWith c ν P s M + (3/4 : ℝ) * δ := by
  simpa only [abs_of_nonneg hδ] using g_lipS_all hc hν P s M δ

/-- The envelope field has the exact global bound `636/875`, for either sign. -/
theorem g_lipM {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100)) (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (P s M δ : ℝ) :
    gWith c ν P s (M + δ) ≤ gWith c ν P s M + (636/875 : ℝ) * |δ| := by
  rw [g_eq_max hc hν, g_eq_max hc hν]
  have hk := k_range hν
  have hm := extendedMSlope_bounds hc hν
  have ha : |-k ν| ≤ (636/875 : ℝ) := by
    rw [abs_neg, abs_of_nonneg (by linarith [hk.1])]
    linarith [hk.2]
  have hb : |-extendedMSlope c ν| ≤ (636/875 : ℝ) := by
    rw [abs_neg, abs_of_nonneg hm.1]
    exact hm.2
  apply max_le_max_add
  · linarith [linear_increment_le ha δ]
  · linarith [linear_increment_le hb δ]

/-- A bound uniform in the density parameter; no width has a sign restriction. -/
theorem g_upper_bound {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100)) (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (P s M : ℝ) :
    gWith c ν P s M ≤ (3/4 : ℝ) * |P| + (3/4 : ℝ) * |s| + (636/875 : ℝ) * |M| := by
  have hP := g_lipP_all hc hν 0 s M P
  have hs := g_lipS_all hc hν 0 0 M s
  have hM := g_lipM hc hν 0 0 0 M
  have hz : gWith c ν 0 0 0 = 0 := by simp [gWith]
  simp only [zero_add] at hP hs hM
  linarith



theorem gain_mem {q : ℝ} (hq : q ∈ Set.Icc (29/50:ℝ) (3/4)) :
    gain q ∈ Set.Icc (0:ℝ) (9/100) := by
  have hk := k_range hq
  constructor
  · apply le_min (by norm_num)
    dsimp [amplitudeFloor]
    linarith [hk.1]
  · exact min_le_left _ _
theorem gain_pos {q : ℝ} (hq : q ∈ Set.Icc (29/50:ℝ) (3/4)) : 0 < gain q := by
  apply lt_min (by norm_num)
  have hk := (k_range hq).1
  dsimp [amplitudeFloor]
  linarith
theorem gain_retained_floor {q ν : ℝ} (hq : q ∈ Set.Icc (29/50:ℝ) (3/4))
    (hν : ν ∈ Set.Icc q (3/4)) : amplitudeFloor ≤ retainedSlope (gain q) ν := by
  have hm := k_mono hq ⟨hq.1.trans hν.1, hν.2⟩ hν.1
  have hc : gain q ≤ k q-amplitudeFloor := min_le_right _ _
  dsimp [retainedSlope]
  linarith
theorem amplitude_gap : amplitudeFloor-amplitudeCutoff = (1/20000:ℝ) := by
  norm_num [amplitudeFloor, amplitudeCutoff]
theorem gain_at_lower : gain (29/50:ℝ) = 263/90000 := by norm_num [gain,k,amplitudeFloor]

/-- A policy supplies a cut range and a gain held fixed throughout each
running density supremum. Fixed-gain physical and adaptive count steps use
the same scalar and StepGates interfaces. -/
structure Policy where
  floor : ℝ
  floor_mem : floor ∈ Set.Icc (29/50:ℝ) (3/4)
  gain : ℝ → ℝ
  gain_mem : ∀ q ∈ Set.Icc floor (3/4), gain q ∈ Set.Icc (0:ℝ) (9/100)
  retained_floor : ∀ q ∈ Set.Icc floor (3/4), amplitudeFloor ≤ k q-gain q

def adaptivePolicy (floor : ℝ) (hf : floor ∈ Set.Icc (29/50:ℝ) (3/4)) : Policy where
  floor := floor
  floor_mem := hf
  gain := gain
  gain_mem _q hq := gain_mem ⟨hf.1.trans hq.1,hq.2⟩
  retained_floor _q hq := gain_retained_floor ⟨hf.1.trans hq.1,hq.2⟩ ⟨le_rfl,hq.2⟩

def fixedPolicy (floor c : ℝ) (hf : floor ∈ Set.Icc (29/50:ℝ) (3/4))
    (hc : c ∈ Set.Icc (0:ℝ) (9/100)) (hr : amplitudeFloor ≤ k floor-c) : Policy where
  floor := floor
  floor_mem := hf
  gain := fun _ => c
  gain_mem _ _ := hc
  retained_floor q hq := by
    have hm := k_mono hf ⟨hf.1.trans hq.1,hq.2⟩ hq.1
    linarith

theorem Policy.retained_bounds (policy : Policy) {q ν : ℝ}
    (hq : q ∈ Set.Icc policy.floor (3/4)) (hν : ν ∈ Set.Icc q (3/4)) :
    retainedSlope (policy.gain q) ν ∈ Set.Icc amplitudeFloor ν := by
  have hνg : ν ∈ Set.Icc (29/50:ℝ) (3/4) := ⟨policy.floor_mem.1.trans (hq.1.trans hν.1),hν.2⟩
  have hqg : q ∈ Set.Icc (29/50:ℝ) (3/4) := ⟨policy.floor_mem.1.trans hq.1,hq.2⟩
  have hm := k_mono hqg hνg hν.1
  have hr := policy.retained_floor q hq
  exact ⟨by dsimp [retainedSlope]; linarith, (retainedSlope_bounds (policy.gain_mem q hq) hνg).2⟩

def supWith (c q P s M : ℝ) : ℝ :=
  ⨆ ν : Set.Icc q (3/4:ℝ), gWith c ν P s M

theorem supWith_bdd {c q : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hq : (29/50:ℝ) ≤ q) (P s M : ℝ) :
    BddAbove (Set.range fun ν : Set.Icc q (3/4:ℝ) => gWith c ν P s M) := by
  refine ⟨(3/4:ℝ)*|P|+(3/4:ℝ)*|s|+(636/875:ℝ)*|M|, ?_⟩
  rintro _ ⟨ν,rfl⟩
  exact g_upper_bound hc ⟨hq.trans ν.2.1,ν.2.2⟩ P s M

theorem le_supWith {c q ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hq : (29/50:ℝ) ≤ q) (hν : ν ∈ Set.Icc q (3/4)) (P s M : ℝ) :
    gWith c ν P s M ≤ supWith c q P s M :=
  le_ciSup (f:=fun ν : Set.Icc q (3/4:ℝ) => gWith c ν P s M)
    (supWith_bdd hc hq P s M) ⟨ν,hν⟩

theorem supWith_le {c q P s M a : ℝ} (hq : q ≤ (3/4:ℝ))
    (h : ∀ ν, q ≤ ν → ν ≤ 3/4 → gWith c ν P s M ≤ a) : supWith c q P s M ≤ a := by
  have : Nonempty (Set.Icc q (3/4:ℝ)) := ⟨⟨3/4,hq,le_rfl⟩⟩
  exact ciSup_le fun ν => h ν ν.2.1 ν.2.2

theorem supWith_mono {c q : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hq : q ∈ Set.Icc (29/50:ℝ) (3/4)) {P P' s s' M : ℝ} (hP : P' ≤ P) (hs : s' ≤ s) :
    supWith c q P' s' M ≤ supWith c q P s M := by
  apply supWith_le hq.2
  intro ν hν hν'
  exact (g_mono hc ⟨hq.1.trans hν,hν'⟩ hP hs).trans (le_supWith hc hq.1 ⟨hν,hν'⟩ P s M)

theorem supWith_lipP {c q : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hq : q ∈ Set.Icc (29/50:ℝ) (3/4)) (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    supWith c q (P+δ) s M ≤ supWith c q P s M+(3/4:ℝ)*δ := by
  apply supWith_le hq.2
  intro ν hν hν'
  exact (g_lipP hc ⟨hq.1.trans hν,hν'⟩ P s M δ hδ).trans
    (add_le_add (le_supWith hc hq.1 ⟨hν,hν'⟩ P s M) le_rfl)
theorem supWith_lipS {c q : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hq : q ∈ Set.Icc (29/50:ℝ) (3/4)) (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    supWith c q P (s+δ) M ≤ supWith c q P s M+(3/4:ℝ)*δ := by
  apply supWith_le hq.2
  intro ν hν hν'
  exact (g_lipS hc ⟨hq.1.trans hν,hν'⟩ P s M δ hδ).trans
    (add_le_add (le_supWith hc hq.1 ⟨hν,hν'⟩ P s M) le_rfl)
theorem supWith_lipM {c q : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hq : q ∈ Set.Icc (29/50:ℝ) (3/4)) (P s M δ : ℝ) :
    supWith c q P s (M+δ) ≤ supWith c q P s M+(636/875:ℝ)*|δ| := by
  apply supWith_le hq.2
  intro ν hν hν'
  exact (g_lipM hc ⟨hq.1.trans hν,hν'⟩ P s M δ).trans
    (add_le_add (le_supWith hc hq.1 ⟨hν,hν'⟩ P s M) le_rfl)

def g (q ν P s M : ℝ) : ℝ := gWith (gain q) ν P s M
def highSup (q P s M : ℝ) : ℝ := supWith (gain q) q P s M

/-- The cleared count denominator for the conservative cap 9/100. -/
def reserveD (ν : ℝ) : ℝ := (3-ν+18/100)*(15-6*ν)-20*ν
/-- The reserve polynomial is certified on the whole widened interval. -/
def reserveP (ν : ℝ) : ℝ :=
  ((15-6*ν)-10*ν)*reserveD ν -
    3*(15-6*ν)*((109/100)*(15-6*ν)-10*ν)*(1-ν) -
    (1/250)*(15-6*ν)*reserveD ν

theorem reserveP_bernstein (ν : ℝ) :
    reserveP ν =
      (2363858/390625:ℝ)*((75-100*ν)/17)^3 +
      3*(94193179/23437500:ℝ)*((100*ν-58)/17)*((75-100*ν)/17)^2 +
      3*(4208323/2500000:ℝ)*((100*ν-58)/17)^2*((75-100*ν)/17) +
      (7299/200000:ℝ)*((100*ν-58)/17)^3 := by
  unfold reserveP reserveD
  ring

theorem reserveP_nonneg {ν : ℝ} (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) : 0 ≤ reserveP ν := by
  have ht : 0 ≤ (100*ν-58)/17 := by linarith [hν.1]
  have hu : 0 ≤ (75-100*ν)/17 := by linarith [hν.2]
  rw [reserveP_bernstein]
  positivity

theorem k_mul_den {ν : ℝ} (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) : k ν*(15-6*ν)=10*ν := by
  exact div_mul_cancel₀ _ (k_den_pos hν).ne'

theorem reserveD_eq {ν : ℝ} (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) :
    reserveD ν = (15-6*ν)*(3-ν-2*(k ν-9/100)) := by
  have hk := k_mul_den hν
  unfold reserveD
  nlinarith

theorem count_den_pos {ν δ : ℝ} (hν : ν ≤ (3/4:ℝ)) (hδ : δ ≤ ν) : 0 < 3-ν-2*δ := by
  linarith

theorem count_difference {ν δ₁ δ₂ : ℝ} (hν : ν ≤ (3/4:ℝ)) (h₁ : δ₁ ≤ ν) (h₂ : δ₂ ≤ ν) :
    jointCountExponent ν δ₁-jointCountExponent ν δ₂ =
      3*(1-ν)^2*(δ₂-δ₁)/((3-ν-2*δ₁)*(3-ν-2*δ₂)) := by
  have hd₁ := (count_den_pos hν h₁).ne'
  have hd₂ := (count_den_pos hν h₂).ne'
  have hm₁ : jointCountExponent ν δ₁*(3-ν-2*δ₁)=3*(1-δ₁)*(1-ν) := by
    rw [jointCountExponent_eq]
    exact div_mul_cancel₀ _ hd₁
  have hm₂ : jointCountExponent ν δ₂*(3-ν-2*δ₂)=3*(1-δ₂)*(1-ν) := by
    rw [jointCountExponent_eq]
    exact div_mul_cancel₀ _ hd₂
  apply (eq_div_iff (mul_ne_zero hd₁ hd₂)).mpr
  calc
    _ = (jointCountExponent ν δ₁*(3-ν-2*δ₁))*(3-ν-2*δ₂)-
      (jointCountExponent ν δ₂*(3-ν-2*δ₂))*(3-ν-2*δ₁) := by ring
    _ = _ := by rw [hm₁,hm₂]; ring

theorem count_mono {ν δ₁ δ₂ : ℝ} (hν : ν ≤ (3/4:ℝ))
    (h₁ : δ₁ ≤ ν) (h₂ : δ₂ ≤ ν) (hδ : δ₁ ≤ δ₂) :
    jointCountExponent ν δ₂ ≤ jointCountExponent ν δ₁ := by
  have hd := mul_pos (count_den_pos hν h₁) (count_den_pos hν h₂)
  have hdiff := count_difference hν h₁ h₂
  have hn : 0 ≤ 3*(1-ν)^2*(δ₂-δ₁)/((3-ν-2*δ₁)*(3-ν-2*δ₂)) :=
    div_nonneg (by positivity) hd.le
  linarith

theorem reserveP_identity {ν : ℝ} (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) :
    reserveP ν = ((1-k ν)-jointCountExponent ν (k ν-9/100)-1/250)*
      ((15-6*ν)*reserveD ν) := by
  have hk := k_mul_den hν
  have hδ : k ν-9/100 ≤ ν := by linarith [k_le_nu hν]
  have hd := (count_den_pos hν.2 hδ).ne'
  have he : jointCountExponent ν (k ν-9/100)*(3-ν-2*(k ν-9/100))=
      3*(1-(k ν-9/100))*(1-ν) := by
    rw [jointCountExponent_eq]
    exact div_mul_cancel₀ _ hd
  unfold reserveP
  rw [reserveD_eq hν, ← hk]
  linear_combination (15-6*ν)^2*he

theorem count_at_cap {ν : ℝ} (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) :
    jointCountExponent ν (k ν-9/100) ≤ (1-k ν)-1/250 := by
  have hδ : k ν-9/100 ≤ ν := by linarith [k_le_nu hν]
  have hD : 0 < reserveD ν := by
    rw [reserveD_eq hν]
    exact mul_pos (k_den_pos hν) (count_den_pos hν.2 hδ)
  have hP := reserveP_nonneg hν
  rw [reserveP_identity hν] at hP
  have hd := mul_pos (k_den_pos hν) hD
  have hn : 0 ≤ (1-k ν)-jointCountExponent ν (k ν-9/100)-1/250 :=
    nonneg_of_mul_nonneg_left hP hd
  linarith

/-- The conservative cap comparison is algebraic even if kν-.09<1/2.
No selected norm is invoked at that auxiliary slope. -/
theorem count_at_retained {c ν : ℝ} (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4)) :
    jointCountExponent ν (retainedSlope c ν) ≤ (1-k ν)-1/250 := by
  have h₁ : k ν-9/100 ≤ ν := by linarith [k_le_nu hν]
  have h₂ := (retainedSlope_bounds hc hν).2
  exact (count_mono hν.2 h₁ h₂ (by dsimp [retainedSlope]; linarith [hc.2])).trans (count_at_cap hν)

/-- Uniform derivative payment on the actual amplitude range. -/
theorem count_decrease {ν δ₁ δ₂ : ℝ}
    (hν : ν ∈ Set.Icc (29/50:ℝ) (3/4))
    (hδ₁ : δ₁ ∈ Set.Icc (1/2:ℝ) ν) (hδ₂ : δ₂ ∈ Set.Icc (1/2:ℝ) ν)
    (hδ : δ₁ ≤ δ₂) :
    jointCountExponent ν δ₂ ≤ jointCountExponent ν δ₁-(3/25:ℝ)*(δ₂-δ₁) := by
  have h₁ := count_den_pos hν.2 hδ₁.2
  have h₂ := count_den_pos hν.2 hδ₂.2
  have hb : 0 ≤ 5*(1-ν) := by linarith [hν.2]
  have hu₁ : 3-ν-2*δ₁ ≤ 5*(1-ν) := by linarith [hν.2,hδ₁.1]
  have hu₂ : 3-ν-2*δ₂ ≤ 5*(1-ν) := by linarith [hν.2,hδ₂.1]
  have hprod := mul_le_mul hu₁ hu₂ h₂.le hb
  have hg : 0 ≤ (3/25:ℝ)*(δ₂-δ₁) := by positivity
  have hpaid := mul_le_mul_of_nonneg_right hprod hg
  have hi : (3/25:ℝ)*(δ₂-δ₁) ≤
      3*(1-ν)^2*(δ₂-δ₁)/((3-ν-2*δ₁)*(3-ν-2*δ₂)) := by
    apply (le_div_iff₀ (mul_pos h₁ h₂)).mpr
    nlinarith
  rw [← count_difference hν.2 hδ₁.2 hδ₂.2] at hi
  linarith

def jointPrice (policy : Policy) (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc policy.floor (3/4)) :
    QRH.SilDensitySplit.CubeFree.Price where
  f w P s M := max
    (QRH.SilDensitySplit.Density.lowPart B₀ L₀ c₀ (q w) P s M)
    (supWith (policy.gain (q w)) (q w) P s M)
  nonneg w P s M := by
    have hq0 : 0 ≤ q w := by linarith [policy.floor_mem.1, (hq w).1]
    exact le_max_of_le_left (mul_nonneg hq0 (deletionNeed_nonneg B₀ L₀ c₀ P s M))
  mono w P P' s s' M hP hs := by
    have hq0 : 0 ≤ q w := by linarith [policy.floor_mem.1, (hq w).1]
    exact max_le_max
      (mul_le_mul_of_nonneg_left (deletionNeed_mono hL hP hs) hq0)
      (supWith_mono (policy.gain_mem (q w) (hq w))
        ⟨policy.floor_mem.1.trans (hq w).1, (hq w).2⟩ hP hs)
  lip := needLip B₀ L₀ c₀
  lip_nonneg := zero_le_one.trans (one_le_needLip B₀ L₀ c₀)
  lipP w P s M δ hδ := by
    have hq0 : 0 ≤ q w := by linarith [policy.floor_mem.1, (hq w).1]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) hδ)
        (deletionNeed_lipP hL hδ)
    · have hhigh := supWith_lipP (policy.gain_mem (q w) (hq w))
        ⟨policy.floor_mem.1.trans (hq w).1, (hq w).2⟩ P s M δ hδ
      have hscale : (3/4 : ℝ) * δ ≤ needLip B₀ L₀ c₀ * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      exact hhigh.trans (add_le_add le_rfl hscale)
  lipS w P s M δ hδ := by
    have hq0 : 0 ≤ q w := by linarith [policy.floor_mem.1, (hq w).1]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) hδ)
        (deletionNeed_lipS hL hδ)
    · have hhigh := supWith_lipS (policy.gain_mem (q w) (hq w))
        ⟨policy.floor_mem.1.trans (hq w).1, (hq w).2⟩ P s M δ hδ
      have hscale : (3/4 : ℝ) * δ ≤ needLip B₀ L₀ c₀ * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      exact hhigh.trans (add_le_add le_rfl hscale)
  lipM w P s M δ := by
    have hq0 : 0 ≤ q w := by linarith [policy.floor_mem.1, (hq w).1]
    have hq1 : q w ≤ 1 := by linarith [(hq w).2]
    have hK := one_le_needLip B₀ L₀ c₀
    apply QRH.SilDensitySplit.Density.max_le_max_add
    · exact QRH.SilDensitySplit.Density.lowPart_lip hq0 hq1
        (mul_nonneg (by linarith : 0 ≤ needLip B₀ L₀ c₀) (abs_nonneg δ))
        (deletionNeed_lipM hL)
    · have hhigh := supWith_lipM (policy.gain_mem (q w) (hq w))
        ⟨policy.floor_mem.1.trans (hq w).1, (hq w).2⟩ P s M δ
      have hscale : (636/875 : ℝ) * |δ| ≤ needLip B₀ L₀ c₀ * |δ| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg δ)
      exact hhigh.trans (add_le_add le_rfl hscale)

theorem jointPrice_f (policy : Policy) (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc policy.floor (3/4))
    (w P s M : ℝ) :
    (jointPrice policy B₀ L₀ c₀ hL q hq).f w P s M =
      max (q w * deletionNeed B₀ L₀ c₀ P s M) (supWith (policy.gain (q w)) (q w) P s M) := rfl

theorem jointPrice_lip (policy : Policy) (B₀ L₀ c₀ : ℝ) (hL : 0 < L₀)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Set.Icc policy.floor (3/4)) :
    (jointPrice policy B₀ L₀ c₀ hL q hq).lip = needLip B₀ L₀ c₀ := rfl

theorem joint_count_above_retainedSlope {c ν δ : ℝ}
    (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4)) (hr : amplitudeFloor ≤ retainedSlope c ν)
    (hδ : δ ∈ Set.Icc (retainedSlope c ν) ν) :
    jointCountExponent ν δ ≤ (1 - k ν) - 1/250 -
      (3/25 : ℝ) * (δ - retainedSlope c ν) := by
  have hκ : retainedSlope c ν ∈ Set.Icc (1/2:ℝ) ν :=
    ⟨by dsimp [amplitudeFloor] at hr; linarith, (retainedSlope_bounds hc hν).2⟩
  have hδ' : δ ∈ Set.Icc (1/2 : ℝ) ν := ⟨hκ.1.trans hδ.1, hδ.2⟩
  have hdec := count_decrease hν hκ hδ' hδ.1
  linarith [count_at_retained hc hν]

/-- The HIGH-amplitude branch pays the retained price with its fixed reserve. -/
theorem joint_energy_small_cap_high {c ν δ P s M : ℝ}
    (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4)) (hr : amplitudeFloor ≤ retainedSlope c ν)
    (hδ : δ ∈ Set.Icc (retainedSlope c ν) ν)
    (hM : 0 ≤ M) (hs : s ≤ M/10) :
    jointCountExponent ν δ * M + ν * P + δ * s ≤
      (1 - k ν) * M + ν * P + retainedSlope c ν * s - M/250 := by
  have hc := mul_le_mul_of_nonneg_right (joint_count_above_retainedSlope hc hν hr hδ) hM
  have hgap : 0 ≤ δ - retainedSlope c ν := sub_nonneg.mpr hδ.1
  have hcap : 0 ≤ (3/25 : ℝ) * M - s := by linarith
  have hpaid := mul_nonneg hgap hcap
  nlinarith

/-- At small retained width, the better of the zero and joint counts pays `g`. -/
theorem joint_energy_small_cap {c ν δ P s M : ℝ}
    (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4)) (hr : amplitudeFloor ≤ retainedSlope c ν)
    (hδ : δ ∈ Set.Icc (1001/2000 : ℝ) ν)
    (hM : 0 ≤ M) (hs0 : 0 ≤ s) (hs : s ≤ M/10) :
    min (1 - k ν) (jointCountExponent ν δ) * M + ν * P + δ * s ≤
      M + gWith c ν P s M := by
  have heq : M + gWith c ν P s M =
      (1 - k ν) * M + ν * P + retainedSlope c ν * s := by
    rw [gWith, max_eq_right (by linarith : s - M/10 ≤ 0), mul_zero]
    ring
  rw [heq]
  by_cases hκ : δ ≤ retainedSlope c ν
  · have hmin := mul_le_mul_of_nonneg_right
      (min_le_left (1 - k ν) (jointCountExponent ν δ)) hM
    have hslot := mul_le_mul_of_nonneg_right hκ hs0
    linarith
  · have hδκ : δ ∈ Set.Icc (retainedSlope c ν) ν := ⟨le_of_not_ge hκ, hδ.2⟩
    have hhigh := joint_energy_small_cap_high hc hν hr hδκ hM hs (P := P)
    have hmin := mul_le_mul_of_nonneg_right
      (min_le_right (1 - k ν) (jointCountExponent ν δ)) hM
    linarith

/-- The scalar extension to all nonnegative slot widths leaves the slots intact. -/
theorem joint_energy_le_g {c ν δ P s M : ℝ}
    (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4)) (hr : amplitudeFloor ≤ retainedSlope c ν)
    (hδ : δ ∈ Set.Icc (1001/2000 : ℝ) ν)
    (hM : 0 ≤ M) (hs0 : 0 ≤ s) :
    min (1 - k ν) (jointCountExponent ν δ) * M + ν * P + δ * s ≤
      M + gWith c ν P s M := by
  by_cases hs : s ≤ M/10
  · exact joint_energy_small_cap hc hν hr hδ hM hs0 hs
  · have hbase := joint_energy_small_cap hc hν hr hδ hM
      (by linarith : 0 ≤ M/10) (le_rfl : M/10 ≤ M/10) (P := P)
    have hshift := mul_le_mul_of_nonneg_right hδ.2
      (by linarith : 0 ≤ s - M/10)
    have hcap : gWith c ν P (M/10) M =
        ν * P - k ν * M + retainedSlope c ν * (M/10) := by simp [gWith]
    rw [hcap] at hbase
    rw [gWith, max_eq_left (by linarith : 0 ≤ s - M/10)]
    dsimp [retainedSlope] at hbase ⊢
    nlinarith

/-- Low-amplitude labels need only the inherited zero count. -/
theorem zero_energy_le_g_of_delta_le {c ν δ P s M : ℝ}
    (hc : c ∈ Set.Icc (0:ℝ) (9/100))
    (hν : ν ∈ Set.Icc (29/50 : ℝ) (3/4))
    (hδ : δ ≤ retainedSlope c ν) (hs : 0 ≤ s) :
    (1 - k ν) * M + ν * P + δ * s ≤ M + gWith c ν P s M := by
  have hslot := mul_le_mul_of_nonneg_right hδ hs
  have hext := mul_nonneg (extensionCoeff_pos hc hν)
    (le_max_right (s - M/10) 0)
  unfold gWith
  nlinarith



/-- The exact count-to-price interface, including the original LOW-amplitude
count and the same-cut supremum. -/
theorem policy_joint_energy (policy : Policy) {q ν δ P s M : ℝ}
    (hq : q ∈ Set.Icc policy.floor (3/4)) (hν : ν ∈ Set.Icc q (3/4))
    (hδ : δ ∈ Set.Icc (1001/2000:ℝ) ν) (hM : 0 ≤ M) (hs : 0 ≤ s) :
    min (1-k ν) (jointCountExponent ν δ)*M+ν*P+δ*s ≤
      M+supWith (policy.gain q) q P s M := by
  have hνg : ν ∈ Set.Icc (29/50:ℝ) (3/4) :=
    ⟨policy.floor_mem.1.trans (hq.1.trans hν.1),hν.2⟩
  exact (joint_energy_le_g (policy.gain_mem q hq) hνg
    (policy.retained_bounds hq hν).1 hδ hM hs).trans
    (add_le_add le_rfl (le_supWith (policy.gain_mem q hq)
      (policy.floor_mem.1.trans hq.1) hν P s M))

def jointRate (ν δ : ℝ) : ℝ :=
  if δ ≤ ν then min (1-k ν) (jointCountExponent ν δ) else min (1-k ν) (1-δ)

/-- The full-row and ordinary-times-slot bounds give slot exponent min(δ,ν).
This pays the top class with SC(.75), without asserting a slot amplitude cap. -/
theorem policy_jointRate_energy (policy : Policy) {q ν δ P s M : ℝ}
    (hq : q ∈ Set.Icc policy.floor (3/4)) (hν : ν ∈ Set.Icc q (3/4))
    (hδ : δ ∈ Set.Icc (1001/2000:ℝ) (3/4)) (hM : 0 ≤ M) (hs : 0 ≤ s) :
    jointRate ν δ*M+ν*P+min δ ν*s ≤ M+supWith (policy.gain q) q P s M := by
  have hνg : ν ∈ Set.Icc (29/50:ℝ) (3/4) :=
    ⟨policy.floor_mem.1.trans (hq.1.trans hν.1),hν.2⟩
  unfold jointRate
  split_ifs with h
  · rw [min_eq_left h]
    exact policy_joint_energy policy hq hν ⟨hδ.1,h⟩ hM hs
  · have hνδ : ν ≤ δ := le_of_not_ge h
    rw [min_eq_right hνδ]
    have he : jointCountExponent ν ν=1-ν := by
      unfold jointCountExponent witnessDen
      have hd : 3*(1-ν) ≠ 0 := by nlinarith [hν.2]
      have hh : 3*(1-ν)+2*(ν-ν)=3*(1-ν) := by ring
      rw [hh]
      field_simp
    have hk := k_le_nu hνg
    have hb := policy_joint_energy policy hq hν
      (show ν ∈ Set.Icc (1001/2000:ℝ) ν from ⟨by linarith [hνg.1],le_rfl⟩) hM hs (P:=P)
    rw [he,min_eq_right (by linarith)] at hb
    have hr := mul_le_mul_of_nonneg_right
      ((min_le_right (1-k ν) (1-δ)).trans (show 1-δ ≤ 1-ν by linarith)) hM
    linarith

theorem policy_zero_energy (policy : Policy) {q ν δ P s M : ℝ}
    (hq : q ∈ Set.Icc policy.floor (3/4)) (hν : ν ∈ Set.Icc q (3/4))
    (hδ : δ ≤ amplitudeCutoff) (hs : 0 ≤ s) :
    (1-k ν)*M+ν*P+δ*s ≤ M+supWith (policy.gain q) q P s M := by
  have hνg : ν ∈ Set.Icc (29/50:ℝ) (3/4) :=
    ⟨policy.floor_mem.1.trans (hq.1.trans hν.1),hν.2⟩
  have hr := (policy.retained_bounds hq hν).1
  have hcut : δ ≤ retainedSlope (policy.gain q) ν := by
    dsimp [amplitudeFloor,amplitudeCutoff] at hδ hr
    linarith
  exact (zero_energy_le_g_of_delta_le (policy.gain_mem q hq) hνg hcut hs).trans
    (add_le_add le_rfl (le_supWith (policy.gain_mem q hq)
      (policy.floor_mem.1.trans hq.1) hν P s M))

/-- The two policies used by the retained count and physical chains. -/
def adaptive58 : Policy := adaptivePolicy (29/50) ⟨le_rfl,by norm_num⟩
def adaptive60 : Policy := adaptivePolicy (3/5) (by norm_num)
def physical65 : Policy := fixedPolicy (13/20) (17/200) (by norm_num) (by norm_num)
  (by norm_num [amplitudeFloor,k])

end
end Qrh.JointDetector.AdaptivePrice

#print axioms Qrh.JointDetector.AdaptivePrice.jointPrice
#print axioms Qrh.JointDetector.AdaptivePrice.count_at_retained
#print axioms Qrh.JointDetector.AdaptivePrice.joint_energy_le_g
#print axioms Qrh.JointDetector.AdaptivePrice.adaptivePolicy

#print axioms Qrh.JointDetector.AdaptivePrice.policy_jointRate_energy
#print axioms Qrh.JointDetector.AdaptivePrice.policy_zero_energy
