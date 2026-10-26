import Candidate.Cycle63.Moment.HighSourceEnergy

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped ContDiff
open Set Filter

def highBuffer (Rs Rp es ep : ℝ) := min (1/2000) (min (es/(32*(Rs+1))) (ep/(48*(Rp+2))))
def highKappa (es ep : ℝ) := min 1 (min (es/4) (ep/32))
def highHeight (J : ℕ) (loss d es ep : ℝ) :=
  min (loss/(2*(J+1))) (min (d*(ep/8)/32) (d*es/16))

lemma high_buffer_pos {Rs Rp es ep : ℝ} (hRs : 0≤Rs) (hRp : 0≤Rp)
    (hes : 0<es) (hep : 0<ep) : 0<highBuffer Rs Rp es ep := by
  dsimp [highBuffer]
  positivity

lemma high_kappa_pos {es ep : ℝ} (hes : 0<es) (hep : 0<ep) :
    0<highKappa es ep := by dsimp [highKappa]; positivity

lemma high_buffer_budgets {Rs Rp es ep : ℝ} (hRs : 0≤Rs) (hRp : 0≤Rp)
    (hes : 0<es) (hep : 0<ep) :
    8*highBuffer Rs Rp es ep*Rs+highKappa es ep≤es ∧
      12*highBuffer Rs Rp es ep*(Rp+2)+8*highKappa es ep+2*(ep/8)≤ep := by
  have hbuf : highBuffer Rs Rp es ep≤es/(32*(Rs+1)) := (min_le_right (1/2000:ℝ) _).trans (min_le_left (es/(32*(Rs+1))) _)
  have hbuf' : highBuffer Rs Rp es ep≤ep/(48*(Rp+2)) := (min_le_right (1/2000:ℝ) _).trans (min_le_right _ (ep/(48*(Rp+2))))
  change highBuffer Rs Rp es ep≤es/(32*(Rs+1)) at hbuf
  change highBuffer Rs Rp es ep≤ep/(48*(Rp+2)) at hbuf'
  have hs := (le_div_iff₀ (by positivity : 0<32*(Rs+1))).mp hbuf
  have hp := (le_div_iff₀ (by positivity : 0<48*(Rp+2))).mp hbuf'
  have hk : highKappa es ep≤es/4 :=
    (min_le_right 1 _).trans (min_le_left _ _)
  have hk' : highKappa es ep≤ep/32 :=
    (min_le_right 1 _).trans (min_le_right _ _)
  have he := high_buffer_pos hRs hRp hes hep
  constructor <;> nlinarith

/-- The analytic parameters exist for every positive requested loss.
The height exponent is selected after the density degree J. -/
def highParameters (W : ℝ→ℂ) (A B Rs Rp es ep lo hi bΦ Mcap Bmask margin d loss : ℝ)
    (J : ℕ) (bound : ℕ→ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hRs : 0≤Rs) (hRp : 0≤Rp) (hes : 0<es) (hep : 0<ep)
    (hbΦ : 0≤bΦ) (hmargin : 0< margin) (hd : 0<d)
    (hsupply : Mcap+Bmask+margin≤d) (hloss : 0<loss) (hbound : ∀k,0≤bound k) :
    HighSourceParameters where
  Wslot := W
  A₀ := A
  B₀ := B
  hA₀ := hA
  hWs := hWs
  hW := hW
  Rwidth := Rs
  Rplain := Rp
  dmax := d
  τ := highHeight J loss d es ep
  εslot := es
  εplain := ep
  e := highBuffer Rs Rp es ep
  κ := highKappa es ep
  vplain := ep/8
  vslot := es
  σmin := lo
  σmax := hi
  bΦ := bΦ
  Mcap := Mcap
  Bmask := Bmask
  margin := margin
  d := d
  hRw := hRs
  hRp := hRp
  hdmax := hd.le
  hτ := by dsimp [highHeight]; positivity
  hεs := hes
  hεp := hep
  he := high_buffer_pos hRs hRp hes hep
  he' := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  hκ := high_kappa_pos hes hep
  hκ' := min_le_left _ _
  hvp := by positivity
  hvs := hes.le
  hslotBudget := (high_buffer_budgets hRs hRp hes hep).1
  hplainBudget := (high_buffer_budgets hRs hRp hes hep).2
  hbΦ := hbΦ
  hmargin := hmargin
  hd := hd
  hdsupply := hsupply
  hdm := le_rfl
  profileBound := bound
  hprofile := hbound

/-- The chosen height loss pays both analytic height gates and the density
polynomial uniformly on the retained height range. The threshold is fixed
before the actual height bin and source data. -/
theorem eventually_high_truncated_heights (P : HighSourceParameters) (J : ℕ)
    (loss : ℝ) (hslot : 8*P.τ≤P.d*P.vslot)
    (hplain : 16*P.τ≤P.d*P.vplain) (hdensity : 2*P.τ*(J+1)≤loss) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀i : ℕ,(i:ℝ)≤Z^P.τ →
      (3+(3*i+2:ℕ)*Z^P.τ)^2≤(Z^P.d)^P.vslot ∧
      (3+(3*i+2:ℕ)*Z^P.τ)^4≤(Z^P.d)^P.vplain ∧
      (1+3*(i+1:ℕ)*Z^P.τ)^J≤Z^loss := by
  filter_upwards [(tendsto_rpow_atTop P.hτ).eventually
    (eventually_ge_atTop (max (8:ℝ) (7^J))),eventually_gt_atTop (1:ℝ)] with Z hbig hZ
  refine ⟨hZ,?_⟩
  intro i hi
  let x := Z^P.τ
  have hx : 8≤x := (le_max_left _ _).trans hbig
  have hx₁ : 1≤x := by linarith
  have hx₀ : 0≤x := by linarith
  have hconst : (7:ℝ)^J≤x^2 := ((le_max_right _ _).trans hbig).trans (by nlinarith)
  have hy : (3+(3*i+2:ℕ)*x)≤x^3 := by
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    change (i:ℝ)≤x at hi
    have hix := mul_le_mul_of_nonneg_right hi hx₀
    have hxx : 8*x^2≤x^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg x)]
    nlinarith [sq_nonneg (x-1)]
  have hd : (1+3*(i+1:ℕ)*x)≤7*x^2 := by
    simp only [Nat.cast_add,Nat.cast_one]
    change (i:ℝ)≤x at hi
    nlinarith [mul_le_mul_of_nonneg_right hi hx₀,sq_nonneg (x-1)]
  have hz : 0<Z := zero_lt_one.trans hZ
  have hp (k : ℕ) : x^k=Z^(P.τ*(k:ℝ)) := by
    dsimp [x]
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ (x^3)^2 := pow_le_pow_left₀ (by positivity) hy 2
      _ = Z^(P.τ*6) := by rw [←pow_mul]; norm_num; exact hp 6
      _ ≤ _ := by
        rw [←Real.rpow_mul hz.le]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        nlinarith [P.hτ]
  · calc
      _ ≤ (x^3)^4 := pow_le_pow_left₀ (by positivity) hy 4
      _ = Z^(P.τ*12) := by rw [←pow_mul]; norm_num; exact hp 12
      _ ≤ _ := by
        rw [←Real.rpow_mul hz.le]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        nlinarith [P.hτ]
  · calc
      _ ≤ (7*x^2)^J := pow_le_pow_left₀ (by positivity) hd J
      _ = 7^J*x^(2*J) := by rw [mul_pow,←pow_mul]
      _ ≤ x^2*x^(2*J) := mul_le_mul_of_nonneg_right hconst (pow_nonneg hx₀ _)
      _ = Z^(P.τ*(2*(J+1))) := by
        rw [←pow_add,hp]
        congr 1
        push_cast
        ring
      _ ≤ Z^loss := Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

end
end OAI.SevenEighths.Cycle63Moment
