import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.CubicRoot

set_option autoImplicit false
set_option maxHeartbeats 0
namespace BelowSevenEighthsTight
noncomputable section

private theorem quadratic_nonneg (A B C r : ℝ)
    (hr : rootLower ≤ r) (hru : r ≤ rootUpper)
    (h0 : 0 ≤ A+B*rootLower+C*rootLower^2)
    (h1 : 0 ≤ A+B*(rootLower+rootUpper)/2+C*rootLower*rootUpper)
    (h2 : 0 ≤ A+B*rootUpper+C*rootUpper^2) : 0 ≤ A+B*r+C*r^2 := by
  have hl := sub_nonneg.mpr hr
  have hu := sub_nonneg.mpr hru
  have he : (rootUpper-rootLower)^2*(A+B*r+C*r^2) =
      (A+B*rootLower+C*rootLower^2)*(rootUpper-r)^2 +
      2*(A+B*(rootLower+rootUpper)/2+C*rootLower*rootUpper)*
        (r-rootLower)*(rootUpper-r) +
      (A+B*rootUpper+C*rootUpper^2)*(r-rootLower)^2 := by ring
  have hmul : 0 ≤ (rootUpper-rootLower)^2*(A+B*r+C*r^2) := by
    rw [he]
    positivity
  exact nonneg_of_mul_nonneg_right hmul (sq_pos_of_pos (sub_pos.mpr root_interval_signs.1))

def optimalPolynomial (r d y : ℝ) : ℝ := (803551705/43283530548 : ℝ) + (-46448048755/21641765274 : ℝ)*y + (1011785587/3606960879 : ℝ)*d + (-123242118827/7213921758 : ℝ)*d*y + (27408175729/3606960879 : ℝ)*d*y^2 + (6048249209/6011601465 : ℝ)*d^2 + (30244888258/2003867155 : ℝ)*d^2*y + (-55151565698/2003867155 : ℝ)*d^2*y^2 + (1636/201 : ℝ)*d^2*y^3 + (-3565011325/28855687032 : ℝ)*r + (97754907775/14427843516 : ℝ)*r*y + (-4231528015/2404640586 : ℝ)*r*d + (125962874335/2404640586 : ℝ)*r*d*y + (-29179198235/1202320293 : ℝ)*r*d*y^2 + (-1371087781/801546862 : ℝ)*r*d^2 + (-17584463029/400773431 : ℝ)*r*d^2*y + (36156089282/400773431 : ℝ)*r*d^2*y^2 + (-1660/67 : ℝ)*r*d^2*y^3 + (3216515335/4809281172 : ℝ)*r^2 + (-6702046285/2404640586 : ℝ)*r^2*y + (93042829/400773431 : ℝ)*r^2*d + (-10229578117/400773431 : ℝ)*r^2*d*y + (4758254578/400773431 : ℝ)*r^2*d*y^2 + (1757311809/2003867155 : ℝ)*r^2*d^2 + (42037065114/2003867155 : ℝ)*r^2*d^2*y + (-88453405524/2003867155 : ℝ)*r^2*d^2*y^2 + (792/67 : ℝ)*r^2*d^2*y^3
def squareK (r : ℝ) : ℝ := (6048249209/6011601465 : ℝ) + (-1371087781/801546862 : ℝ)*r + (1757311809/2003867155 : ℝ)*r^2
def centralCoefficient1 (r d : ℝ) : ℝ := (-46448048755/21641765274 : ℝ) + (-123242118827/7213921758 : ℝ)*d + (30244888258/2003867155 : ℝ)*d^2 + (97754907775/14427843516 : ℝ)*r + (125962874335/2404640586 : ℝ)*r*d + (-17584463029/400773431 : ℝ)*r*d^2 + (-6702046285/2404640586 : ℝ)*r^2 + (-10229578117/400773431 : ℝ)*r^2*d + (42037065114/2003867155 : ℝ)*r^2*d^2
def centralCoefficient2 (r d : ℝ) : ℝ := (27408175729/3606960879 : ℝ)*d + (-55151565698/2003867155 : ℝ)*d^2 + (-29179198235/1202320293 : ℝ)*r*d + (36156089282/400773431 : ℝ)*r*d^2 + (4758254578/400773431 : ℝ)*r^2*d + (-88453405524/2003867155 : ℝ)*r^2*d^2
def centralCoefficient3 (r d : ℝ) : ℝ := (1636/201 : ℝ)*d^2 + (-1660/67 : ℝ)*r*d^2 + (792/67 : ℝ)*r^2*d^2

theorem central_square_identity (r d y : ℝ) (hr : deltaPolynomial r = 0) :
    optimalPolynomial r d y = squareK r*(d-r)^2+
      centralCoefficient1 r d*y+centralCoefficient2 r d*y^2+centralCoefficient3 r d*y^3 := by
  unfold optimalPolynomial squareK centralCoefficient1 centralCoefficient2 centralCoefficient3
  unfold deltaPolynomial at hr
  linear_combination ((8458439/86567061096 : ℝ) + (53251873/36069608790 : ℝ)*d + (-53251873/72139217580 : ℝ)*r)*hr

private theorem squareK_nonneg (r : ℝ) (hr : rootLower ≤ r) (hru : r ≤ rootUpper) : 0 ≤ squareK r := by
  have hk : 0 ≤ ((6048249209/6011601465 : ℝ)*r^0 + (-1371087781/801546862 : ℝ)*r^1 + (1757311809/2003867155 : ℝ)*r^2) := by
    convert quadratic_nonneg (6048249209/6011601465 : ℝ) (-1371087781/801546862 : ℝ) (1757311809/2003867155 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  simpa [squareK] using hk

private theorem central1_nonneg (r d : ℝ)
    (hr : rootLower ≤ r) (hru : r ≤ rootUpper)
    (hd : (7/20 : ℝ) ≤ d) (hdu : d ≤ (9/20 : ℝ)) : 0 ≤ centralCoefficient1 r d := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hc0 : 0 ≤ ((-33959571589504/54104413185 : ℝ)*r^0 + (28472946192061/14427843516 : ℝ)*r^1 + (-11002355879471/12023202930 : ℝ)*r^2) := by
    convert quadratic_nonneg (-33959571589504/54104413185 : ℝ) (28472946192061/14427843516 : ℝ) (-11002355879471/12023202930 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc1 : 0 ≤ ((-71446018210271/54104413185 : ℝ)*r^0 + (30036190080457/7213921758 : ℝ)*r^1 + (-11654014229627/6011601465 : ℝ)*r^2) := by
    convert quadratic_nonneg (-71446018210271/54104413185 : ℝ) (30036190080457/7213921758 : ℝ) (-11654014229627/6011601465 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc2 : 0 ≤ ((-36669834637801/54104413185 : ℝ)*r^0 + (30966393299809/14427843516 : ℝ)*r^1 + (-12053450189099/12023202930 : ℝ)*r^2) := by
    convert quadratic_nonneg (-36669834637801/54104413185 : ℝ) (30966393299809/14427843516 : ℝ) (-12053450189099/12023202930 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have he : centralCoefficient1 r d = ((-33959571589504/54104413185 : ℝ)*r^0 + (28472946192061/14427843516 : ℝ)*r^1 + (-11002355879471/12023202930 : ℝ)*r^2)*(d-(7/20 : ℝ))^0*((9/20 : ℝ)-d)^2 + ((-71446018210271/54104413185 : ℝ)*r^0 + (30036190080457/7213921758 : ℝ)*r^1 + (-11654014229627/6011601465 : ℝ)*r^2)*(d-(7/20 : ℝ))^1*((9/20 : ℝ)-d)^1 + ((-36669834637801/54104413185 : ℝ)*r^0 + (30966393299809/14427843516 : ℝ)*r^1 + (-12053450189099/12023202930 : ℝ)*r^2)*(d-(7/20 : ℝ))^2*((9/20 : ℝ)-d)^0 := by
    unfold centralCoefficient1
    ring
  rw [he]
  positivity

private theorem central2_nonneg (r d : ℝ)
    (hr : rootLower ≤ r) (hru : r ≤ rootUpper)
    (hd : (7/20 : ℝ) ≤ d) (hdu : d ≤ (9/20 : ℝ)) : 0 ≤ centralCoefficient2 r d := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hc0 : 0 ≤ ((-2568058731259/36069608790 : ℝ)*r^0 + (614928685777/2404640586 : ℝ)*r^1 + (-250859666519/2003867155 : ℝ)*r^2) := by
    convert quadratic_nonneg (-2568058731259/36069608790 : ℝ) (614928685777/2404640586 : ℝ) (-250859666519/2003867155 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc1 : 0 ≤ ((-4672198583783/18034804395 : ℝ)*r^0 + (1082414578349/1202320293 : ℝ)*r^1 + (-882980442806/2003867155 : ℝ)*r^2) := by
    convert quadratic_nonneg (-4672198583783/18034804395 : ℝ) (1082414578349/1202320293 : ℝ) (-882980442806/2003867155 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc2 : 0 ≤ ((-863229624319/4007734310 : ℝ)*r^0 + (588945668871/801546862 : ℝ)*r^1 + (-720574181811/2003867155 : ℝ)*r^2) := by
    convert quadratic_nonneg (-863229624319/4007734310 : ℝ) (588945668871/801546862 : ℝ) (-720574181811/2003867155 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have he : centralCoefficient2 r d = ((-2568058731259/36069608790 : ℝ)*r^0 + (614928685777/2404640586 : ℝ)*r^1 + (-250859666519/2003867155 : ℝ)*r^2)*(d-(7/20 : ℝ))^0*((9/20 : ℝ)-d)^2 + ((-4672198583783/18034804395 : ℝ)*r^0 + (1082414578349/1202320293 : ℝ)*r^1 + (-882980442806/2003867155 : ℝ)*r^2)*(d-(7/20 : ℝ))^1*((9/20 : ℝ)-d)^1 + ((-863229624319/4007734310 : ℝ)*r^0 + (588945668871/801546862 : ℝ)*r^1 + (-720574181811/2003867155 : ℝ)*r^2)*(d-(7/20 : ℝ))^2*((9/20 : ℝ)-d)^0 := by
    unfold centralCoefficient2
    ring
  rw [he]
  positivity

private theorem central3_nonneg (r d : ℝ)
    (hr : rootLower ≤ r) (hru : r ≤ rootUpper)
    (hd : (7/20 : ℝ) ≤ d) (hdu : d ≤ (9/20 : ℝ)) : 0 ≤ centralCoefficient3 r d := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hc0 : 0 ≤ ((20041/201 : ℝ)*r^0 + (-20335/67 : ℝ)*r^1 + (9702/67 : ℝ)*r^2) := by
    convert quadratic_nonneg (20041/201 : ℝ) (-20335/67 : ℝ) (9702/67 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc1 : 0 ≤ ((17178/67 : ℝ)*r^0 + (-52290/67 : ℝ)*r^1 + (24948/67 : ℝ)*r^2) := by
    convert quadratic_nonneg (17178/67 : ℝ) (-52290/67 : ℝ) (24948/67 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc2 : 0 ≤ ((11043/67 : ℝ)*r^0 + (-33615/67 : ℝ)*r^1 + (16038/67 : ℝ)*r^2) := by
    convert quadratic_nonneg (11043/67 : ℝ) (-33615/67 : ℝ) (16038/67 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have he : centralCoefficient3 r d = ((20041/201 : ℝ)*r^0 + (-20335/67 : ℝ)*r^1 + (9702/67 : ℝ)*r^2)*(d-(7/20 : ℝ))^0*((9/20 : ℝ)-d)^2 + ((17178/67 : ℝ)*r^0 + (-52290/67 : ℝ)*r^1 + (24948/67 : ℝ)*r^2)*(d-(7/20 : ℝ))^1*((9/20 : ℝ)-d)^1 + ((11043/67 : ℝ)*r^0 + (-33615/67 : ℝ)*r^1 + (16038/67 : ℝ)*r^2)*(d-(7/20 : ℝ))^2*((9/20 : ℝ)-d)^0 := by
    unfold centralCoefficient3
    ring
  rw [he]
  positivity

private theorem outer0_nonneg (r d y : ℝ)
    (hr : rootLower ≤ r) (hru : r ≤ rootUpper)
    (hd : 0 ≤ d) (hdu : d ≤ (7/40 : ℝ))
    (hy : 0 ≤ y) (hyu : y ≤ (1/2 : ℝ)) : 0 ≤ optimalPolynomial r d y := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hy0 := sub_nonneg.mpr hy
  have hy1 := sub_nonneg.mpr hyu
  have hc0 : 0 ≤ ((2571365456000/530223249213 : ℝ)*r^0 + (-5704018120000/176741083071 : ℝ)*r^1 + (10292849072000/58913694357 : ℝ)*r^2) := by
    convert quadratic_nonneg (2571365456000/530223249213 : ℝ) (-5704018120000/176741083071 : ℝ) (10292849072000/58913694357 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc1 : 0 ≤ ((-140919659648000/530223249213 : ℝ)*r^0 + (139295798080000/176741083071 : ℝ)*r^1 + (9431999104000/58913694357 : ℝ)*r^2) := by
    convert quadratic_nonneg (-140919659648000/530223249213 : ℝ) (139295798080000/176741083071 : ℝ) (9431999104000/58913694357 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc2 : 0 ≤ ((-289553415664000/530223249213 : ℝ)*r^0 + (295703650520000/176741083071 : ℝ)*r^1 + (-1716364144000/8416242051 : ℝ)*r^2) := by
    convert quadratic_nonneg (-289553415664000/530223249213 : ℝ) (295703650520000/176741083071 : ℝ) (-1716364144000/8416242051 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc3 : 0 ≤ ((-726678560000/2637926613 : ℝ)*r^0 + (249923440000/293102957 : ℝ)*r^1 + (-55491040000/293102957 : ℝ)*r^2) := by
    convert quadratic_nonneg (-726678560000/2637926613 : ℝ) (249923440000/293102957 : ℝ) (-55491040000/293102957 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc4 : 0 ≤ ((11941930056640/530223249213 : ℝ)*r^0 + (-25625970370400/176741083071 : ℝ)*r^1 + (21210945954880/58913694357 : ℝ)*r^2) := by
    convert quadratic_nonneg (11941930056640/530223249213 : ℝ) (-25625970370400/176741083071 : ℝ) (21210945954880/58913694357 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc5 : 0 ≤ ((-468488481491440/530223249213 : ℝ)*r^0 + (447555422651600/176741083071 : ℝ)*r^1 + (-13631640832480/58913694357 : ℝ)*r^2) := by
    convert quadratic_nonneg (-468488481491440/530223249213 : ℝ) (447555422651600/176741083071 : ℝ) (-13631640832480/58913694357 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc6 : 0 ≤ ((-926757017928080/530223249213 : ℝ)*r^0 + (922967703379600/176741083071 : ℝ)*r^1 + (-11843178834080/8416242051 : ℝ)*r^2) := by
    convert quadratic_nonneg (-926757017928080/530223249213 : ℝ) (922967703379600/176741083071 : ℝ) (-11843178834080/8416242051 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc7 : 0 ≤ ((-2220530380000/2637926613 : ℝ)*r^0 + (745914279200/293102957 : ℝ)*r^1 + (-239102811200/293102957 : ℝ)*r^2) := by
    convert quadratic_nonneg (-2220530380000/2637926613 : ℝ) (745914279200/293102957 : ℝ) (-239102811200/293102957 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc8 : 0 ≤ ((68191046212552/2651116246065 : ℝ)*r^0 + (-22340551096084/176741083071 : ℝ)*r^1 + (56657083101784/294568471785 : ℝ)*r^2) := by
    convert quadratic_nonneg (68191046212552/2651116246065 : ℝ) (-22340551096084/176741083071 : ℝ) (56657083101784/294568471785 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc9 : 0 ≤ ((-19366760149696/36316660905 : ℝ)*r^0 + (3698422400704/2421110727 : ℝ)*r^1 + (-1156172730592/4035184545 : ℝ)*r^2) := by
    convert quadratic_nonneg (-19366760149696/36316660905 : ℝ) (3698422400704/2421110727 : ℝ) (-1156172730592/4035184545 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc10 : 0 ≤ ((-589564497441316/530223249213 : ℝ)*r^0 + (589859941502960/176741083071 : ℝ)*r^1 + (-9280240878304/8416242051 : ℝ)*r^2) := by
    convert quadratic_nonneg (-589564497441316/530223249213 : ℝ) (589859941502960/176741083071 : ℝ) (-9280240878304/8416242051 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc11 : 0 ≤ ((-1437094239176/2637926613 : ℝ)*r^0 + (486161852368/293102957 : ℝ)*r^1 + (-179371816096/293102957 : ℝ)*r^2) := by
    convert quadratic_nonneg (-1437094239176/2637926613 : ℝ) (486161852368/293102957 : ℝ) (-179371816096/293102957 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have he : optimalPolynomial r d y = ((2571365456000/530223249213 : ℝ)*r^0 + (-5704018120000/176741083071 : ℝ)*r^1 + (10292849072000/58913694357 : ℝ)*r^2)*(d-0)^0*((7/40 : ℝ)-d)^2*(y-0)^0*((1/2 : ℝ)-y)^3 + ((-140919659648000/530223249213 : ℝ)*r^0 + (139295798080000/176741083071 : ℝ)*r^1 + (9431999104000/58913694357 : ℝ)*r^2)*(d-0)^0*((7/40 : ℝ)-d)^2*(y-0)^1*((1/2 : ℝ)-y)^2 + ((-289553415664000/530223249213 : ℝ)*r^0 + (295703650520000/176741083071 : ℝ)*r^1 + (-1716364144000/8416242051 : ℝ)*r^2)*(d-0)^0*((7/40 : ℝ)-d)^2*(y-0)^2*((1/2 : ℝ)-y)^1 + ((-726678560000/2637926613 : ℝ)*r^0 + (249923440000/293102957 : ℝ)*r^1 + (-55491040000/293102957 : ℝ)*r^2)*(d-0)^0*((7/40 : ℝ)-d)^2*(y-0)^3*((1/2 : ℝ)-y)^0 + ((11941930056640/530223249213 : ℝ)*r^0 + (-25625970370400/176741083071 : ℝ)*r^1 + (21210945954880/58913694357 : ℝ)*r^2)*(d-0)^1*((7/40 : ℝ)-d)^1*(y-0)^0*((1/2 : ℝ)-y)^3 + ((-468488481491440/530223249213 : ℝ)*r^0 + (447555422651600/176741083071 : ℝ)*r^1 + (-13631640832480/58913694357 : ℝ)*r^2)*(d-0)^1*((7/40 : ℝ)-d)^1*(y-0)^1*((1/2 : ℝ)-y)^2 + ((-926757017928080/530223249213 : ℝ)*r^0 + (922967703379600/176741083071 : ℝ)*r^1 + (-11843178834080/8416242051 : ℝ)*r^2)*(d-0)^1*((7/40 : ℝ)-d)^1*(y-0)^2*((1/2 : ℝ)-y)^1 + ((-2220530380000/2637926613 : ℝ)*r^0 + (745914279200/293102957 : ℝ)*r^1 + (-239102811200/293102957 : ℝ)*r^2)*(d-0)^1*((7/40 : ℝ)-d)^1*(y-0)^3*((1/2 : ℝ)-y)^0 + ((68191046212552/2651116246065 : ℝ)*r^0 + (-22340551096084/176741083071 : ℝ)*r^1 + (56657083101784/294568471785 : ℝ)*r^2)*(d-0)^2*((7/40 : ℝ)-d)^0*(y-0)^0*((1/2 : ℝ)-y)^3 + ((-19366760149696/36316660905 : ℝ)*r^0 + (3698422400704/2421110727 : ℝ)*r^1 + (-1156172730592/4035184545 : ℝ)*r^2)*(d-0)^2*((7/40 : ℝ)-d)^0*(y-0)^1*((1/2 : ℝ)-y)^2 + ((-589564497441316/530223249213 : ℝ)*r^0 + (589859941502960/176741083071 : ℝ)*r^1 + (-9280240878304/8416242051 : ℝ)*r^2)*(d-0)^2*((7/40 : ℝ)-d)^0*(y-0)^2*((1/2 : ℝ)-y)^1 + ((-1437094239176/2637926613 : ℝ)*r^0 + (486161852368/293102957 : ℝ)*r^1 + (-179371816096/293102957 : ℝ)*r^2)*(d-0)^2*((7/40 : ℝ)-d)^0*(y-0)^3*((1/2 : ℝ)-y)^0 := by
    unfold optimalPolynomial
    ring
  rw [he]
  positivity

private theorem outer1_nonneg (r d y : ℝ)
    (hr : rootLower ≤ r) (hru : r ≤ rootUpper)
    (hd : (7/40 : ℝ) ≤ d) (hdu : d ≤ (7/20 : ℝ))
    (hy : 0 ≤ y) (hyu : y ≤ (1/2 : ℝ)) : 0 ≤ optimalPolynomial r d y := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hy0 := sub_nonneg.mpr hy
  have hy1 := sub_nonneg.mpr hyu
  have hc0 : 0 ≤ ((68191046212552/2651116246065 : ℝ)*r^0 + (-22340551096084/176741083071 : ℝ)*r^1 + (56657083101784/294568471785 : ℝ)*r^2) := by
    convert quadratic_nonneg (68191046212552/2651116246065 : ℝ) (-22340551096084/176741083071 : ℝ) (56657083101784/294568471785 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc1 : 0 ≤ ((-19366760149696/36316660905 : ℝ)*r^0 + (3698422400704/2421110727 : ℝ)*r^1 + (-1156172730592/4035184545 : ℝ)*r^2) := by
    convert quadratic_nonneg (-19366760149696/36316660905 : ℝ) (3698422400704/2421110727 : ℝ) (-1156172730592/4035184545 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc2 : 0 ≤ ((-589564497441316/530223249213 : ℝ)*r^0 + (589859941502960/176741083071 : ℝ)*r^1 + (-9280240878304/8416242051 : ℝ)*r^2) := by
    convert quadratic_nonneg (-589564497441316/530223249213 : ℝ) (589859941502960/176741083071 : ℝ) (-9280240878304/8416242051 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc3 : 0 ≤ ((-1437094239176/2637926613 : ℝ)*r^0 + (486161852368/293102957 : ℝ)*r^1 + (-179371816096/293102957 : ℝ)*r^2) := by
    convert quadratic_nonneg (-1437094239176/2637926613 : ℝ) (486161852368/293102957 : ℝ) (-179371816096/293102957 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc4 : 0 ≤ ((213054534567008/2651116246065 : ℝ)*r^0 + (-63736234013936/176741083071 : ℝ)*r^1 + (120573602632736/294568471785 : ℝ)*r^2) := by
    convert quadratic_nonneg (213054534567008/2651116246065 : ℝ) (-63736234013936/176741083071 : ℝ) (120573602632736/294568471785 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc5 : 0 ≤ ((-3312651556254032/2651116246065 : ℝ)*r^0 + (632383918353968/176741083071 : ℝ)*r^1 + (-269444233170464/294568471785 : ℝ)*r^2) := by
    convert quadratic_nonneg (-3312651556254032/2651116246065 : ℝ) (632383918353968/176741083071 : ℝ) (-269444233170464/294568471785 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc6 : 0 ≤ ((-1431500971837184/530223249213 : ℝ)*r^0 + (1436472062632240/176741083071 : ℝ)*r^1 + (-25277784679136/8416242051 : ℝ)*r^2) := by
    convert quadratic_nonneg (-1431500971837184/530223249213 : ℝ) (1436472062632240/176741083071 : ℝ) (-25277784679136/8416242051 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc7 : 0 ≤ ((-3527846576704/2637926613 : ℝ)*r^0 + (1198733130272/293102957 : ℝ)*r^1 + (-478384453184/293102957 : ℝ)*r^2) := by
    convert quadratic_nonneg (-3527846576704/2637926613 : ℝ) (1198733130272/293102957 : ℝ) (-478384453184/293102957 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc8 : 0 ≤ ((166201711563808/2651116246065 : ℝ)*r^0 + (-43814281763536/176741083071 : ℝ)*r^1 + (65983118218336/294568471785 : ℝ)*r^2) := by
    convert quadratic_nonneg (166201711563808/2651116246065 : ℝ) (-43814281763536/176741083071 : ℝ) (65983118218336/294568471785 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc9 : 0 ≤ ((-1674807447036832/2651116246065 : ℝ)*r^0 + (324124293782368/176741083071 : ℝ)*r^1 + (-154126033488064/294568471785 : ℝ)*r^2) := by
    convert quadratic_nonneg (-1674807447036832/2651116246065 : ℝ) (324124293782368/176741083071 : ℝ) (-154126033488064/294568471785 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc10 : 0 ≤ ((-794297369573104/530223249213 : ℝ)*r^0 + (809208009772640/176741083071 : ℝ)*r^1 + (-15150969989056/8416242051 : ℝ)*r^2) := by
    convert quadratic_nonneg (-794297369573104/530223249213 : ℝ) (809208009772640/176741083071 : ℝ) (-15150969989056/8416242051 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc11 : 0 ≤ ((-2033994756704/2637926613 : ℝ)*r^0 + (702742291072/293102957 : ℝ)*r^1 + (-294772681984/293102957 : ℝ)*r^2) := by
    convert quadratic_nonneg (-2033994756704/2637926613 : ℝ) (702742291072/293102957 : ℝ) (-294772681984/293102957 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have he : optimalPolynomial r d y = ((68191046212552/2651116246065 : ℝ)*r^0 + (-22340551096084/176741083071 : ℝ)*r^1 + (56657083101784/294568471785 : ℝ)*r^2)*(d-(7/40 : ℝ))^0*((7/20 : ℝ)-d)^2*(y-0)^0*((1/2 : ℝ)-y)^3 + ((-19366760149696/36316660905 : ℝ)*r^0 + (3698422400704/2421110727 : ℝ)*r^1 + (-1156172730592/4035184545 : ℝ)*r^2)*(d-(7/40 : ℝ))^0*((7/20 : ℝ)-d)^2*(y-0)^1*((1/2 : ℝ)-y)^2 + ((-589564497441316/530223249213 : ℝ)*r^0 + (589859941502960/176741083071 : ℝ)*r^1 + (-9280240878304/8416242051 : ℝ)*r^2)*(d-(7/40 : ℝ))^0*((7/20 : ℝ)-d)^2*(y-0)^2*((1/2 : ℝ)-y)^1 + ((-1437094239176/2637926613 : ℝ)*r^0 + (486161852368/293102957 : ℝ)*r^1 + (-179371816096/293102957 : ℝ)*r^2)*(d-(7/40 : ℝ))^0*((7/20 : ℝ)-d)^2*(y-0)^3*((1/2 : ℝ)-y)^0 + ((213054534567008/2651116246065 : ℝ)*r^0 + (-63736234013936/176741083071 : ℝ)*r^1 + (120573602632736/294568471785 : ℝ)*r^2)*(d-(7/40 : ℝ))^1*((7/20 : ℝ)-d)^1*(y-0)^0*((1/2 : ℝ)-y)^3 + ((-3312651556254032/2651116246065 : ℝ)*r^0 + (632383918353968/176741083071 : ℝ)*r^1 + (-269444233170464/294568471785 : ℝ)*r^2)*(d-(7/40 : ℝ))^1*((7/20 : ℝ)-d)^1*(y-0)^1*((1/2 : ℝ)-y)^2 + ((-1431500971837184/530223249213 : ℝ)*r^0 + (1436472062632240/176741083071 : ℝ)*r^1 + (-25277784679136/8416242051 : ℝ)*r^2)*(d-(7/40 : ℝ))^1*((7/20 : ℝ)-d)^1*(y-0)^2*((1/2 : ℝ)-y)^1 + ((-3527846576704/2637926613 : ℝ)*r^0 + (1198733130272/293102957 : ℝ)*r^1 + (-478384453184/293102957 : ℝ)*r^2)*(d-(7/40 : ℝ))^1*((7/20 : ℝ)-d)^1*(y-0)^3*((1/2 : ℝ)-y)^0 + ((166201711563808/2651116246065 : ℝ)*r^0 + (-43814281763536/176741083071 : ℝ)*r^1 + (65983118218336/294568471785 : ℝ)*r^2)*(d-(7/40 : ℝ))^2*((7/20 : ℝ)-d)^0*(y-0)^0*((1/2 : ℝ)-y)^3 + ((-1674807447036832/2651116246065 : ℝ)*r^0 + (324124293782368/176741083071 : ℝ)*r^1 + (-154126033488064/294568471785 : ℝ)*r^2)*(d-(7/40 : ℝ))^2*((7/20 : ℝ)-d)^0*(y-0)^1*((1/2 : ℝ)-y)^2 + ((-794297369573104/530223249213 : ℝ)*r^0 + (809208009772640/176741083071 : ℝ)*r^1 + (-15150969989056/8416242051 : ℝ)*r^2)*(d-(7/40 : ℝ))^2*((7/20 : ℝ)-d)^0*(y-0)^2*((1/2 : ℝ)-y)^1 + ((-2033994756704/2637926613 : ℝ)*r^0 + (702742291072/293102957 : ℝ)*r^1 + (-294772681984/293102957 : ℝ)*r^2)*(d-(7/40 : ℝ))^2*((7/20 : ℝ)-d)^0*(y-0)^3*((1/2 : ℝ)-y)^0 := by
    unfold optimalPolynomial
    ring
  rw [he]
  positivity

private theorem outer2_nonneg (r d y : ℝ)
    (hr : rootLower ≤ r) (hru : r ≤ rootUpper)
    (hd : (9/20 : ℝ) ≤ d) (hdu : d ≤ (5/6 : ℝ))
    (hy : 0 ≤ y) (hyu : y ≤ (1/2 : ℝ)) : 0 ≤ optimalPolynomial r d y := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hy0 := sub_nonneg.mpr hy
  have hy1 := sub_nonneg.mpr hyu
  have hc0 : 0 ≤ ((60342164886088/3180137174985 : ℝ)*r^0 + (-14564197011796/212009144999 : ℝ)*r^1 + (54876001809288/1060045724995 : ℝ)*r^2) := by
    convert quadratic_nonneg (60342164886088/3180137174985 : ℝ) (-14564197011796/212009144999 : ℝ) (54876001809288/1060045724995 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc1 : 0 ≤ ((-405690859546552/3180137174985 : ℝ)*r^0 + (80172982163848/212009144999 : ℝ)*r^1 + (-124654799110512/1060045724995 : ℝ)*r^2) := by
    convert quadratic_nonneg (-405690859546552/3180137174985 : ℝ) (80172982163848/212009144999 : ℝ) (-124654799110512/1060045724995 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc2 : 0 ≤ ((-217127402635564/636027434997 : ℝ)*r^0 + (225240599442440/212009144999 : ℝ)*r^1 + (-4050599519472/9217788913 : ℝ)*r^2) := by
    convert quadratic_nonneg (-217127402635564/636027434997 : ℝ) (225240599442440/212009144999 : ℝ) (-4050599519472/9217788913 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc3 : 0 ≤ ((-25262117128/137578939 : ℝ)*r^0 + (1839772153728/3164315597 : ℝ)*r^1 + (-34914984192/137578939 : ℝ)*r^2) := by
    convert quadratic_nonneg (-25262117128/137578939 : ℝ) (1839772153728/3164315597 : ℝ) (-34914984192/137578939 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc4 : 0 ≤ ((13293105914240/212009144999 : ℝ)*r^0 + (-43725969667200/212009144999 : ℝ)*r^1 + (26469723582720/212009144999 : ℝ)*r^2) := by
    convert quadratic_nonneg (13293105914240/212009144999 : ℝ) (-43725969667200/212009144999 : ℝ) (26469723582720/212009144999 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc5 : 0 ≤ ((-138277774855160/636027434997 : ℝ)*r^0 + (145079469457000/212009144999 : ℝ)*r^1 + (-51003194375760/212009144999 : ℝ)*r^2) := by
    convert quadratic_nonneg (-138277774855160/636027434997 : ℝ) (145079469457000/212009144999 : ℝ) (-51003194375760/212009144999 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc6 : 0 ≤ ((-490467394554680/636027434997 : ℝ)*r^0 + (526707799474600/212009144999 : ℝ)*r^1 + (-10129520224560/9217788913 : ℝ)*r^2) := by
    convert quadratic_nonneg (-490467394554680/636027434997 : ℝ) (526707799474600/212009144999 : ℝ) (-10129520224560/9217788913 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc7 : 0 ≤ ((-61840356400/137578939 : ℝ)*r^0 + (4643170333200/3164315597 : ℝ)*r^1 + (-92611807200/137578939 : ℝ)*r^2) := by
    convert quadratic_nonneg (-61840356400/137578939 : ℝ) (4643170333200/3164315597 : ℝ) (-92611807200/137578939 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc8 : 0 ≤ ((10976707632000/212009144999 : ℝ)*r^0 + (-32062994400000/212009144999 : ℝ)*r^1 + (16981911936000/212009144999 : ℝ)*r^2) := by
    convert quadratic_nonneg (10976707632000/212009144999 : ℝ) (-32062994400000/212009144999 : ℝ) (16981911936000/212009144999 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc9 : 0 ≤ ((-1127659474000/212009144999 : ℝ)*r^0 + (18994098290000/212009144999 : ℝ)*r^1 + (-3819982452000/212009144999 : ℝ)*r^2) := by
    convert quadratic_nonneg (-1127659474000/212009144999 : ℝ) (18994098290000/212009144999 : ℝ) (-3819982452000/212009144999 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc10 : 0 ≤ ((-216194671168000/636027434997 : ℝ)*r^0 + (256599229720000/212009144999 : ℝ)*r^1 + (-5151720816000/9217788913 : ℝ)*r^2) := by
    convert quadratic_nonneg (-216194671168000/636027434997 : ℝ) (256599229720000/212009144999 : ℝ) (-5151720816000/9217788913 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have hc11 : 0 ≤ ((-100854280000/412736817 : ℝ)*r^0 + (2697285240000/3164315597 : ℝ)*r^1 + (-55706640000/137578939 : ℝ)*r^2) := by
    convert quadratic_nonneg (-100854280000/412736817 : ℝ) (2697285240000/3164315597 : ℝ) (-55706640000/137578939 : ℝ) r hr hru
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper])
      (by norm_num [rootLower, rootUpper]) using 1 <;> ring
  have he : optimalPolynomial r d y = ((60342164886088/3180137174985 : ℝ)*r^0 + (-14564197011796/212009144999 : ℝ)*r^1 + (54876001809288/1060045724995 : ℝ)*r^2)*(d-(9/20 : ℝ))^0*((5/6 : ℝ)-d)^2*(y-0)^0*((1/2 : ℝ)-y)^3 + ((-405690859546552/3180137174985 : ℝ)*r^0 + (80172982163848/212009144999 : ℝ)*r^1 + (-124654799110512/1060045724995 : ℝ)*r^2)*(d-(9/20 : ℝ))^0*((5/6 : ℝ)-d)^2*(y-0)^1*((1/2 : ℝ)-y)^2 + ((-217127402635564/636027434997 : ℝ)*r^0 + (225240599442440/212009144999 : ℝ)*r^1 + (-4050599519472/9217788913 : ℝ)*r^2)*(d-(9/20 : ℝ))^0*((5/6 : ℝ)-d)^2*(y-0)^2*((1/2 : ℝ)-y)^1 + ((-25262117128/137578939 : ℝ)*r^0 + (1839772153728/3164315597 : ℝ)*r^1 + (-34914984192/137578939 : ℝ)*r^2)*(d-(9/20 : ℝ))^0*((5/6 : ℝ)-d)^2*(y-0)^3*((1/2 : ℝ)-y)^0 + ((13293105914240/212009144999 : ℝ)*r^0 + (-43725969667200/212009144999 : ℝ)*r^1 + (26469723582720/212009144999 : ℝ)*r^2)*(d-(9/20 : ℝ))^1*((5/6 : ℝ)-d)^1*(y-0)^0*((1/2 : ℝ)-y)^3 + ((-138277774855160/636027434997 : ℝ)*r^0 + (145079469457000/212009144999 : ℝ)*r^1 + (-51003194375760/212009144999 : ℝ)*r^2)*(d-(9/20 : ℝ))^1*((5/6 : ℝ)-d)^1*(y-0)^1*((1/2 : ℝ)-y)^2 + ((-490467394554680/636027434997 : ℝ)*r^0 + (526707799474600/212009144999 : ℝ)*r^1 + (-10129520224560/9217788913 : ℝ)*r^2)*(d-(9/20 : ℝ))^1*((5/6 : ℝ)-d)^1*(y-0)^2*((1/2 : ℝ)-y)^1 + ((-61840356400/137578939 : ℝ)*r^0 + (4643170333200/3164315597 : ℝ)*r^1 + (-92611807200/137578939 : ℝ)*r^2)*(d-(9/20 : ℝ))^1*((5/6 : ℝ)-d)^1*(y-0)^3*((1/2 : ℝ)-y)^0 + ((10976707632000/212009144999 : ℝ)*r^0 + (-32062994400000/212009144999 : ℝ)*r^1 + (16981911936000/212009144999 : ℝ)*r^2)*(d-(9/20 : ℝ))^2*((5/6 : ℝ)-d)^0*(y-0)^0*((1/2 : ℝ)-y)^3 + ((-1127659474000/212009144999 : ℝ)*r^0 + (18994098290000/212009144999 : ℝ)*r^1 + (-3819982452000/212009144999 : ℝ)*r^2)*(d-(9/20 : ℝ))^2*((5/6 : ℝ)-d)^0*(y-0)^1*((1/2 : ℝ)-y)^2 + ((-216194671168000/636027434997 : ℝ)*r^0 + (256599229720000/212009144999 : ℝ)*r^1 + (-5151720816000/9217788913 : ℝ)*r^2)*(d-(9/20 : ℝ))^2*((5/6 : ℝ)-d)^0*(y-0)^2*((1/2 : ℝ)-y)^1 + ((-100854280000/412736817 : ℝ)*r^0 + (2697285240000/3164315597 : ℝ)*r^1 + (-55706640000/137578939 : ℝ)*r^2)*(d-(9/20 : ℝ))^2*((5/6 : ℝ)-d)^0*(y-0)^3*((1/2 : ℝ)-y)^0 := by
    unfold optimalPolynomial
    ring
  rw [he]
  positivity

theorem limiting_polynomial_nonneg (r d y : ℝ)
    (hr : rootLower ≤ r) (hru : r ≤ rootUpper) (hp : deltaPolynomial r = 0)
    (hd : 0 ≤ d) (hdu : d ≤ 5/6) (hy : 0 ≤ y) (hyu : y ≤ 1/2) :
    0 ≤ optimalPolynomial r d y := by
  by_cases hlow : d ≤ 7/20
  · by_cases hsmall : d ≤ 7/40
    · exact outer0_nonneg r d y hr hru hd hsmall hy hyu
    · exact outer1_nonneg r d y hr hru (by linarith) hlow hy hyu
  · by_cases hmid : d ≤ 9/20
    · have hK := squareK_nonneg r hr hru
      have h1 := central1_nonneg r d hr hru (by linarith) hmid
      have h2 := central2_nonneg r d hr hru (by linarith) hmid
      have h3 := central3_nonneg r d hr hru (by linarith) hmid
      rw [central_square_identity r d y hp]
      positivity
    · exact outer2_nonneg r d y hr hru (by linarith) hdu hy hyu

#print axioms limiting_polynomial_nonneg
end
end BelowSevenEighthsTight
