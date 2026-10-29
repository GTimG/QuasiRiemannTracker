/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01921_01952
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99705391946442,99705214697540,99705037425241,99704860129548,99704682810462,99704505467985,99704328102118,99704150712864,99703973300224,99703795864201,99703618404797,99703440922013,99703263415851,99703085886313,99702908333401,99702730757117,99702553157463,99702375534440,99702197888050,99702020218296,99701842525179,99701664808701,99701487068864,99701309305670,99701131519121,99700953709219,99700775875965,99700598019362,99700420139411,99700242236114,99700064309473,99699886359491,99699708386168]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1920+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(62027899179377672660704/86480120433634879479885:Fraction),(1378275527564090599042/1921741565191925099553:Fraction),(459384430649565128774/640567558767691699851:Fraction),(8858771053044275420506/12353552919091447068555:Fraction),(34200715758613130936/47696150266763309145:Fraction),(74326301193300130/103662189655096569:Fraction),(2296107416142438700384/3202578534579458499255:Fraction),(61989402502344594622642/86467870433647129479885:Fraction),(4132260307018868287978/5764408028909925298659:Fraction),(20659468848223911061169/28821456811216876493295:Fraction),(1377175767771556481408/1921391565192275099553:Fraction),(983609720496257044903/1372394768788160785395:Fraction),(1674646386447055473331/2336732984693402148105:Fraction),(20652140423867156270252/28819123477885876493295:Fraction),(2950044099106734296387/4116934306364732356185:Fraction),(61945430727470437571314/86453870433661129479885:Fraction),(61939936439580461929964/86452120433662879479885:Fraction),(1376320933073890958468/1921119342970325099553:Fraction),(12385789720604761749580/17289724086733275895977:Fraction),(3642556251984029392762/5085110025509889969405:Fraction),(20639320857271320512008/28815040144556626493295:Fraction),(12382494231060435890551/17288674086734325895977:Fraction),(61906979575555233988756/86441620433673379479885:Fraction),(4126765855505509575104/5762658028911675298659:Fraction),(20631999051928827567961/28812706811225626493295:Fraction),(5626409665073749390597/7857851857607148134535:Fraction),(1375222589824121577838/1920769342970675099553:Fraction),(12375905321045435712940/17286574086736425895977:Fraction),(1672271290126822653061/2335976227937402148105:Fraction),(20622849567023556973412/28809790144561876493295:Fraction),(61863059504371385306903/86427620433687379479885:Fraction),(12371514520716592438003/17285174086737825895977:Fraction)]
abbrev p1921 := params 0
abbrev ray1921 := rays 0
def bank1921 : Fin 1 → Cell := oneBank p1921 ray1921
theorem signs1921 : ∀ j, Signs p1921 (bank1921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1922 := params 1
abbrev ray1922 := rays 1
def bank1922 : Fin 1 → Cell := oneBank p1922 ray1922
theorem signs1922 : ∀ j, Signs p1922 (bank1922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1923 := params 2
abbrev ray1923 := rays 2
def bank1923 : Fin 1 → Cell := oneBank p1923 ray1923
theorem signs1923 : ∀ j, Signs p1923 (bank1923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1924 := params 3
abbrev ray1924 := rays 3
def bank1924 : Fin 1 → Cell := oneBank p1924 ray1924
theorem signs1924 : ∀ j, Signs p1924 (bank1924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1925 := params 4
abbrev ray1925 := rays 4
def bank1925 : Fin 1 → Cell := oneBank p1925 ray1925
theorem signs1925 : ∀ j, Signs p1925 (bank1925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1926 := params 5
abbrev ray1926 := rays 5
def bank1926 : Fin 1 → Cell := oneBank p1926 ray1926
theorem signs1926 : ∀ j, Signs p1926 (bank1926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1927 := params 6
abbrev ray1927 := rays 6
def bank1927 : Fin 1 → Cell := oneBank p1927 ray1927
theorem signs1927 : ∀ j, Signs p1927 (bank1927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1928 := params 7
abbrev ray1928 := rays 7
def bank1928 : Fin 1 → Cell := oneBank p1928 ray1928
theorem signs1928 : ∀ j, Signs p1928 (bank1928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1929 := params 8
abbrev ray1929 := rays 8
def bank1929 : Fin 1 → Cell := oneBank p1929 ray1929
theorem signs1929 : ∀ j, Signs p1929 (bank1929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1930 := params 9
abbrev ray1930 := rays 9
def bank1930 : Fin 1 → Cell := oneBank p1930 ray1930
theorem signs1930 : ∀ j, Signs p1930 (bank1930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1931 := params 10
abbrev ray1931 := rays 10
def bank1931 : Fin 1 → Cell := oneBank p1931 ray1931
theorem signs1931 : ∀ j, Signs p1931 (bank1931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1932 := params 11
abbrev ray1932 := rays 11
def bank1932 : Fin 1 → Cell := oneBank p1932 ray1932
theorem signs1932 : ∀ j, Signs p1932 (bank1932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1933 := params 12
abbrev ray1933 := rays 12
def bank1933 : Fin 1 → Cell := oneBank p1933 ray1933
theorem signs1933 : ∀ j, Signs p1933 (bank1933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1934 := params 13
abbrev ray1934 := rays 13
def bank1934 : Fin 1 → Cell := oneBank p1934 ray1934
theorem signs1934 : ∀ j, Signs p1934 (bank1934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1935 := params 14
abbrev ray1935 := rays 14
def bank1935 : Fin 1 → Cell := oneBank p1935 ray1935
theorem signs1935 : ∀ j, Signs p1935 (bank1935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1936 := params 15
abbrev ray1936 := rays 15
def bank1936 : Fin 1 → Cell := oneBank p1936 ray1936
theorem signs1936 : ∀ j, Signs p1936 (bank1936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1937 := params 16
abbrev ray1937 := rays 16
def bank1937 : Fin 1 → Cell := oneBank p1937 ray1937
theorem signs1937 : ∀ j, Signs p1937 (bank1937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1938 := params 17
abbrev ray1938 := rays 17
def bank1938 : Fin 1 → Cell := oneBank p1938 ray1938
theorem signs1938 : ∀ j, Signs p1938 (bank1938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1939 := params 18
abbrev ray1939 := rays 18
def bank1939 : Fin 1 → Cell := oneBank p1939 ray1939
theorem signs1939 : ∀ j, Signs p1939 (bank1939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1940 := params 19
abbrev ray1940 := rays 19
def bank1940 : Fin 1 → Cell := oneBank p1940 ray1940
theorem signs1940 : ∀ j, Signs p1940 (bank1940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1941 := params 20
abbrev ray1941 := rays 20
def bank1941 : Fin 1 → Cell := oneBank p1941 ray1941
theorem signs1941 : ∀ j, Signs p1941 (bank1941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1942 := params 21
abbrev ray1942 := rays 21
def bank1942 : Fin 1 → Cell := oneBank p1942 ray1942
theorem signs1942 : ∀ j, Signs p1942 (bank1942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1943 := params 22
abbrev ray1943 := rays 22
def bank1943 : Fin 1 → Cell := oneBank p1943 ray1943
theorem signs1943 : ∀ j, Signs p1943 (bank1943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1944 := params 23
abbrev ray1944 := rays 23
def bank1944 : Fin 1 → Cell := oneBank p1944 ray1944
theorem signs1944 : ∀ j, Signs p1944 (bank1944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1945 := params 24
abbrev ray1945 := rays 24
def bank1945 : Fin 1 → Cell := oneBank p1945 ray1945
theorem signs1945 : ∀ j, Signs p1945 (bank1945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1946 := params 25
abbrev ray1946 := rays 25
def bank1946 : Fin 1 → Cell := oneBank p1946 ray1946
theorem signs1946 : ∀ j, Signs p1946 (bank1946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1947 := params 26
abbrev ray1947 := rays 26
def bank1947 : Fin 1 → Cell := oneBank p1947 ray1947
theorem signs1947 : ∀ j, Signs p1947 (bank1947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1948 := params 27
abbrev ray1948 := rays 27
def bank1948 : Fin 1 → Cell := oneBank p1948 ray1948
theorem signs1948 : ∀ j, Signs p1948 (bank1948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1949 := params 28
abbrev ray1949 := rays 28
def bank1949 : Fin 1 → Cell := oneBank p1949 ray1949
theorem signs1949 : ∀ j, Signs p1949 (bank1949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1950 := params 29
abbrev ray1950 := rays 29
def bank1950 : Fin 1 → Cell := oneBank p1950 ray1950
theorem signs1950 : ∀ j, Signs p1950 (bank1950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1951 := params 30
abbrev ray1951 := rays 30
def bank1951 : Fin 1 → Cell := oneBank p1951 ray1951
theorem signs1951 : ∀ j, Signs p1951 (bank1951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1952 := params 31
abbrev ray1952 := rays 31
def bank1952 : Fin 1 → Cell := oneBank p1952 ray1952
theorem signs1952 : ∀ j, Signs p1952 (bank1952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01921_01952
