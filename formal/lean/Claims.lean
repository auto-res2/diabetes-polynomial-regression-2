import Mathlib
import References
/-!
レポート 2 の各文の claims を、命題として書いたもの。
値はすべて引数で受ける。値を入れるのは parse_claims.py が生成する Theorems.lean。
引用した claims は References.lean（parse_claims.py が引用先から生成する）に公理として置かれる。
検証器が無い claims は、対象を opaque な定数として置き、公理として宣言する（末尾）。
-/
namespace Claims

/-! ## R01 -/
/-- 文献 [1] の訓練データ（Ref1.trainDataSha256）と一致する。 -/
abbrev R01_c1 (trainDataSha256 : String) : Prop := trainDataSha256 = Ref1.trainDataSha256
/-- 文献 [1] のテストデータ（Ref1.testDataSha256）と一致する。 -/
abbrev R01_c2 (testDataSha256 : String) : Prop := testDataSha256 = Ref1.testDataSha256

theorem R01_c1_of_eq (trainDataSha256 : String) (h : trainDataSha256 = "7968ccfdb6b347591a4a86e80dc98088c8d74ccc118ef1c80694e02748c425e2") : R01_c1 trainDataSha256 :=
  h.trans Ref1.R06_c4_cited.symm
theorem R01_c1_not_of_ne (trainDataSha256 : String) (h : trainDataSha256 ≠ "7968ccfdb6b347591a4a86e80dc98088c8d74ccc118ef1c80694e02748c425e2") : ¬ R01_c1 trainDataSha256 :=
  fun e => h (e.trans Ref1.R06_c4_cited)
theorem R01_c2_of_eq (testDataSha256 : String) (h : testDataSha256 = "cb0d6b45a5531af0e7818c582c9f92b56ad466c787539acfbeef143da4349091") : R01_c2 testDataSha256 :=
  h.trans Ref1.R06_c5_cited.symm
theorem R01_c2_not_of_ne (testDataSha256 : String) (h : testDataSha256 ≠ "cb0d6b45a5531af0e7818c582c9f92b56ad466c787539acfbeef143da4349091") : ¬ R01_c2 testDataSha256 :=
  fun e => h (e.trans Ref1.R06_c5_cited)

/-! ## R02 -/
abbrev R02_c1 (outputKeys : List String) : Prop :=
  ["trainMse", "trainRmse", "trainMae", "trainR2", "testMse", "testRmse", "testMae", "testR2"] ⊆ outputKeys

/-! ## R03 -/
abbrev R03_c1 (polyDegree nPolyFeatures : ℕ) : Prop := polyDegree = 2 ∧ nPolyFeatures = 65
abbrev R03_c2 (fitSteps : List String) : Prop :=
  fitSteps = ["sklearn.preprocessing.PolynomialFeatures", "sklearn.linear_model.LinearRegression"]

/-! ## R04 -/
/-- 検証器なし。正則化の係数は 0 である。 -/
abbrev R04_c1 (penaltyWeight : ℚ) : Prop := penaltyWeight = 0

/-! ## R05 -/
abbrev R05_c1 (testMse : ℚ) : Prop := (round (testMse / 0.1) : ℚ) * 0.1 = 3637.1

/-! ## R06 -/
/-- 同じテストデータ（文献 [1] と一致）で、文献 [1] の線形回帰のテストの MSE（Ref1.testMse）より小さい。 -/
abbrev R06_c1 (testDataSha256 : String) (testMse : ℚ) : Prop := R01_c2 testDataSha256 ∧ testMse < Ref1.testMse

/-- 引用した [1, R20] の c1 から、Ref1.testMse は 3424.25 以上 3424.35 以下。 -/
theorem ref1_testMse_bounds : 3424.25 ≤ Ref1.testMse ∧ Ref1.testMse ≤ 3424.35 := by
  have h := Ref1.R20_c1_cited
  have hr : (round (Ref1.testMse / 0.1) : ℚ) = 34243 := by linarith
  have ha := abs_sub_round (Ref1.testMse / 0.1)
  rw [hr] at ha
  rw [abs_le] at ha
  norm_num at ha
  constructor <;> linarith [ha.1, ha.2]

theorem R06_c1_of (testDataSha256 : String) (testMse : ℚ)
    (h : testDataSha256 = "cb0d6b45a5531af0e7818c582c9f92b56ad466c787539acfbeef143da4349091" ∧ testMse < 3424.25) : R06_c1 testDataSha256 testMse :=
  ⟨R01_c2_of_eq testDataSha256 h.1, lt_of_lt_of_le h.2 ref1_testMse_bounds.1⟩

theorem R06_c1_not_of (testDataSha256 : String) (testMse : ℚ)
    (h : testDataSha256 ≠ "cb0d6b45a5531af0e7818c582c9f92b56ad466c787539acfbeef143da4349091" ∨ 3424.35 ≤ testMse) : ¬ R06_c1 testDataSha256 testMse := by
  rintro ⟨e, lt⟩
  rcases h with h | h
  · exact R01_c2_not_of_ne testDataSha256 h e
  · exact absurd lt (not_lt.mpr (le_trans ref1_testMse_bounds.2 h))

/-! ## R07 -/
abbrev R07_c1 (trainMse trainRmse trainMae trainR2 testMse testRmse testMae testR2 : ℚ) : Prop :=
  (round (trainMse / 0.1) : ℚ) * 0.1 = 2256.1 ∧ (round (trainRmse / 0.1) : ℚ) * 0.1 = 47.5 ∧
  (round (trainMae / 0.1) : ℚ) * 0.1 = 38.0 ∧ (round (trainR2 / 0.001) : ℚ) * 0.001 = 0.632 ∧
  (round (testMse / 0.1) : ℚ) * 0.1 = 3637.1 ∧ (round (testRmse / 0.1) : ℚ) * 0.1 = 60.3 ∧
  (round (testMae / 0.1) : ℚ) * 0.1 = 46.4 ∧ (round (testR2 / 0.001) : ℚ) * 0.001 = 0.291

/-! ## 検証器が無い claims の公理 -/
namespace Unobserved
opaque penaltyWeight : ℚ
end Unobserved

axiom R04_c1_axiom : R04_c1 Unobserved.penaltyWeight

end Claims
