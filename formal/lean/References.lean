import Mathlib
/-! 引用した claims の公理。parse_claims.py が引用先から生成する。手で編集しない。 -/
namespace Ref1
-- https://github.com/auto-res2/diabetes-linear-regression-5 の commit 163eaf98735b391c5df51e08c9b52f6fb93d1bec
opaque trainDataSha256 : String
opaque testDataSha256 : String
opaque outputKeys : List String
noncomputable opaque mean {n : ℕ} (y : Fin n → ℝ) : ℝ
noncomputable opaque mse {n : ℕ} (y ŷ : Fin n → ℝ) : ℝ
noncomputable opaque r2 {n : ℕ} (y ŷ : Fin n → ℝ) : ℝ
noncomputable opaque mae {n : ℕ} (y ŷ : Fin n → ℝ) : ℝ
noncomputable opaque rmse {n : ℕ} (y ŷ : Fin n → ℝ) : ℝ
opaque testMse : ℚ
opaque trainMse : ℚ
opaque trainRmse : ℚ
opaque trainMae : ℚ
opaque trainR2 : ℚ
opaque testRmse : ℚ
opaque testMae : ℚ
opaque testR2 : ℚ
abbrev R06_c4 (trainDataSha256 : String) : Prop := trainDataSha256 = "7968ccfdb6b347591a4a86e80dc98088c8d74ccc118ef1c80694e02748c425e2"
abbrev R06_c5 (testDataSha256 : String) : Prop := testDataSha256 = "cb0d6b45a5531af0e7818c582c9f92b56ad466c787539acfbeef143da4349091"
abbrev R11_c1 (outputKeys : List String) : Prop :=
  ["trainMse", "trainRmse", "trainMae", "trainR2", "testMse", "testRmse", "testMae", "testR2"] ⊆ outputKeys
abbrev R12_c1 : Prop := ∀ (n : ℕ) (y ŷ : Fin n → ℝ),
  mse y ŷ = (1 / (n : ℝ)) * ∑ i, (y i - ŷ i) ^ 2 ∧
  r2 y ŷ = 1 - (∑ i, (y i - ŷ i) ^ 2) / ∑ i, (y i - mean y) ^ 2
abbrev R13_c1 : Prop := ∀ (n : ℕ) (y : Fin n → ℝ), mean y = (1 / (n : ℝ)) * ∑ i, y i
abbrev R14_c3 : Prop := ∀ (n : ℕ) (y ŷ : Fin n → ℝ), mae y ŷ = (1 / (n : ℝ)) * ∑ i, |y i - ŷ i|
abbrev R14_c4 : Prop := ∀ (n : ℕ) (y ŷ : Fin n → ℝ), rmse y ŷ = Real.sqrt (mse y ŷ)
abbrev R15_c1 (outputKeys : List String) : Prop := R11_c1 outputKeys
abbrev R20_c1 (testMse : ℚ) : Prop := (round (testMse / 0.1) : ℚ) * 0.1 = 3424.3
abbrev R26_c1 (trainMse trainRmse trainMae trainR2 testMse testRmse testMae testR2 : ℚ) : Prop :=
  (round (trainMse / 0.1) : ℚ) * 0.1 = 2734.8 ∧ (round (trainRmse / 0.1) : ℚ) * 0.1 = 52.3 ∧
  (round (trainMae / 0.1) : ℚ) * 0.1 = 42.6 ∧ (round (trainR2 / 0.001) : ℚ) * 0.001 = 0.554 ∧
  (round (testMse / 0.1) : ℚ) * 0.1 = 3424.3 ∧ (round (testRmse / 0.1) : ℚ) * 0.1 = 58.5 ∧
  (round (testMae / 0.1) : ℚ) * 0.1 = 46.2 ∧ (round (testR2 / 0.001) : ℚ) * 0.001 = 0.332
axiom R06_c4_cited : R06_c4 trainDataSha256
axiom R06_c5_cited : R06_c5 testDataSha256
axiom R11_c1_cited : R11_c1 outputKeys
axiom R12_c1_cited : R12_c1
axiom R13_c1_cited : R13_c1
axiom R14_c3_cited : R14_c3
axiom R14_c4_cited : R14_c4
axiom R15_c1_cited : R15_c1 outputKeys
axiom R20_c1_cited : R20_c1 testMse
axiom R26_c1_cited : R26_c1 trainMse trainRmse trainMae trainR2 testMse testRmse testMae testR2
end Ref1
