import Values
import Claims
open Claims
/-! 各命題の判定。parse_claims.py が生成する。 -/
theorem R01_c1_holds : R01_c1 (trainDataSha256 := Values.trainDataSha256) := R01_c1_of_eq Values.trainDataSha256 (by decide +kernel)
theorem R01_c2_holds : R01_c2 (testDataSha256 := Values.testDataSha256) := R01_c2_of_eq Values.testDataSha256 (by decide +kernel)
theorem R02_c1_holds : R02_c1 (outputKeys := Values.outputKeys) := by decide +kernel
theorem R03_c1_holds : R03_c1 (polyDegree := Values.polyDegree) (nPolyFeatures := Values.nPolyFeatures) := by decide +kernel
theorem R03_c2_holds : R03_c2 (fitSteps := Values.fitSteps) := by decide +kernel
theorem R05_c1_holds : R05_c1 (testMse := Values.testMse) := by decide +kernel
theorem R06_c1_fails : ¬ (R06_c1 (testDataSha256 := Values.testDataSha256) (testMse := Values.testMse)) := R06_c1_not_of Values.testDataSha256 Values.testMse (by decide +kernel)
theorem R07_c1_holds : R07_c1 (trainMse := Values.trainMse) (trainRmse := Values.trainRmse) (trainMae := Values.trainMae) (trainR2 := Values.trainR2) (testMse := Values.testMse) (testRmse := Values.testRmse) (testMae := Values.testMae) (testR2 := Values.testR2) := by decide +kernel
