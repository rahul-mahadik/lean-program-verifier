import MiniVerify
import MiniVerify.Tests

#print axioms MiniVerify.vcgen_sound
#print axioms MiniVerify.totalCorrect_of_vcs
#print axioms MiniVerify.Exec.deterministic
#print axioms MiniVerify.Exec.run_result
#print axioms MiniVerify.Exec.run_complete
#print axioms MiniVerify.run_sound
#print axioms MiniVerify.verified_execution
#print axioms MiniVerify.Language.verified_program
#print axioms MiniVerify.Language.absoluteValue_verified
#print axioms MiniVerify.Examples.BinarySearch.verification_conditions
#print axioms MiniVerify.Examples.BinarySearch.sortedCheck_correct
#print axioms MiniVerify.Examples.BinarySearch.executable_correct
#print axioms MiniVerify.Examples.Reverse.verification_conditions
#print axioms MiniVerify.Examples.Reverse.executable_correct
#print axioms MiniVerify.Examples.InsertionSort.vcs
#print axioms MiniVerify.Examples.InsertionSort.executable_correct

#check @MiniVerify.vcgen_sound
#check @MiniVerify.verified_execution
#check @MiniVerify.Examples.BinarySearch.executable_correct
#check @MiniVerify.Examples.Reverse.executable_correct
#check @MiniVerify.Examples.InsertionSort.executable_correct
