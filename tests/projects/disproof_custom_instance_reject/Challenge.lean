def myPred (n : Nat) : Prop := ∀ k : Nat, k + n = n + k

-- Elaborates `ite` using `Classical.propDecidable (myPred 0)`.
open Classical in
theorem custom_inst : (if myPred 0 then 0 else 1) = 1 := by
  sorry
