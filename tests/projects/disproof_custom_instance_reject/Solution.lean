def myPred (n : Nat) : Prop := ∀ k : Nat, k + n = n + k

-- Declares a custom `Decidable` instance before `.disproof`, shifting `ite` away from
-- `Classical.propDecidable` (`Decidable` lives in `Type`, so the two statements are not
-- kernel-defeq and must be rejected).
instance : Decidable (myPred 0) := isTrue (by intro k; omega)

open Classical in
theorem custom_inst.disproof (h : (if myPred 0 then 0 else 1) = 1) : False := by
  exact absurd h (by decide)
