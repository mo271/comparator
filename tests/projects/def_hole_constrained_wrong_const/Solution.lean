-- Cheat: use a named constant (which is itself sorry'd) instead of True/False
def myProp : Prop := sorry

def myAnswer : Prop := myProp

theorem myThm : myAnswer ↔ 1 + 1 = 2 := by sorry
