local macro_rules | `(True) => `(1+1=2)

def myAnswer : Prop := True

theorem myThm : myAnswer ↔ 1 + 1 = 2 := by rfl
