import Books.TypeSoundness.Report.Active

def main : List String → IO UInt32 := Checker.Soundness.Typed.ActiveReport.main
