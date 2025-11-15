import Lean

open Lean Elab Tactic

syntax chainSteps := sepBy1IndentSemicolon(term:lead)
syntax "chain " chainSteps : tactic

elab "chain " steps:chainSteps : tactic => do
  let `(chainSteps| $stepsList:term*) := steps | throwUnsupportedSyntax
  let stepsElems := stepsList.getElems

  let firstStep : Term := stepsElems[0]!
  let firstHypName ← withMainContext do
    let hypName ← mkFreshUserName `h
    let hypIdent : TSyntax `ident := ⟨mkIdent hypName⟩
    evalTactic (← `(tactic| have $hypIdent := $firstStep))
    return hypName

  let mut prevHyp := firstHypName
  for step in stepsElems[1:] do
    let stepTerm : Term := step
    let hypName ← withMainContext do
      let hypName ← mkFreshUserName `h
      let hypIdent : TSyntax `ident := ⟨mkIdent hypName⟩
      let prevHypIdent : TSyntax `term := ⟨mkIdent prevHyp⟩
      evalTactic (← `(tactic| have $hypIdent := $stepTerm $prevHypIdent))
      return hypName
    prevHyp := hypName

  let lastHypIdent : TSyntax `term := ⟨mkIdent prevHyp⟩
  evalTactic (← `(tactic| exact $lastHypIdent))
