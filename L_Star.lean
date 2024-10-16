structure DFAState := (name : String) deriving BEq

structure FiniteAutomaton (Alph : List Char) :=
(Q : List DFAState)
(S : DFAState)
(δ : DFAState → Char → DFAState)
(Accept : List DFAState)

def validateWord (DFA : FiniteAutomaton Alph)
  (word : List Char) (curState : DFAState) : Bool :=
  match word with
  | [] => DFA.Accept.contains curState
  | w :: lst => validateWord DFA lst (DFA.δ curState w)

def T_Equivalent (Alph : List Char) (T : List String)
  (w1 : String) (w2 : String) (Mem : String → Bool)
  : Bool :=
    match T with
    | [] => true
    | s :: strs => (Mem (w1 ++ s) = Mem (w2 ++ s)) ∧ T_Equivalent Alph strs w1 w2 Mem

def for_Q2 (Alph : List Char) (Q_loop : List String)
  (Q : List String) (T : List String) (q : String) (a : Char) (Mem : String → Bool)
  : Option (String × Char) :=
  match Q_loop with
  | q0 :: rem => if T_Equivalent Alph T q0 (q ++ Char.toString a) Mem then
    for_Q2 Alph rem Q T q a Mem else some (q, a)
  | [] => none

def for_Alph (Alph : List Char) (Alph_loop : List Char)
  (Q : List String) (T : List String) (q : String) (Mem : String → Bool) : Option (String × Char) :=
  match Alph_loop with
  | a :: rem => match for_Q2 Alph Q Q T q a Mem with
                    | some (q1, b) => some (q1, b)
                    | none => for_Alph Alph rem Q T q Mem
  | [] => none

def complete_loop (Alph : List Char) (Q : List String) (Q_Iterator : List String)
  (T : List String) (Mem : String → Bool)
  : Option (String × Char) :=
  match Q_Iterator with
  | q0 :: rem => match for_Alph Alph Alph Q T q0 Mem with
                     | some (q1, b) => some (q1, b)
                     | none => complete_loop Alph Q rem T Mem
  | [] => none

def complete (Alph : List Char) (T : List String) (Q : List String)
  (Q_New : List String) (Mem : String → Bool)
  : List String :=
  match complete_loop Alph Q Q T Mem with
  | some (s, c) => complete Alph T Q ((s ++ Char.toString c) :: Q_New) Mem
  | none => Q_New

def findAcceptingStates (Q : List String) (Mem : String → Bool) : List String :=
  match Q with
  | w :: rem => if Mem w then w :: findAcceptingStates rem Mem else findAcceptingStates rem Mem
  | [] => []

def toAutomaton (Alph : List Char) (T : List String) (Q : List String) (Mem : String → Bool)
  : FiniteAutomaton Alph :=
  {Q := Q.map (fun x => {name := x}), S := {name := ""},
    Accept := (findAcceptingStates Q Mem).map (fun x => {name := x}), δ := fun q0 => fun a =>
    match for_Q2 Alph Q Q T q0.name a Mem with
    | some (s, c) => {name := s ++ Char.toString c}
    | none => {name := ""}
  }

def getSuffixes (w : String) : List String :=
  tail :: getSuffixes tail
  where tail := w.drop 1

def removeStringDuplicates (l : List String) : List String :=
  match l with
  | a :: b :: tail => if a = b then removeStringDuplicates (a :: tail)
     else a :: removeStringDuplicates (b :: tail)
  | a :: [] => [a]
  | [] => []

def LStar (Alph : List Char) (Q : List String) (T : List String) (Mem : String → Bool)
  (Eqiv : FiniteAutomaton Alph → Option (String))
  : FiniteAutomaton Alph := match Eqiv dfa with
    | none => dfa
    | some w => LStar Alph Q_compl (removeStringDuplicates (T ++ getSuffixes w).mergeSort) Mem Eqiv
    where Q_compl := complete Alph T Q Q Mem; dfa := toAutomaton Alph T Q_compl Mem
