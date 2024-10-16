structure DFAState := (name : String) deriving BEq

structure FiniteAutomaton (Alph : List Char) :=
(Q : List DFAState)
(S : DFAState)
(start_in_Q : S ∈ Q)
(δ : DFAState → Char → DFAState)
(trans_in_Q : ∀q ∈ Q, ∀a ∈ Alph, δ q a ∈ Q)
(Accept : List DFAState)
(accept_in_Q : a ∈ Accept → a ∈ Q)

def validateWord (DFA : FiniteAutomaton Alph)
  (word : List Char) (curState : DFAState) : Bool :=
  match word with
  | [] => DFA.Accept.contains curState
  | w :: lst => validateWord DFA lst (DFA.δ curState w)

def minimal_regularity (Alph : List Char) (Mem : String → Bool) : Prop :=
  ∃automaton : FiniteAutomaton Alph, (∀w : List Char, Mem (w.toString) = validateWord automaton w automaton.S
  ∧ ∀automaton2 : FiniteAutomaton Alph, ∀w : List Char, (Mem (w.toString) = validateWord automaton2 w automaton2.S
  → sizeOf automaton2.Q >= sizeOf automaton.Q))

def findAcceptingStates (Q : List String) (Mem : String → Bool) : List String :=
  match Q with
  | w :: rem => if Mem w then w :: findAcceptingStates rem Mem else findAcceptingStates rem Mem
  | [] => []

theorem accepting_in_q : a ∈ findAcceptingStates Q Mem → a ∈ Q := by
  induction Q with
  | nil => {
    intro h
    assumption
  }
  | cons b tail tail_ih => {
    intro h
    simp [findAcceptingStates] at h
    split at h
    case cons.isTrue => rw [List.mem_cons] at h
                        rw [List.mem_cons]
                        apply Or.elim h
                        case left => apply Or.intro_left
                        case right => intro h2
                                      have h3 : a ∈ tail := tail_ih h2
                                      apply Or.intro_right
                                      exact h3
    case cons.isFalse => have h2 : a ∈ tail := tail_ih h
                         rw [List.mem_cons]
                         apply Or.intro_right
                         exact h2
  }

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

def toAutomaton (Alph : List Char) (T : List String) (Q : List String) (Mem : String → Bool)
  (h : "" ∈ Q): FiniteAutomaton Alph :=
  {Q := Q.map (fun x => {name := x}), S := {name := ""},
    Accept := (findAcceptingStates Q Mem).map (fun x => {name := x}), δ := fun q0 => fun a =>
    match for_Q2 Alph Q Q T q0.name a Mem with
    | some (s, c) => {name := s ++ Char.toString c}
    | none => {name := ""},
    start_in_Q := by
      rw [List.mem_map]
      exact ⟨"", by apply And.intro
                    case right => rfl
                    case left => exact h⟩
    ,
    accept_in_Q := by
      intro a
      intro hy
      rw [List.mem_map]
      rw [List.mem_map] at hy
      match hy with
      | ⟨w, hw⟩ => exact ⟨w, by apply And.intro
                                case right => exact hw.right
                                case left => exact accepting_in_q hw.left⟩
  }

def complete_loop (Alph : List Char) (Q : List String) (Q_Iterator : List String)
  (T : List String) (Mem : String → Bool)
  : Option (String × Char) :=
  match Q_Iterator with
  | q0 :: rem => match for_Alph Alph Alph Q T q0 Mem with
                     | some (q1, b) => some (q1, b)
                     | none => complete_loop Alph Q rem T Mem
  | [] => none

def complete (Alph : List Char) (T : List String) (Q : List String) (Mem : String → Bool)
  (reg : minimal_regularity Alph Mem): List String :=
  match complete_loop Alph Q Q T Mem with
  | some (s, c) => complete Alph T ((s ++ Char.toString c) :: Q) Mem reg
  | none => Q

def getSuffixes (w : List Char) : List String :=
  match w with
  | _ :: tail => tail.toString :: getSuffixes tail
  | [] => []

def removeStringDuplicates (l : List String) : List String :=
  match l with
  | a :: b :: tail => if a = b then removeStringDuplicates (a :: tail)
     else a :: removeStringDuplicates (b :: tail)
  | a :: [] => [a]
  | [] => []

def LStar (Alph : List Char) (Q : List String) (T : List String) (Mem : String → Bool)
  (Eqiv : FiniteAutomaton Alph → Option (String))
  (reg : minimal_regularity Alph Mem)
  : FiniteAutomaton Alph := match Eqiv dfa with
    | none => dfa
    | some w => LStar Alph Q_compl (removeStringDuplicates (T ++ getSuffixes w.data).mergeSort) Mem Eqiv reg
    where Q_compl := complete Alph T Q Mem reg; dfa := toAutomaton Alph T Q_compl Mem 
