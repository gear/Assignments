(* fmcs_a2_ans3.v Author: Hoang NT
 * 
 * This is the solution for the
 * questions of Assignment 3: Coq Programming.
 *
 * This file can be access at:
 *   https://github.com/gear/Assignments/
 *)

(* begin hide *)

Require Export fmcs_a2_q3.

(* end hide *)

(** %\subsection*{Q3.1 - Modified Stack Machine.}% *)

(** %\noindent% *)
(** Since we are given new [instrDenote'] function, I am going to change the [compile] and [progDenote] function into [compile'] and [progDenote'] function that accept the new definition of [instrDenote']. The new functions are defined as follow:*)

Fixpoint progDenote' (p : prog) (s : stack) : option stack :=
  match p with
  | nil => Some s
  | i :: p' => match instrDenote' i s with
               | None => None
               | Some s' => progDenote' p' s'
               end
  end.

Fixpoint compile' (e : exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => (compile e1) ++ (compile e2) ++ (iBinop b :: nil)
  end.

(** Before going to the proof, I would like to test out the new Stack Machine with few examples of program evaluation and compiler evaluation:*)

Eval simpl in progDenote' (compile' (Const 3)) nil.
(** [= Some (3 :: nil) : option stack] *)

Eval simpl in progDenote' (compile' (Binop Plus (Const 3) (Const 4))) nil.
(** [= Some (7 :: nil) : option stack] *)

Eval simpl in progDenote' (compile' (Binop Times 
             (Binop Plus (Const 3) (Const 4)) 
             (Binop Plus (Const 5) (Const 6)))) nil.
(** [= Some (77 :: nil) : option stack] *)

Eval simpl in compile' (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)).
(** [= iConst 3 :: iConst 2 :: iBinopPlus :: iConst 7 :: iBinop Times :: nil : prog] *)

(** Our modified compiler should work with %\emph{all}% input, therefore we have the compiple'_correct theorem as follow: *)

Theorem compile'_correct : forall e, progDenote' (compile' e) nil = Some (expDenote e :: nil).
(* begin hide *)
Abort.
(* end hide *)

(** To prove this theorem, as in %\cite{cpdt}%, I will use the standard trick of %\emph{strengthening the induction hypothesis}%. By proving the fact that, given %\emph{any}% expression, program list state, and stack state, the modified compiler will correctly compile the program to run with progDenote'.*)

Lemma compile'_correct' : forall e p s,
  progDenote' (compile' e ++ p) s = progDenote' p (expDenote e :: s).
(* [[
1 subgoal

  ============================
   forall (e : exp) (p : list instr) (s : stack),
   progDenote' (compile' e ++ p) s = progDenote' p (expDenote e :: s)  
]] *)

(**  Firstly I use [intros] tactic to handle the "[forall]" condition. We have: *)

intros.

(** [[
1 subgoal
  e : exp
  p : list instr
  s : stack
  ============================
   progDenote' (compile' e ++ p) s = progDenote' p (expDenote e :: s)
]] *)

(** Using induction on [e], we will have 2 subgoals corresponding to 2 cases of [e]: [Const n] and [Binop b e1 e2].*)

induction e.

(** [[
2 subgoals
  n : nat
  p : list instr
  s : stack
  ============================
   progDenote' (compile' (Const n) ++ p) s =
   progDenote' p (expDenote (Const n) :: s)

subgoal 2 is:
 progDenote' (compile' (Binop b e1 e2) ++ p) s =
 progDenote' p (expDenote (Binop b e1 e2) :: s)
]] *)
Abort.
