(* begin hide *)

Require Export fmcs_a2_q3.

(* end hide *)

(** %\subsection*{Q3.1 - Modified Stack Machine.}% *)

(** %\noindent% *)
(** Since we are given new [instrDenote'] function, I am going to change the [compile] and [progDenote] function into [compile'] and [progDenote'] function that accept the new definition of [instrDenote']. The new functions are defined as follow:*)
(** %\vspace{0.5em}% *)

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
  | Binop b e1 e2 => (compile' e1) ++ (compile' e2) ++ (iBinop b :: nil)
  end.
(** %\vspace{1em}% *)

(** %\noindent% Before going to the proof, I would like to test out the new Stack Machine with few examples of program evaluation and compiler evaluation:*)
(** %\vspace{0.5em}% *)

Eval simpl in progDenote' (compile' (Const 3)) nil.
(** [= Some (3 :: nil) : option stack] *)

Eval simpl in progDenote' (compile' (Binop Plus (Const 3) (Const 4))) nil.
(** [= Some (7 :: nil) : option stack] *)

Eval simpl in progDenote' (compile' (Binop Times 
             (Binop Plus (Const 3) (Const 4)) 
             (Binop Plus (Const 5) (Const 6)))) nil.
(** [= Some (77 :: nil) : option stack] *)

Eval simpl in compile' (Binop Times (Binop Plus (Const 2) (Const 3)) (Const 7)).
(** [= iConst 3 :: iConst 2 :: iBinop Plus :: iConst 7 :: iBinop Times :: nil : prog] *)
(** %\vspace{1em}% *)

(** %\noindent% Our modified compiler should work with %\emph{all}% input, therefore we have the [compiple'_correct] theorem as follow: *)

(** %\vspace{0.5em}% *)
Theorem compile'_correct : forall e, 
  progDenote' (compile' e) nil = Some (expDenote e :: nil).
(** %\vspace{0.5em}% *)
(* begin hide *)
Abort.
(* end hide *)

(** %\noindent% To prove this theorem, as in CPDT book, I will use the standard trick of %\emph{strengthening the induction hypothesis}%. By proving the fact that, given %\emph{any}% expression, program list state, and stack state, the modified compiler will correctly compile the program to run with [progDenote'].*)
(** %\vspace{0.5em}% *)

Lemma compile'_correct' : forall e p s,
  progDenote' (compile' e ++ p) s = progDenote' p (expDenote e :: s).
(** %\vspace{-1em}% 
[[
1 subgoal

  ============================
   forall (e : exp) (p : list instr) (s : stack),
   progDenote' (compile' e ++ p) s = progDenote' p (expDenote e :: s)  
]]

*)
(** %\vspace{0.5em}% *)
(** %\noindent% A typical strategy for handling "[forall]" is to use [intros] tactic. However, if we use [intros] now, before performing [induction] on expression e, we will have some problem with Coq cannot recognize some pattern later. Therefore, the tactic [induction] will be used to break down expression e into basic cases first, then I will apply [intros] tactic for each case. *)
(** %\vspace{0.5em}% *)

induction e.
(** %\vspace{-1em}% 
[[
2 subgoals
  n : nat
  ============================
   forall (p : list instr) (s : stack),
   progDenote' (compile' (Const n) ++ p) s = 
   progDenote' p (expDenote (Const n) :: s)
subgoal 2 is:
 forall (p : list instr) (s : stack),
 progDenote' (compile' (Binop b e1 e2) ++ p) s = 
 progDenote' p (expDenote (Binop b e1 e2) :: s)
]] 

*)

intros.
(** %\vspace{-1em}% 
[[
2 subgoals
  n : nat
  p : list instr
  s : stack
  ============================
   progDenote' (compile' (Const n) ++ p) s = 
   progDenote' p (expDenote (Const n) :: s)
subgoal 2 is:
 forall (p : list instr) (s : stack),
 progDenote' (compile' (Binop b e1 e2) ++ p) s = 
 progDenote' p (expDenote (Binop b e1 e2) :: s)
]]

*)
(** %\vspace{1em}% *)
(** %\noindent% The first subgoal can be proved by simplify the function [compile'] and [expDenote]. The tactic named [simpl] and [reflexivity] does exactly what we want. *)
(** %\vspace{0.5em}% *)

simpl.
(** %\vspace{-1em}% 
[[
2 subgoals
 n : nat
 p : list instr
 s : stack
 ============================
  progDenote' p (n :: s) = progDenote' p (n :: s)

subgoal 2 is
 forall (p : list instr) (s : stack),
 progDenote' (compile' (Binop b e1 e2) ++ p) s =
 progDenote' p (expDenote (Binop b e1 e2) :: s)
]]

*)
(** %\vspace{0.5em}% *)
(** %\noindent% By using simple [reflexivity] tactic, I have proved the first subgoal. *)
(** %\vspace{0.5em}% *)

reflexivity.

(** %\vspace{-1em}%
[[
1 subgoal
 b : binop
 e1 : exp
 e2 : exp
 IHe1 : progDenote' (compile' e1 ++ p) s = progDenote' p (expDenote e1 :: s)
 IHe2 : progDenote' (compile' e2 ++ p) s = progDenote' p (expDenote e2 :: s)
 ============================
  forall (p : list instr) (s : stack),
  progDenote' (compile' (Binop b e1 e2) ++ p) s =
  progDenote' p (expDenote (Binop b e1 e2) :: s)
]]

*)

(** %\noindent% Here we have [IHe1] and [IHe2] as two inductive hypothesis. By making the same assumption to handle with "[forall]", we have: *)
(** %\vspace{0.5em}% *)

intros.

(** %\vspace{-1em}%
[[
1 subgoal
 b : binop
 e1 : exp
 e2 : exp
 IHe1 : progDenote' (compile' e1 ++ p) s = progDenote' p (expDenote e1 :: s)
 IHe2 : progDenote' (compile' e2 ++ p) s = progDenote' p (expDenote e2 :: s)
 p : list instr
 s : stack
 ============================
  progDenote' (compile' (Binop b e1 e2) ++ p) s =
  progDenote' p (expDenote (Binop b e1 e2) :: s)
]]

*)
(** %\vspace{1em}% *)
(** %\noindent% The tactic [simpl] will evaluate the [compile'] and [expDenote] functions: *)
(** %\vspace{0.5em}% *)

simpl.

(** %\vspace{-1em}%
[[
1 subgoal
 b : binop
 e1 : exp
 e2 : exp
 IHe1 : progDenote' (compile' e1 ++ p) s = progDenote' p (expDenote e1 :: s)
 IHe2 : progDenote' (compile' e2 ++ p) s = progDenote' p (expDenote e2 :: s)
 p : list instr
 s : stack
 ============================
  progDenote' ((compile' e1 ++ compile' e2 ++ iBinop b :: nil) ++ p) s =
  progDenote' p (binopDenote b (expDenote e1) (expDenote e2) :: s)
]]

*)
(** %\vspace{1em}% *)
(** %\noindent% To make the LHS of our target goal similar to the first inductive hypothesis [IHe1], I will apply the reverse association rule for [list] concatenation. *)
(** %\vspace{0.5em}% *)

Check app_assoc_reverse.

(** %\vspace{-1.5em}%
[[
app_assoc_reverse
     : forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ m ++ n
]]

*)

rewrite app_assoc_reverse.

(** %\vspace{-1em}%
[[
1 subgoal
 b : binop
 e1 : exp
 e2 : exp
 IHe1 : progDenote' (compile' e1 ++ p) s = progDenote' p (expDenote e1 :: s)
 IHe2 : progDenote' (compile' e2 ++ p) s = progDenote' p (expDenote e2 :: s)
 p : list instr
 s : stack
 ============================
  progDenote' (compile' e1 ++ (compile' e2 ++ iBinop b :: nil) ++ p) s =
  progDenote' p (binopDenote b (expDenote e1) (expDenote e2) :: s)
]]

*)
(** %\vspace{1em}% *)
(** %\noindent% Now we can apply the inductive hypotheses to "push" [e1] and [e2] of the LHS to the LHS stack. *)
(** %\vspace{0.5em}% *)

rewrite IHe1.

(** %\vspace{-1em}%
[[
1 subgoal
 b : binop
 e1 : exp
 e2 : exp
 IHe1 : progDenote' (compile' e1 ++ p) s = progDenote' p (expDenote e1 :: s)
 IHe2 : progDenote' (compile' e2 ++ p) s = progDenote' p (expDenote e2 :: s)
 p : list instr
 s : stack
 ============================
  progDenote' ((compile' e2 ++ iBinop b :: nil) ++ p) (expDenote e1 :: s) =
  progDenote' p (binopDenote b (expDenote e1) (expDenote e2) :: s)
]]

*)

rewrite app_assoc_reverse.

rewrite IHe2.

(** %\vspace{-1em}%
[[
1 subgoal
 b : binop
 e1 : exp
 e2 : exp
 IHe1 : progDenote' (compile' e1 ++ p) s = progDenote' p (expDenote e1 :: s)
 IHe2 : progDenote' (compile' e2 ++ p) s = progDenote' p (expDenote e2 :: s)
 p : list instr
 s : stack
 ============================
  progDenote' ((iBinop b :: nil) ++ p) (expDenote e2 :: expDenote e1 :: s) =
  progDenote' p (binopDenote b (expDenote e1) (expDenote e2) :: s)
]]

*)

(** %\vspace{1em}% *)
(** %\noindent% At this step, we can use the [simpl] tactic again since it is trivial to evaluate the LHS's [progDenote'] with [iBinop p :: nil]. *)
(** %\vspace{0.5em}% *)

simpl.

(** %\vspace{-1em}%
[[
1 subgoal
 b : binop
 e1 : exp
 e2 : exp
 IHe1 : progDenote' (compile' e1 ++ p) s = progDenote' p (expDenote e1 :: s)
 IHe2 : progDenote' (compile' e2 ++ p) s = progDenote' p (expDenote e2 :: s)
 p : list instr
 s : stack
 ============================
  progDenote' p (binopDenote b (expDenote e1) (expDenote e2) :: s) =
  progDenote' p (binopDenote b (expDenote e1) (expDenote e2) :: s)
]]

*)
(** %\vspace{1em}% *)
(** %\noindent% I comple the proof of this lemma by [reflexivity] and save it with [Qed]. *)
(** %\vspace{0.5em}% *)

reflexivity.
Qed.

(** %\vspace{-2em}%
[[
compile'_correct' is defined
]]

*)

(** %\noindent% Now we can go back to prove the main theorem: *)
(** %\vspace{0.5em}% *)

Theorem compile'_correct : forall e, progDenote' (compile' e) nil = Some (expDenote e :: nil).
(** %\vspace{0.5em}% *)
(** %\noindent% Just like with the lemma [compile'_correct'], I will firstly introduce the expression [e] and then append [nil] to e so that the LHS has the form of [compile'_correct']. *)
(** %\vspace{0.5em}% *)

intros.
rewrite (app_nil_end (compile' e)).

(**
[[
1 subgoal
  e : exp
  ============================
   progDenote' (compile' e ++ nil) nil = Some (expDenote e :: nil)
]]

*)
(** %\vspace{1em}% *)
(** %\noindent% The theorem is proved by applying lemma [compile'_correct'] and [reflexivility. *)
(** %\vspace{0.5em}% *)

rewrite compile'_correct'.

(** %\vspace{-1em}%
[[
1 subgoal
  e : exp
  ============================
   progDenote' nil (expDenote e :: nil) = Some (expDenote e :: nil)
]]

*)

reflexivity.
Qed.

(** %\vspace{-2em}%
[[
compile'_correct is defined
]]
*)

(** %\subsection*{Q3.2 - Extended Stack Machine.}% *)

(** %\noindent% *)
(** The new Stack Machine is defined in module ext as follow: (I keep the definition of [stack] since it is not necessary to re-define it).*)

Module ext.

Require Import List.

Inductive binop : Set := Plus | Times | Minus.
Definition binopDenote (b:binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  | Minus => minus
  end.
Inductive exp : Set :=
  | Const : nat -> exp
  | Binop : binop -> exp -> exp -> exp.
Fixpoint expDenote (e:exp) : nat :=
  match e with
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.
Inductive instr : Set :=
  | iConst : nat -> instr
  | iBinop : binop -> instr.
Definition prog := list instr.
Definition  instrDenote (i : instr) (s : stack) : option stack :=
  match i with
  | iConst n => Some (n :: s)
  | iBinop b => match s with
                | arg2 :: arg1 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
                | _ => None
                end
  end.
Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
  | nil => Some s
  | i :: p' => match instrDenote i s with
               | None => None
               | Some s' => progDenote p' s'
               end
  end.
Fixpoint compile (e : exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => (compile e1) ++ (compile e2) ++ (iBinop b :: nil)
  end.

End ext.

(** %\vspace{1em}% *)
(** %\noindent% Some example with the new extended stack machine: *)

Eval simpl in ext.progDenote (ext.compile (ext.Const 3)) nil.
(** [= Some (3 :: nil) : option stack] *)

Eval simpl in ext.progDenote (ext.compile (ext.Binop ext.Minus (ext.Const 42) (ext.Const 24))) nil.
(** [= Some (18 :: nil) : option stack] *)

Eval simpl in ext.progDenote (ext.compile (ext.Binop ext.Times 
             (ext.Binop ext.Plus (ext.Const 3) (ext.Const 4)) 
             (ext.Binop ext.Minus (ext.Const 8) (ext.Const 6)))) nil.
(** [= Some (14 :: nil) : option stack] *)

Eval simpl in ext.compile (ext.Binop ext.Times (ext.Binop ext.Minus (ext.Const 2) (ext.Const 3)) (ext.Const 7)).
(** [= Some (14 :: nil) : option stack] *)

(** %\vspace{1em}% *)
(** %\noindent% *)
(** The theorem for this extended machine's correctness is proven in a similar way to %\textbf{Q3.1}%. I will prove an auxilary lemma [ext_compile_correct'], and use it to prove the [ext_compile_correct] theorem. *)

(** %\vspace{0.5em}% *)
Theorem ext_compile_correct : forall (e : ext.exp),
  ext.progDenote (ext.compile e) nil = Some (ext.expDenote e :: nil).

Lemma ext_compile_correct' : forall (e : ext.exp) (p : ext.prog) (s : stack),
  ext.progDenote (ext.compile e ++ p) s = ext.progDenote p (ext.expDenote e :: s).

induction e.
intros.
simpl.
reflexivity.

intros.
simpl.
rewrite app_assoc_reverse.
rewrite IHe1.
rewrite app_assoc_reverse.
rewrite IHe2.
simpl.
reflexivity.
Qed.

(** %\vspace{-2em}%
[[
ext_compile_correct' is defined
]]
*)

intros.
rewrite (app_nil_end (ext.compile e)).
rewrite ext_compile_correct'.
reflexivity.
Qed.

(** %\vspace{-2em}%
[[
ext_compile_correct is defined
]]
*)
