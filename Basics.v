Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d: day): day := 
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
 (next_weekday (next_weekday saturday)) = tuesday.

simpl. reflexivity. Qed.
(* "The assertion we've just made can be proved by observing that both sides
of the equality evaluate to the same thing, after some simplification."*)

Extraction Language Haskell.
Extraction "day.hs" day next_weekday.

Inductive bool: Type :=
  | false: bool
  | true: bool.

Definition not (a: bool): bool :=
  match a with
  | true => false
  | false => true
  end.

Definition and (a b: bool): bool := 
  match a with
  | false => false
  | true => b
  end.

Example test_and: (and true true) = true.
Proof. simpl. reflexivity. Qed.

Infix "&&" := and.

Eval simpl in (true && true).

Definition or (a: bool) (b: bool): bool := 
  match a with
  | false => b
  | true => true
  end.

Infix "||" := or.

Definition nandb (b1:bool) (b2:bool) : bool := not (b1 && b2). 

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Compute (false || (not (true && (not false)))).
Check and.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  b1 && b2 && b3. (* and (and b1 b2) b3 *)

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Module Playground1.

Inductive nat : Type :=
  | O: nat
  | S: nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Definition succ (n : nat) : nat :=
  match n with
    | O => S O
    | n' => S n'
  end.

Compute (succ (S O)).

Extraction Language Haskell.
Extraction "nat.hs" nat pred.

End Playground1.

Definition minusTwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minusTwo 5).
Check S.
Check pred.
Check minusTwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := not (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n m: nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint minus (n m: nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Example test_plus: plus 5 5 = 10.
Proof. simpl. reflexivity. Qed.

Compute (plus 5 5).

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
           | O => true
           | S m' => false
           end
  | S n' => match m with
           | O => false
           | S m' => beq_nat n' m'
           end
  end.

Fixpoint beq_nat2 (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => beq_nat n' m'
  | _, _ => false
  end.

Example test_beq_nat: (beq_nat 5 5) = (beq_nat2 5 5).
Proof. simpl. reflexivity. Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* less than for natural numbers *)
Definition blt_nat (n m : nat) : bool := 
  leb n m && not (beq_nat n m)
.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Proof by Simplification *)
(* (Until now) The proofs of these claims were always the same: use simpl
 to simplify both sides of the equation, then use reflexivity to check that
 both sides contain identical values.*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n: nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

(* Example and Theorem (and a few others, including Lemma, Fact, and Remark) 
   mean exactly the same thing to Coq*)

(* Theorem plus_n_O : forall n, n = n + 0.
Proof.
  intros n. simpl. *)

Theorem plus_id_example : forall n m: nat, n = m -> n+n = m+m .
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H. 
  reflexivity. Qed.

(* The first line of the proof moves the universally quantified variables
   n and m into the context.
   The second moves the hypothesis n = m into the context and gives it the name H.
   The third tells Coq to rewrite the current goal (n + n = m + m) by
   replacing the left side of the equality hypothesis H with the right side. *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity. Qed.

(* Proof by case analysis *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n']. (* intro pattern *)
  - reflexivity.
  - reflexivity.
  Qed.
  
