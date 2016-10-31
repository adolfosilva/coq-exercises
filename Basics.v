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

Example test_plus: plus 5 5 = 10.
Proof. simpl. reflexivity. Qed.

Compute (plus 5 5).

End Playground2.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => n * (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.