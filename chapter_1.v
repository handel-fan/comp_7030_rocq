Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.


Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

From Stdlib Require Export String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example orb1 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example orb2 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example orb4 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b 
  then false 
  else true.

Definition andb' (b1:bool)(b2:bool) : bool :=
  if b1
  then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

(* Section about using conditional expressions on non-boolean types *)

Inductive bw : Type :=
  | bw_black
  | bw_white.

Definition invert (x: bw) : bw :=
  if x then bw_white
  else bw_black.

Compute (invert bw_black).
Compute (invert bw_white).

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => 
    match b2 with
    | true => false
    | false => true
    end
  end.

Example testnand1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example testnand2: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example testnand3: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
Example testnand4: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | false => false
  | true => 
    match b2 with
    | false => false
    | true => 
      match b3 with
      | false => false
      | true => true
      end
    end
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check (negb true).
Check (negb).

(*New Types from Old*)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c: color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module Playground.
  Definition foo : rgb := blue.
  End Playground.

Definition foo : bool := true.
Check Playground.foo : rgb.
Check foo : bool.

Module TuplePlayground.
  Inductive bit : Type :=
    | B1
    | B0.
  
  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).

  Check (bits B1 B0 B1 B0)
    : nybble.

    Definition all_zero (nb : nybble) :=
      match nb with
      | (bits B0 B0 B0 B0) => true
      | (bits _ _ _ _) => false
    end.

  Compute (all_zero(bits B0 B0 B0 B0)).
  Compute (all_zero(bits B1 B0 B0 B0)).
End TuplePlayground.


Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Inductive otherNat : Type :=
    | stop
    | tick (o : otherNat).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
End NatPlayground.

Definition minustwo (n: nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S(S n') => n'
  end.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 6 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n: nat) (m: nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with 
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => 0
  | S _, O => n
  | S n', S m' => minus n' m'
  end.
