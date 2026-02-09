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
