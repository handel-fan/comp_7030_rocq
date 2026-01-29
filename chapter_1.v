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

Definition andb (b1:bool, b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool, b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example orb1 (orb(true, true)) => true
Example orb2 (orb(true, false)) => true
Example orb3 (orb(false, true)) => true
Example orb4 (orb(false, false)) => false
