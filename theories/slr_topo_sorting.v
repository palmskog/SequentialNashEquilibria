(*******************************************)
(*                                         *)
(*          slr_topo_sorting.v             *)
(*                                         *)
(*           Stéphane Le Roux              *)
(*                                         *)
(*     LIP (ENS Lyon, CNRS, INRIA)         *)
(*                                         *)
(*             Coq v8.1                    *)
(*                                         *)
(*              2007/03                    *)
(*                                         *)
(*******************************************)

Require Import List.
Require Import Relations. 
Require Import Arith.
Require Import Lia.
Require Import Sumbool.

Set Implicit Arguments.

(* *********************************************************************)
(* ON EXCLUDED MIDDLE AND DECIDABILITY *)

Section EM_DEC.

Variable A : Type.
Variable R : relation A.

Definition eq_midex :=  forall x y : A, x=y \/ x<>y.
Definition rel_midex := forall x y, R x y \/ ~R x y.

Definition eq_dec := forall x y : A, {x=y}+{x<>y}.
Definition rel_dec := forall x y, {R x y}+{~R x y}.

Lemma eq_dec_midex : eq_dec -> eq_midex.
Proof.
do 3 intro. destruct (X x y); tauto.  
Qed.

Lemma rel_dec_midex : rel_dec -> rel_midex.
Proof.
do 3 intro. destruct (X x y); tauto. 
Qed.

Lemma bool_rel_dec :
{f : A -> A -> bool | forall x y : A, if f x y then R x y else ~R x y} -> rel_dec.
Proof. 
intros (f,H) x y. generalize (H x y). case (f x y) ; intros ; tauto.
Qed.

Lemma rel_dec_bool : 
rel_dec -> { f : A -> A -> bool | forall x y : A, if f x y then R x y else ~R x y }.
Proof.
intro H. exists (fun x y : A => if H x y then true else false).
intros x y. destruct (H x y) ; trivial.
Qed.

End EM_DEC.

(* *********************************************************************)
(* GENERAL DEFINITIONS AND LEMMAS ON LISTS *)

Section On_List.

Variable A : Type.

Lemma In_midex : eq_midex A -> forall (x : A) l, In x l \/ ~In x l. 
Proof.
induction l. tauto. simpl. destruct (H a x); destruct IHl; tauto.
Qed.

Lemma In_elim_right : eq_midex A -> forall (x : A) l, 
In x l -> exists l', exists l'', l=l'++(x::l'') /\ ~In x l''. 
Proof.
induction l; simpl; intros. contradiction. 
destruct (In_midex H x l). destruct IHl. assumption. destruct H2. 
exists (a::x0). exists x1. rewrite (proj1 H2). rewrite <- (app_comm_cons x0 (x::x1) a). tauto.  
destruct H0. exists (nil : list A). exists l. simpl. rewrite H0. tauto. contradiction.
Qed.

Lemma incl_nil : forall l : list A, incl nil l. 
Proof.
do 2 intro. simpl. tauto.
Qed.

Lemma incl_elim_cons : forall l l' (x : A), incl (x::l) l' -> incl l l'.
Proof.
unfold incl. simpl. intros. apply H. tauto.
Qed.

Lemma incl_double_cons : forall (x : A) l l', incl l l' -> incl (x::l) (x::l').
Proof.
unfold incl. simpl. intros. pose (H a). tauto. 
Qed.

Lemma length_app : forall l l' : list A, length (l++l')=length l + length l'.
Proof.
induction l; simpl; intro; try rewrite IHl; trivial.  
Qed.

(* *********************************************************************)
(* repeat-free *)

Fixpoint repeat_free (l : list A) : Prop :=
match l with
| nil => True
| a::l' => ~In a l' /\ repeat_free l'
end.

Lemma repeat_free_app_elim_right : forall l l' ,
repeat_free (l++l') -> repeat_free l'. 
Proof.
induction l; simpl; intros. assumption. apply IHl. tauto. 
Qed.

Lemma repeat_free_incl_length : eq_midex A -> forall l l',
repeat_free l -> incl l l' -> length l<=length l'.
Proof.
induction l; simpl; intros. apply le_O_n. 
destruct (In_elim_right H a l'). apply H1. simpl. tauto. destruct H2. rewrite (proj1 H2). 
rewrite (length_app x (a::x0)). assert (length l <= length (x++x0)). apply IHl. 
tauto. unfold incl in *|-* . intros. apply in_or_app. destruct (H a0 a). 
rewrite H4 in H3. tauto. assert (In a0 x \/ In a0 (a::x0)). apply in_app_or. 
rewrite <- (proj1 H2). apply H1. simpl. tauto. simpl in H5. intuition. rewrite H5 in H4. tauto. 
rewrite (length_app x x0) in H3. simpl. lia. 
Qed. 
 
End On_List.

(* *********************************************************************)
(* GENERAL DEFINITIONS AND LEMMAS ON BINARY RELATIONS *)

Section On_Rel_Gen.

Variable A : Type.

Definition sub_rel (B: Type) (R R' : relation B) : Prop := forall x y, R x y -> R' x y.

Lemma transitive_sub_rel : forall R R' R'' : relation A, sub_rel R R' -> sub_rel R' R'' -> sub_rel R R''.
Proof.
unfold sub_rel. intros. apply H0. apply H. assumption.
Qed.

Lemma clos_trans_monotonic : forall R' R'',
sub_rel R' R'' -> sub_rel (clos_trans A R')(clos_trans A R'').
Proof.
unfold sub_rel. intros. induction H0. constructor. apply H. assumption. 
constructor 2 with y; assumption.  
Qed. 

Definition irreflexive (R : relation A) : Prop := forall x, ~R x x.

Lemma irreflexive_preserved : forall R R',
sub_rel R R' -> irreflexive R' -> irreflexive R.
Proof.
unfold sub_rel, irreflexive. intros. intro. exact (H0 x (H x x H1)).
Qed.

Section restriction.

Variable R : relation A.
Variable l : list A.

Lemma reflexive_sub_rel : sub_rel R R.
Proof. 
do 2 intro. tauto. 
Qed.

Lemma sub_rel_clos_trans : sub_rel R (clos_trans A R).
Proof. 
do 3 intro. constructor. assumption. 
Qed.

Lemma transitive_clos_trans : transitive A (clos_trans A R).
Proof.
do 5 intro. constructor 2 with y; assumption.   
Qed.

Lemma transitive_sub_rel_clos_trans :
transitive A R -> sub_rel (clos_trans A R) R.
Proof.
unfold transitive, sub_rel. intros. induction H0. assumption. 
apply H with y; assumption.   
Qed.

(***********************************************************************)
(*  Restriction *)

Definition restriction x y : Prop := In x l /\ In y l /\ R x y.

Definition is_restricted : Prop := forall x y, R x y -> In x l /\ In y l.

Lemma sub_rel_restriction : sub_rel restriction R.
Proof.
unfold sub_rel, restriction. intros. tauto.
Qed. 

Lemma restriction_dec : eq_dec A -> rel_dec R -> rel_dec restriction.
Proof.
unfold restriction. do 4 intro. destruct (X0 x y). destruct (In_dec X x l). destruct (In_dec X y l). 
constructor. tauto. constructor 2. tauto. constructor 2. tauto. constructor 2. tauto.
Qed.

Lemma restriction_midex : eq_midex A -> rel_midex R -> rel_midex restriction.
Proof.
unfold restriction. do 4 intro. destruct (H0 x y). destruct (In_midex H x l). destruct (In_midex H y l). 
constructor. tauto. constructor 2. tauto. constructor 2. tauto. constructor 2. tauto.
Qed. 

End restriction.

Lemma restricted_restriction : forall R l, is_restricted (restriction R l) l.
Proof.
unfold restriction, is_restricted. tauto. 
Qed.

Lemma restricted_clos_trans : forall R l,
is_restricted R l -> is_restricted (clos_trans  A R) l.
Proof.
unfold is_restricted. intros. induction H0. apply H. assumption. tauto. 
Qed. 

Lemma clos_trans_restricted_pair : forall R x y,
is_restricted R (x::y::nil) -> clos_trans A R x y -> R x y.
Proof.
intros. induction H0. assumption. 
destruct (restricted_clos_trans H H0_).
destruct H1. rewrite H1 in H. rewrite H1. tauto.
destruct H1. rewrite H1 in H. rewrite H1. tauto.
contradiction. 
Qed.

Lemma clos_trans_restricted_pair_bis : forall R x y,
is_restricted R (x::y::nil) -> clos_trans A R y x -> R y x.
Proof.
intros. induction H0. assumption. 
destruct (restricted_clos_trans H H0_).
destruct H1. rewrite H1 in H. rewrite H1. tauto.
destruct H1. rewrite H1 in H. rewrite H1. tauto.
contradiction. 
Qed.

Lemma clos_trans_restriction : forall (R : relation A) x y,
R x y -> clos_trans A (restriction R (x :: y :: nil)) x y.
Proof.
intros. constructor. unfold restriction. simpl. tauto.
Qed.

End On_Rel_Gen.

(* **********************************************************************)
(*  ON TRANSITIVE CLOSURE *)

Section On_transitive_closure.

Variable A : Type.

(* *********************************************************************)
(*  Path *)

Section Path.

Variable R : relation A.

Fixpoint is_path (x y : A)(l : list A){struct l} : Prop :=
match l with
| nil => R x y
| z::l' => R x z /\ is_path z y l'
end.

Lemma path_clos_trans : forall y l x, 
is_path x y l -> clos_trans A R x y.
Proof.
induction l; simpl; intros. constructor. assumption.
constructor 2 with a. constructor. tauto. apply IHl. tauto.
Qed.

Lemma path_app : forall y z l' l x,
is_path x y l -> is_path y z l' -> is_path x z (l++(y::l')). 
Proof.
induction l; simpl; intros. tauto. split. tauto. apply IHl; tauto.
Qed. 

Lemma clos_trans_path : forall x y, 
clos_trans A R x y -> exists l, is_path x y l. 
Proof.
intros. induction H. exists (nil : list A). simpl. assumption.
destruct IHclos_trans1. destruct IHclos_trans2. exists (x0++(y::x1)). 
apply path_app; assumption.
Qed.

Lemma path_app_elim_right : forall y z l l' x, 
is_path x z (l++(y::l')) -> is_path y z l'.
Proof.
induction l; simpl; intros. tauto. apply IHl with a. tauto. 
Qed.  

Lemma path_repeat_free_length : 
eq_midex A -> forall y l x,  is_path x y l -> 
exists l',  ~In x l' /\ ~In y l' /\ repeat_free l' /\ length l'<= length l /\ incl l' l /\ is_path x y l'.
Proof.
induction l; intros; simpl in H0. exists (nil : list A). simpl.
pose (incl_nil (nil : list A)). pose (le_O_n 0). tauto. 
destruct (IHl a). tauto.
destruct (H y a). exists (nil : list A). simpl.
pose (le_O_n (S (length l))). pose (incl_nil (a::l)). rewrite H2. tauto. 
destruct (In_midex H x x0). destruct (In_elim_right H x x0). assumption. 
destruct H4. exists x2. split. tauto. split. intro. absurd (In y x0). tauto. 
rewrite (proj1 H4). apply in_or_app. simpl. tauto. rewrite (proj1 H4) in H1. split. 
destruct (repeat_free_app_elim_right x1 (x::x2)). tauto. tauto.   
split. rewrite (length_app x1 (x::x2)) in H1. simpl in H1|-* . lia. split.
apply incl_tran with (x::x2). apply incl_tl. apply incl_refl.
apply incl_tran with (x1++(x::x2)). apply incl_appr. apply incl_refl. apply incl_tran with l. 
tauto. apply incl_tl. apply incl_refl. apply path_app_elim_right with x1 a. tauto. 
destruct (H x a). exists x0. rewrite H4. simpl. assert (length x0 <= S (length l)). lia. 
assert (incl x0 (a :: l)). apply incl_tl. tauto. tauto. exists (a::x0). simpl.
assert (S (length x0) <= S (length l)). lia. 
assert (incl (a :: x0) (a :: l)). apply incl_double_cons. tauto. 
assert (a<>x). intro. rewrite H7 in H4. tauto. 
assert (a<>y). intro. rewrite H8 in H2. tauto. tauto. 
Qed.

Lemma path_restricted_incl : forall y l l' x,
is_restricted R l -> is_path x y l' -> incl l' l.
Proof.
unfold is_restricted. induction l'; simpl; intros. intro. simpl. tauto.
apply incl_cons. pose (H x a). tauto. apply IHl' with a; tauto.
Qed. 

(* *********************************************************************)
(* bounded_path *)

Inductive bounded_path (n : nat) : relation A :=
| bp_intro : forall x y l, length l<= n -> is_path x y l -> bounded_path n x y.

Lemma bounded_path_clos_trans : forall n,
sub_rel (bounded_path n) (clos_trans A R).
Proof.
unfold sub_rel. intros. inversion H. apply path_clos_trans with l. assumption. 
Qed.

Lemma clos_trans_bounded_path : eq_midex A -> forall l,
is_restricted R l -> sub_rel (clos_trans A R) (bounded_path (length l)).
Proof.
do 6 intro. destruct (clos_trans_path H1).
destruct (path_repeat_free_length H y x0 x H2). apply bp_intro with x1. 
apply repeat_free_incl_length. assumption. tauto. 
apply path_restricted_incl with y x;tauto. tauto. 
Qed.

Lemma bounded_path_n_Sn : forall n x y,
bounded_path n x y -> bounded_path (S n) x y.
Proof.
intros. inversion H. apply bp_intro with l. apply le_trans with n. assumption. 
apply le_n_Sn. assumption.
Qed.

Lemma bounded_path_Sn_n_or_Rn : forall n x y,
bounded_path (S n) x y ->
bounded_path n x y \/ exists z : A, R x z /\ bounded_path n z y.
Proof.
intros. inversion H. destruct (le_le_S_dec (length l) n). 
constructor. apply bp_intro with l; assumption. constructor 2. 
destruct l. simpl in l0. pose (le_Sn_O n l0). tauto. exists a. simpl in H0, H1.  
split. tauto. apply bp_intro with l. apply le_S_n. assumption. tauto.
Qed.

Lemma R_bounded_path_n_Sn : forall x y z n,
R x y -> bounded_path n y z -> bounded_path (S n) x z.
Proof.
intros. inversion H0. apply bp_intro with (y::l). simpl. apply le_n_S. assumption. 
simpl. tauto. 
Qed.

End Path.

Lemma path_preserved : forall R R' y l x,
sub_rel R R' -> is_path R x y l -> is_path R' x y l.
Proof.
unfold sub_rel. induction l; intros; simpl in H0 |- * . apply H. assumption. 
split. pose (H x a). tauto. pose (IHl a). tauto.
Qed.

Lemma path_restriction : forall R y l x, is_path R x y l -> is_path (restriction R (x::y::l)) x y l.
Proof.
unfold restriction. induction l; simpl; intros. tauto. split. tauto. simpl in IHl. 
apply path_preserved with (fun x0 y0 : A =>  (a = x0 \/ y = x0 \/ In x0 l) /\
(a = y0 \/ y = y0 \/ In y0 l) /\ R x0 y0). unfold sub_rel. intros. tauto. 
apply IHl. tauto.
Qed.

(* **********************************************************************)
(* bounded_path preserves middle exclusion and decidability for restrictions *)

Section bp_restriction_midex_dec.

Variable R : relation A.

Lemma dec_lem : forall R' R'' x y l,
rel_dec R' -> rel_dec R'' -> 
{z : A| In z l /\ R' x z /\ R'' z y}+{~exists z : A, In z l /\ R' x z /\ R'' z y}.
Proof.
induction l; intros. simpl. constructor 2. intro. destruct H. tauto. 
destruct IHl; try assumption. constructor. destruct s. exists x0. simpl. tauto. 
destruct (X x a). destruct (X0 a y). constructor. exists a. simpl. tauto. 
constructor 2. intro. destruct H. simpl in H. decompose [and or] H.  
rewrite H2 in n0. tauto. assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. 
tauto. contradiction. constructor 2. intro. destruct H. simpl in H.
decompose  [and or] H. rewrite H2 in n0. contradiction.
assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. tauto. contradiction.
Qed. 

Lemma midex_lem : forall R' R'' x y l, rel_midex R' -> rel_midex R'' -> 
(exists z : A,  In z l /\ R' x z /\ R'' z y) \/ (~exists z : A, In z l /\ R' x z /\ R'' z y).
Proof.
induction l; intros. simpl. constructor 2. intro. destruct H1. tauto.  
destruct IHl; try assumption. constructor. destruct H1. exists x0. simpl. tauto. 
destruct (H x a). destruct (H0 a y). constructor. exists a. simpl. tauto. 
constructor 2. intro. destruct H4. simpl in H4. decompose [and or] H4.  
rewrite H7 in H3. tauto. assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. 
tauto. contradiction. constructor 2. intro. destruct H3. simpl in H3. 
decompose  [and or] H3. rewrite H6 in H2. contradiction.
assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. tauto. contradiction.
Qed.

Lemma bounded_path_dec : forall l n,
is_restricted R l -> rel_dec R -> rel_dec (bounded_path R n).
Proof.
unfold rel_dec. induction n; intros. destruct (X x y). constructor. 
apply bp_intro with (nil : list A). trivial. simpl. assumption. constructor 2. intro. 
inversion H0. destruct l0. simpl in H2. contradiction. simpl in H1. 
exact (le_Sn_O (length l0) H1). destruct (IHn H X x y). constructor. 
apply bounded_path_n_Sn. assumption. 
assert ({z : A | In z l /\ R x z /\ bounded_path R n z y}
+{~exists z : A, In z l /\ R x z /\ bounded_path R n z y}).
apply dec_lem; tauto. destruct X0. constructor. destruct s. 
apply R_bounded_path_n_Sn with x0; tauto. 
constructor 2. intro. pose (bounded_path_Sn_n_or_Rn H0). destruct o. contradiction.
destruct H1. assert (exists z : A, In z l /\ R x z /\ bounded_path R n z y). 
exists x0. split. pose (H x x0). tauto. assumption. contradiction.   
Qed.

Lemma bounded_path_midex : forall l n,
is_restricted R l -> rel_midex R -> rel_midex (bounded_path R n).
Proof.
unfold rel_midex. induction n; intros. destruct (H0 x y). constructor. 
apply bp_intro with (nil : list A). trivial. simpl. assumption. constructor 2. intro. 
inversion H2. destruct l0. simpl in H4. contradiction. simpl in H3. 
exact (le_Sn_O (length l0) H3). destruct (IHn H H0 x y). constructor. 
apply bounded_path_n_Sn. assumption. 
assert ((exists z : A,  In z l /\ R x z /\  bounded_path R n z y) \/
(~exists z : A,  In z l /\ R x z /\  bounded_path R n z y)).
apply midex_lem; tauto. destruct H2. destruct H2. constructor. 
apply R_bounded_path_n_Sn with x0; tauto. 
constructor 2. intro. destruct (bounded_path_Sn_n_or_Rn H3). contradiction.
destruct H4. assert (exists z : A, In z l /\ R x z /\ bounded_path R n z y). 
exists x0. split. pose (H x x0). tauto. assumption. contradiction.   
Qed.

Lemma resticted_dec_clos_trans_dec : 
eq_dec A -> rel_dec R -> forall l, is_restricted R l  -> rel_dec (clos_trans A R).
Proof.
do 6 intro. destruct (bounded_path_dec (length l) H X0 x y). 
constructor. apply (bounded_path_clos_trans b). 
constructor 2. intro. pose (clos_trans_bounded_path (eq_dec_midex X) H H0). 
contradiction. 
Qed.

Lemma resticted_midex_clos_trans_midex : 
eq_midex A -> rel_midex R -> forall l, is_restricted R l  -> rel_midex (clos_trans A R).
Proof.
do 6 intro. destruct (bounded_path_midex (length l) H1 H0 x y) . 
constructor. apply (bounded_path_clos_trans H2). 
constructor 2. intro. pose (clos_trans_bounded_path H H1 H3). 
contradiction. 
Qed. 

End bp_restriction_midex_dec.

(***********************************************************************)
(* middle-excluding/decidability of a relation
is equivalent to middle-excluding/decidability of
the transitive closure of every finite restriction of the relation *)

Section em_dec_clos_trans.

Variable R : relation A.

Theorem R_midex_clos_trans_restriction_midex :
eq_midex A -> rel_midex R -> forall l, rel_midex (clos_trans A (restriction R l)).
Proof.
intros. apply resticted_midex_clos_trans_midex with l. assumption. 
apply restriction_midex; assumption. apply restricted_restriction.  
Qed.  

Theorem R_dec_clos_trans_restriction_dec :
eq_dec A -> rel_dec R -> forall l, rel_dec (clos_trans A (restriction R l)).
Proof.
intros. apply resticted_dec_clos_trans_dec with l. assumption. 
apply restriction_dec; assumption. apply restricted_restriction.  
Qed. 

Theorem clos_trans_restriction_dec_R_dec :
(forall l, rel_dec (clos_trans A (restriction R l))) -> rel_dec R.
Proof.
do 3 intro. destruct (X (x::y::nil) x y). constructor.
pose sub_rel_restriction. unfold sub_rel in s. apply s with A (x::y::nil). 
apply clos_trans_restricted_pair. apply restricted_restriction. assumption. 
constructor 2. intro. pose (clos_trans_restriction R x y). tauto.  
Qed. 

Theorem clos_trans_restriction_midex_R_midex :
(forall l, rel_midex (clos_trans A (restriction R l))) -> rel_midex R.
Proof.
do 3 intro. destruct (H (x::y::nil) x y). constructor.
pose sub_rel_restriction. unfold sub_rel in s. apply s with A (x::y::nil). 
apply clos_trans_restricted_pair. apply restricted_restriction. assumption. 
constructor 2. intro. pose (clos_trans_restriction R x y). tauto. 
Qed. 

End em_dec_clos_trans.
End On_transitive_closure.


(* *********************************************************************)
(*  RELATION COMPLETION *)

Section On_relation_completion.

Variable A : Type.

(* *********************************************************************)
(* total *)

Section total.

Variable R : relation A.

Definition trichotomy x y : Prop := R x y \/ x=y \/ R y x.

Definition total l : Prop := forall x y,  In x l -> In y l -> trichotomy x y.

End total.

Lemma trichotomy_preserved : forall R R' x y,
sub_rel R R' -> trichotomy R x y -> trichotomy R' x y.
Proof.
unfold sub_rel, trichotomy. intros. pose (H x y). pose (H y x). tauto.
Qed. 

(* *********************************************************************)
(* add *)

Section try_add_arc.

Variable R : relation A.

Inductive try_add_arc (x y : A) : A -> A -> Prop :=
| keep : forall z t, R z t -> try_add_arc x y z t
| try_add : x<>y -> ~R y x ->  try_add_arc x y x y.

Lemma sub_rel_try_add_arc : forall x y, sub_rel R (try_add_arc x y).
Proof.
unfold sub_rel. intros. constructor. assumption. 
Qed.

Lemma try_add_arc_sym :  forall x y z t,
try_add_arc x y z t -> try_add_arc x y t z -> R z t.
Proof.
intros. inversion H. assumption. inversion H0. contradiction. 
rewrite H3 in H7. contradiction. 
Qed.

Lemma not_try_add_arc : rel_midex R -> forall x y, x<>y -> ~try_add_arc x y x y -> R y x. 
Proof.
intros. destruct (H y x). assumption. absurd (try_add_arc x y x y). assumption. 
constructor 2; assumption.  
Qed. 

Lemma restricted_try_add_arc : forall x y l, 
In x l -> In y l -> is_restricted R l -> is_restricted (try_add_arc x y) l.
Proof.
unfold is_restricted. intros. inversion H2. apply H1. assumption. 
rewrite <- H5. rewrite <- H6. tauto.  
Qed.

Lemma try_add_arc_dec : eq_dec A -> forall x y,  rel_dec R -> rel_dec (try_add_arc x y).
Proof.
repeat intro. destruct (X0 x0 y0). do 2 constructor. assumption. 
destruct (X x0 y0). constructor 2. intro. inversion H; contradiction. 
destruct (X0 y0 x0). constructor 2. intro. inversion H; contradiction. 
destruct (X x x0). destruct (X y y0). rewrite e. rewrite e0. 
constructor. constructor 2; assumption. 
constructor 2. intro. inversion H; contradiction. 
constructor 2. intro. inversion H; contradiction. 
Qed.

Lemma try_add_arc_midex : eq_midex A -> forall x y, rel_midex R -> rel_midex (try_add_arc x y).
Proof.
do 6 intro. destruct (H0 x0 y0). do 2 constructor. assumption. 
destruct (H x0 y0). constructor 2. intro. inversion H3; contradiction. 
destruct (H0 y0 x0). constructor 2. intro. inversion H4; contradiction. 
destruct (H x x0). destruct (H y y0). rewrite H4. rewrite H5. 
constructor. constructor 2; assumption. 
constructor 2. intro. inversion H6; contradiction. 
constructor 2. intro. inversion H5; contradiction. 
Qed.

Lemma try_add_arc_trichotomy : eq_midex A -> rel_midex R ->
forall x y, trichotomy (try_add_arc x y) x y.
Proof.
unfold trichotomy. intros. destruct (H x y). tauto. destruct (H0 x y). do 2 constructor. assumption. 
destruct (H0 y x). do 2 constructor 2. constructor. assumption. constructor. 
constructor 2; assumption. 
Qed.

Lemma trichotomy_restriction : forall x y l,
In x l -> In y l -> trichotomy R x y -> trichotomy (restriction R l) x y.
Proof.
unfold trichotomy, restriction. intros. tauto. 
Qed.

Lemma  path_try_add_arc_path : forall t x y l z, 
~(x=z \/ In x l) \/ ~(y=t \/ In y l) -> is_path (try_add_arc x y) z t l -> is_path R z t l. 
Proof.
induction l; simpl; intros. inversion H0; tauto. 
destruct H0. split. inversion H0. assumption. rewrite H5 in H. tauto. 
apply IHl. pose sym_equal. pose (e A x a). tauto. assumption. 
Qed.

Lemma trans_try_add_arc_sym : forall x y z t,
transitive A R -> try_add_arc x y z t -> try_add_arc x y t z -> R z z.
Proof.
unfold transitive. intros. apply H with t; apply try_add_arc_sym with x y; assumption. 
Qed.

Lemma trans_bounded_path_try_add_arc : eq_midex A -> forall x y z n,
transitive A R -> bounded_path (try_add_arc x y ) n z z -> R z z.
Proof.
intros. induction n. inversion H1. destruct l. simpl in H2. 
apply trans_try_add_arc_sym with x y z; assumption. 
simpl in H1. pose (le_Sn_O (length l) H2). contradiction. apply IHn.
inversion H1. clear IHn H1 H4 H5 x0 y0. 
(* repeat_free *)
destruct (path_repeat_free_length (try_add_arc x y) H z l z H3). decompose [and] H1.
assert (length x0 <= S n). apply le_trans with (length l); assumption.
clear H1 H2 H3 H6 H7 H8. 
(* x0=nil *) 
destruct x0. exists (nil : list A). apply le_O_n. tauto. 
(* length x0 = 1 *) 
destruct x0; simpl in * |- . exists (nil : list A). apply le_O_n. simpl. 
apply sub_rel_try_add_arc. apply trans_try_add_arc_sym with x y a; tauto. 
(* length x0 >= 2*)
destruct H10.  destruct H2. 
inversion H1; inversion H2.
exists (a0::x0). simpl. apply le_S_n. assumption.
simpl. split. apply (sub_rel_try_add_arc). apply H0 with a; assumption. assumption.  
(**)
absurd (R a0 a). tauto. apply transitive_sub_rel_clos_trans. assumption. 
apply path_clos_trans with (x0++(z::nil)). apply path_app. 
apply path_try_add_arc_path with x y. rewrite H13. tauto. assumption. simpl. assumption.  
(**)
absurd (R a z). tauto. apply transitive_sub_rel_clos_trans. assumption. 
apply path_clos_trans with (a0::x0). split. assumption.  
apply path_try_add_arc_path with x y. rewrite H10. tauto. assumption. 
(**) 
rewrite H8 in H13. tauto. 
Qed.

Lemma try_add_arc_irrefl : eq_midex A -> forall x y, 
transitive A R ->  irreflexive R -> irreflexive (clos_trans A (try_add_arc x y)).
Proof.
do 7 intro. apply H1 with x0. destruct (clos_trans_path H2).
apply trans_bounded_path_try_add_arc with x y (length x1); try assumption.
apply bp_intro with x1; trivial. 
Qed.

End try_add_arc.

(***********************************************************************)
(* try_add_arc_one_to_many: multiple try_add_arc with one list *)

Section try_add_arc_one_to_many.

Variable R : relation A.

Fixpoint try_add_arc_one_to_many (x : A)(l : list A){struct l} : relation A :=
match l with
| nil => R
| y::l' => clos_trans A (try_add_arc (try_add_arc_one_to_many x l') x y) 
end.

Lemma sub_rel_try_add_arc_one_to_many : forall x l, sub_rel R (try_add_arc_one_to_many x l). 
Proof.
induction l; simpl; intros. apply reflexive_sub_rel. 
apply transitive_sub_rel with (try_add_arc_one_to_many x l). assumption. 
apply transitive_sub_rel with (try_add_arc (try_add_arc_one_to_many x l) x a).
apply sub_rel_try_add_arc. apply sub_rel_clos_trans. 
Qed. 

Lemma restricted_try_add_arc_one_to_many : forall l x l', 
In x l -> incl l' l -> is_restricted R l -> is_restricted (try_add_arc_one_to_many x l') l.
Proof.
induction l'; simpl; intros. assumption. apply restricted_clos_trans. 
apply restricted_try_add_arc. assumption. apply H0. simpl. tauto. apply IHl'. 
assumption. exact (incl_elim_cons H0). assumption. 
Qed.

Lemma try_add_arc_one_to_many_dec : eq_dec A -> forall x l l',
In x l -> incl l' l -> is_restricted R l -> rel_dec R -> rel_dec (try_add_arc_one_to_many x l').
Proof.
induction l'; simpl; intros. assumption. pose (incl_elim_cons H0). 
apply resticted_dec_clos_trans_dec with l. assumption. 
apply try_add_arc_dec. assumption. apply IHl'; tauto. 
apply restricted_try_add_arc. assumption. apply H0. simpl. tauto. 
apply restricted_try_add_arc_one_to_many; simpl; tauto. 
Qed.

Lemma try_add_arc_one_to_many_midex : eq_midex A -> forall x l l',
In x l -> incl l' l -> is_restricted R l -> rel_midex R ->  rel_midex (try_add_arc_one_to_many x l').
Proof.
induction l'; simpl; intros. assumption. pose (incl_elim_cons H1). 
apply resticted_midex_clos_trans_midex with l. assumption. 
apply try_add_arc_midex. assumption. apply IHl'; tauto. 
apply restricted_try_add_arc. assumption. apply H1. simpl. tauto. 
apply restricted_try_add_arc_one_to_many; simpl; tauto. 
Qed.

Lemma try_add_arc_one_to_many_trichotomy : eq_midex A -> rel_midex R -> forall x y l l',
In y l' -> In x l ->  incl l' l -> is_restricted R l -> trichotomy (try_add_arc_one_to_many x l') x y.
Proof.
induction l';  simpl; intros. contradiction. pose (incl_elim_cons H3). 
apply trichotomy_preserved with (try_add_arc (try_add_arc_one_to_many x l') x a). 
apply sub_rel_clos_trans. destruct H1. rewrite H1. 
apply try_add_arc_trichotomy. assumption. apply try_add_arc_one_to_many_midex with l; assumption. 
apply trichotomy_preserved with (try_add_arc_one_to_many x l'). apply sub_rel_try_add_arc. tauto. 
Qed.

Lemma try_add_arc_one_to_many_irrefl : eq_midex A -> forall x l l',
is_restricted R l -> transitive A R -> irreflexive R -> irreflexive (try_add_arc_one_to_many x l').
Proof.
induction l'; simpl; intros. assumption.  
apply try_add_arc_irrefl. assumption. 
destruct l'; simpl. assumption. apply transitive_clos_trans. tauto. 
Qed.

End try_add_arc_one_to_many.


(***********************************************************************)
(* try_add_arc_many_to_many: multiple try_add_arc with two lists *)

Section try_add_arc_many_to_many.

Variable R : relation A.

Fixpoint try_add_arc_many_to_many (l' l: list A){struct l'}: relation A :=
match l' with
| nil => R
| x::l'' => try_add_arc_one_to_many (try_add_arc_many_to_many l'' l) x l
end.

Lemma sub_rel_try_add_arc_many_to_many : forall l l', sub_rel R (try_add_arc_many_to_many l' l). 
Proof. 
induction l'; simpl; intros. apply reflexive_sub_rel. 
apply transitive_sub_rel with (try_add_arc_many_to_many l' l). assumption. 
apply sub_rel_try_add_arc_one_to_many. 
Qed.

Lemma restricted_try_add_arc_many_to_many : forall l l', incl l' l ->
is_restricted R l -> is_restricted (try_add_arc_many_to_many l' l) l. 
Proof.
induction l'; simpl; intros. assumption. 
apply restricted_try_add_arc_one_to_many. apply H. simpl. tauto. apply incl_refl. 
apply IHl'. exact (incl_elim_cons H). assumption. 
Qed.

Lemma try_add_arc_many_to_many_dec : eq_dec A ->  forall l l',
incl l' l -> is_restricted R l -> rel_dec R -> rel_dec (try_add_arc_many_to_many l' l).
Proof.
induction l'; simpl; intros. assumption. pose (incl_elim_cons H). 
apply try_add_arc_one_to_many_dec with l. assumption. apply H. simpl. tauto. apply incl_refl. 
apply  restricted_try_add_arc_many_to_many; assumption. tauto. 
Qed.

Lemma try_add_arc_many_to_many_midex : eq_midex A ->  forall l l',
incl l' l -> is_restricted R l -> rel_midex R -> rel_midex (try_add_arc_many_to_many l' l).
Proof.
induction l'; simpl; intros. assumption. pose (incl_elim_cons H0). 
apply try_add_arc_one_to_many_midex with l. assumption. apply H0. simpl. tauto. apply incl_refl. 
apply  restricted_try_add_arc_many_to_many; assumption. tauto. 
Qed.

Lemma try_add_arc_many_to_many_trichotomy : eq_midex A -> rel_midex R -> forall x y l l',
is_restricted R l -> incl l' l -> In y l -> In x l' -> trichotomy (try_add_arc_many_to_many l' l) x y.
Proof.
induction l';  simpl; intros. contradiction. pose (incl_elim_cons H2). 
destruct H4. rewrite H4. 
apply try_add_arc_one_to_many_trichotomy with l; try assumption. 
apply try_add_arc_many_to_many_midex; assumption. 
rewrite <- H4. apply H2. simpl. tauto. apply incl_refl. 
apply restricted_try_add_arc_many_to_many; assumption. 
apply trichotomy_preserved with  (try_add_arc_many_to_many l' l). 
apply sub_rel_try_add_arc_one_to_many. tauto. 
Qed.

Lemma try_add_arc_many_to_many_irrefl : eq_midex A -> forall l l',
incl l' l -> is_restricted R l -> transitive A R -> irreflexive R -> irreflexive (try_add_arc_many_to_many l' l).
Proof.
induction l'; simpl; intros. assumption. pose (incl_elim_cons H0).   
apply try_add_arc_one_to_many_irrefl with l. assumption. 
apply restricted_try_add_arc_many_to_many; assumption. 
destruct l'; simpl. assumption. destruct l. pose (i a0). simpl in i0. tauto. 
simpl. apply transitive_clos_trans. tauto.   
Qed. 

End try_add_arc_many_to_many.

Section LETS.

Variable R : relation A.
Variable l : list A.

Definition LETS : relation A := try_add_arc_many_to_many (clos_trans A (restriction R l)) l l.

Lemma LETS_sub_rel_clos_trans : sub_rel (clos_trans A (restriction R l)) LETS.
Proof.
intros. unfold LETS. apply sub_rel_try_add_arc_many_to_many. 
Qed.

Lemma LETS_sub_rel : sub_rel (restriction R l) LETS.
Proof.
intros. unfold LETS. apply transitive_sub_rel with (clos_trans A (restriction R l)). 
apply sub_rel_clos_trans. apply  LETS_sub_rel_clos_trans. 
Qed.

Lemma LETS_restricted : is_restricted LETS l.
Proof.
unfold sub_rel, LETS. intros. apply restricted_try_add_arc_many_to_many. apply incl_refl. 
apply restricted_clos_trans. apply restricted_restriction.  
Qed.

Lemma LETS_transitive : transitive A LETS.
Proof.
intros. unfold LETS. destruct l; simpl; apply transitive_clos_trans.
Qed.

Lemma LETS_irrefl : eq_midex A -> 
(irreflexive (clos_trans A (restriction R l)) <-> irreflexive LETS).
Proof.
split;intros. unfold LETS. apply try_add_arc_many_to_many_irrefl; try assumption. apply incl_refl. 
apply restricted_clos_trans. apply restricted_restriction. apply transitive_clos_trans.  
apply irreflexive_preserved with LETS. apply LETS_sub_rel_clos_trans. assumption. 
Qed. 

Lemma LETS_total : eq_midex A -> rel_midex R -> total LETS l.
Proof.
unfold LETS, total. intros. pose (R_midex_clos_trans_restriction_midex H H0 l). 
apply try_add_arc_many_to_many_trichotomy; try assumption. apply restricted_clos_trans. 
apply restricted_restriction. apply incl_refl. 
Qed.

Lemma LETS_dec : eq_dec A -> rel_dec R -> rel_dec LETS.
Proof.
intros. unfold LETS. apply try_add_arc_many_to_many_dec. assumption. apply incl_refl. 
apply restricted_clos_trans. apply restricted_restriction.  
apply R_dec_clos_trans_restriction_dec; assumption.  
Qed.

Lemma LETS_midex : eq_midex A -> rel_midex R -> rel_midex LETS.
Proof.
intros. unfold LETS. apply try_add_arc_many_to_many_midex. assumption. apply incl_refl. 
apply restricted_clos_trans. apply restricted_restriction.  
apply R_midex_clos_trans_restriction_midex; assumption.  
Qed.

End LETS.


(* Linear Extension *)

Definition linear_extension R l R' := is_restricted R' l /\ sub_rel (restriction R l) R' /\ 
transitive A R' /\ irreflexive R' /\ total R' l.

Lemma local_global_acyclic : forall R : relation A,
(forall l, exists R', sub_rel (restriction R l) R' /\ transitive A R' /\ irreflexive R') ->
irreflexive (clos_trans A R).
Proof.
intros. do 2 intro. destruct (clos_trans_path H0). 
assert (clos_trans A (restriction R (x::x::x0)) x x). apply path_clos_trans with x0. 
apply path_restriction. assumption. destruct (H (x::x::x0)). destruct H3. destruct H4. 
apply H5 with x. apply transitive_sub_rel_clos_trans. assumption. 
apply clos_trans_monotonic with (restriction R (x :: x :: x0)). assumption. assumption. 
Qed.

Lemma total_order_eq_midex: 
(forall l, exists R, transitive A R /\ irreflexive R /\ total R l /\ rel_midex R) ->
eq_midex A. 
Proof.
do 3 intro. destruct (H (x::y::nil)). decompose [and] H0. destruct (H5 x y); destruct (H5 y x). 
absurd (x0 x x). apply H3. apply H1 with y; assumption. 
constructor 2. intro. rewrite H7 in H4. rewrite H7 in H6. contradiction.
constructor 2. intro. rewrite H7 in H4. rewrite H7 in H6. contradiction. 
destruct (H2 x y); simpl; try tauto. 
Qed.

Theorem linearly_extendable :  forall R, rel_midex R ->
(eq_midex A /\ irreflexive (clos_trans A R) <-> 
forall l, exists R', linear_extension R l R' /\ rel_midex R').
Proof.
unfold linear_extension. split; intros. exists (LETS R l). split. split. apply LETS_restricted. split. 
apply LETS_sub_rel. split. apply LETS_transitive. split. destruct (LETS_irrefl R l). 
tauto. apply H1. apply irreflexive_preserved with (clos_trans A R).
unfold sub_rel. apply clos_trans_monotonic. apply sub_rel_restriction. tauto.
apply LETS_total; tauto. apply LETS_midex; tauto. 
(**)
split. apply total_order_eq_midex. intro. destruct (H0 l). exists x. tauto. 
apply local_global_acyclic. intro. destruct (H0 l). exists x. tauto. 
Qed.

(* Topological Sorting *)

Definition non_uni_topo_sortable R := 
forall l, exists  R',
linear_extension R l (fun x y => R' x y=true).

Definition uni_topo_sortable R := 
{F | forall l, linear_extension R l (fun x y => F l x y=true )}.

Definition asym R SC :=
forall x y : A, x<>y -> ~R x y -> ~R y x -> ~(SC (x::y::nil) x y /\ SC (y::x::nil) x y). 

Definition asym_topo_sortable R := 
{F : list A -> A -> A -> bool | let G:= (fun l x y => F l x y=true) in 
asym R G /\ forall l, linear_extension R l (G l)}.

Lemma total_order_eq_dec : 
{F : list A -> A -> A -> bool | forall l, let G := fun x y => F l x y=true in 
transitive A G /\ irreflexive G /\ total G l} ->
eq_dec A. 
Proof.
unfold transitive, irreflexive, total, trichotomy. do 3 intro. destruct X.  pose (a (x::y::nil)). 
assert ({x0 (x::y::nil) x y=true}+{x0  (x::y::nil) x y=false}). case (x0 (x::y::nil) x y); tauto. 
assert ({x0 (x::y::nil) y x=true}+{x0 (x::y::nil) y x=false}). case (x0 (x::y::nil) y x); tauto. 
destruct a0. destruct H2. pose (H3 x y). simpl in o. 
destruct H. constructor 2. intro. rewrite H in e. rewrite H in H2. exact (H2 y e). 
destruct H0. constructor 2. intro. rewrite H in e0. rewrite H in H2. exact (H2 y e0). 
constructor. destruct o; try tauto. rewrite H in e. inversion e. destruct H. assumption. 
rewrite H in e0. inversion e0. 
Qed.

Lemma LETS_asym : forall R, asym R (LETS R). 
Proof.
unfold LETS. do 7 intro. simpl in *|- . destruct H2. 
assert (is_restricted (restriction R (x :: y :: nil)) (x::y::nil)). apply restricted_restriction. 
assert (is_restricted (try_add_arc (clos_trans A (restriction R (x :: y :: nil))) y y) (x::y::nil)). 
apply restricted_try_add_arc; simpl; try tauto. apply restricted_clos_trans. assumption.
assert (is_restricted (try_add_arc (clos_trans A (try_add_arc (clos_trans A (restriction R (x :: y :: nil))) y y)) y x) (x::y::nil)). 
apply restricted_try_add_arc; simpl; try tauto. apply restricted_clos_trans. assumption.
assert (is_restricted (try_add_arc (clos_trans A (try_add_arc (clos_trans A (try_add_arc (clos_trans A (restriction R (x :: y :: nil))) y y)) y x)) x y) (x::y::nil)).
apply restricted_try_add_arc; simpl; try tauto. apply restricted_clos_trans. assumption.
assert (is_restricted (try_add_arc (clos_trans A (try_add_arc (clos_trans A (try_add_arc (clos_trans A (try_add_arc (clos_trans A (restriction R (x :: y :: nil))) y y)) y x)) x y)) x x)  (x::y::nil)).
apply restricted_try_add_arc; simpl; try tauto. apply restricted_clos_trans. assumption.
(**)
pose (clos_trans_restricted_pair H8 H2). inversion t; try tauto. clear H10 H11 z t0.
pose (clos_trans_restricted_pair H7 H9). inversion t0. clear H11 H12 z t1.
pose (clos_trans_restricted_pair H6 H10). inversion t1; try tauto. clear H12 H13 z t2.
pose (clos_trans_restricted_pair H5 H11). inversion t2. clear H13 H14 z t3.
assert (restriction R (x :: y :: nil) x y). apply clos_trans_restricted_pair; assumption. 
unfold restriction in H13. tauto. tauto.
(**)
absurd (clos_trans A (try_add_arc (clos_trans A (try_add_arc (clos_trans A (restriction R (x :: y :: nil))) y y)) y x) y x). 
assumption. constructor. constructor 2. intro. rewrite H14 in H10. tauto. 
intro. pose (clos_trans_restricted_pair H5 H14). inversion t1; try tauto. clear H16 H17 z t2. 
pose (clos_trans_restricted_pair H4 H15). unfold restriction in r. tauto. 
Qed.

Theorem possible_asym_topo_sort : forall R, 
eq_dec A -> rel_dec R -> irreflexive (clos_trans A R) -> asym_topo_sortable R. 
Proof.
do 4 intro. assert (forall l, rel_dec (LETS R l)). intro. apply LETS_dec; assumption. 
pose (eq_dec_midex X). pose (rel_dec_midex X0).
exists (fun l x y => if (X1 l x y) then true else false). simpl. split.
do 5 intro. case (X1 (x :: y :: nil) x y). case (X1 (y :: x :: nil) x y). 
do 2 intro. absurd (LETS R (x :: y :: nil) x y /\ LETS R (y :: x :: nil) x y). 
apply LETS_asym; assumption. tauto. do 3 intro. destruct H3. inversion H4. 
do 2 intro. destruct H3. inversion H3. split.
do 3 intro. destruct (X1 l x y). apply (LETS_restricted R l x y). assumption. inversion H0. split. 
do 3 intro. destruct (X1 l x y). trivial. absurd (LETS R l x y). assumption.
apply LETS_sub_rel_clos_trans. apply sub_rel_clos_trans. assumption. split. 
do 5 intro. destruct (X1 l x y). destruct (X1 l y z). pose (LETS_transitive R l x y z l0 l1). 
destruct (X1 l x z). trivial. contradiction. inversion H1. inversion H0. split. 
do 2 intro. destruct (X1 l x x). absurd (LETS R l x x). destruct (LETS_irrefl R l). 
assumption. apply H1. apply irreflexive_preserved with (clos_trans A R). 
apply clos_trans_monotonic. apply sub_rel_restriction. assumption. assumption. inversion H0. 
do 4 intro. unfold trichotomy. destruct (X1 l x y). tauto. destruct (X1 l y x). tauto. 
destruct (LETS_total l e r x y); tauto.  
Qed. 

Theorem asym_topo_sortable_topo_sortable : forall R, 
asym_topo_sortable R -> uni_topo_sortable R.
Proof.
intros. exists (let (f,s):= X in f). intros. destruct X. destruct a.  pose (H0 l). 
unfold linear_extension in *|-* . tauto. 
Qed. 

Theorem asym_topo_sortable_rel_dec : forall R, 
rel_midex R -> asym_topo_sortable R -> rel_dec R.
Proof.
unfold asym_topo_sortable, linear_extension. 
intros. assert (irreflexive (clos_trans A R)). apply local_global_acyclic. 
intro. exists (fun x y => (let (f,s):= X in f) l x y=true). destruct X. destruct a. pose (H1 l). tauto. 
assert (eq_dec A). apply total_order_eq_dec. exists (let (f,s):= X in f). intro. destruct X. 
destruct a. pose (H2 l). split; tauto. 
(**)
do 2 intro. destruct (X0 x y). rewrite e. constructor 2. intro. apply (H0 y). constructor. assumption. 
destruct X. destruct a. pose (H1 x y). decompose [and] (H2 (x::y::nil)). 
destruct (sumbool_of_bool (x0 (x::y::nil) x y)). destruct (sumbool_of_bool (x0 (y::x::nil) x y)). 
constructor. destruct (H x y). assumption. destruct (H y x). absurd (x0 (x :: y :: nil) y x=true). 
intro. apply (H6 x). apply H4 with y; assumption. apply H5. unfold restriction. simpl. tauto.
generalize n0 e e0. case (x0 (x :: y :: nil) x y); case (x0 (y :: x :: nil) x y); tauto.  
constructor 2. intro. absurd (x0 (y :: x :: nil) x y=true). intro. rewrite e0 in H9. inversion H9. 
pose (H2 (y::x::nil)). decompose [and] a. apply H11. unfold restriction. simpl. tauto. 
constructor 2. intro. absurd (x0 (x::y:: nil) x y=true). intro. rewrite e in H9. inversion H9. 
apply H5. unfold restriction. simpl. tauto. 
Qed. 

Theorem uni_topo_sortable_non_uni_topo_sortable : forall R, 
 uni_topo_sortable R -> non_uni_topo_sortable R.
Proof.
repeat intro. destruct X. exists (x l). apply l0.   
Qed.

Theorem rel_dec_uni_topo_sortable_eq_dec :  forall R, 
rel_dec R -> uni_topo_sortable R -> eq_dec A.
Proof.
intros. apply total_order_eq_dec. exists (let (first,second):=X0 in first). 
destruct X0. intro. pose (l l0). destruct l1. split; tauto. 
Qed. 

Theorem rel_dec_non_uni_topo_sortable_acyclic :  forall R, 
rel_dec R -> non_uni_topo_sortable R -> irreflexive (clos_trans A R).
Proof.
intros. apply local_global_acyclic. intro. destruct (H l). exists (fun x0 y => x x0 y=true). 
destruct H0. tauto. 
Qed.

End On_relation_completion.

