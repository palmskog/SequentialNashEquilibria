(* *****************************************************************)
(* Coq formalisation accompanying                                  *)
(* ["A Constructive Approach to Sequential Nash Equilibria"],      *)
(* Information Processing Letters, 97, 2006.                       *)
(*                                                                 *)
(* Edited with more meaningful identifiers.                        *)
(* Oct. 2006: added subgame perfectness and One Deviation Property *)
(*                                                                 *)
(* Author: Rene Vestergaard, JAIST.                                *)
(*                                                                 *)
(* Developed in Coq, v8.0                                          *)
(*                                                                 *)
(* All rights reserved by the author.                              *)
(* *****************************************************************)

(* == Requirements == *)

Require Import Le.
Require Import Bool_nat.

Section const_SeqNashEq.

(* == Basic Structures == *)

Variable Agents : Type.

Definition Payoff := nat.

Definition Payoffs := Agents -> Payoff.

Inductive Game : Type :=
| gLeaf : Payoffs -> Game
| gNode : Agents -> Game -> Game -> Game.

Inductive Choices : Set := | left | right.

Inductive Strategy : Type :=
| sLeaf : Payoffs -> Strategy
| sNode : Agents -> Choices -> Strategy -> Strategy -> Strategy.

(* == Misc Fcts == *)

Fixpoint stratPO (s:Strategy) {struct s} : Payoffs :=
match s with
| (sLeaf po) => po
| (sNode a c sl sr) => 
    match c with
    |  left => (stratPO sl)
    | right => (stratPO sr)
    end
  end.

Fixpoint s2g (s:Strategy) {struct s} : Game :=
match s with
| (sLeaf po) => (gLeaf po)
| (sNode a c sl sr) 
  => (gNode a (s2g sl) (s2g sr))
end.

(* == Equilibria == *)

Fixpoint agentConv (a:Agents) (s1 s2:Strategy) {struct s1} : Prop :=
match s1 with
| (sLeaf po1) => match s2 with
                 | (sLeaf po2) => forall a, po1 a = po2 a
                 | (sNode _ _ _ _) => False
                 end
| (sNode a1 c1 s11 s12) => match s2 with
                           | (sLeaf _) => False
                           | (sNode a2 c2 s21 s22)
                              => a1 = a2 /\ (a1 = a \/ c1 = c2)
                                 /\ agentConv a s11 s21
                                 /\ agentConv a s12 s22
                           end
end.

Definition NashEq (s:Strategy) : Prop := 
 forall s', forall a, agentConv a s s' -> (stratPO s') a <= (stratPO s) a.

(* == Backward Induction == *)

Fixpoint BI (s:Strategy) {struct s} : Prop :=
match s with
| (sLeaf po) => True
| (sNode a c sl sr) => 
   (BI sl) /\ (BI sr) /\
   match c with
   |  left => (stratPO sr) a <= (stratPO sl) a
   | right => (stratPO sl) a <= (stratPO sr) a
   end
end.

Fixpoint compBI (g:Game) {struct g} : Strategy :=
match g with
| (gLeaf po) => (sLeaf po)
| (gNode a gl gr)  => 
   let sl := compBI gl in
   let sr := compBI gr in
     if (le_ge_dec ((stratPO sl) a) 
                   ((stratPO sr) a))
     then (sNode a right sl sr)
     else (sNode a  left sl sr)
end.

(* == Lemmas == *)

Lemma compBI_is_BI : forall g, BI (compBI g).
Proof.
induction g.
(* gLeaf case *) unfold compBI. unfold BI. trivial.
(* gNode case *) unfold compBI. fold compBI. elim le_ge_dec.
  (* le subsub-case *) intro leAssm. unfold BI. fold BI.
                       split. apply IHg1.
                       split. apply IHg2. apply leAssm.
  (* ge subsub-case *) intro geAssm. unfold BI. fold BI.
                       split. apply IHg1.
                       split. apply IHg2. apply geAssm.
Qed.

Lemma s2g_inv_compBI : forall g, g = s2g (compBI g).
Proof.
induction g.
(* gLeaf case *) unfold compBI. unfold s2g. trivial.
(* gNode case *) unfold compBI. fold compBI. elim le_ge_dec.
  (* le sub-case *) intro. unfold s2g. fold s2g.
                    apply f_equal3 with Agents Game Game.
                    trivial. apply IHg1. apply IHg2.
  (* ge sub-case *) intro. unfold s2g. fold s2g.
                    apply f_equal3 with Agents Game Game.
                    trivial. apply IHg1. apply IHg2.
Qed.

Lemma BI_is_NashEq : forall s, BI s -> NashEq s.
Proof.
induction s.
(* sLeaf case *) intro. unfold NashEq. intros s' a. case s'.
  (* sLeaf on sLeaf *) simpl. intros p0 pEQ. rewrite pEQ. trivial. 
  (* sLeaf on sNode *) simpl. intros. contradiction.  
(* sNode case *) simpl. intros [BIs1 [BIs2 Majorise]].
                 unfold NashEq. intros s' a0. case s'.
  (* sNode on sLeaf *) simpl. intros. contradiction.  
  (* sNode on sNode *) simpl. intros a1 c0 s1a s2a [Equal_a [disj [aC_sx1 aC_sx2]]]. 
                       subst a. unfold stratPO. fold stratPO. generalize Majorise disj.
                       clear Majorise disj. elim c.
                       (* c = lchoice *) elim c0.
                         (* c0 = lchoice *) intros _ _. generalize (IHs1 BIs1). unfold NashEq.
                                            intro Eq_s1. exact (Eq_s1 s1a a0 aC_sx1).
                         (* c0 = rchoice *) intros Majorise_s2s1 disj. case disj.
                           (* a1 = a0 case *) intro. subst a1. generalize (IHs2 BIs2). unfold NashEq.
                                              intro Eq_s2s'. generalize (Eq_s2s' s2a a0 aC_sx2).
                                              intro Majorise_s2as2.
                                              apply (le_trans ((stratPO s2a) a0) ((stratPO s2) a0) ((stratPO s1) a0)
                                                     Majorise_s2as2 Majorise_s2s1).
                           (* left = right *) intro Contradiction. discriminate Contradiction.
                       (* c = rchoice *) elim c0.
                         (* c0 = lchoice *) intros Majorise_s1s2 disj. case disj.
                           (* a1 = a0 case *) intro. subst a1. generalize (IHs1 BIs1). unfold NashEq.
                                              intro Eq_s1s'. generalize (Eq_s1s' s1a a0 aC_sx1).
                                              intro Majorise_s1as1.
                                              apply (le_trans ((stratPO s1a) a0) ((stratPO s1) a0) ((stratPO s2) a0)
                                                     Majorise_s1as1 Majorise_s1s2).
                           (* right = left *) intro Contradiction. discriminate Contradiction.
                         (* c0 = rchoice *) intros _ _.  generalize (IHs2 BIs2). unfold NashEq.
                                            intro Eq_s2. exact (Eq_s2 s2a a0 aC_sx2).
Qed.

(* == Deskolemisation tactic == *)
(* The input of Jevgenijs Sallinens and Dimitri Hendriks   *)
(* to the deskolem_apply tactic is gratefully acknowledged *)

Ltac deskolem_apply skolemised :=
   let var := fresh in
(* parameterise the variable of the current universal goal *)
   intro var;
(* get the skolemised result into play *)
   destruct skolemised as [comp_witness generic_evidence];
(* compute the primitive witness for the current existential goal *)
   exists (comp_witness var);
(* the old argument for the central property can now be re-used *)
   apply generic_evidence.

(* == Theorems == *)

Theorem BI_fctExists : 
 exists F, forall g, BI (F g) /\ g = s2g (F g).
Proof.
exists compBI. intro g. split.
  (*  BI part *) exact (compBI_is_BI g).
  (* Inv part *) exact (s2g_inv_compBI g).
Qed.

Theorem NashEq_fctExists : 
 exists F, forall g, NashEq (F g) /\ g = s2g (F g).
Proof.
exists compBI. intro g. split.
  (*  Eq part *) apply BI_is_NashEq. exact (compBI_is_BI g).
  (* Inv part *) exact (s2g_inv_compBI g).
Qed.

Theorem NashEq_Exists : 
 forall g, exists s, NashEq s /\ g = s2g s.
Proof.
deskolem_apply NashEq_fctExists.
Qed.

(* = Alternative route: last two steps reversed = *)

Theorem BI_Exists : 
 forall g, exists s, BI s /\ g = s2g s.
Proof.
deskolem_apply BI_fctExists.
Qed.

Theorem NashEq_Exists_B : 
 forall g, exists s, NashEq s /\ g = s2g s.
Proof.
intro g.
exists (compBI g). split.
 (*  Eq part *) apply BI_is_NashEq. exact (compBI_is_BI g).
 (* Inv part *) exact (s2g_inv_compBI g).
Qed.

(* ===== Subgame Perfectness ===== *)

Fixpoint SGP (s:Strategy) {struct s} : Prop :=
match s with
| (sLeaf po) => True
| (sNode a c sl sr) => 
   (SGP sl) /\ (SGP sr) /\ (NashEq s)
end.

Lemma SGP_is_NashEq : forall s, SGP s -> NashEq s.
Proof.
  induction s.
(* sLeaf case *)
  unfold NashEq. intros _.  induction s'. 
  (* sLeaf case *)
    intros. unfold stratPO. unfold agentConv in H. rewrite (H a). trivial. 
  (* sNode case *)
    unfold agentConv. intros. contradiction.
(* sNode case *)
  unfold SGP. intros [_ [_ done]]. trivial.
Qed. 

Lemma agentConv_id : forall a s, agentConv a s s.
Proof.
  induction s.
  (* sLeaf case *)
    unfold agentConv. trivial.
  (* sNode case *)
    unfold agentConv. auto.
Qed.

Theorem OneDeviation : forall s, BI s <-> SGP s.
Proof.
  split.
  (* BI_is_SGP *)
  induction s.
  (* sLeaf case *)
    intro. unfold SGP. trivial.
  (* sNode case *) 
    simpl. intros [BIs1 [BIs2 Majorise]].
    (* IHs1 *)
      split. apply (IHs1 BIs1).
    (* IHs2 *)
      split. apply (IHs2 BIs2).
    (* BI_is_NashEq *)
      apply BI_is_NashEq. unfold BI. auto.
  (* SGP_is_BI *)
  induction s. 
  (* sLeaf case *)
    unfold BI. trivial. 
  (* sNode case *)
    simpl. intros [SGPs1 [SGPs2 Nashs]].
    (* IHs1 *)
    split. apply (IHs1 SGPs1). 
    (* IHs2 *)
    split. apply (IHs2 SGPs2).
    (* One Deviation *) 
      generalize Nashs. clear Nashs. case c.
      (* left case *)
        unfold NashEq. intros. generalize (Nashs (sNode a right s1 s2) a).
        unfold agentConv. fold agentConv. intro cMaj. simpl in cMaj.
        apply cMaj. split. trivial. split. apply or_introl. trivial. split; apply agentConv_id. 
      (* right case *)
        unfold NashEq. intros. generalize (Nashs (sNode a left s1 s2) a).
        unfold agentConv. fold agentConv. intro cMaj. simpl in cMaj.
        apply cMaj. split. trivial. split. apply or_introl. trivial. split; apply agentConv_id. 
Qed.

End const_SeqNashEq.
