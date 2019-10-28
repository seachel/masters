
(****************************************************************
   File: Hsl_Thesis.v
   Authors: Chelsea Battell and Alberto Momigliano and Amy Felty
   Version: Coq V8.5
   Date: June 2016

   An intuitionistic sequent calculus used as a specification
   logic in the style of Abella 2.0
  ***************************************************************)


Require Export Hybrid.
Require Export Ensembles.

(*****
Ensembles documentation:
 https://coq.inria.fr/library/Coq.Sets.Ensembles.html
****)

Set Implicit Arguments.

Section Hsl.

(****************************************************************
   The intuitionistic object logic.
  ****************************************************************)

(* Variables are parameters in later uses of this SL for encoding example OLs *)

Variable atm : Set.
Variable con : Set.
Variable X : Set.

(* oo is an inductive type for constructing formulas *)

Inductive oo : Type :=
  | atom : atm -> oo
  | T : oo
  | Conj : oo -> oo -> oo
  | Imp : oo -> oo -> oo
  | All : (expr con -> oo) -> oo
  | Allx : (X -> oo) -> oo
  | Some : (expr con -> oo) -> oo.

(* prog is a parameter of OLs that is intended to represent the derivability of the assertion that an atom is implied by a formula (i.e. has type oo) *)

Variable prog : atm -> oo -> Prop.

Notation "a & b" := (Conj a b) (at level 60, right associativity).
Notation "a ---> b" := (Imp a b) (at level 61, right associativity).
Notation "<< a >>" := (atom a) (at level 30).

Notation "A :- b" := (prog A b) (at level 61).


(*** Contexts ***)

(* contexts are built on Ensembles here. We add definitions and lemmas to make it easier to work with contexts later. *)

Definition context := Ensemble oo.

Definition empty_con : context := Empty_set oo.

Definition context_cons (c : context) (o : oo) : context :=
 Add oo c o.

Definition elem (o : oo) (c : context) := In oo c o.

Notation " '{}' " := empty_con (at level 50).
Notation " c ',,' o " := (context_cons c o)
  (at level 45, left associativity).

(*** Context Lemmas ***)

(** Lemma 4.1 **)
Lemma elem_inv : forall (c : context) (o1 o2 : oo),
 elem o1 (c,, o2) -> (elem o1 c \/ o1 = o2).
Proof.
 intros c0 o F Helem;
 inversion Helem; subst.
 apply or_introl; assumption.
 apply or_intror; inversion H; reflexivity.
Qed.

(** Lemma 4.2 **)
Lemma elem_sub : forall (c : context) (o1 o2 : oo),
 elem o1 c -> elem o1 (c ,, o2).
Proof.
intros; apply Union_introl; auto.
Qed.

(** Lemma 4.3 **)
Lemma elem_self : forall (c : context) (o : oo),
 elem o (c ,, o).
Proof.
 intros; apply Union_intror;
 apply In_singleton.
Qed.

(** Lemma 4.4 **)
Lemma elem_rep : forall (c : context) (o1 o2 : oo),
 elem o1 (c,, o2,, o2) -> elem o1 (c ,, o2).
Proof.
 intros c t1 t2 H;
 apply elem_inv in H.
 inversion H as [Hl | Hr]; clear H; auto.
 subst; apply elem_self.
Qed.

(** Lemma 4.5 **)
Lemma context_swap : forall (c : context) (o1 o2 : oo),
(c,, o1,, o2) = (c,, o2,, o1).
Proof.
 intros.
 apply Extensionality_Ensembles.
 unfold Same_set.
 split; intros o3 H; apply elem_inv in H;
 inversion H as [H1 | H2]; subst; clear H.
 apply elem_inv in H1; inversion H1;
 subst; clear H1.
 repeat (apply elem_sub); auto.
 apply elem_self.
 apply elem_sub; apply elem_self.
 apply elem_inv in H1; inversion H1;
 subst; clear H1.
 repeat (apply elem_sub); auto.
 apply elem_self.
 apply elem_sub; apply elem_self.
Qed.

Definition context_subset (L1 L2 : context) :=
 forall (o : oo), elem o L1 -> elem o L2.

(** Lemma 4.6 **)
Lemma context_sub_sup : forall (L1 L2 : context) (o : oo),
 context_subset L1 L2 -> context_subset (L1,, o) (L2,, o).
Proof.
Hint Resolve elem_sub elem_self.
intros L1 L2 o H o0 Helem.
apply elem_inv in Helem; inversion Helem;
clear Helem; subst; auto.
Qed.



(*** Sequents ***)

(* Below is a mutually inductive type defining goal-reduction and backchaining sequents (with focusing). We don't include proof height in the definition because it isn't necessary for later proofs of structural rules. *)

Inductive grseq : context -> oo -> Prop :=
  | g_prog :    (* m=1, n=1, p=0 *)
      forall (L : context) (G : oo) (A : atm),
      (A :- G) -> grseq L G
      -> grseq L (<< A >>)
  | g_dyn :    (* m=1, n=0, p=1 *)
      forall (L : context) (D : oo) (A : atm),
      elem D L -> bcseq L D A
      -> grseq L (<< A >>)
  | g_tt :    (* m=0, n=0, p=0 *)
      forall (L : context), grseq L T
  | g_and :    (* m=0, n=2, p=0 *)
      forall (L : context) (G1 G2 : oo),
      grseq L G1 -> grseq L G2
      -> grseq L (G1 & G2)
  | g_imp :    (* m=0, n=1, p=0 *)
      forall (L : context) (D G : oo),
      grseq (L,, D) G
      -> grseq L (D ---> G)
  | g_all :    (* m=0, n=1, p=0 *)
      forall (L : context) (G : expr con -> oo),
      (forall E : expr con, proper E -> grseq L (G E))
      -> grseq L (All G)
  | g_allx :    (* m=0, n=1, p=0 *)
      forall (L : context) (G : X -> oo),
      (forall E : X, grseq L (G E))
      -> grseq L (Allx G)
  | g_some :    (* m=1, n=1, p=0*)
      forall (L : context) (G : expr con -> oo) (E : expr con),
      proper E -> grseq L (G E)
      -> grseq L (Some G)

with bcseq : context -> oo ->  atm -> Prop :=
 | b_match :    (* m=0, n=0, p=0 *)
     forall (L : context) (A : atm),
     bcseq L (<< A >>) A
 | b_and1 :    (* m=0, n=0, p=1 *)
     forall (L : context) (D1 D2 : oo) (A : atm),
     bcseq L D1 A
     -> bcseq L (D1 & D2) A
 | b_and2 :    (* m=0, n=0, p=1 *)
     forall (L : context) (D1 D2 : oo) (A : atm),
     bcseq L D2 A
     -> bcseq L (D1 & D2) A
 | b_imp :    (* m=0, n=1, p=1 *)
      forall (L : context) (D G : oo) (A : atm),
      grseq L G -> bcseq L D A
     -> bcseq L (G ---> D) A
 | b_all :    (* m=1, n=0, p=1 *)
     forall (L : context) (D : expr con -> oo) (E : expr con) (A : atm),
     proper E -> bcseq L (D E) A
     -> bcseq L (All D) A
 | b_allx :    (* m=0, n=0, p=1 *)
     forall (L : context) (D : X -> oo) (E : X) (A : atm),
     bcseq L (D E) A
     -> bcseq L (Allx D) A
 | b_some :    (* m=0, n=0, p=1 *)
     forall (L : context) (D : expr con -> oo) (A : atm),
     (forall E : expr con, proper E -> bcseq L (D E) A)
     -> bcseq L (Some D) A.

Tactic Notation "inv_and_sub" tactic(h) :=
  inversion h; subst; clear h; try trivial.


(* Minimality - used to define induction principle for mutually inductive type *)

Scheme gr_bc_seq := Minimality for grseq Sort Prop
  with bc_gr_seq := Minimality for bcseq Sort Prop.

Combined Scheme seq_mutind from gr_bc_seq, bc_gr_seq.


(* Monotonicity - covers weakening, contraction and exchange *)

(*
uses con_sub_sup :
 con_subset L1 L2 -> con_subset (L1,, o) (L2,, o)
*)
(** Theorem 5.7 **)
Theorem monotone :
 ((forall (L1 : context) (G : oo),
   grseq L1 G ->
    (forall (L2 : context),
      context_subset L1 L2 -> grseq L2 G))) /\
 ((forall (L1 : context) (G : oo) (A : atm),
   bcseq L1 G A ->
    (forall L2 : context,
      context_subset L1 L2 -> bcseq L2 G A))).
Proof.
Hint Resolve context_sub_sup.
eapply seq_mutind; intros;
try (econstructor; eauto; eassumption).
Qed.

Corollary gr_monotone :
forall (L1 L2 : context) (G : oo),
 context_subset L1 L2 -> grseq L1 G ->  grseq L2 G.
Proof.
intros L1 L2 G H1 H2;
revert L1 G H2 L2 H1;
apply monotone.
Qed.

Corollary bc_monotone :
forall (L1 L2 : context) (G : oo) (A : atm),
 context_subset L1 L2 -> bcseq L1 G A ->  bcseq L2 G A.
Proof.
intros L1 L2 G A H1 H2;
revert L1 G A H2 L2 H1;
apply monotone.
Qed.

(** Theorem 5.1 **)
Corollary gr_weakening : forall (L : context) (G1 G2 : oo),
 grseq L G2 -> grseq (L,, G1) G2.
Proof.
intros; eapply gr_monotone;
 [ intros o He; apply elem_sub; eassumption
 | eassumption ].
Qed.

(** Theorem 5.2 **)
Corollary bc_weakening : forall (L : context) (G1 G2 : oo) (A : atm),
 bcseq L G2 A -> bcseq (L,, G1) G2 A.
Proof.
intros; eapply bc_monotone;
 [ intros o He; apply elem_sub; eassumption
 | eassumption ].
Qed.

Corollary weakening :
(forall (L : context) (G1 G2 : oo),
 grseq L G2 -> grseq (L,, G1) G2) /\
(forall (L : context) (G1 G2 : oo) (A : atm),
 bcseq L G2 A -> bcseq (L,, G1) G2 A).
Proof.
apply conj; [apply gr_weakening | apply bc_weakening].
Qed.

(** Theorem 5.3 **)
Corollary gr_contraction : forall (L : context) (G1 G2 : oo),
 grseq (L,, G1,, G1) G2 -> grseq (L,, G1) G2.
Proof.
intros; eapply gr_monotone;
try eassumption.
intros o He; apply elem_rep; auto.
Qed.

(** Theorem 5.4 **)
Corollary bc_contraction : forall (L : context) (G1 G2 : oo) (A : atm),
 bcseq (L,, G1,, G1) G2 A -> bcseq (L,, G1) G2 A.
Proof.
intros; eapply bc_monotone;
try eassumption.
intros o He; apply elem_rep; auto.
Qed.

Corollary contraction :
(forall (L : context) (G1 G2 : oo),
 grseq (L,, G1,, G1) G2 -> grseq (L,, G1) G2) /\
(forall (L : context) (G1 G2 : oo) (A : atm),
 bcseq (L,, G1,, G1) G2 A -> bcseq (L,, G1) G2 A).
Proof.
apply conj; [apply gr_contraction | apply bc_contraction].
Qed.

(** Theorem 5.5 **)
Corollary gr_exchange : forall (L : context) (G1 G2 G3 : oo),
 grseq (L,, G2,, G1) G3 -> grseq (L,, G1,, G2) G3.
Proof.
intros; eapply gr_monotone;
try eassumption;
intros o He;
rewrite context_swap; auto.
Qed.

(** Theorem 5.6 **)
Corollary bc_exchange : forall (L : context) (G1 G2 G3 : oo) (A : atm),
 bcseq (L,, G2,, G1) G3 A -> bcseq (L,, G1,, G2) G3 A.
Proof.
intros; eapply bc_monotone;
try eassumption;
intros o He;
rewrite context_swap; auto.
Qed.

Corollary exchange :
(forall (L : context) (G1 G2 G3 : oo),
 grseq (L,, G2,, G1) G3 -> grseq (L,, G1,, G2) G3) /\
(forall (L : context) (G1 G2 G3 : oo) (A : atm),
 bcseq (L,, G2,, G1) G3 A -> bcseq (L,, G1,, G2) G3 A).
Proof.
apply conj; [apply gr_exchange | apply bc_exchange].
Qed.


Corollary monotone_cor : forall (L : context) (G : oo) (A : atm),
 bcseq L G A -> grseq (L,, G) (<<A>>).
Proof.
intros; eapply g_dyn;
 [ apply elem_self | apply bc_weakening; auto ].
Qed.


Theorem grseq_specialization :
  forall (L : context) (G : expr con -> oo),
  grseq L (All G) -> forall (E : expr con), proper E -> grseq L (G E).
Proof.
intros L G H0 E H1.
inversion H0. subst.
apply H3; auto.
Qed.

Theorem bcseq_specialization :
  forall (L : context) (G : expr con -> oo) (A : atm),
  bcseq L (Some G) A -> forall (E : expr con), proper E -> bcseq L (G E) A.
Proof.
intros L G A H0 E H1.
inv_and_sub H0.
auto.
Qed.


Theorem Xseq_specialization :
  forall (L : context) (G : X -> oo),
  grseq L (Allx G) -> forall (E : X), grseq L (G E).
Proof.
intros L G H0 E.
inversion H0; subst; auto.
Qed.


(* Cut *)

Lemma pre_cut : forall o1 : oo,
(forall (L0 : context) (o2 : oo),
 grseq L0 o2 ->
  forall (L : context),
   grseq L o1 -> L0 = (L,, o1) -> grseq L o2)
/\
(forall (L0 : context) (o2 : oo) (a : atm),
 bcseq L0 o2 a ->
  forall (L : context),
   grseq L o1 ->
    L0 = (L,, o1) -> bcseq L o2 a).
Proof.
Hint Resolve gr_weakening context_swap.
induction o1;
eapply seq_mutind;
intros; subst;
try (econstructor; eauto; eassumption).

(* Case : o1 = <a>, g_dyn, D = o1 *)

apply elem_inv in H;
inversion H; subst; clear H.
eapply g_dyn; eauto.

inversion H0; subst; auto.

(* Case : o1 = T, g_dyn, D = o1 *)

apply elem_inv in H;
inversion H; subst; clear H.
eapply g_dyn; eauto.

inversion H0; subst; auto.

(* Case : o1 = o1_1 & o1_2, g_dyn, D = o1 *)

apply elem_inv in H;
inversion H; subst; clear H.
eapply g_dyn; eauto.

generalize (H1 L0 H2 eq_refl); intro Hb.
inversion H2; subst.
inversion Hb; subst.

eapply IHo1_1; auto;
apply monotone_cor; auto.

eapply IHo1_2; auto;
apply monotone_cor; auto.

(* Case : o1 = o1_1 ---> o1_2, g_dyn, D = o1 *)

apply elem_inv in H;
inversion H; subst; clear H.
eapply g_dyn; eauto.

generalize (H1 L0 H2 eq_refl); intro Hb.
inversion Hb; subst.
inversion H2; subst.
eapply IHo1_2; auto.
apply monotone_cor; auto.
eapply IHo1_1; auto; eassumption.

(* Case : o1 = All o, g_dyn, D = o1 *)

apply elem_inv in H0;
inversion H0; subst; clear H0.
eapply g_dyn; eauto.

generalize (H2 L0 H3 eq_refl); intro Hb.
inversion Hb; subst.
inversion H3; subst.
eapply H; auto.
apply monotone_cor; eassumption.
auto.

(* Case : o1 = Allx o, g_dyn, D = o1 *)

apply elem_inv in H0;
inversion H0; subst; clear H0.
eapply g_dyn; eauto.

generalize (H2 L0 H3 eq_refl); intro Hb.
inversion Hb; subst.
inversion H3; subst.
eapply H; auto.
apply monotone_cor; eassumption.

(* Case : o1 = Some o, g_dyn, D = o1 *)

apply elem_inv in H0;
inversion H0; subst; clear H0.
eapply g_dyn; eauto.

generalize (H2 L0 H3 eq_refl); intro Hb.
inversion Hb; subst.
inversion H3; subst.
apply H5 in H4.
eapply H; auto.
apply monotone_cor; eassumption.
auto.

Qed.


Lemma gr_cut : forall (L : context) (o1 o2 : oo),
grseq (L,, o1) o2 -> grseq L o1 -> grseq L o2.
Proof.
intros; eapply pre_cut; auto; eassumption.
Qed.


Lemma bc_cut : forall (L : context) (o1 o2 : oo) (a : atm),
bcseq (L,, o1) o2 a -> grseq L o1 -> bcseq L o2 a.
Proof.
intros; eapply pre_cut; auto; eassumption.
Qed.

(** Theorem 5.8 **)
Theorem cut_admissible :
(forall (L : context) (o1 o2 : oo),
  grseq (L,, o1) o2 -> grseq L o1 -> grseq L o2) /\
(forall (L : context) (o1 o2 : oo) (a : atm),
  bcseq (L,, o1) o2 a -> grseq L o1 -> bcseq L o2 a).
Proof.
split; [apply gr_cut | apply bc_cut].
Qed.

Lemma cut_lem : forall (L : context) (o : oo) (a : atm),
grseq L o -> bcseq L o a -> grseq L (<<a>>).
Proof.
intros.
apply gr_cut with o; auto.
apply g_dyn with o.
apply elem_self.
apply bc_weakening; auto.
Qed.


Unset Implicit Arguments.

End Hsl.
