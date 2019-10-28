
(****************************************************************
   File: Hsl_lists.v
   Authors: Chelsea Battell
   Date: June 2019
   Current Coq Version: V8.9.1

   An intuitionistic sequent calculus based on higher-order
   hereditary Harrop formulas used as a specification logic, for
   use in two-level Hybrid.  See:

   Amy Felty and Alberto Momigliano, "Hybrid: A Definitional Two Level
   Approach to Reasoning with Higher-Order Abstract Syntax."  Journal
   of Automated Reasoning, 48(1):43-105, 2012.

   This SL uses lists as context, unlike the earlier HSL which
   used Coq ensembles. Morphisms are now required to define equality
   of contexts.
  ***************************************************************)


Require Export Hybrid.
Require Import Setoid.

Section hsl.

Set Implicit Arguments.

(* Variables are parameters in later uses of this SL for encoding example OLs *)

Variable atm : Set.
Variable con : Set.
Variable X : Set.

(*** Type of formulas ***)

Inductive oo : Type :=
  | atom : atm -> oo
  | T : oo
  | Conj : oo -> oo -> oo
  | Imp : oo -> oo -> oo
  | All : (expr con -> oo) -> oo
  | AllX : (X -> oo) -> oo
  | Some : (expr con -> oo) -> oo.

(* prog is a parameter of OLs that is intended to represent the derivability of the assertion that an atom is implied by a formula (i.e. has type oo) *)

Variable prog : atm -> oo -> Prop.


(*** Notations ***)

Notation "a & b" := (Conj a b) (at level 60, right associativity).
Notation "a ---> b" := (Imp a b) (at level 61, right associativity).
Notation "<< a >>" := (atom a) (at level 30).

Notation "A :- b" := (prog A b) (at level 61).


(*** Contexts ***)

(* Contexts are built on lists here. We add definitions and lemmas to make it easier to work with contexts later. Definitions allow us to write cons on the right to be consistent with standard sequent context treatment, rather than standard list cons which is on the left. Morphisms allow us to create a notion of equality on contexts to treat them as sets. *)

Definition context := list oo.
Definition empty_con : context := nil.

(* Write cons with new element on the right: *)
Definition context_cons (c : context) (o : oo) : context := cons o c.

Definition elem (o : oo) (c : context) := In o c.

Notation " '{}' " := empty_con (at level 50).
Notation " c ',,' o " := (context_cons c o)
  (at level 45, left associativity).


(*** Context Lemmas ***)


(* elem version of weakening *)
Lemma elem_sub : forall (c : context) (o1 o2 : oo),
 elem o1 c -> elem o1 (c ,, o2).
Proof.
intros; right; auto.
Qed.

Lemma elem_self : forall (c : context) (o : oo),
 elem o (c ,, o).
Proof.
 intros; left; auto.
Qed.


Lemma elem_inv : forall (c : context) (o1 o2 : oo),
 elem o1 (c,, o2) <-> (elem o1 c \/ o1 = o2).
Proof.
 intros c0 o F. split; intro H.
 - inversion H; subst; simpl in H;
   rewrite or_comm; auto.
 - inversion H as [H0 | H0]; clear H.
   + apply elem_sub; auto.
   + subst; apply elem_self.
Qed.


(* elem version of contraction *)
Lemma elem_rep : forall (c : context) (o1 o2 : oo),
 elem o1 (c,, o2,, o2) -> elem o1 (c ,, o2).
Proof.
 intros c t1 t2 H;
 apply elem_inv in H.
 inversion H as [Hl | Hr]; clear H; auto.
 subst; apply elem_self.
Qed.


(* Subset for contexts; subcontext? *)
Definition context_subset (L1 L2 : context) :=
 forall (o : oo), elem o L1 -> elem o L2.

Lemma context_sub_sup : forall (L1 L2 : context) (o : oo),
 context_subset L1 L2 -> context_subset (L1,, o) (L2,, o).
Proof.
Hint Resolve elem_sub elem_self.
intros L1 L2 o H o0 Helem.
apply elem_inv in Helem; inversion Helem;
clear Helem; subst; auto.
Qed.

Lemma context_subset_swap (L : context) (o1 o2 : oo) :
  context_subset (L,, o1,, o2 ) (L,, o2,, o1).
Proof.
unfold context_subset. intros. inversion H; subst.
- apply in_cons. apply in_eq.
- inversion H0; subst.
  + apply in_eq.
  + apply in_cons. apply in_cons. apply H1.
Qed.

(* Equality of contexts *)
Definition context_equal (L1 L2 : context) :=
 context_subset L1 L2 /\ context_subset L2 L1.

(* Equivalence relation lemmas for context equality *)
Lemma context_equal_refl : forall (L : context),
  context_equal L L.
Proof.
split; intro; auto.
Qed.

Lemma context_equal_sym : forall (L1 L2 : context),
  context_equal L1 L2 -> context_equal L2 L1.
Proof.
intros L1 L2 H. inversion H; subst.
split; auto.
Qed.

Lemma context_equal_trans : forall (L1 L2 L3 : context),
  context_equal L1 L2 -> context_equal L2 L3 -> context_equal L1 L3.
Proof.
unfold context_equal; unfold context_subset. intros L1 L2 L3 H1 H2.
inversion H1 as [He1 He2]; inversion H2 as [He3 He4]; subst; clear H1; clear H2.
split; intros o H; auto.
Qed.

(* Parametric relations and morphisms for context equality *)

Add Parametric Relation : context context_equal
  reflexivity proved by context_equal_refl
  symmetry proved by context_equal_sym
  transitivity proved by context_equal_trans
  as context_equal_S.


(* Morphism to be able to rewrite the context to an equivalent one that elem is applied to *)

Add Parametric Morphism : elem
  with signature (eq) ==> (context_equal) ==> (Basics.impl)
    as context_elem_morph.
Proof.
unfold Basics.impl. intros.
unfold context_equal in H. unfold context_subset in H.
inversion H; clear H.
apply H1. auto.
Qed.


Add Parametric Morphism : context_cons
  with signature (context_equal) ==> (eq) ==> (context_equal)
    as context_cons_morph.
Proof.
intros x y Heq y0.
unfold context_equal.
split; unfold context_subset; intros o H; apply elem_inv in H.
- rewrite Heq in H; apply elem_inv in H; auto.
- rewrite <- Heq in H; apply elem_inv in H; auto.
Qed.


(*** Sequents ***)


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


(*** Weakening ***)

Corollary gr_weakening : forall (L : context) (G1 G2 : oo),
 grseq L G2 -> grseq (L,, G1) G2.
Proof.
intros; eapply gr_monotone;
 [ intros o He; apply elem_sub; eassumption
 | eassumption ].
Qed.

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



(*** Contraction ***)

Corollary gr_contraction : forall (L : context) (G1 G2 : oo),
 grseq (L,, G1,, G1) G2 -> grseq (L,, G1) G2.
Proof.
intros; eapply gr_monotone;
try eassumption.
intros o He; apply elem_rep; auto.
Qed.

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


(*** Exchange ***)

Corollary gr_exchange : forall (L : context) (G1 G2 G3 : oo),
 grseq (L,, G2,, G1) G3 -> grseq (L,, G1,, G2) G3.
Proof.
intros. eapply gr_monotone.
- apply context_subset_swap.
- auto.
Qed.

Corollary bc_exchange : forall (L : context) (G1 G2 G3 : oo) (A : atm),
 bcseq (L,, G2,, G1) G3 A -> bcseq (L,, G1,, G2) G3 A.
Proof.
intros; eapply bc_monotone.
- apply context_subset_swap.
- auto.
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


(* Cut *)

Lemma pre_cut : forall o1 : oo,
(forall (L0 : context) (o2 : oo),
 grseq L0 o2 ->
  forall (L : context),
   grseq L o1 -> context_equal L0 (L,, o1) -> grseq L o2)
/\
(forall (L0 : context) (o2 : oo) (a : atm),
 bcseq L0 o2 a ->
  forall (L : context),
   grseq L o1 ->
    context_equal L0 (L,, o1) -> bcseq L o2 a).
Proof.
Hint Resolve gr_weakening context_subset_swap.
induction o1;
eapply seq_mutind;
intros; subst;
try (econstructor; eauto; eassumption).

(* Case : o1 = <a>, g_dyn, D = o1 *)

rewrite H3 in H.
apply elem_inv in H;
inversion H; subst; clear H.
eapply g_dyn; eauto.

inversion H0; subst; auto.

(* o1 = D ---> G ... *)

econstructor. apply H0; auto.
rewrite H2; split; auto.

(* TODO: bug?: need to focus using bullets for remainder even if bulleted subcases cleared? *)

(* Case : o1 = T, g_dyn, D = o1 *)

rewrite H3 in H.
apply elem_inv in H;
inversion H; subst; clear H.
eapply g_dyn; eauto.

inversion H0; subst; auto.

(* o1 = D ---> G*)

econstructor. apply H0; auto.
rewrite H2; split; auto.

(* Case : o1 = o1_1 & o1_2, g_dyn, D = o1 *)

rewrite H3 in H.
apply elem_inv in H;
inversion H; subst; clear H.
eapply g_dyn; eauto.

generalize (H1 L0 H2 H3); intro Hb.
inversion H2; subst.
inversion Hb; subst.

eapply IHo1_1; auto.
apply monotone_cor. apply H9; auto.

reflexivity. (* why is explicit reflexivity required? not part of auto? *)

eapply IHo1_2; auto.

apply monotone_cor; auto.
apply H9.

reflexivity.

(* o1 = D ---> G*)

econstructor. apply H0; auto.
rewrite H2; split; auto.

(* Case : o1 = o1_1 ---> o1_2, g_dyn, D = o1 *)

rewrite H3 in H.
apply elem_inv in H;
inversion H; subst; clear H.
eapply g_dyn; eauto.

generalize (H1 L0 H2 H3); intro Hb.
inversion Hb; subst.
inversion H2; subst.
eapply IHo1_2; auto.
apply monotone_cor; auto.

apply H8.

eapply IHo1_1; eauto; reflexivity.

reflexivity.

(* o1 = D ---> G*)

econstructor. apply H0; auto.
rewrite H2; split; auto.

(* Case : o1 = All o, g_dyn, D = o1 *)

rewrite H4 in H0.
apply elem_inv in H0;
inversion H0; subst; clear H0.
eapply g_dyn; eauto.

generalize (H2 L0 H3 H4); intro Hb.
inversion Hb; subst.
inversion H3; subst.

Print monotone_cor.

eapply H; auto.
eapply monotone_cor; eassumption.
apply H8; eauto.
reflexivity.


(* o1 = D ---> G*)

econstructor. apply H1; auto.
rewrite H3; split; auto.

(* Case : o1 = Some o, g_dyn, D = o1 *)

rewrite H4 in H0.
apply elem_inv in H0;
inversion H0; subst; clear H0.
eapply g_dyn; eauto.

generalize (H2 L0 H3 H4); intro Hb.
inversion Hb; subst.
inversion H3; subst.
apply H6 in H5.
eapply H; auto.
apply monotone_cor; eassumption.
eassumption.

reflexivity.

(* o1 = D ---> G*)

econstructor. apply H1; auto.
rewrite H3; split; auto.

Qed.


Lemma gr_cut : forall (L : context) (o1 o2 : oo),
grseq (L,, o1) o2 -> grseq L o1 -> grseq L o2.
Proof.
intros; eapply pre_cut; try eauto; try reflexivity.
Qed.


Lemma bc_cut : forall (L : context) (o1 o2 : oo) (a : atm),
bcseq (L,, o1) o2 a -> grseq L o1 -> bcseq L o2 a.
Proof.
intros; eapply pre_cut; try eauto; try reflexivity.
Qed.

(* Proof that cut is admissible, using theorems above *)

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

End hsl.