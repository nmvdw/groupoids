Require Import HoTT.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory prod_grpd sum_grpd.
From GR.groupoid.path_groupoid Require Import
     path_space.
From GR.basics Require Import
     polynomial.

(** We can apply polynomial functors to groupoids. *)
Definition poly_groupoid (G : groupoid) (P : polynomial) : groupoid.
Proof.
  induction P ; simpl.
  - exact G.
  - exact (path_space T).
  - apply prod_groupoid ; assumption.
  - apply sum_groupoid ; assumption.
Defined.