(** This file defines a groupoid quotient HIT and derives some recursion/induction principles for it. *)
Require Import HoTT.
From GR Require Import general.
From GR Require Export globe_over path_over square groupoid.

(** * The groupoid quotient over a type. *)
(** Given a type [A] and a groupoid [G], we construct a type [gquot G] such that
    we have [A -> gquot A G] and the equality of [gquot A G] is described by [G].
    We use the standard method to define the HIT
    <<
    HIT gquot G :=
     | gcl : A -> gquot G
     | gcleq : Π(a₁ a₂ : A), hom G a₁ a₂ -> gcl a₁ = gcl a₂
     | ge : Π(a : A), gcleq (e a) = idpath
     | ginv : Π(a₁ a₂ : A) (g : hom G a₁ a₂), gcleq g⁻¹ = (gcleq g)^
     | gconcat : Π(a₁ a₂ a₃ : A) (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
               gcleq (g₁ × g₂) = gcleq g₁ @ gcleq g₂
     | gtrunc : Is-1-Type (gquot G)
    >>
*)
Module Export gquot.
  Private Inductive gquot {A : Type} (G : groupoid A) :=
  | gcl : A -> gquot G.

  Arguments gcl {_} _ _.

  Axiom gcleq
    : forall {A : Type} (G : groupoid A) {a₁ a₂ : A} (g : hom G a₁ a₂),
      gcl G a₁ = gcl G a₂.

  Axiom ge
    : forall {A : Type} (G : groupoid A) (a : A),
      gcleq G (e a) = idpath.

  Axiom ginv
    : forall {A : Type} (G : groupoid A) {a₁ a₂ : A} (g : hom G a₁ a₂),
      gcleq G (inv g) = (gcleq G g)^.

  Axiom gconcat
    : forall {A : Type} (G : groupoid A)
             {a₁ a₂ a₃ : A}
             (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
      gcleq G (g₁ × g₂) = gcleq G g₁ @ gcleq G g₂.
  
  Axiom gtrunc
    : forall {A : Type} (G : groupoid A), IsTrunc 1 (gquot G).

  Section gquot_ind.
    Variable (A : Type)
             (G : groupoid A)
             (Y : gquot G -> Type)
             (gclY : forall (a : A), Y(gcl G a))
             (gcleqY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
                 path_over Y (gcleq G g) (gclY a₁) (gclY a₂))
             (geY : forall (a : A), globe_over Y
                                                (path_to_globe (ge G a))
                                                (gcleqY a a (e a))
                                                (path_over_id (gclY a)))
             (ginvY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
                 globe_over Y
                            (path_to_globe (ginv G g))
                            (gcleqY a₂ a₁ (inv g))
                            (path_over_inv (gcleqY a₁ a₂ g)))
             (gconcatY : forall (a₁ a₂ a₃ : A)
                                (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
                 globe_over Y
                            (path_to_globe (gconcat G g₁ g₂))
                            (gcleqY a₁ a₃ (g₁ × g₂))
                            (path_over_concat (gcleqY a₁ a₂ g₁)
                                              (gcleqY a₂ a₃ g₂)))
             (truncY : forall (x : gquot G), IsTrunc 1 (Y x)).

    Fixpoint gquot_ind (g : gquot G) : Y g
      := (match g with
         | gcl a => fun _ _ _ _ _ => gclY a
          end) gcleqY geY ginvY gconcatY truncY.

    Axiom gquot_ind_beta_gcleq : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
        apd_po gquot_ind (gcleq G g)
        =
        gcleqY a₁ a₂ g.
  End gquot_ind.
End gquot.

Arguments gquot_ind {A G} Y gclY gcleqY geY ginvY gconcatY truncY.

(** * Derived recursion/induction principles *)
(** The recursion principle of the HIT. *)
Section gquot_rec.
  Variable (A : Type)
           (G : groupoid A)
           (Y : Type)
           (gclY : A -> Y)
           (gcleqY : forall (a₁ a₂ : A),
               hom G a₁ a₂ -> gclY a₁ = gclY a₂)
           (geY : forall (a : A), gcleqY _ _ (e a) = idpath)
           (ginvY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
               gcleqY a₂ a₁ (inv g) = (gcleqY a₁ a₂ g)^)
           (gconcatY : forall (a₁ a₂ a₃: A) (g₁: hom G a₁ a₂) (g₂: hom G a₂ a₃),
               gcleqY _ _ (g₁ × g₂) = gcleqY _ _ g₁ @ gcleqY _ _ g₂)
           (truncY : IsTrunc 1 Y).

  Definition gquot_rec : gquot G -> Y.
  Proof.
    simple refine (gquot_ind (fun _ => Y)
                             gclY
                             (fun a₁ a₂ g => const_path_over (gcleqY a₁ a₂ g))
                             (fun a => const_globe_over
                                         (path_to_globe (ge G a))
                                         (gcleqY a a (e a))
                                         idpath
                                         (path_to_globe (geY a)))
                             _ _ _) ; cbn.
    - intros a₁ a₂ g.
      simple refine (globe_over_whisker
                       (fun _ => Y)
                       _
                       idpath
                       (const_path_over_inv _)
                       (const_globe_over
                          (path_to_globe (ginv G g))
                          (gcleqY a₂ a₁ (inv g))
                          ((gcleqY a₁ a₂ g)^)
                          (path_to_globe (ginvY a₁ a₂ g))
                       )
                    ).
    - intros a₁ a₂ a₃ g₁ g₂.
      simple refine (globe_over_whisker
                       (fun _ => Y)
                       _
                       idpath
                       (const_path_over_concat _ _)
                       (const_globe_over
                          (path_to_globe (gconcat G g₁ g₂))
                          (gcleqY a₁ a₃ (g₁ × g₂))
                          (gcleqY a₁ a₂ g₁ @ gcleqY a₂ a₃ g₂)
                          (path_to_globe (gconcatY a₁ a₂ a₃ g₁ g₂))
                       )
                    ).
  Defined.

  Definition gquot_rec_beta_gcleq (a₁ a₂ : A) (g : hom G a₁ a₂)
    : ap gquot_rec (gcleq G g) = gcleqY a₁ a₂ g.
  Proof.
    apply (const_path_over_inj (gcleq G g)).
    refine ((apd_po_const _ _)^ @ _).
    apply gquot_ind_beta_gcleq.
  Defined.
End gquot_rec.

Arguments gquot_rec {A G}.

(** If the we have a family of sets, then we can simplify the induction principle. *)
Section gquot_ind_set.
  Variable (A : Type)
           (G : groupoid A)
           (Y : gquot G -> Type)
           (gclY : forall (a : A), Y(gcl G a))
           (gcleqY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
               path_over Y (gcleq G g) (gclY a₁) (gclY a₂))
           (truncY : forall (x : gquot G), IsHSet (Y x)).

  Definition gquot_ind_set : forall (g : gquot G), Y g.
  Proof.
    simple refine (gquot_ind Y gclY gcleqY _ _ _ _)
    ; intros ; apply path_globe_over_hset ; apply _.
  Defined.

  Definition gquot_ind_set_beta_gcleq : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
      apd_po gquot_ind_set (gcleq G g)
      =
      gcleqY a₁ a₂ g.
  Proof.
    apply gquot_ind_beta_gcleq.
  Defined.
End gquot_ind_set.

Arguments gquot_ind_set {A G} Y gclY gcleqY truncY.

(** If the we have a family of propositions, then we can simplify the induction principle. *)
Section gquot_ind_prop.
  Variable (A : Type)
           (G : groupoid A)
           (Y : gquot G -> Type)
           (gclY : forall (a : A), Y(gcl G a)).
  Context `{forall (x : gquot G), IsHProp (Y x)}.

  Definition gquot_ind_prop : forall (g : gquot G), Y g.
  Proof.
    simple refine (gquot_ind_set Y gclY _ _).
    intros ; apply path_over_path_hprop ; apply _.
  Qed.
End gquot_ind_prop.

Arguments gquot_ind_prop {A G} Y gclY.

(** The double recursion principle.
    We use [gquot_rec], [gquot_ind_set] and [gquot_ind_prop] to define it.
 *)
Section gquot_double_rec.
  Variable (A B : Type)
           (G₁ : groupoid A)
           (G₂ : groupoid B)
           (Y : Type).
  Context `{IsTrunc 1 Y}
          `{Funext}.

  Variable (f : A -> B -> Y)
           (fr : forall (a : A) (b₁ b₂ : B), hom G₂ b₁ b₂ -> f a b₁ = f a b₂)
           (fre : forall (a : A) (b : B), fr a b b (e b) = idpath)
           (fri : forall (a : A) (b₁ b₂ : B) (g : hom G₂ b₁ b₂),
               fr a b₂ b₁ (inv g) = (fr a b₁ b₂ g)^)
           (frc : forall (a : A) (b₁ b₂ b₃ : B)
                         (g₁ : hom G₂ b₁ b₂) (g₂ : hom G₂ b₂ b₃),
               fr a b₁ b₃ (g₁ × g₂)
               =
               (fr a b₁ b₂ g₁) @ (fr a b₂ b₃ g₂))
           (fl : forall (a₁ a₂ : A) (b : B), hom G₁ a₁ a₂ -> f a₁ b = f a₂ b)
           (fle : forall (a : A) (b : B), fl a a b (e a) = idpath)
           (fli : forall (a₁ a₂ : A) (b : B) (g : hom G₁ a₁ a₂),
               fl a₂ a₁ b (inv g) = (fl a₁ a₂ b g)^)
           (flc : forall (a₁ a₂ a₃ : A) (b : B)
                         (g₁ : hom G₁ a₁ a₂) (g₂ : hom G₁ a₂ a₃),
               fl a₁ a₃ b (g₁ × g₂)
               =
               (fl a₁ a₂ b g₁) @ (fl a₂ a₃ b g₂))
           (fp : forall (a₁ a₂ : A) (b₁ b₂ : B)
                        (g₁ : hom G₁ a₁ a₂) (g₂ : hom G₂ b₁ b₂),
               square (fl a₁ a₂ b₂ g₁)
                      (fr a₁ b₁ b₂ g₂)
                      (fr a₂ b₁ b₂ g₂)
                      (fl a₁ a₂ b₁ g₁)).

  Definition gquot_double_rec' : gquot G₁ -> gquot G₂ -> Y.
  Proof.
    intros x y.
    simple refine (gquot_rec _ _ _ _ _ _ _ x).
    - exact (fun a => gquot_rec Y (f a) (fr a) (fre a) (fri a) (frc a) _ y).
    - intros a₁ a₂ g₁ ; simpl.
      simple refine (gquot_ind_set (fun z => _) _ _ _ y).
      + exact (fun b => fl a₁ a₂ b g₁).
      + intros b₁ b₂ g₂.
        apply map_path_over.
        refine (whisker_square idpath _ _ idpath _).
        * symmetry.
          apply gquot_rec_beta_gcleq.
        * symmetry.
          apply gquot_rec_beta_gcleq.
        * exact (fp a₁ a₂ b₁ b₂ g₁ g₂).
    - intros a.
      simple refine (gquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => fle a b).
    - intros a₁ a₂ g.
      simple refine (gquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => fli a₁ a₂ b g).
    - intros a₁ a₂ a₃ g.
      simple refine (gquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => flc a₁ a₂ a₃ b g).
  Defined.

  Definition gquot_double_rec'_beta_l_gcleq
             {a₁ a₂ : A} (b : B) (g : hom G₁ a₁ a₂)
    : ap (fun z => gquot_double_rec' z (gcl G₂ b)) (gcleq G₁ g)
      =
      fl a₁ a₂ b g.
  Proof.
    apply gquot_rec_beta_gcleq.
  Defined.

  Definition gquot_double_rec'_beta_r_gcleq
             (a : A) {b₁ b₂ : B} (g : hom G₂ b₁ b₂)
    : ap (gquot_double_rec' (gcl G₁ a)) (gcleq G₂ g)
      =
      fr a b₁ b₂ g.
  Proof.
    apply (gquot_rec_beta_gcleq _ G₂).
  Defined.

  Definition gquot_double_rec : gquot G₁ * gquot G₂ -> Y
    := uncurry gquot_double_rec'.

  Definition gquot_double_rec_point (a : A) (b : B)
    : gquot_double_rec (gcl G₁ a, gcl G₂ b) = f a b
    := idpath.

  Definition gquot_double_rec_beta_gcleq
             {a₁ a₂ : A} {b₁ b₂ : B}
             (g₁ : hom G₁ a₁ a₂) (g₂ : hom G₂ b₁ b₂)
    : ap gquot_double_rec (path_prod' (gcleq G₁ g₁) (gcleq G₂ g₂))
      =
      fl a₁ a₂ b₁ g₁ @ fr a₂ b₁ b₂ g₂.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (ap (fun p => p @ _) (gquot_rec_beta_gcleq A G₁ _ _ _ _ _ _ _ _ _ _) @ _).
    exact (ap (fun p => _ @ p) (gquot_rec_beta_gcleq B G₂ _ _ _ _ _ _ _ _ _ _)).
  Qed.

  Definition gquot_double_rec_beta_l_gcleq
             {a₁ a₂ : A} (b : B) (g : hom G₁ a₁ a₂)
    : ap gquot_double_rec (path_prod' (gcleq G₁ g) (idpath : gcl G₂ b = _))
      =
      fl a₁ a₂ b g.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (ap (fun p => p @ _) (gquot_rec_beta_gcleq A G₁ _ _ _ _ _ _ _ _ _ _) @ _).
    apply concat_p1.
  Qed.
  
  Definition gquot_double_rec_beta_r_gcleq
             (a : A) {b₁ b₂ : B} (g : hom G₂ b₁ b₂)
    : ap gquot_double_rec (path_prod' (idpath  : gcl G₁ a = _) (gcleq G₂ g))
      =
      fr a b₁ b₂ g.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (ap (fun p => _ @ p) (gquot_rec_beta_gcleq B G₂ _ _ _ _ _ _ _ _ _ _) @ _).
    apply concat_1p.
  Qed.
End gquot_double_rec.

Arguments gquot_double_rec {A B G₁ G₂} Y {_ _}.
Arguments gquot_double_rec' {A B G₁ G₂} Y {_ _}.
Arguments gquot_double_rec_beta_gcleq {A B G₁ G₂} Y {_ _}.

(** Double induction over a family of sets.
    We use the same trick as for double recursion.
 *)
Section gquot_double_ind_set.
  Variable (A B : Type)
           (G₁ : groupoid A)
           (G₂ : groupoid B)
           (Y : gquot G₁ -> gquot G₂ -> Type).
  Context `{forall (a : gquot G₁) (b : gquot G₂), IsHSet (Y a b)}
          `{Funext}.
  
  Variable (f : forall (a : A) (b : B), Y (gcl G₁ a) (gcl G₂ b))
           (fr : forall (a : A) (b₁ b₂ : B) (g : hom G₂ b₁ b₂),
               path_over (Y (gcl G₁ a)) (gcleq G₂ g) (f a b₁) (f a b₂))
           (fl : forall (a₁ a₂ : A) (b : B) (g : hom G₁ a₁ a₂),
               path_over (fun z : gquot G₁ => Y z (gcl G₂ b)) (gcleq G₁ g) (f a₁ b) (f a₂ b)).
  
  Definition gquot_double_ind_set : forall (a : gquot G₁) (b : gquot G₂), Y a b.
  Proof.
    intros x y.
    simple refine (gquot_ind_set (fun z => _) _ _ _ x).
    - exact (fun a => gquot_ind_set (fun z => _) (f a) (fr a) _ y).
    - intros a₁ a₂ g ; simpl.
      simple refine (gquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => fl a₁ a₂ b g).
  Defined.
End gquot_double_ind_set.

Arguments gquot_double_ind_set {A B G₁ G₂} Y {_ _}.

(** Double induction over a family of propositions.
    We use the same trick as before.
 *)
Section gquot_double_ind_prop.
  Variable (A B : Type)
           (G₁ : groupoid A)
           (G₂ : groupoid B)
           (Y : gquot G₁ -> gquot G₂ -> Type).
  Context `{forall (a : gquot G₁) (b : gquot G₂), IsHProp (Y a b)}
          `{Funext}.
  
  Variable (f : forall (a : A) (b : B), Y (gcl G₁ a) (gcl G₂ b)).
  
  Definition gquot_double_ind_prop : forall (a : gquot G₁) (b : gquot G₂), Y a b.
  Proof.
    intros x y.
    simple refine (gquot_ind_prop (fun z => _) _ _ x).
    exact (fun a => gquot_ind_prop (fun z => _) (f a) _ y).
  Defined.
End gquot_double_ind_prop.

Arguments gquot_double_ind_prop {A B G₁ G₂} Y.

(*
Definition gquot_encode_ind
           {A : Type}
           {G : groupoid A}
           (P : gquot G -> gquot G -> hSet)
           (p : forall (a b : A), P (gcl G a) (gcl G b) -> gcl G a = gcl G b)
           (pl : forall (a b₁ b₂ : A) (g : hom G b₁ b₂) (x : P (gcl G a) (gcl G b₂)),
               (p a b₁ (transport (fun z : gquot G => P (gcl G a) z) (geqcl G g)^ x))
                 @ geqcl G g = p a b₂ x)
           (pr : forall (a₁ a₂ b : A) (g : hom G a₁ a₂) (x : P (gcl G a₂) (gcl G b)),
               ((geqcl G g)^)
                 @ p a₁ b (transport (fun z : gquot G => P z (gcl G b)) (geqcl G g)^ x)
               =
               p a₂ b x)
           `{Funext}
  : forall (x y : gquot G), P x y -> x = y.
Proof.
  simple refine (gquot_double_ind_set (fun z₁ z₂ => P z₁ z₂ -> z₁ = z₂) _ _).
  - exact p.
  - intros a b₁ b₂ g ; simpl.
    apply path_to_path_over.
    funext x.
    refine (transport_arrow _ _ _ @ transport_paths_FlFr _ _ @ _).
    refine (ap (fun p => (p^ @ _) @ _) (ap_const _ _) @ _).
    refine (ap (fun p => p @ _) (concat_1p _) @ _).
    refine (ap (fun p => _ @ p) (ap_idmap _) @ _).
    apply pl.
  - intros a₁ a₂ b g ; simpl.
    apply path_to_path_over.
    funext x.        
    refine (transport_arrow _ _ _ @ transport_paths_FlFr _ _ @ _).
    refine (ap (fun p => (p^ @ _) @ _) (ap_idmap _) @ _).
    refine (ap (fun p => _ @ p) (ap_const _ _) @ _).
    refine (concat_p1 _ @ _).
    apply pr.
Defined.
*)

(** A special instance of double recursion for defining set-relations.
    This requires univalence, because we need to give equalities in [hSet].
    These equalities are made with [path_hset] and two functions need to be given.
    For the higher coherencies, these functions need to satisfy some laws.
 *)
Section gquot_relation.
  Variable (A B : Type)
           (G₁ : groupoid A)
           (G₂ : groupoid B)
           (R : A -> B -> hSet)
           (fl : forall (a₁ a₂ : A) (b : B), hom G₁ a₁ a₂ -> R a₁ b -> R a₂ b)
           (fr : forall (a : A) (b₁ b₂ : B), hom G₂ b₁ b₂ -> R a b₁ -> R a b₂).
  
  Context `{forall (a₁ a₂ : A) (b : B) (g : hom G₁ a₁ a₂), IsEquiv (fl a₁ a₂ b g)}
          `{forall (a : A) (b₁ b₂ : B) (g : hom G₂ b₁ b₂), IsEquiv (fr a b₁ b₂ g)}.
  Context `{Univalence}.

  Variable (fl_id : forall (a : A) (b : B), fl a a b (e a) == idmap)
           (fl_inv : forall (a₁ a₂ : A) (b : B) (g : hom G₁ a₁ a₂),
               fl a₂ a₁ b (inv g) == (fl a₁ a₂ b g)^-1)
           (fl_comp : forall (a₁ a₂ a₃ : A) (b : B) (g₁ : hom G₁ a₁ a₂) (g₂ : hom G₁ a₂ a₃),
               fl a₁ a₃ b (g₁ × g₂) == fl a₂ a₃ b g₂ o (fl a₁ a₂ b g₁))
           (fr_id : forall (a : A) (b : B), fr a b b (e b) == idmap)
           (fr_inv : forall (a : A) (b₁ b₂ : B) (g : hom G₂ b₁ b₂),
               fr a b₂ b₁ (inv g) == (fr a b₁ b₂ g)^-1)
           (fr_comp : forall (a : A) (b₁ b₂ b₃ : B) (g₁ : hom G₂ b₁ b₂) (g₂ : hom G₂ b₂ b₃),
               fr a b₁ b₃ (g₁ × g₂) == fr a b₂ b₃ g₂ o (fr a b₁ b₂ g₁))
           (fc : forall (a₁ a₂ : A) (b₁ b₂ : B)
                        (g₁ : hom G₁ a₁ a₂) (g₂ : hom G₂ b₁ b₂),
               fl a₁ a₂ b₂ g₁ o fr a₁ b₁ b₂ g₂
               ==
               fr a₂ b₁ b₂ g₂ o fl a₁ a₂ b₁ g₁
           ).

  Definition gquot_relation : gquot G₁ -> gquot G₂ -> hSet.
  Proof.
    simple refine (gquot_double_rec' _ _ _ _ _ _ _ _ _ _ _).
    - exact R.
    - exact (fun a b₁ b₂ g => path_hset (BuildEquiv _ _ (fr a b₁ b₂ g) _)).
    - intros a b ; simpl.
      refine (_ @ path_trunctype_1).
      apply path_trunctype_eq ; cbn.
      apply fr_id.
    - intros a b₁ b₂ g ; simpl.
      refine (_ @ path_trunctype_V _).
      apply path_trunctype_eq ; cbn.
      apply fr_inv.
    - intros a b₁ b₂ b₃ g₁ g₂ ; simpl.
      refine (_ @ path_trunctype_pp _ _).
      apply path_trunctype_eq ; cbn.
      apply fr_comp.
    - exact (fun a₁ a₂ b g => path_hset (BuildEquiv _ _ (fl a₁ a₂ b g) _)).
    - intros a b ; simpl.
      refine (_ @ path_trunctype_1).
      apply path_trunctype_eq ; cbn.
      apply fl_id.
    - intros a₁ a₂ b g ; simpl.
      refine (_ @ path_trunctype_V _).
      apply path_trunctype_eq ; cbn.
      apply fl_inv.
    - intros a₁ a₂ a₃ b g₁ g₂ ; simpl.
      refine (_ @ path_trunctype_pp _ _).
      apply path_trunctype_eq ; cbn.
      apply fl_comp.
    - intros a₁ a₂ b₁ b₂ g₁ g₂.
      apply path_to_square.
      refine ((path_trunctype_pp _ _)^ @ _ @ path_trunctype_pp _ _).
      apply path_trunctype_eq ; cbn.
      apply fc.
  Defined.

  Definition gquot_relation_beta_l_gcleq
             {a₁ a₂ : A} (b : B) (g : hom G₁ a₁ a₂)
    : ap (fun z => gquot_relation z (gcl G₂ b)) (gcleq G₁ g)
      =
      path_hset (BuildEquiv _ _ (fl a₁ a₂ b g) _).
  Proof.
    exact (gquot_double_rec'_beta_l_gcleq A B G₁ G₂ hSet R _ _ _ _ _ _ _ _ _ b g).
  Defined.

  Definition gquot_relation_beta_r_gcleq
             (a : A) {b₁ b₂ : B} (g : hom G₂ b₁ b₂)
    : ap (gquot_relation (gcl G₁ a)) (gcleq G₂ g)
      =
      path_hset (BuildEquiv _ _ (fr a b₁ b₂ g) _).
  Proof.
    exact (gquot_double_rec'_beta_r_gcleq A B G₁ G₂ hSet R _ _ _ _ _ _ _ _ _ a g).
  Defined.
End gquot_relation.
